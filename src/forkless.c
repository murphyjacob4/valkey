#include "forkless.h"
#include "server.h"
#include "bgiteration.h"
#include "mutexqueue.h"
#include "rdb.h"
#include "bio.h"
#include "module.h"

static const void *PROCESS_COMPLETE_ITEM = (void *)-1;
static const int SNAPSHOT_FILE_CLOSE_MONITOR_INTERVAL_MS = 200;
static const int REPLICATION_MONITOR_INTERVAL_MS = 100;

typedef struct {
    rio save_rio; /* Must be 1st to permit cast from rio back to forklessSaveInfo */
    int cur_db;   /* Last selectDb issued */
    bgIterator *iterator;
    uint64_t bytes_written;
    int err_code;
    mutexQueue *foreground_queue;
    bool terminated;
    int write_target;
    union {
        struct {
            sds temp_file;
            sds final_file;
        } file;
        struct {
            list *clients;
            char eofmark[RDB_EOF_MARK_SIZE];
            /* Replication aux fields and module aux (after RDB), rendered on the
             * main thread at iteration done, so the bg thread can end the RDB. */
            sds footer;
            long long done_offset; /* primary_repl_offset at iteration done */
        } repl;
    } u;
} forklessSaveInfo;

/* Keep a global indicator of the current iterator (for cancellation purposes). */
static forklessSaveInfo *currentForklessSave = NULL;

/* During a socket forkless save, incoming (live) write commands must keep
 * reaching the syncing replica. There are two channels for them, used in
 * sequence as the sync progresses:
 *
 *   1. Into the RDB stream, by the bg iterator. While the iterator is scanning
 *      the keyspace it also captures live writes and inlines them into the RDB
 *      it is generating.
 *   2. Into the shared replication backlog. When the iterator finishes, the
 *      main thread records the replication offset (forklessDoneIteratingKeyspace)
 *      and stops excluding the save's replicas from the shared buffer, so they
 *      are pinned there exactly like a WAIT_BGSAVE_END replica of a fork-based
 *      socket sync. The recorded offset is sent in the RDB aux fields, and the
 *      buffered stream is sent after the replica ACKs the RDB.
 *
 * Each live write belongs to exactly one channel: never zero (a lost write) and
 * never two (a duplicate / desync).
 *
 * This flag marks the 1 -> 2 boundary. True while the iterator still owns
 * capture (channel 1), so the save's replicas must NOT also reference the
 * shared replication buffer (see canFeedReplicaReplBuffer). Cleared on the main
 * thread when the iterator finishes. */
static bool iteratorOwnsIncomingReplication = false;

bool forklessIteratorOwnsReplication(void) {
    return iteratorOwnsIncomingReplication;
}

/* rio check_abort_between_writes callback: checks if the forkless save iterator is being terminated. */
static int forklessSaveShouldAbort(rio *r) {
    static_assert(offsetof(forklessSaveInfo, save_rio) == 0, "rio must be castable to forklessSaveInfo");
    forklessSaveInfo *saveInfo = (forklessSaveInfo *)r;
    return saveInfo->iterator && bgIteratorIsTerminating(saveInfo->iterator);
}


static int connSetBlocking(connection *conn, bool blocking) {
    int rc = (blocking) ? connBlock(conn) : connNonBlock(conn);
    if (rc == ANET_ERR) {
        serverLog(LL_WARNING, "forkless-save: error setting FD blocking(%d)", blocking);
        return C_ERR;
    }

    if (blocking) {
        if (connSendTimeout(conn, server.repl_timeout * 1000) == ANET_ERR) {
            serverLog(LL_WARNING, "forkless-save: error setting send timeout");
            return C_ERR;
        }
        if (connRecvTimeout(conn, server.repl_timeout * 1000) == ANET_ERR) {
            serverLog(LL_WARNING, "forkless-save: error setting send timeout");
            return C_ERR;
        }
    }

    return C_OK;
}

static int writeSelectDb(forklessSaveInfo *saveInfo, int new_db) {
    if (new_db == saveInfo->cur_db) return C_OK;

    if (rdbSaveType(&saveInfo->save_rio, RDB_OPCODE_SELECTDB) == -1) {
        serverLog(LL_WARNING, "forkless-save: error while writing OPCODE_SELECTDB");
        return C_ERR;
    }
    if (rdbSaveLen(&saveInfo->save_rio, new_db) == -1) {
        serverLog(LL_WARNING, "forkless-save: error while writing selectDb value");
        return C_ERR;
    }
    saveInfo->cur_db = new_db;
    return C_OK;
}

static int writeDbSizeHints(forklessSaveInfo *saveInfo) {
    for (int dbid = 0; dbid < server.dbnum; dbid++) {
        serverDb *db = server.db[dbid];
        if (db == NULL || dbSize(db) == 0) continue;
        if (writeSelectDb(saveInfo, dbid) != C_OK) return C_ERR;
        if (rdbSaveDbSizeHints(&saveInfo->save_rio, db, 0) < 0) return C_ERR;
    }
    return C_OK;
}


/* Write an inline replication command into the RDB stream using RDB_OPCODE_UPDATE.
 * The command is serialized as RESP (multi-bulk) so the replica can replay it during RDB load. */
static int writeReplicationData(forklessSaveInfo *saveInfo, bgIteratorItem *item) {
    serverAssert(item->type == BGITERATOR_ITEM_REPLICATION);

    if (rdbSaveType(&saveInfo->save_rio, RDB_OPCODE_UPDATE) == -1) return C_ERR;

    char llaux[LONG_STR_SIZE + 3];
    char llstr[LONG_STR_SIZE];
    int auxlen;

    /* Multi bulk length */
    auxlen = 0;
    llaux[auxlen++] = '*';
    auxlen += ll2string(llaux + auxlen, LONG_STR_SIZE, item->u.repl.argc);
    llaux[auxlen++] = '\r';
    llaux[auxlen++] = '\n';
    if (!rioWrite(&saveInfo->save_rio, llaux, auxlen)) return C_ERR;

    for (int i = 0; i < item->u.repl.argc; i++) {
        robj *o = item->u.repl.argv[i];
        int objlen;
        char *p;

        if (sdsEncodedObject(o)) {
            p = objectGetVal(o);
            objlen = sdslen(objectGetVal(o));
        } else {
            p = llstr;
            objlen = ll2string(p, LONG_STR_SIZE, (long)objectGetVal(o));
        }

        auxlen = 0;
        llaux[auxlen++] = '$';
        auxlen += ll2string(llaux + auxlen, LONG_STR_SIZE, objlen);
        llaux[auxlen++] = '\r';
        llaux[auxlen++] = '\n';
        if (!rioWrite(&saveInfo->save_rio, llaux, auxlen)) return C_ERR;
        if (!rioWrite(&saveInfo->save_rio, p, objlen)) return C_ERR;
        if (!rioWrite(&saveInfo->save_rio, "\r\n", 2)) return C_ERR;
    }

    return C_OK;
}

/* End a socket RDB stream: the replication and module aux fields rendered on the
 * main thread at iteration done, then the EOF opcode, checksum and EOF mark. */
static int writeSocketFooter(forklessSaveInfo *saveInfo) {
    sds footer = saveInfo->u.repl.footer;
    if (footer == NULL) {
        serverLog(LL_WARNING, "forkless-save: no replication info at iteration done");
        return C_ERR;
    }
    if (!rioWrite(&saveInfo->save_rio, footer, sdslen(footer)) ||
        rdbWriteEofAndChecksum(&saveInfo->save_rio) == C_ERR ||
        rdbWriteEofMarkEnd(&saveInfo->save_rio, saveInfo->u.repl.eofmark) == C_ERR) {
        serverLog(LL_WARNING, "forkless-save: error while writing RDB footer");
        return C_ERR;
    }
    return C_OK;
}

/* If a client is unresponsive or is being closed by the main thread, we might have to drop it
 * from the current replication activity. */
static void dropReplicaFromSaveAndQueueForMainThreadFree(forklessSaveInfo *saveInfo, client *c) {
    serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
    listNode *ln = listSearchKey(saveInfo->u.repl.clients, c);
    serverAssert(ln != NULL);
    listDelNode(saveInfo->u.repl.clients, ln);

    int remaining = listLength(saveInfo->u.repl.clients);
    if (atomic_load_explicit(&c->repl_data->forkless_pending_close, memory_order_relaxed)) {
        serverLog(LL_WARNING, "forkless-save: client(%llu) closed by primary. %d clients remain.",
                  (unsigned long long)c->id, remaining);
    } else {
        serverLog(LL_WARNING, "forkless-save: client(%llu) unresponsive. %d clients remain.",
                  (unsigned long long)c->id, remaining);
    }

    /* If the client connection is part of a connection set, remove it */
    if (rioCheckType(&saveInfo->save_rio) == RIO_TYPE_CONNSET) {
        rioFreeConnectionFromConnset(&saveInfo->save_rio, c->conn);
    }

    connSetBlocking(c->conn, false);

    /* Hand the client to the main thread for freeing. */
    mutexQueueAdd(saveInfo->foreground_queue, c);
}

/* Prunes replicas that are closing or disconnected. */
static void handleClosingClients(forklessSaveInfo *saveInfo) {
    serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
    listNode *ln;
    listIter li;
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        waitForClientIO(c);
        int pending_close = c->repl_data && atomic_load_explicit(&c->repl_data->forkless_pending_close, memory_order_relaxed);
        int connset_error = c->conn && rioCheckType(&saveInfo->save_rio) == RIO_TYPE_CONNSET &&
                            rioConnsetConnErrno(&saveInfo->save_rio, c->conn);
        if (pending_close || connset_error || !c->conn || connGetState(c->conn) != CONN_STATE_CONNECTED) {
            if (pending_close) {
                serverLog(LL_DEBUG, "forkless-save: detected pending close on client(%llu).",
                          (unsigned long long)c->id);
            } else if (connset_error) {
                serverLog(LL_WARNING, "forkless-save: client(%llu) connection error during stream, dropping.",
                          (unsigned long long)c->id);
            }
            dropReplicaFromSaveAndQueueForMainThreadFree(saveInfo, c);
        }
    }
}

/* Before writing directly to the connection, we need to wait for various buffers to drain. */
static void waitForBuffersToDrain(forklessSaveInfo *saveInfo) {
    serverAssert(!onServerMainThread());
    serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);

    listNode *ln;
    listIter li;

    monotime startTimeMono;
    elapsedStart(&startTimeMono);

    /* Give clients a chance to flush COBs */
    while (elapsedUs(startTimeMono) < (unsigned long long)server.repl_timeout * 1000000) {
        const unsigned long loopDelayUs = 100000; // 100ms
        usleep(loopDelayUs);
        atomic_thread_fence(__ATOMIC_ACQUIRE);

        handleClosingClients(saveInfo);

        listRewind(saveInfo->u.repl.clients, &li);
        bool allFlushed = true;
        while ((ln = listNext(&li)) != NULL) {
            client *c = listNodeValue(ln);
            /* Check for pending data in the COB */
            if (clientHasPendingReplies(c)) {
                allFlushed = false;
                break;
            }
        }
        if (allFlushed) break;
    }

    /* Kill off clients which still have COB data */
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        if (clientHasPendingReplies(c)) {
            serverLog(LL_WARNING, "forkless-save: socket not draining (COB), client(%llu)", (unsigned long long)c->id);
            dropReplicaFromSaveAndQueueForMainThreadFree(saveInfo, c);
        }
    }

    handleClosingClients(saveInfo);
}

/* Waits until all of the COBs have drained and transitions the RIO to a CONNSET.
 *
 * Two reasons for the transition:
 *   1. The COB send path is driven by the main-thread event loop, so it can't be
 *      used from the background save thread. There is also no need to: the bg
 *      thread's only job is to stream the DB, so it is fine with blocking writes
 *      straight to the sockets.
 *   2. We may be streaming to more than one replica at once, so we transition to
 *      a CONNSET (connection set) to abstract writing the same bytes to N sockets.
 *
 * Returns:  C_OK - successful transition, saveInfo->save_rio is now a CONNSET
 *           C_ERR - failure, saveInfo->save_rio is still ReplicaCOB */
static int transitionRioReplicaCobToRioConnset(forklessSaveInfo *saveInfo) {
    serverAssert(!onServerMainThread());
    serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);

    /* Drain the existing COB data before switching (e.g. the +FULLRESYNC handshake
     * reply already queued on the socket) so the RDB stream stays in order. */
    waitForBuffersToDrain(saveInfo);

    listNode *ln;
    listIter li;

    /* Set remaining clients to blocking */
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        if (connSetBlocking(c->conn, true) == C_ERR) {
            dropReplicaFromSaveAndQueueForMainThreadFree(saveInfo, c);
        }
    }

    /* Hopefully we still have some clients left */
    int numConns = listLength(saveInfo->u.repl.clients);
    if (numConns == 0) return C_ERR;

    /* At this point, we are done with ReplicaCOB RIO. */
    uint64_t current_cksum = saveInfo->save_rio.cksum;
    size_t current_processed_bytes = saveInfo->save_rio.processed_bytes;
    rioFreeReplicaCOB(&saveInfo->save_rio);

    connection **conns = zmalloc(sizeof(connection *) * numConns);
    listRewind(saveInfo->u.repl.clients, &li);
    int pos = 0;
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        conns[pos++] = c->conn;
    }

    rioInitWithConnset(&saveInfo->save_rio, conns, numConns);
    saveInfo->save_rio.cksum = current_cksum;
    saveInfo->save_rio.processed_bytes = current_processed_bytes;
    if (server.rdb_checksum) {
        saveInfo->save_rio.update_cksum = rioGenericUpdateChecksum;
    }

    zfree(conns);
    return C_OK;
}

/* Entry point for background thread.
 * Upon entering:
 *  - The RDB header has been written (magic, aux fields, functions)
 *  - The DB size hints have been written
 * This function is responsible for writing all of the dictionary entries. */
static void *forklessSaveProcessor(void *arg) {
    serverAssert(!onServerMainThread());
    forklessSaveInfo *saveInfo = arg;

    /* Pin this background save thread to the configured bgsave CPU list, the
     * same way the fork-based bgsave child does */
    serverSetCpuAffinity(server.bgsave_cpulist);

    serverLog(LL_NOTICE, "forkless-save: background processor started");
    int err = C_OK;

    bool rioIsConnset = false;
    if (saveInfo->write_target == RDB_WRITE_TARGET_SOCKET) {
        err = transitionRioReplicaCobToRioConnset(saveInfo);
        rioIsConnset = (err == C_OK);
        serverLog(LL_DEBUG, "forkless-save: transition to connset %s, %d clients remain",
                  rioIsConnset ? "OK" : "FAILED", (int)listLength(saveInfo->u.repl.clients));
    }

    saveInfo->save_rio.check_abort_between_writes = forklessSaveShouldAbort;

    const unsigned statsIntervalMs = 1000;
    monotime lastStatsTime;
    elapsedStart(&lastStatsTime);

    bool done = false;
    bool terminated = false;
    long items = 0;
    while (!done && err == C_OK) {
        bgIteratorItem *item = bgIteratorRead(saveInfo->iterator);

        if (saveInfo->write_target == RDB_WRITE_TARGET_SOCKET) {
            handleClosingClients(saveInfo);
            if (listLength(saveInfo->u.repl.clients) == 0) {
                serverLog(LL_WARNING, "forkless-save: all replicas disconnected, aborting");
                err = C_ERR;
                break;
            }
        }

        switch (item->type) {
        case BGITERATOR_ITEM_COMPLETE:
            done = true;
            if (saveInfo->write_target == RDB_WRITE_TARGET_SOCKET) {
                /* forklessDoneIteratingKeyspace rendered the footer on the main
                 * thread, in the same step that queued this item. */
                serverAssert(saveInfo->u.repl.footer == NULL ||
                             item->u.master_repl_offset == saveInfo->u.repl.done_offset);
                err = writeSocketFooter(saveInfo);
            }
            break;

        case BGITERATOR_ITEM_TERMINATED:
            terminated = true;
            done = true;
            break;

        case BGITERATOR_ITEM_DBENTRY:
            if ((err = writeSelectDb(saveInfo, item->dbid)) == C_ERR) break;
            items++;

            robj key;
            initStaticStringObject(key, objectGetKey(item->u.dbe.de));
            robj *o = item->u.dbe.de;

            long long expire = objectGetExpire(item->u.dbe.de);
            if (rdbSaveKeyValuePair(&saveInfo->save_rio, &key, o, expire, item->dbid, RDB_VERSION) == -1) {
                serverLog(LL_WARNING, "forkless-save: error writing KV pair");
                err = C_ERR;
            }
            break;

        case BGITERATOR_ITEM_REPLICATION:
            serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
            if ((err = writeSelectDb(saveInfo, item->dbid)) == C_ERR) break;
            err = writeReplicationData(saveInfo, item);
            break;

        case BGITERATOR_ITEM_SWAPDB:
            /* Should only get SWAPDB for inconsistent (replication) iteration. */
            serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
            /* Iterator tracks swapdb internally; no special action needed. */
            break;

        case BGITERATOR_ITEM_FLUSHDB:
            /* Should only get FLUSHDB for inconsistent (replication) iteration. */
            serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
            /* Flush command will be replicated via the replication stream. */
            break;

        default:
            /* bgIteration may deliver item types that are not necessarily relevant to us.
             * New types may also be added in the future. It is the client's responsibility
             * to filter out irrelevant types, so we simply ignore them here. */
            break;
        }

        if (elapsedMs(lastStatsTime) >= statsIntervalMs) {
            elapsedStart(&lastStatsTime);
            atomic_store_explicit(&server.stat_current_save_keys_processed, items, memory_order_relaxed);
        }
    }

    if (err != C_OK && bgIteratorIsTerminating(saveInfo->iterator) && !rioGetWriteError(&saveInfo->save_rio)) {
        /* The write returned an error because the abort check stopped it, not
         * from a real I/O failure (no RIO write error is set). Treat it as a
         * cancel. */
        terminated = true;
        err = C_OK;
    }

    char *message = "";
    if (terminated)
        message = "TERMINATED";
    else if (err != C_OK)
        message = "***ERROR***";
    serverLog(LL_NOTICE, "forkless-save: background processor finished. %ld items processed. %s",
              items, message);

    /* For socket saves the bg thread has written the whole RDB, including the
     * footer and EOF mark. Return the connections to the main thread. */
    if (saveInfo->write_target == RDB_WRITE_TARGET_SOCKET) {
        if (!terminated && err == C_OK) {
            if (!rioFlush(&saveInfo->save_rio)) err = C_ERR;
            /* Don't put replicas whose final writes failed online. */
            if (rioIsConnset) handleClosingClients(saveInfo);
        }

        saveInfo->bytes_written = saveInfo->save_rio.processed_bytes;

        /* Return clients to non-blocking IO. */
        listNode *ln;
        listIter li;
        listRewind(saveInfo->u.repl.clients, &li);
        while ((ln = listNext(&li)) != NULL) {
            client *c = listNodeValue(ln);
            if (connSetBlocking(c->conn, false) == C_ERR) {
                dropReplicaFromSaveAndQueueForMainThreadFree(saveInfo, c);
            }
        }

        if (rioIsConnset) {
            rioFreeConnset(&saveInfo->save_rio);
        } else {
            /* Error before transitioning to connset — still a COB rio. */
            rioFreeReplicaCOB(&saveInfo->save_rio);
        }
    }

    saveInfo->err_code = err;
    bgIteratorClose(saveInfo->iterator);
    return NULL;
}

/* After the bg thread finishes, some clients may have been marked for close
 * (e.g., by the main thread's freeClient path). Remove them from the client
 * list so we don't try to finish the RDB stream to dead connections. */
static void freeClientsMarkedForCloseAfterBgThreadStopped(forklessSaveInfo *saveInfo) {
    serverAssert(onServerMainThread());

    listNode *ln;
    listIter li;
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        if (c->repl_data && atomic_load_explicit(&c->repl_data->forkless_pending_close, memory_order_relaxed)) {
            listDelNode(saveInfo->u.repl.clients, ln);
            c->flag.forkless_managed = 0;
            atomic_store_explicit(&c->repl_data->forkless_pending_close, 0, memory_order_relaxed);
            c->repl_data->using_cob = 0;
            freeClient(c);
        }
    }
}


static void resumeRegularReplicaActivity(client *c) {
    serverAssert(onServerMainThread());


    connSetBlocking(c->conn, false);

    c->flag.forkless_managed = 0;
    c->repl_data->using_cob = 0;

    /* Since this is a replica client, re-register with priority */
    connSetReadHandler(c->conn, readQueryFromClient);
    connSetPrivateData(c->conn, c);
}

static void resumeClientsAndFreeClientList(forklessSaveInfo *saveInfo, bool successful) {
    serverAssert(onServerMainThread());

    listNode *ln;
    listIter li;
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        if (successful) {
            serverLog(LL_NOTICE, "forkless-save: resuming regular activity for client(%llu)", (unsigned long long)c->id);
            resumeRegularReplicaActivity(c);
        } else {
            serverLog(LL_NOTICE, "forkless-save: error or canceled, terminating client(%llu)", (unsigned long long)c->id);
            c->flag.forkless_managed = 0;
            if (c->repl_data) c->repl_data->using_cob = 0;
            freeClient(c);
        }
    }

    listRelease(saveInfo->u.repl.clients);
    saveInfo->u.repl.clients = NULL;
}

static void cleanupSaveInfoAndEmitEndMetrics(forklessSaveInfo *saveInfo) {
    bool cancelled = saveInfo->terminated && saveInfo->err_code == C_OK;
    bool success = !saveInfo->terminated && saveInfo->err_code == C_OK;

    /* A cancel must not count as a failed save, so skip the metrics that set
     * lastbgsave_status (like the fork child's SIGUSR1 whitelist). */
    if (!cancelled && saveInfo->write_target == RDB_WRITE_TARGET_DISK) {
        rdbRecordEndMetrics(RDB_BGSAVE_TYPE_FORKLESS, saveInfo->err_code, time(NULL));
    }
    /* startSaving() fired the persistence start event in this process, so a
     * terminal event must be emitted even on cancel to balance it. */
    stopSaving(success);
    /* Finalize the save state in any case. */
    rdbClearSaveState(time(NULL));

    if (cancelled) {
        serverLog(LL_WARNING, "forkless-save: forkless save cancelled. %lld seconds.", (long long)server.rdb_save_time_last);
    } else if (success) {
        serverLog(LL_NOTICE, "forkless-save: forkless save complete. %lld seconds.", (long long)server.rdb_save_time_last);
    } else {
        serverLog(LL_WARNING, "forkless-save: forkless save failed. %lld seconds.", (long long)server.rdb_save_time_last);
    }

    /* Notify replicas waiting for BGSAVE to complete */
    updateReplicasWaitingBgsave(success ? C_OK : C_ERR, saveInfo->write_target);

    currentForklessSave = NULL;
    iteratorOwnsIncomingReplication = false;
    atomic_store_explicit(&server.stat_current_save_keys_processed, 0, memory_order_relaxed);
    atomic_store_explicit(&server.stat_current_save_keys_total, 0, memory_order_relaxed);

    serverAssert(saveInfo->u.file.temp_file == NULL);
    zfree(saveInfo);
}

/* Routine for background thread to close and rename the forkless save snapshot file.
 * Closing the file requires synchronously flushing the content to disk, which can
 * take some time. */
static void forklessSaveCloseSnapshotFile(void *args[]) {
    serverAssert(!onServerMainThread());
    forklessSaveInfo *saveInfo = (forklessSaveInfo *)args[0];
    /* Error or not, close the file... */
    /* Flush the RIO buffer to the OS before fsync, otherwise any bytes still
     * buffered (including the tail written after the last autosync boundary and
     * the RDB footer) are not covered by the fsync below. */
    if (rioFlush(&saveInfo->save_rio) == 0) {
        serverLog(LL_WARNING, "forkless-save: error flushing temp file [%s]: %s",
                  saveInfo->u.file.temp_file, strerror(errno));
        saveInfo->err_code = C_ERR;
    }
    if (valkey_fsync(fileno(saveInfo->save_rio.io.file.fp)) != 0) {
        serverLog(LL_WARNING, "forkless-save: error fsyncing temp file [%s]: %s",
                  saveInfo->u.file.temp_file, strerror(errno));
        saveInfo->err_code = C_ERR;
    }
    if (fclose(saveInfo->save_rio.io.file.fp) != 0) {
        serverLog(LL_WARNING, "forkless-save: error closing temp file [%s]: %s",
                  saveInfo->u.file.temp_file, strerror(errno));
        saveInfo->err_code = C_ERR;
    }

    if (!saveInfo->terminated && saveInfo->err_code == C_OK) {
        if (rename(saveInfo->u.file.temp_file, saveInfo->u.file.final_file) != 0) {
            serverLog(LL_WARNING, "forkless-save: error moving temp file [%s] to destination [%s]: %s",
                      saveInfo->u.file.temp_file, saveInfo->u.file.final_file, strerror(errno));
            saveInfo->err_code = C_ERR;
        } else if (fsyncFileDir(saveInfo->u.file.final_file) != 0) {
            /* fsync the directory so the rename itself survives a crash. */
            serverLog(LL_WARNING, "forkless-save: error syncing directory for [%s]: %s",
                      saveInfo->u.file.final_file, strerror(errno));
            saveInfo->err_code = C_ERR;
        }
    }

    if (saveInfo->terminated || saveInfo->err_code != C_OK) {
        bg_unlink(saveInfo->u.file.temp_file);
    }
    sdsfree(saveInfo->u.file.temp_file);
    sdsfree(saveInfo->u.file.final_file);
    saveInfo->u.file.temp_file = NULL;
    saveInfo->u.file.final_file = NULL;
    /* Notify the main thread that I am done closing the file. */
    mutexQueueAdd(saveInfo->foreground_queue, (void *)PROCESS_COMPLETE_ITEM);
}

/* Timer proc which runs in the main valkey event loop. It monitors to see when the background thread
 * completes the action to close and rename the snapshot file at the end of disk based forkless save,
 * and performs the final clean-up actions. */
static long long snapshotEndMonitorTimeProc(struct aeEventLoop *eventLoop, long long id, void *clientData) {
    UNUSED(eventLoop);
    UNUSED(id);
    serverAssert(onServerMainThread());

    forklessSaveInfo *saveInfo = (forklessSaveInfo *)clientData;

    /* I own this mutex queue from the main thread, check to see if the background
       job is done or not. Note we only expect a single notification event here. */
    if (mutexQueuePop(saveInfo->foreground_queue, false) != NULL) {
        mutexQueueRelease(saveInfo->foreground_queue);
        saveInfo->foreground_queue = NULL;
        cleanupSaveInfoAndEmitEndMetrics(saveInfo);
        return AE_NOMORE;
    }
    return SNAPSHOT_FILE_CLOSE_MONITOR_INTERVAL_MS;
}


/* Retire a replica client that is owned by a forkless save from the server's
 * replication tracking. The client object is left alive (the forkless save is
 * still using its connection) and will be freed later by the save; this only
 * removes it from the shared replica state so the rest of the server stops
 * treating it as an attached replica: it is taken out of
 * server.replicas / server.monitors, the derived replica counters are
 * refreshed, its replica/monitor flags are cleared and its referenced
 * replication buffer is released. */
void retireForklessManagedReplica(client *c) {
    list *client_list = (c->flag.monitor) ? server.monitors : server.replicas;
    listNode *ln = listSearchKey(client_list, c);
    serverAssert(ln != NULL);
    listDelNode(client_list, ln);

    if (!(c->flag.monitor)) {
        if (listLength(server.replicas) == 0) server.repl_no_replicas_since = server.unixtime;
        refreshGoodReplicasCount();
    }
    c->flag.replica = 0;
    c->flag.monitor = 0;

    freeReplicaReferencedReplBuffer(c);
}

/* Free a replica the bg thread abandoned onto the foreground queue: clear the
 * forkless flags, reset its repl state, and free it. Runs on the main thread. */
static void freeAbandonedForklessReplica(client *c) {
    serverAssert(onServerMainThread());
    serverLog(LL_WARNING, "forkless-save: client(%llu) ended replication early", (unsigned long long)c->id);
    c->flag.forkless_managed = 0;
    if (c->repl_data) {
        atomic_store_explicit(&c->repl_data->forkless_pending_close, 0, memory_order_relaxed);
        c->repl_data->using_cob = 0;
        c->repl_data->repl_state = REPL_STATE_NONE;
    }
    freeClient(c);
}

static void forklessSaveComplete(bool terminated, void *privdata) {
    serverAssert(onServerMainThread());
    serverLog(LL_NOTICE, "forkless-save: completion proc - %s", (terminated) ? "terminated" : "ok");

    forklessSaveInfo *saveInfo = privdata;
    saveInfo->terminated = terminated;
    /* The save iterator should be terminated and freed at this point in time. */
    saveInfo->iterator = NULL;
    currentForklessSave = NULL;
    iteratorOwnsIncomingReplication = false;

    if (saveInfo->write_target == RDB_WRITE_TARGET_SOCKET) {
        /* Abandoned forkless replicas are usually freed by the timer proc, but
         * drain the queue here too: anything queued after the last timer tick and
         * before this sync completion must be freed now. */
        if (saveInfo->foreground_queue) {
            void *item;
            while ((item = mutexQueuePop(saveInfo->foreground_queue, false)) != NULL) {
                freeAbandonedForklessReplica((client *)item);
            }
        }

        /* Get rid of any clients which may have been closed after the bg thread completed. */
        freeClientsMarkedForCloseAfterBgThreadStopped(saveInfo);
        if (listLength(saveInfo->u.repl.clients) == 0) saveInfo->terminated = true;

        /* The bg thread already wrote the whole RDB (including the footer) and
         * freed its rio. The remaining replicas go online through the same path
         * as a fork-based socket sync (updateReplicasWaitingBgsave): the stream
         * buffered in the shared backlog since iteration done is sent after
         * their first REPLCONF ACK. */
        sdsfree(saveInfo->u.repl.footer);
        saveInfo->u.repl.footer = NULL;

        resumeClientsAndFreeClientList(saveInfo, !saveInfo->terminated && saveInfo->err_code == C_OK);

        /* Shut down the replication monitor timer */
        mutexQueueAdd(saveInfo->foreground_queue, (void *)PROCESS_COMPLETE_ITEM);
        saveInfo->foreground_queue = NULL;

        cleanupSaveInfoAndEmitEndMetrics(saveInfo);
    } else {
        /* For file based forkless save, we need to generate the RDB end marker. and complete the save */
        if (!saveInfo->terminated && saveInfo->err_code == C_OK) {
            saveInfo->err_code = rdbWriteFooter(&saveInfo->save_rio, REPLICA_REQ_NONE) == C_ERR ? C_ERR : C_OK;
        }

        /* Done writing, capture bytes written (regardless of pass/fail) */
        saveInfo->bytes_written = saveInfo->save_rio.processed_bytes;

        /* Start a cron job to check for the background job completion */
        aeCreateTimeEvent(server.el, SNAPSHOT_FILE_CLOSE_MONITOR_INTERVAL_MS, snapshotEndMonitorTimeProc, saveInfo, NULL);
        /* Submit a background job to close and rename the snapshot file */
        saveInfo->foreground_queue = mutexQueueCreate(); // The monitor proc will delete this
        bioCreateLazyFreeJob(forklessSaveCloseSnapshotFile, 1, saveInfo);
        serverLog(LL_NOTICE, "forkless-save: created background thread to perform snapshot file close and rename");
        /* We will now wait for the background closeSnapshotFile job to complete.
         * The remainder of the cleanup will be performed in the snapshotEndMonitorTimeProc. */
    }
}

static int forklessSaveCommonStart(forklessSaveInfo *saveInfo) {
    serverAssert(onServerMainThread());

    saveInfo->cur_db = -1;

    serverLog(LL_NOTICE, "Using forkless save for next backup");
    rdbRecordStartMetrics(RDB_BGSAVE_TYPE_FORKLESS, saveInfo->write_target);
    startSaving(RDBFLAGS_FORKLESS_SAVE);

    rdbSaveInfo rsi, *rsiptr = rdbPopulateSaveInfo(&rsi);
    if (rdbWriteHeader(&saveInfo->save_rio, REPLICA_REQ_NONE, RDB_VERSION, RDBFLAGS_NONE, rsiptr) == C_ERR) return C_ERR;

    if (writeDbSizeHints(saveInfo) == C_ERR) return C_ERR;

    return C_OK;
}

static void startBackgroundThread(forklessSaveInfo *saveInfo) {
    serverAssert(onServerMainThread());

    pthread_t thread_id;
    pthread_attr_t attr;
    int pthread_rc;
    serverInitThreadAttribute(&attr);
    pthread_rc = pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    serverAssert(pthread_rc == 0);
    pthread_rc = pthread_create(&thread_id, &attr, &forklessSaveProcessor, saveInfo);
    serverAssert(pthread_rc == 0);
    pthread_rc = pthread_attr_destroy(&attr);
    serverAssert(pthread_rc == 0);
}

static void forklessMarkSaveFailed(forklessSaveInfo *saveInfo) {
    saveInfo->err_code = C_ERR;
    if (saveInfo->write_target == RDB_WRITE_TARGET_DISK) {
        rdbRecordEndMetrics(RDB_BGSAVE_TYPE_FORKLESS, C_ERR, time(NULL));
    }
    rdbClearSaveState(time(NULL));
    stopSaving(0);
    currentForklessSave = NULL;
    iteratorOwnsIncomingReplication = false;
    serverLog(LL_WARNING, "forkless-save: save failed. %lld seconds.", (long long)server.rdb_save_time_last);
}

/* Save a point-in-time snapshot to the given filename.
 * The filename must be under the server's current working directory.
 * Writes to a temp file and renames to the final filename on completion. */
int forklessSaveToDisk(const char *filename) {
    serverAssert(onServerMainThread());
    serverAssert(currentForklessSave == NULL);
    serverAssert(!isSaveInProgress());
    serverAssert(filename);
    serverLog(LL_NOTICE, "Beginning forklessSaveToDisk");

    server.stat_rdb_saves++;

    /* Use a forkless-specific name with a unique counter so the temp file can't
     * collide with a fork-based rdbSave() (same process) or another forkless
     * save. */
    char tmpfile[256];
    snprintf(tmpfile, sizeof(tmpfile), "temp-forkless-%d-%lld.rdb", (int)getpid(), (long long)server.stat_rdb_saves);

    FILE *file = fopen(tmpfile, "wb");
    if (file == NULL) {
        serverLog(LL_WARNING, "forkless-save: failed to open temp file [%s] for forkless save: %s",
                  tmpfile, strerror(errno));
        return C_ERR;
    }

    forklessSaveInfo *saveInfo = zcalloc(sizeof(forklessSaveInfo));
    saveInfo->u.file.temp_file = sdsnew(tmpfile);
    saveInfo->u.file.final_file = sdsnew(filename);
    saveInfo->write_target = RDB_WRITE_TARGET_DISK;

    rioInitWithFile(&saveInfo->save_rio, file);
    if (server.rdb_save_incremental_fsync) {
        rioSetAutoSync(&saveInfo->save_rio, REDIS_AUTOSYNC_BYTES);
        rioSetReclaimCache(&saveInfo->save_rio, 1);
    }

    int rc = forklessSaveCommonStart(saveInfo);
    if (rc != C_OK) goto werr;

    /* Saving to a file indicates a consistent snapshot (a backup at a point in time) */
    saveInfo->iterator = bgIteratorCreateFullScanIter(FORKLESS_SAVE_FILE_ITER_NAME,
                                                      BGITERATOR_CONSISTENCY_START, NULL, forklessSaveComplete, saveInfo);
    if (saveInfo->iterator == NULL) {
        serverLog(LL_WARNING, "forkless-save: error creating iterator");
        goto werr;
    }
    currentForklessSave = saveInfo;

    atomic_store_explicit(&server.stat_current_save_keys_total, dbTotalServerKeyCount(), memory_order_relaxed);
    atomic_store_explicit(&server.stat_current_save_keys_processed, 0, memory_order_relaxed);

    startBackgroundThread(saveInfo);

    /* at this point, background iteration has started (saveInfo will be freed later) */
    return C_OK;

werr:
    forklessMarkSaveFailed(saveInfo);

    if (file != NULL) {
        if (fclose(file) != 0) {
            serverLog(LL_WARNING, "forkless-save: Could not close temp file [%s]: %s",
                      saveInfo->u.file.temp_file, strerror(errno));
        }
        if (unlink(saveInfo->u.file.temp_file) != 0) {
            serverLog(LL_WARNING, "forkless-save: Could not delete temp file [%s]: %s",
                      saveInfo->u.file.temp_file, strerror(errno));
        }
    }
    sdsfree(saveInfo->u.file.temp_file);
    sdsfree(saveInfo->u.file.final_file);
    zfree(saveInfo);
    return C_ERR;
}

/* Cancels the currently running forkless save, if one is in progress. */
void forklessSaveCancel(void) {
    serverAssert(onServerMainThread());
    if (currentForklessSave == NULL) return;
    bgIteratorTerminate(currentForklessSave->iterator);
}

int isForklessSaveInProgress(void) {
    return server.cur_bgsave_type == RDB_BGSAVE_TYPE_FORKLESS;
}


/* Timer proc that runs on the main thread during socket-based forkless save.
 * The bg thread may need to abandon unresponsive replicas, but can't free
 * clients from a non-main thread. It queues them to foreground_queue, and
 * this timer frees them. Also handles the PROCESS_COMPLETE_ITEM sentinel
 * which signals the timer to stop. */
static long long replicationMonitorTimeProc(struct aeEventLoop *eventLoop, long long id, void *clientData) {
    UNUSED(eventLoop);
    UNUSED(id);
    serverAssert(onServerMainThread());

    mutexQueue *monitorQueue = clientData;

    void *item;
    while ((item = mutexQueuePop(monitorQueue, false)) != NULL) {
        if (item == PROCESS_COMPLETE_ITEM) {
            serverLog(LL_DEBUG, "forkless-save: replication monitor timer proc completing");
            mutexQueueRelease(monitorQueue);
            return AE_NOMORE;
        }

        client *c = item;
        freeAbandonedForklessReplica(c);
    }
    return REPLICATION_MONITOR_INTERVAL_MS;
}

/* Called on the main thread when the bg iterator finishes iterating all keys,
 * in the same step that queues BGITERATOR_ITEM_COMPLETE for the bg thread.
 *
 * This is the boundary between the two channels for live writes (see
 * iteratorOwnsIncomingReplication): every write up to the current replication
 * offset has been captured into the RDB stream, and every later write goes to
 * the shared replication backlog, where the save's replicas are now pinned
 * (lazily, by feedReplicationBuffer) like any WAIT_BGSAVE_END replica.
 *
 * Render the replication aux fields for that offset (and the module aux fields,
 * which need the main thread) so the bg thread can end the RDB with them. The
 * bg thread reads them after it dequeues the COMPLETE item. */
static bool forklessDoneIteratingKeyspace(void *privdata) {
    serverAssert(onServerMainThread());

    forklessSaveInfo *saveInfo = privdata;
    serverAssert(saveInfo->write_target == RDB_WRITE_TARGET_SOCKET);
    serverAssert(saveInfo->u.repl.footer == NULL);

    serverLog(LL_NOTICE, "forkless-save: replication done - primary_repl_offset: %lld",
              server.primary_repl_offset);

    rdbSaveInfo rsi;
    if (rdbPopulateSaveInfo(&rsi) != NULL) {
        rio r;
        rioInitWithBuffer(&r, sdsempty());
        if (rdbSaveAuxFieldStrInt(&r, "repl-stream-db", rsi.repl_stream_db) == -1 ||
            rdbSaveAuxFieldStrStr(&r, "repl-id", server.replid) == -1 ||
            rdbSaveAuxFieldStrInt(&r, "repl-offset", server.primary_repl_offset) == -1 ||
            rdbSaveModulesAux(&r, VALKEYMODULE_AUX_AFTER_RDB) == -1) {
            sdsfree(r.io.buffer.ptr);
        } else {
            saveInfo->u.repl.footer = r.io.buffer.ptr;
            saveInfo->u.repl.done_offset = server.primary_repl_offset;
        }
    }
    /* Without the replication info, the bg thread fails the save. */
    if (saveInfo->u.repl.footer == NULL) {
        serverLog(LL_WARNING, "forkless-save: unable to capture replication info at iteration done");
    }

    iteratorOwnsIncomingReplication = false;

    return true;
}

int forklessSaveToSockets(void) {
    serverAssert(onServerMainThread());
    serverAssert(currentForklessSave == NULL);
    serverLog(LL_NOTICE, "Beginning forklessSaveToSockets");

    forklessSaveInfo *saveInfo = zmalloc(sizeof(forklessSaveInfo));
    memset(saveInfo, 0, sizeof(forklessSaveInfo));
    saveInfo->terminated = false;
    saveInfo->write_target = RDB_WRITE_TARGET_SOCKET;

    /* Collect replicas in WAIT_BGSAVE_END state (already set up by startBgsaveForReplication) */
    saveInfo->u.repl.clients = listCreate();
    listNode *ln;
    listIter li;
    listRewind(server.replicas, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        serverAssert(c->repl_data);
        if (c->repl_data->repl_state == REPLICA_STATE_WAIT_BGSAVE_END) {
            serverLog(LL_NOTICE, "forkless-save: beginning save to client ID: %llu", (unsigned long long)c->id);
            listAddNodeTail(saveInfo->u.repl.clients, c);
            c->flag.forkless_managed = 1;
            c->repl_data->using_cob = 1;
        }
    }
    serverAssert(listLength(saveInfo->u.repl.clients) > 0);
    saveInfo->foreground_queue = NULL;

    /* Initialize RIO with ReplicaCOB. This lets the main thread write sync metadata
     * to all pending replicas through a single rioWrite() call in a non-blocking
     * manner — it places the data into each replica's Client Output Buffer (COB),
     * and the event loop flushes it to the network asynchronously.
     *
     * Later, when the background thread takes over, it waits for the COBs to drain,
     * switches the connections to blocking mode, and begins writing directly to the
     * sockets — blocking is acceptable since it's no longer on the main thread. */
    rioInitWithReplicaCOB(&saveInfo->save_rio);

    /* Write diskless sync framing before the RDB header.
     * The replica expects: $EOF:<40-byte-marker>\r\n<RDB data><marker>\r\n */
    if (rdbWriteEofMarkStart(&saveInfo->save_rio, saveInfo->u.repl.eofmark) == C_ERR) {
        serverLog(LL_WARNING, "forkless-save: error writing EOF start marker");
        goto werr;
    }

    int rc = forklessSaveCommonStart(saveInfo);
    if (rc != C_OK) goto werr;

    /* Flush the ReplicaCOB intermediate buffer into the actual COBs so the
     * background thread only needs to wait for COBs to drain. */
    if (!rioFlush(&saveInfo->save_rio)) {
        serverLog(LL_WARNING, "forkless-save: unable to flush replica COB before transition");
        goto werr;
    }

    /* Disable read handlers on replica connections. We don't want the main
     * thread processing REPLCONF ACK or other commands from replicas while
     * the bg thread is writing to their sockets. Read handlers are restored
     * in resumeRegularReplicaActivity(). */
    listRewind(saveInfo->u.repl.clients, &li);
    while ((ln = listNext(&li)) != NULL) {
        client *c = listNodeValue(ln);
        connSetReadHandler(c->conn, NULL);
    }

    /* Create a timer to process abandoned clients from the bg thread.
     * The bg thread can't free clients directly — it queues them to
     * foreground_queue, and this timer frees them on the main thread. */
    saveInfo->foreground_queue = mutexQueueCreate();
    long long timeProcId = aeCreateTimeEvent(server.el, REPLICATION_MONITOR_INTERVAL_MS,
                                             replicationMonitorTimeProc, saveInfo->foreground_queue, NULL);
    if (timeProcId == AE_ERR) {
        mutexQueueRelease(saveInfo->foreground_queue);
        saveInfo->foreground_queue = NULL;
        serverLog(LL_WARNING, "forkless-save: error creating replicationMonitorTimeProc");
        goto werr;
    }

    /* Create iterator with CONSISTENCY_EVENTUAL flag (no consistent snapshot needed).
     * forklessDoneIteratingKeyspace is called on the main thread when iteration finishes. */
    saveInfo->iterator = bgIteratorCreateFullScanIter(FORKLESS_SOCKET_ITER_NAME,
                                                      BGITERATOR_CONSISTENCY_EVENTUAL, forklessDoneIteratingKeyspace, forklessSaveComplete, saveInfo);
    if (saveInfo->iterator == NULL) {
        serverLog(LL_WARNING, "forkless-save: error creating iterator");
        goto werr;
    }
    currentForklessSave = saveInfo;
    iteratorOwnsIncomingReplication = true;

    startBackgroundThread(saveInfo);

    return C_OK;

werr:
    forklessMarkSaveFailed(saveInfo);
    if (saveInfo->foreground_queue) {
        /* Signal the monitor timer to stop */
        mutexQueueAdd(saveInfo->foreground_queue, (void *)PROCESS_COMPLETE_ITEM);
        saveInfo->foreground_queue = NULL;
    }
    if (saveInfo->u.repl.clients) {
        resumeClientsAndFreeClientList(saveInfo, false);
    }
    rioFreeReplicaCOB(&saveInfo->save_rio);
    zfree(saveInfo);
    serverLog(LL_WARNING, "Error in forklessSaveToSockets before starting thread");
    return C_ERR;
}

/* Appends forkless save INFO metrics to the provided sds string. */
sds forkless_catInfo(sds info) {
    long long estimated_seconds_remaining = -1;

    if (onServerMainThread()) {
        bgIterator *iter = bgIteratorFind(FORKLESS_SAVE_FILE_ITER_NAME);
        if (iter != NULL) {
            bgIteratorStatus status = {0};
            bgIteratorGetStatus(iter, &status);

            if (status.dbentries_processed > 0) {
                long long total_keys =
                    (long long)atomic_load_explicit(&server.stat_current_save_keys_total, memory_order_relaxed);
                /* The ETA is best effort. Clamp at 0 since dbentries_processed
                 * can exceed total_keys (e.g. a full sync may process more than
                 * the start-time key count). */
                long long remaining = max(total_keys - (long long)status.dbentries_processed, 0);
                estimated_seconds_remaining = remaining * status.runtime_ms / status.dbentries_processed / 1000;
            }
        }
    }

    return sdscatprintf(info, "forkless_estimated_seconds_remaining:%lld\r\n", estimated_seconds_remaining);
}

/* Appends forkless debug metrics to the provided sds string. */
sds forkless_catDebugInfo(sds info) {
    bgIteratorStatus status = {0};
    long long current_item_ms = -1;

    if (onServerMainThread()) {
        bgIterator *iter = bgIteratorFind(FORKLESS_SAVE_FILE_ITER_NAME);
        if (iter != NULL) {
            bgIteratorGetStatus(iter, &status);
            current_item_ms = status.current_item_ms;
        }
    }

    return sdscatprintf(info,
                        "forkless_current_item_ms:%lld\r\n"
                        "forkless_current_queue_length:%lu\r\n"
                        "forkless_queue_length_target:%lu\r\n"
                        "forkless_dbentries_queued:%lu\r\n"
                        "forkless_dbentries_processed:%lu\r\n",
                        current_item_ms,
                        status.queue_length,
                        status.queue_length_target,
                        status.dbentries_queued,
                        status.dbentries_processed);
}

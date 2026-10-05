/*
 * Copyright (c) Valkey Contributors
 * All rights reserved.
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Replication backlog tiering. See repl_backlog_tier.h for an overview.
 */

#include "server.h"
#include "repl_backlog_tier.h"
#include "bio.h"
#include "io_threads.h"

#include <fcntl.h>
#include <unistd.h>
#include <sys/uio.h>
#include <sys/stat.h>
#ifdef HAVE_SENDFILE
#include <sys/sendfile.h>
#endif

/* Configuration instance. */
struct replTierConfig replTier_config;

/* Upper bound on a single background write. Everything that is ready is
 * written in one go (up to this and IOV_MAX blocks), so that one fsync covers
 * as much as possible when the primary produces data faster than the disk can
 * sync it. Also bounds how long the main thread waits if it ever has to drain
 * an in-flight write. */
static const long long MAX_BYTES_PER_JOB = 64 * 1024 * 1024;

/* Blocks to trim per beforeSleep() once a write completed: they are on disk
 * already, and a replica reading them is only moved to the tier when the
 * backlog head reaches its block. */
static const size_t TRIM_BLOCKS_AFTER_WRITE = 1024;

/* Upper bound on bytes sent to a replica from the tier per write call. */
static const size_t MAX_SEND_PER_CALL = 1024 * 1024;

/* A batch of full replication buffer blocks handed to the bio thread. The main
 * thread guarantees the blocks stay alive and unmodified until the job is
 * done: full blocks are never appended to, and the tier holds a reference on
 * the first block of the batch, which stops the backlog from trimming it or
 * anything after it. */
typedef struct replTierWriteJob {
    int fd;
    off_t file_offset;    /* Where in the file the first block goes. */
    long long end_offset; /* Repl offset right after the last byte of the batch. */
    size_t bytes;         /* Total bytes in the batch. */
    off_t punch_offset;   /* Optional range at the start of the file to free. */
    off_t punch_len;
    int err; /* Set by the bio thread: 0 on success, otherwise errno. */
    int iovcnt;
    struct iovec iov[];
} replTierWriteJob;

typedef struct {
    int fd;                              /* -1 when the tier is inactive. */
    char replid[CONFIG_RUN_ID_SIZE + 1]; /* Replication history the tier belongs to. */
    long long file_base;                 /* Repl offset stored at file position 0. */
    long long start_offset;              /* First repl offset still available in the file. */
    long long end_offset;                /* Repl offset one past the last durable byte. */
    long long punched_offset;            /* File space before this repl offset was freed. */
    off_t punch_align;                   /* Holes are only punched in multiples of this (a power of 2). */
    listNode *spill_node;                /* Block starting at end_offset, i.e. the first block
                                          * not on disk yet. We hold a reference on it. */
    replTierWriteJob *job;               /* Write in flight in the bio thread, or NULL. */
    unsigned long readers;               /* Replicas currently fed from the tier. */
} replTier;

/* Replicas that disconnected keep referencing the stream from where they
 * stopped for repl-backlog-tiering-retention seconds, so that they can PSYNC
 * when they come back, even if the in-memory backlog moved past that point in
 * the meantime: a hold makes the tier keep (and if needed, start) extending
 * the backlog on disk. Holds aren't tied to a specific replica, since replicas
 * are only identified by their offset when they come back; a successful PSYNC
 * consumes the closest hold at or before its offset. */
#define MAX_HOLDS 64
typedef struct {
    long long offset; /* First byte the replica may still need. */
    time_t until;     /* When the hold expires. */
} replTierHold;

static struct {
    char replid[CONFIG_RUN_ID_SIZE + 1]; /* Replication history the holds belong to. */
    int count;
    replTierHold list[MAX_HOLDS];
} holds;

typedef struct {
    unsigned long long activations;     /* Times the tier was created. */
    unsigned long long resets;          /* Times the tier was dropped while still in use. */
    unsigned long long tiered;          /* Times a replica was moved to the tier. */
    unsigned long long psyncs;          /* Partial resyncs served from the tier. */
    unsigned long long evicted_readers; /* Readers dropped by repl-backlog-tiering-max-size. */
    unsigned long long written_bytes;   /* Bytes written to the tier file. */
    unsigned long long sent_bytes;      /* Bytes sent to replicas from the tier file. */
} replTierStats;

static replTier tier = {.fd = -1};
static replTierStats stats = {0};

/* --- Internal helpers --- */

static long long streamEndOffset(void) {
    /* primary_repl_offset is the offset of the last byte produced, so the next
     * byte to be produced has this offset. */
    return server.primary_repl_offset + 1;
}

static replBufBlock *blockOf(listNode *node) {
    return listNodeValue(node);
}

/* Replicas that can be moved to the tier. Compressed links need every byte to
 * go through the compressor; replicas that are not online yet (including
 * dual-channel ones) keep their data pinned as before. */
static bool isTierableReplica(client *c) {
    if (!c->repl_data || c->repl_data->repl_tier_reader) return false;
    if (c->repl_data->ref_repl_buf_node == NULL) return false;
    if (c->repl_data->repl_state != REPLICA_STATE_ONLINE) return false;
    if (c->repl_data->repl_compression) return false;
    if (c->flag.close_asap) return false;
    /* An IO thread may be reading the replica's blocks right now. */
    if (c->io_write_state != CLIENT_IDLE) return false;
    return true;
}

static bool anyTierableReplicaOn(listNode *node) {
    listIter li;
    listNode *ln;
    listRewind(server.replicas, &li);
    while ((ln = listNext(&li))) {
        client *c = ln->value;
        if (c->repl_data->ref_repl_buf_node == node && isTierableReplica(c)) return true;
    }
    return false;
}

/* Stream position of a replica still fed from memory. */
static long long memoryOffset(client *c) {
    return blockOf(c->repl_data->ref_repl_buf_node)->repl_offset + (long long)c->repl_data->ref_block_pos;
}

/* The lowest offset of the tier a replica still references. That is not its
 * position in the stream, but the first byte it hasn't acknowledged yet
 * (REPLCONF ACK): sendfile() is zero-copy, so data handed to the socket can
 * still be queued in it as page-cache pages of the tier file, and freeing
 * that part of the file would corrupt it. A replica that was just moved back
 * to memory can still have such data queued, too. */
static long long replicaReference(client *c) {
    long long position;
    if (c->repl_data->repl_tier_reader) {
        position = c->repl_data->repl_tier_offset;
    } else if (c->repl_data->ref_repl_buf_node) {
        position = memoryOffset(c);
    } else {
        return LLONG_MAX;
    }
    long long unacked = c->repl_data->repl_ack_off + 1;
    return unacked < position ? unacked : position;
}

/* Returns true if some replica fed from memory still references the tier:
 * it may become a reader soon, or still has tier data queued. */
static bool anyReplicaBehindTierEnd(void) {
    listIter li;
    listNode *ln;
    listRewind(server.replicas, &li);
    while ((ln = listNext(&li))) {
        client *c = ln->value;
        if (!c->repl_data || !c->repl_data->ref_repl_buf_node || c->repl_data->repl_tier_evicted) continue;
        /* Includes replicas whose last acknowledgement predates the tier:
         * their position may well be in it. */
        if (replicaReference(c) < tier.end_offset) return true;
    }
    return false;
}

static void addReader(client *c, long long offset) {
    c->repl_data->repl_tier_reader = 1;
    c->repl_data->repl_tier_offset = offset;
    tier.readers++;
}

static void removeReader(client *c) {
    serverAssert(tier.readers > 0);
    c->repl_data->repl_tier_reader = 0;
    c->repl_data->repl_tier_offset = 0;
    tier.readers--;
}

/* First offset that can still be held: anything before it is gone. */
static long long holdFloor(void) {
    if (tier.fd != -1) return tier.start_offset;
    return server.repl_backlog ? server.repl_backlog->offset : LLONG_MAX;
}

static void removeHold(int i) {
    holds.list[i] = holds.list[--holds.count];
}

/* Drop holds that expired, refer to data that is gone, or belong to another
 * replication history. */
static void pruneHolds(void) {
    if (holds.count == 0) return;
    if (!replTier_config.enabled || replTier_config.retention <= 0 || !server.repl_backlog) {
        holds.count = 0;
        return;
    }
    if (strcmp(holds.replid, server.replid) != 0) {
        if (strcmp(holds.replid, server.replid2) != 0) {
            holds.count = 0;
            return;
        }
        /* Same history continued under a new ID (e.g. after a failover). */
        memcpy(holds.replid, server.replid, sizeof(holds.replid));
    }
    long long floor = holdFloor();
    for (int i = holds.count - 1; i >= 0; i--) {
        if (server.unixtime >= holds.list[i].until || holds.list[i].offset < floor) removeHold(i);
    }
}

/* Lowest held offset, or LLONG_MAX if there is no hold. */
static long long minHold(void) {
    pruneHolds();
    long long min = LLONG_MAX;
    for (int i = 0; i < holds.count; i++) {
        if (holds.list[i].offset < min) min = holds.list[i].offset;
    }
    return min;
}

static void addHold(long long offset) {
    pruneHolds();
    if (!replTier_config.enabled || replTier_config.retention <= 0 || !server.repl_backlog) return;
    /* Data before the floor is gone already; the rest may still be useful. */
    long long floor = holdFloor();
    if (offset < floor) offset = floor;
    time_t until = server.unixtime + replTier_config.retention;
    if (holds.count == 0) memcpy(holds.replid, server.replid, sizeof(holds.replid));
    if (holds.count == MAX_HOLDS) {
        /* Merge into the lowest hold. That retains more, never less. */
        int min = 0;
        for (int i = 1; i < holds.count; i++) {
            if (holds.list[i].offset < holds.list[min].offset) min = i;
        }
        if (offset < holds.list[min].offset) holds.list[min].offset = offset;
        if (until > holds.list[min].until) holds.list[min].until = until;
        return;
    }
    holds.list[holds.count].offset = offset;
    holds.list[holds.count].until = until;
    holds.count++;
}

/* Create the tier, starting with the block 'head' (the head of the backlog). */
static int activate(listNode *head) {
    serverAssert(tier.fd == -1);

    /* If we just failed to create the file (e.g. the disk is full or 'dir' is
     * not writable), don't retry on every trim attempt. */
    static time_t last_failure = 0;
    if (last_failure && server.unixtime - last_failure < 1) return C_ERR;

    char path[128];
    snprintf(path, sizeof(path), "temp-repl-backlog-tier-%d-%llu.dat", (int)getpid(), stats.activations);
    int fd = open(path, O_RDWR | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd == -1) {
        serverLog(LL_WARNING, "Replication backlog tiering: failed to create tier file %s: %s", path,
                  strerror(errno));
        last_failure = server.unixtime;
        return C_ERR;
    }
    /* Unlink right away: the data only needs to live as long as the fd, and
     * this guarantees the space is reclaimed even if we crash. */
    if (unlink(path) == -1) {
        serverLog(LL_WARNING, "Replication backlog tiering: failed to unlink tier file %s: %s", path,
                  strerror(errno));
        close(fd);
        last_failure = server.unixtime;
        return C_ERR;
    }

    long long offset = blockOf(head)->repl_offset;
    tier.fd = fd;
    /* Larger of the page size and the filesystem block size. */
    long page = sysconf(_SC_PAGESIZE);
    tier.punch_align = page > 0 ? page : 4096;
    struct stat st;
    if (fstat(fd, &st) == 0 && st.st_blksize > tier.punch_align) tier.punch_align = st.st_blksize;
    if (tier.punch_align & (tier.punch_align - 1)) tier.punch_align = 0; /* Not a power of 2: don't punch. */
    memcpy(tier.replid, server.replid, sizeof(tier.replid));
    tier.file_base = tier.start_offset = tier.end_offset = tier.punched_offset = offset;
    tier.spill_node = head;
    blockOf(head)->refcount++;
    tier.job = NULL;
    tier.readers = 0;
    stats.activations++;
    serverLog(LL_NOTICE, "Replication backlog tiering: tier activated at offset %lld (replication ID %s)", offset,
              tier.replid);
    return C_OK;
}

/* Collect the in-flight background write, if it finished (or always, if
 * 'wait' is set). Returns -1 if the write failed (errno is set), 1 if a write
 * completed, 0 otherwise. */
static int collectJob(bool wait) {
    replTierWriteJob *job = tier.job;
    if (job == NULL) return 0;
    if (wait) {
        bioDrainWorker(BIO_REPL_TIER_WRITE);
    } else if (bioPendingJobsOfType(BIO_REPL_TIER_WRITE) > 0) {
        return 0;
    }
    tier.job = NULL;

    if (job->err) {
        int err = job->err;
        zfree(job);
        errno = err;
        return -1;
    }

    /* The batch is durable: move our reference past its blocks, so the
     * backlog can trim them. */
    for (int i = 0; i < job->iovcnt; i++) {
        replBufBlock *b = blockOf(tier.spill_node);
        serverAssert(job->iov[i].iov_base == (void *)b->buf && job->iov[i].iov_len == b->used);
        listNode *next = listNextNode(tier.spill_node);
        serverAssert(next != NULL);
        b->refcount--;
        blockOf(next)->refcount++;
        tier.spill_node = next;
    }
    tier.end_offset = job->end_offset;
    serverAssert(blockOf(tier.spill_node)->repl_offset == tier.end_offset);
    if (job->punch_len) tier.punched_offset = tier.file_base + job->punch_offset + job->punch_len;
    stats.written_bytes += job->bytes;
    zfree(job);
    return 1;
}

/* Release the tier. There must be no readers left. This doesn't trim the
 * backlog, since it may be called while trimming; callers do it. */
static void release(void) {
    if (tier.fd == -1) return;
    serverAssert(tier.readers == 0);

    /* The bio thread may still be reading our blocks. */
    collectJob(true);

    replBufBlock *b = blockOf(tier.spill_node);
    serverAssert(b->refcount > 0);
    b->refcount--;
    tier.spill_node = NULL;

    /* Closing the last reference to a large unlinked file frees its blocks,
     * which can take a while, so do it in the background. */
    bioCreateCloseJob(tier.fd, 0, 0);
    tier.fd = -1;
    tier.file_base = tier.start_offset = tier.end_offset = tier.punched_offset = 0;
}

static void trimBacklog(void) {
    if (server.repl_backlog) incrementalTrimReplicationBacklog(REPL_BACKLOG_TRIM_BLOCKS_PER_CALL);
}

/* Drop the tier if it can no longer be used to resume the current replication
 * stream: the replication ID changed to a different history, or the offsets
 * no longer line up with the in-memory backlog. */
static void validate(void) {
    if (!replTier_isActive()) return;
    if (!server.repl_backlog) {
        replTier_reset("replication backlog freed");
        return;
    }
    if (strcmp(tier.replid, server.replid) != 0) {
        if (strcmp(tier.replid, server.replid2) == 0 && tier.end_offset <= server.second_replid_offset) {
            /* Same history, continued under a new ID (e.g. after a failover):
             * everything in the file is still valid. */
            serverLog(LL_NOTICE, "Replication backlog tiering: replication ID changed from %s to %s, keeping the tier",
                      tier.replid, server.replid);
            memcpy(tier.replid, server.replid, sizeof(tier.replid));
        } else {
            replTier_reset("replication ID changed");
            return;
        }
    }
    if (tier.end_offset > streamEndOffset() || tier.end_offset < server.repl_backlog->offset) {
        replTier_reset("replication offset no longer matches the tier");
    }
}

/* Trim the start of the tier up to the lowest offset still referenced (see
 * replicaReference()): readers, replicas fed from memory that are behind the
 * end of the tier (they become readers once the backlog trims their block) or
 * still have tier data queued, and the PSYNC hold of readers that
 * disconnected. Like the in-memory backlog, the tier only keeps what someone
 * still references. The file space is freed by the next background write.
 *
 * With repl-backlog-tiering-max-size, nothing more than that far behind the
 * end of the tier is kept: readers that are further behind are disconnected. */
static void trimTierStart(void) {
    long long cut = LLONG_MIN;
    if (replTier_config.max_size && (unsigned long long)(tier.end_offset - tier.start_offset) > replTier_config.max_size) {
        cut = tier.end_offset - (long long)replTier_config.max_size;
    }

    /* Never past the head of the in-memory backlog: a replica can PSYNC into
     * memory anywhere from there, and must be able to move to the tier later. */
    long long start = tier.end_offset;
    if (server.repl_backlog && server.repl_backlog->offset < start) start = server.repl_backlog->offset;
    listIter li;
    listNode *ln;
    listRewind(server.replicas, &li);
    while ((ln = listNext(&li))) {
        client *c = ln->value;
        if (!c->repl_data || c->repl_data->repl_tier_evicted) continue;
        /* Readers, and replicas in memory that would be moved to the tier
         * next (their position is in it), that are too far behind. Judged by
         * position, not by the last acknowledgement, which can be stale. */
        long long position = LLONG_MAX;
        if (replTier_isReader(c)) {
            position = c->repl_data->repl_tier_offset;
        } else if (c->repl_data->ref_repl_buf_node && isTierableReplica(c)) {
            long long mem = memoryOffset(c);
            if (mem >= tier.start_offset) position = mem;
        }
        if (position < cut) {
            serverLog(LL_NOTICE,
                      "Replication backlog tiering: disconnecting replica %s, it is %lld bytes behind "
                      "(repl-backlog-tiering-max-size)",
                      replicationGetReplicaName(c), streamEndOffset() - position);
            if (replTier_isReader(c)) removeReader(c);
            c->repl_data->repl_tier_evicted = 1;
            freeClientAsync(c);
            stats.evicted_readers++;
            continue;
        }
        /* Replicas in memory further behind than max-size keep pinning memory
         * instead, as without tiering (see replTier_unpinBlock()). */
        long long offset = replicaReference(c);
        if (offset >= cut && offset < start) start = offset;
    }
    pruneHolds();
    for (int i = holds.count - 1; i >= 0; i--) {
        if (holds.list[i].offset < cut) {
            removeHold(i);
        } else if (holds.list[i].offset < start) {
            start = holds.list[i].offset;
        }
    }
    if (start > tier.start_offset) tier.start_offset = start;
}

/* Hand the next batch of blocks to the bio thread, if there is enough to
 * write. We only write blocks that will have to leave memory anyway, i.e. the
 * ones beyond repl-backlog-size, and only full blocks that are not the tail. */
static void submitJob(void) {
    if (tier.job) return;

    trimTierStart();
    /* Only free whole blocks. Punching a partial block makes the filesystem
     * write zeros into its page-cache page, which may still be queued in a
     * replica's socket by sendfile(). Whole pages are only dropped from the
     * page cache, their content stays intact for whoever still holds them.
     * punched_offset stays aligned, so nothing is left behind. */
    off_t punch_offset = (off_t)(tier.punched_offset - tier.file_base);
    off_t punch_end = (off_t)(tier.start_offset - tier.file_base) & ~(tier.punch_align - 1);
    off_t punch_len = punch_end > punch_offset ? punch_end - punch_offset : 0;

    long long batch = (long long)replTier_config.batch_size;
    long long keep_from = streamEndOffset() - server.repl_backlog_size;
    int iovcnt = 0;
    long long bytes = 0;
    for (listNode *node = tier.spill_node; node && listNextNode(node); node = listNextNode(node)) {
        replBufBlock *b = blockOf(node);
        if (b->repl_offset + (long long)b->used > keep_from) break;
        if (iovcnt == IOV_MAX || bytes >= MAX_BYTES_PER_JOB) break;
        serverAssert(b->used == b->size);
        iovcnt++;
        bytes += b->used;
    }
    /* Batch writes (and freeing space at the start) so we don't hit the disk
     * on every new block. */
    if (bytes < batch && punch_len < batch) return;

    replTierWriteJob *job = zmalloc(sizeof(*job) + sizeof(struct iovec) * iovcnt);
    job->fd = tier.fd;
    job->file_offset = (off_t)(tier.end_offset - tier.file_base);
    job->end_offset = tier.end_offset + bytes;
    job->bytes = (size_t)bytes;
    job->punch_offset = punch_offset;
    job->punch_len = punch_len;
    job->err = 0;
    job->iovcnt = iovcnt;
    listNode *node = tier.spill_node;
    for (int i = 0; i < iovcnt; i++, node = listNextNode(node)) {
        job->iov[i].iov_base = blockOf(node)->buf;
        job->iov[i].iov_len = blockOf(node)->used;
    }
    tier.job = job;
    bioCreateReplTierWriteJob(job);
}

static void demoteReplica(client *c) {
    listNode *node = c->repl_data->ref_repl_buf_node;
    replBufBlock *b = blockOf(node);
    long long offset = b->repl_offset + (long long)c->repl_data->ref_block_pos;
    serverAssert(offset >= tier.start_offset && offset <= tier.end_offset);

    serverAssert(b->refcount > 0);
    b->refcount--;
    c->repl_data->ref_repl_buf_node = NULL;
    c->repl_data->ref_block_pos = 0;
    addReader(c, offset);
    stats.tiered++;
    serverLog(LL_NOTICE,
              "Replication backlog tiering: replica %s fell behind the replication backlog, serving it from disk "
              "starting at offset %lld",
              replicationGetReplicaName(c), offset);
}

static bool connCanSendfile(connection *conn) {
#ifdef HAVE_SENDFILE
    int type = connGetType(conn);
    return type == CONN_TYPE_SOCKET || type == CONN_TYPE_UNIX;
#else
    UNUSED(conn);
    return false;
#endif
}

/* --- Public API --- */

bool replTier_isActive(void) {
    return tier.fd != -1;
}

bool replTier_isReader(client *c) {
    return c->repl_data && c->repl_data->repl_tier_reader;
}

bool replTier_unpinBlock(listNode *node) {
    if (!replTier_config.enabled) return false;

    if (!replTier_isActive()) {
        /* Only start writing the stream to disk once a replica actually
         * falls behind the backlog. */
        if (!anyTierableReplicaOn(node)) return false;
        activate(node);
        return false; /* The block isn't on disk yet. */
    }

    /* Blocks from the spill node onwards aren't durable yet. */
    if (blockOf(node)->repl_offset >= tier.end_offset) return false;

    listIter li;
    listNode *ln;
    listRewind(server.replicas, &li);
    while ((ln = listNext(&li))) {
        client *c = ln->value;
        if (c->repl_data->ref_repl_buf_node != node || !isTierableReplica(c)) continue;
        /* Further behind than repl-backlog-tiering-max-size: the tier no
         * longer has its data, so it keeps pinning memory as without tiering
         * (and is subject to client-output-buffer-limit). */
        if (memoryOffset(c) < tier.start_offset) continue;
        demoteReplica(c);
    }
    return blockOf(node)->refcount == 1;
}

bool replTier_hasPendingData(client *c) {
    serverAssert(c->repl_data->repl_tier_reader);
    return c->repl_data->repl_tier_offset < streamEndOffset();
}

bool replTier_maybePromoteReader(client *c) {
    if (!c->repl_data->repl_tier_reader) return false;
    if (c->repl_data->repl_tier_offset < tier.end_offset) return false;
    serverAssert(c->repl_data->repl_tier_offset == tier.end_offset);

    /* Everything on disk was sent. The next byte is the first byte of the
     * spill node, which is still in memory: resume from there. */
    c->repl_data->ref_repl_buf_node = tier.spill_node;
    c->repl_data->ref_block_pos = 0;
    blockOf(tier.spill_node)->refcount++;
    removeReader(c);
    serverLog(LL_NOTICE, "Replication backlog tiering: replica %s caught up, serving it from memory again",
              replicationGetReplicaName(c));
    return true;
}

void replTier_writeToReplica(client *c) {
    serverAssert(inMainThread());
    serverAssert(c->repl_data->repl_tier_reader && replTier_isActive());

    long long offset = c->repl_data->repl_tier_offset;
    serverAssert(offset >= tier.start_offset);
    size_t len = (size_t)(tier.end_offset - offset);
    if (len > MAX_SEND_PER_CALL) len = MAX_SEND_PER_CALL;
    c->nwritten = 0;
    if (len == 0) return;

    off_t file_offset = (off_t)(offset - tier.file_base);

#ifdef HAVE_SENDFILE
    if (connCanSendfile(c->conn)) {
        ssize_t n = sendfile(c->conn->fd, tier.fd, &file_offset, len);
        if (n >= 0 || errno == EAGAIN) {
            c->nwritten = n;
            if (n <= 0) c->write_flags |= WRITE_FLAGS_WRITE_ERROR;
            return;
        }
        if (errno != EINVAL && errno != ENOSYS && errno != EOPNOTSUPP) {
            /* Mirror connSocketWrite() error handling. */
            c->conn->last_errno = errno;
            if (errno != EINTR && c->conn->state == CONN_STATE_CONNECTED) c->conn->state = CONN_STATE_ERROR;
            c->nwritten = -1;
            c->write_flags |= WRITE_FLAGS_WRITE_ERROR;
            return;
        }
        /* sendfile() isn't supported for this pair of fds: fall back to a
         * buffered copy below. */
        file_offset = (off_t)(offset - tier.file_base);
    }
#endif

    /* Buffered fallback, e.g. for TLS connections. */
    static char buf[NET_MAX_WRITES_PER_EVENT];
    if (len > sizeof(buf)) len = sizeof(buf);
    ssize_t nread;
    do {
        nread = pread(tier.fd, buf, len, file_offset);
    } while (nread < 0 && errno == EINTR);
    if (nread <= 0) {
        serverLog(LL_WARNING, "Replication backlog tiering: failed reading tier file for replica %s: %s",
                  replicationGetReplicaName(c), nread < 0 ? strerror(errno) : "unexpected EOF");
        freeClientAsync(c);
        return;
    }
    c->nwritten = connWrite(c->conn, buf, (size_t)nread);
    if (c->nwritten <= 0) c->write_flags |= WRITE_FLAGS_WRITE_ERROR;
}

void replTier_postWriteToReplica(client *c) {
    serverAssert(c->repl_data->repl_tier_reader);
    if (c->nwritten <= 0) return;
    c->repl_data->repl_tier_offset += c->nwritten;
    serverAssert(c->repl_data->repl_tier_offset <= tier.end_offset);
    stats.sent_bytes += c->nwritten;
    replTier_maybePromoteReader(c);
}

void replTier_replicaFreed(client *c) {
    if (!c->repl_data) return;
    bool reader = replTier_isReader(c);
    /* Evicted for repl-backlog-tiering-max-size: the tier can't serve it. */
    if (c->repl_data->repl_tier_evicted) {
        if (reader) removeReader(c);
        return;
    }
    /* Leave a hold so the replica can PSYNC when it comes back, from wherever
     * it stopped: somewhere between what it acknowledged and what we sent it.
     * Replicas that weren't streaming yet have nothing to resume, and
     * compressed links can't be served from the tier. */
    long long position = -1;
    if (reader) {
        position = c->repl_data->repl_tier_offset;
    } else if (c->repl_data->ref_repl_buf_node && c->repl_data->repl_state == REPLICA_STATE_ONLINE &&
               !c->repl_data->repl_compression) {
        position = memoryOffset(c);
    }
    if (position != -1) addHold(c->repl_data->repl_ack_off > 0 ? replicaReference(c) : position);
    if (reader) removeReader(c);
}

bool replTier_retainBlock(listNode *node) {
    if (!replTier_config.enabled || replTier_isActive() || holds.count == 0) return false;
    replBufBlock *b = blockOf(node);
    long long min = minHold();
    if (min >= b->repl_offset + (long long)b->used) return false;
    /* A replica that disconnected may still need this block: keep extending
     * the backlog on disk for it. */
    if (activate(node) != C_OK) return false;
    serverLog(LL_NOTICE,
              "Replication backlog tiering: a disconnected replica may still need offset %lld, extending the "
              "backlog on disk",
              min);
    return true;
}

void replTier_psyncAccepted(long long offset) {
    /* Consume the hold closest at or before the offset: most likely the one
     * this replica left. Lower holds keep protecting the others. */
    pruneHolds();
    int best = -1;
    for (int i = 0; i < holds.count; i++) {
        if (holds.list[i].offset <= offset && (best == -1 || holds.list[i].offset > holds.list[best].offset)) best = i;
    }
    if (best != -1) removeHold(best);
}

bool replTier_canServePsync(long long offset) {
    validate();
    if (!replTier_isActive() || !server.repl_backlog) return false;
    return offset >= tier.start_offset && offset < server.repl_backlog->offset;
}

long long replTier_attachPsyncReader(client *c, long long offset) {
    serverAssert(replTier_canServePsync(offset));
    serverAssert(c->repl_data->ref_repl_buf_node == NULL && !c->repl_data->repl_tier_reader);
    /* Install a write handler first, while the client has nothing pending. */
    prepareClientToWrite(c);
    addReader(c, offset);
    stats.psyncs++;
    return streamEndOffset() - offset;
}

void replTier_reset(const char *reason) {
    if (!replTier_isActive()) return;

    unsigned long disconnected = 0;
    if (tier.readers > 0) {
        listIter li;
        listNode *ln;
        listRewind(server.replicas, &li);
        while ((ln = listNext(&li))) {
            client *replica = ln->value;
            if (!replTier_isReader(replica)) continue;
            /* The replica can't continue its stream without the tier. */
            removeReader(replica);
            freeClientAsync(replica);
            disconnected++;
        }
    }
    serverAssert(tier.readers == 0);

    serverLog(LL_NOTICE,
              "Replication backlog tiering: dropping tier [%lld, %lld) (%s), disconnected %lu replica(s) reading "
              "from it",
              tier.start_offset, tier.end_offset, reason, disconnected);
    stats.resets++;
    release();
}

void replTier_beforeSleep(void) {
    if (!replTier_isActive()) return;

    int collected = collectJob(false);
    if (collected < 0) {
        serverLog(LL_WARNING, "Replication backlog tiering: failed writing to tier file: %s", strerror(errno));
        replTier_reset("tier file write error");
        trimBacklog();
        return;
    }
    validate();
    if (replTier_isActive()) submitJob();
    /* Blocks that just became durable can be trimmed now, and lagging
     * replicas on them moved to the tier. */
    if (server.repl_backlog) {
        incrementalTrimReplicationBacklog(collected ? TRIM_BLOCKS_AFTER_WRITE : REPL_BACKLOG_TRIM_BLOCKS_PER_CALL);
    }
}

void replTier_cron(void) {
    if (!replTier_isActive()) return;
    validate();
    if (!replTier_isActive()) {
        trimBacklog();
        return;
    }
    /* Release the tier once nothing references it anymore: no reader, no
     * replica that dropped recently and may PSYNC from it, and no replica in
     * memory that may still fall behind into it. */
    if (tier.readers > 0 || minHold() != LLONG_MAX) return;
    if (replTier_config.enabled && anyReplicaBehindTierEnd()) return;
    /* Don't block on the bio thread, try again on the next run. */
    if (tier.job) return;
    serverLog(LL_NOTICE, "Replication backlog tiering: releasing tier [%lld, %lld), no replica needs it anymore",
              tier.start_offset, tier.end_offset);
    release();
    trimBacklog();
}

void replTier_bioProcessWrite(void *ptr) {
    replTierWriteJob *job = ptr;
    job->err = 0;

#if defined(__linux__) && defined(FALLOC_FL_PUNCH_HOLE) && defined(FALLOC_FL_KEEP_SIZE)
    /* Free the space of data trimmed from the start of the tier. Offsets in
     * the file don't change. Best effort: not every filesystem supports it. */
    if (job->punch_len > 0) {
        fallocate(job->fd, FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE, job->punch_offset, job->punch_len);
    }
#endif

    off_t offset = job->file_offset;
    for (int i = 0; i < job->iovcnt; i++) {
        const char *p = job->iov[i].iov_base;
        size_t left = job->iov[i].iov_len;
        while (left > 0) {
            ssize_t n = pwrite(job->fd, p, left, offset);
            if (n < 0) {
                if (errno == EINTR) continue;
                job->err = errno;
                return;
            }
            if (n == 0) {
                job->err = EIO;
                return;
            }
            p += n;
            left -= (size_t)n;
            offset += n;
        }
    }
    if (job->iovcnt > 0 && valkey_fsync(job->fd) == -1) job->err = errno;
}

sds replTier_sdscatInfo(sds info) {
    pruneHolds();
    bool active = replTier_isActive();
    return sdscatprintf(info,
                        "repl_backlog_tier_active:%d\r\n"
                        "repl_backlog_tier_first_byte_offset:%lld\r\n"
                        "repl_backlog_tier_size:%lld\r\n"
                        "repl_backlog_tier_write_in_progress:%d\r\n"
                        "repl_backlog_tier_readers:%lu\r\n"
                        "repl_backlog_tier_activations:%llu\r\n"
                        "repl_backlog_tier_resets:%llu\r\n"
                        "repl_backlog_tier_tiered_replicas:%llu\r\n"
                        "repl_backlog_tier_psyncs:%llu\r\n"
                        "repl_backlog_tier_evicted_readers:%llu\r\n"
                        "repl_backlog_tier_written_bytes:%llu\r\n"
                        "repl_backlog_tier_sent_bytes:%llu\r\n"
                        "repl_backlog_tier_psync_holds:%d\r\n",
                        active, active ? tier.start_offset : 0, active ? tier.end_offset - tier.start_offset : 0,
                        tier.job != NULL, tier.readers, stats.activations, stats.resets, stats.tiered, stats.psyncs,
                        stats.evicted_readers, stats.written_bytes, stats.sent_bytes, holds.count);
}

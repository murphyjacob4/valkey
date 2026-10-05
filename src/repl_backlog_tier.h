/*
 * Copyright (c) Valkey Contributors
 * All rights reserved.
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Replication backlog tiering.
 *
 * The replication backlog (repl-backlog-size) is the part of the replication
 * stream that is always kept in memory. Without tiering, a replica that falls
 * further behind than the backlog keeps the blocks it still needs pinned in
 * memory (its "output buffer"), until it either catches up or reaches its
 * client-output-buffer-limit and is disconnected, forcing a full resync.
 *
 * With tiering, a replica never pins memory beyond the backlog. Instead, the
 * stream extends past the in-memory backlog into an append-only file:
 *
 *        disk tier                     in-memory backlog
 *   [start_offset ......... end_offset)
 *                           [backlog->offset ................. stream end]
 *
 *  - The file grows at its end with blocks that are about to be trimmed from
 *    the head of the in-memory backlog. Blocks are written in batches (at
 *    least repl-backlog-tiering-batch-size bytes) by a bio thread, which
 *    writes and fsyncs them. Only once a batch is durable does the main thread
 *    move its reference forward and let the in-memory backlog trim those
 *    blocks, so there is never a gap between the disk tier and memory (they
 *    may overlap while trimming catches up).
 *  - A replica whose position is in a block being trimmed is switched to read
 *    from the file instead (with sendfile(2) where possible), and switches
 *    back to the in-memory buffer when it reaches end_offset.
 *  - A replica that disconnects (from the tier or from memory) leaves a hold
 *    on the stream from where it stopped, for repl-backlog-tiering-retention
 *    seconds. If the in-memory backlog is about to drop held data, the tier
 *    is started for it, so it can partially resync from the tier.
 *  - Like the in-memory backlog, the file only keeps what is still
 *    referenced: its start follows the lowest of the replicas' references
 *    (the first byte they haven't acknowledged yet, since sendfile() leaves
 *    file pages queued in sockets), for readers and for replicas in memory
 *    that may still become readers, and the holds. Whole blocks before the
 *    start are freed by punching holes in the file. Once nothing references
 *    the tier, it is released.
 *  - repl-backlog-tiering-max-size limits how far behind the end of the tier
 *    a reader can be; readers further behind are disconnected.
 *
 * The tier is tied to a replication history: it records the replication ID it
 * was created under. If the replication ID or offsets change such that the
 * current stream can no longer be resumed from the file contents (e.g. a full
 * sync from a new primary, DEBUG CHANGE-REPL-ID, the backlog being freed or
 * rebased), the tier is dropped and readers are disconnected. A failover that
 * continues the same history (replid2) keeps it.
 *
 * The file is created in the working directory and immediately unlinked, so
 * its space is reclaimed as soon as it is released, including on a crash.
 */

#ifndef REPL_BACKLOG_TIER_H
#define REPL_BACKLOG_TIER_H

#include <stdbool.h>
#include <time.h>
#include "sds.h"
#include "adlist.h"

struct client;

struct replTierConfig {
    int enabled;                   /* repl-backlog-tiering-enabled */
    unsigned long long batch_size; /* repl-backlog-tiering-batch-size */
    unsigned long long max_size;   /* repl-backlog-tiering-max-size, 0 means unlimited */
    time_t retention;              /* repl-backlog-tiering-retention, in seconds */
};
extern struct replTierConfig replTier_config;

/* Returns true if the disk tier currently exists. */
bool replTier_isActive(void);

/* Returns true if this replica is currently being fed from the disk tier. */
bool replTier_isReader(struct client *c);

/* Called by incrementalTrimReplicationBacklog() when the head block of the
 * replication buffer can't be trimmed because something else references it.
 * Creates the tier if a replica that can be tiered is holding the block, and
 * moves such replicas to the tier once the block is on disk. Returns true if
 * the backlog is now the only reference to the block. */
bool replTier_unpinBlock(listNode *node);

/* Returns true if a tier reader has data that hasn't been sent yet. */
bool replTier_hasPendingData(struct client *c);

/* If the reader has consumed everything on disk, move it back to the in-memory
 * replication buffer. Returns true if the replica was moved. */
bool replTier_maybePromoteReader(struct client *c);

/* Write the next chunk of the tier to the replica. Sets c->nwritten. Must be
 * called from the main thread. */
void replTier_writeToReplica(struct client *c);

/* Account for bytes written by replTier_writeToReplica(). */
void replTier_postWriteToReplica(struct client *c);

/* Called when a replica's replication buffer references are released (it is
 * being freed). Stops treating it as a tier reader, and leaves a hold so it
 * can PSYNC when it comes back. */
void replTier_replicaFreed(struct client *c);

/* Called by incrementalTrimReplicationBacklog() before trimming the head block
 * when nothing else references it. If a replica that disconnected may still
 * need the block, creates the tier (which then references the block) and
 * returns true. */
bool replTier_retainBlock(listNode *node);

/* A PSYNC at 'offset' was accepted: consume the matching hold. */
void replTier_psyncAccepted(long long offset);

/* Returns true if a PSYNC for 'offset' must be served from the disk tier, i.e.
 * 'offset' is no longer in the in-memory backlog but is in the tier. */
bool replTier_canServePsync(long long offset);

/* Attach a replica that was accepted for partial resync at 'offset' to the
 * disk tier. Returns the number of bytes that will be sent. */
long long replTier_attachPsyncReader(struct client *c, long long offset);

/* Drop the disk tier, disconnecting any replica currently reading from it.
 * Used when the tier can no longer be used to resume the current replication
 * stream. 'reason' is logged. */
void replTier_reset(const char *reason);

/* Collect finished background writes, validate the tier against the current
 * replication ID/offsets, and submit the next batch. Called from beforeSleep(). */
void replTier_beforeSleep(void);

/* Housekeeping, called once per second from serverCron(): releases the tier
 * once nothing references it anymore. */
void replTier_cron(void);

/* Append the tier's INFO replication fields. */
sds replTier_sdscatInfo(sds info);

/* Executed by the bio thread for BIO_REPL_TIER_WRITE jobs. */
void replTier_bioProcessWrite(void *job);

#endif

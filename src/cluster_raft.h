#ifndef __CLUSTER_RAFT_H
#define __CLUSTER_RAFT_H

#include "server.h"
#include "sds.h"
#include "cluster.h"
#include "util.h"

/* Forward declarations */
typedef struct clusterMsg clusterMsg;
typedef struct clusterMsgPingExt clusterMsgPingExt;

/* Raft message types */
#define CLUSTERMSG_TYPE_RAFT_VOTE_REQUEST 0
#define CLUSTERMSG_TYPE_RAFT_VOTE_RESPONSE 1
#define CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES_ACK 2
#define CLUSTERMSG_TYPE_RAFT_PROPOSE_ENTRY 3
#define CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES 4
#define CLUSTERMSG_TYPE_RAFT_SNAPSHOT_REQUEST 5
#define CLUSTERMSG_TYPE_RAFT_SNAPSHOT_RESPONSE 6
#define CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REQUEST 7
#define CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REPLY 8

/* Raft todo flags */
#define RAFT_TODO_BROADCAST_APPEND_ENTRIES (1 << 0)

/* Raft message header */
typedef struct {
    char sig[4];     /* Signature "RAFT" */
    uint32_t totlen; /* Total length of this message */
    uint16_t ver;    /* Protocol version */
    uint16_t type;   /* Message type */
} clusterRaftHeader;


/* Raft roles */
#define RAFT_ROLE_FOLLOWER 0
#define RAFT_ROLE_CANDIDATE 1
#define RAFT_ROLE_LEADER 2
#define RAFT_ROLE_JOINING 3
#define RAFT_ROLE_HANDSHAKING 4
#define RAFT_ROLE_EXTERNAL 5

/* Raft constants */
#define RAFT_ELECTION_TIMEOUT_MIN 1000
#define RAFT_ELECTION_TIMEOUT_MAX 2000
#define RAFT_HEARTBEAT_INTERVAL 200

typedef struct raftKeyValue {
    sds key;
    sds value;
} raftKeyValue;

/* A single Raft log entry */
typedef struct raftLogEntry {
    uint64_t index;
    uint64_t term;
    uint32_t count;
    raftKeyValue *mutations;
} raftLogEntry;

typedef struct raftAppliedEntry {
    uint64_t index;
    uint64_t term;
    sds value;
} raftAppliedEntry;

typedef struct raftBackupState {
    dict *applied_entries;
    uint64_t last_applied_index;
    uint64_t last_applied_term;
    uint64_t term;

} raftBackupState;

typedef struct clusterRaftState {
    bool enabled;                      /* Whether Raft is enabled or not for metadata changes */
    int todo_before_sleep;             /* Pending tasks to do before sleep */
    uint64_t term;                     /* Current term */
    char voted_for[CLUSTER_NAMELEN];   /* Node name we voted for in this term */
    int granted_vote_count;            /* Votes granted in current term */
    int denied_vote_count;             /* Votes denied in current term */
    char leader_name[CLUSTER_NAMELEN]; /* Name of the current leader */
    mstime_t election_timer;           /* Time when election will be triggered */
    mstime_t heartbeat_timer;          /* Time for the next heartbeat (leader only) */
    mstime_t proposal_retry_timer;     /* Time for next join proposal retry */

    /* Applied Entries
     *
     * Raft is a distributed log. But we collapse the log immediately upon being committed for
     * simplicity. This means in some cases we need to install snapshots where sending entries
     * would have been sufficient, but it keeps the logic simpler. */
    uint64_t last_applied_index; /* Index of the newest entry in applied_entries */
    uint64_t last_applied_term;  /* Term of the newest entry in applied_entries */
    dict *applied_entries;       /* Map of key -> raftAppliedEntry */

    /* Pending Entries
     *
     * These are values that have been proposed but not yet committed. It is managed as a log,
     * but is collapsed into the applied dictionary once commit conditions are met. */
    list *pending_entries;             /* List of pending raftLogEntry */
    list *nodes_to_pong_once_disabled; /* List of nodes that need to be sent a PONG once Raft is disabled */

    mstime_t join_start_time; /* Time when we started joining */
    raftBackupState *prev_group_state; /* Backup state for rollback */
} clusterRaftState;

typedef struct clusterNodeRaftData {
    uint64_t match_index;          /* The index of the highest value this node has acked. */
    int role;                      /* Node's Raft role (Follower, Leader, Candidate, Joining) */
    uint32_t member_count;         /* Raft member count of the node */

    int outbound_link_established; /* Flag indicating outbound link is established */
} clusterNodeRaftData;

/* Access Raft protocol-specific data from a clusterNode. */
#define RAFT_DATA(n) ((clusterNodeRaftData *)(n)->protocol_data)

/* Raft AppendEntries Extension
 *
 * This extension is sent by the Raft leader to its followers as a heartbeat and to catch them
 * up on any missing log entries.
 */
typedef struct {
    uint64_t term;                     /* Raft current term. */
    char leader_name[CLUSTER_NAMELEN]; /* Name of the current Raft leader. */
    uint64_t prev_log_index;           /* The index of the previous log entry. */
    uint64_t prev_log_term;            /* The term of the previous log entry. */
    uint64_t leader_commit;            /* The index of the last committed value. */
    uint64_t entries_len;              /* Number of new entries. */
    char entries[7];                   /* The new entries. 7 bytes just a placeholder. */
} clusterMsgRaftAppendEntries;

typedef struct {
    uint64_t term; /* Requesting node's current term. */
} clusterMsgRaftSnapshotRequest;

typedef struct {
    uint64_t term;                     /* Responding node's current term. */
    char leader_name[CLUSTER_NAMELEN]; /* Name of the current leader. */
    uint32_t count;                    /* Number of entries in snapshot. */
    char data[];                       /* Encoded entries: array of {key_len, value_len, key, value} */
} clusterMsgRaftSnapshotResponse;

typedef struct {
    uint64_t term;
    char sender_name[CLUSTER_NAMELEN];
    uint32_t member_count;
    char remote_ip[NET_IP_STR_LEN];
    uint16_t plaintext_port;
    uint16_t tls_port;
    uint16_t cluster_port;
} clusterMsgRaftHandshake;

/* Raft Vote Request Message
 *
 * This message is sent by a Raft candidate to another Raft member to request their vote to become
 * leader.
 */
typedef struct {
    uint64_t term;             /* Requesting node's current term. */
    uint64_t last_entry_index; /* The index of the last entry this requesting node has (either applied or pending). */
    uint64_t last_entry_term;  /* The term of the last entry this requesting node has (either applied or pending). */
} clusterMsgRaftVoteRequest;

/* Raft Vote Response Message
 *
 * This message is sent by a Raft member to another Raft member in response to a vote request to
 * become leader.
 */
typedef struct {
    uint64_t term;     /* Voter's current term. */
    bool vote_granted; /* Whether the vote was granted. */
} clusterMsgRaftVoteResponse;

/* Raft AppendEntries Ack Message
 *
 * This message is sent by a Raft member to another Raft member in response to an AppendEntries
 * request.
 *
 * This includes the highest index/term of the local pending values so the leader can keep track of
 * what each node has without mapping each AppendEntriesAck to a specific request.
 *
 * The leader can also identify divergence if the returned index/term doesn't match a index/term
 * the leader is aware of. This case is effectively the same as "failed RPC" in the Raft paper.
 */
typedef struct {
    uint64_t term;        /* Responder's current term. */
    uint64_t value_index; /* The index of the highest value this responder has persisted. */
    uint64_t value_term;  /* The term of the highest value this responder has persisted. */
} clusterMsgRaftAppendEntriesAck;

/* Raft Propose Entry Message
 *
 * This message is sent by a Raft follower to the leader to propose a new entry.
 */
typedef struct {
    uint64_t term;          /* Follower's current term. */
    uint32_t num_checks;    /* Number of CAS checks (assertions). */
    uint32_t num_proposals; /* Number of blind proposals (set only). */
    char data[];            /* Encoded entries: First num_checks entries, then num_proposals. */
} clusterMsgRaftProposeEntries;

struct clusterLink;

void clusterRaftInit(void);
void clusterRaftFree(void);
void clusterRaftCron(void);

void clusterRaftDisable(clusterNode *node_to_pong_once_disabled);
void clusterRaftProcessVoteRequest(clusterNode *sender, clusterMsgRaftVoteRequest *req);
void clusterRaftProcessVoteResponse(clusterNode *sender, clusterMsgRaftVoteResponse *resp);
void clusterRaftProcessAppendEntriesAck(clusterNode *sender, clusterMsgRaftAppendEntriesAck *ack);
void clusterRaftProcessAppendEntries(clusterNode *sender, clusterMsgRaftAppendEntries *ext, size_t payload_len);
void clusterRaftProcessProposeEntries(struct clusterLink *link, clusterMsgRaftProposeEntries *prop, size_t payload_len);
void clusterRaftInfo(struct client *c);
void clusterRaftGetMetadata(struct client *c);
void clusterRaftSetMetadata(struct client *c);
uint32_t clusterRaftAddAppendEntriesExtIfNeeded(clusterNode *node, clusterMsgPingExt *cursor);

#endif

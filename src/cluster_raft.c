#include "adlist.h"
#include "dict.h"
#include "sds.h"
#include "server.h"
#include <arpa/inet.h>
#include "cluster.h"
#include "cluster_bus.h"
#include "cluster_raft.h"
#include "cluster_state.h"
#include "cluster_link.h"
#include "endianconv.h"
#include "connection.h"

#define RAFT_NODE_PREFIX "node:"

/* Forward declarations */
static void freeRaftKeyValue(void *ptr);
void clusterRaftSendJoinProposal(clusterNode *leader);
void clusterRaftSendVoteRequests(void);
void clusterRaftSendAppendEntries(void);
bool clusterRaftProposeEntry(sds key, sds val);
void clusterRaftReconcileRaftMembership(void);
void clusterRaftAdvanceCommitIndexToMajority(void);
int clusterRaftGetMemberCount(void);
void clusterRaftConnectToNode(clusterNode *node);
void clusterRaftProcessSnapshotRequest(clusterLink *link, void *payload);
static void clusterRaftOnAppendEntry(raftLogEntry *entry);
static void clusterRaftRecognizeLeader(clusterNode *sender, uint64_t term);
void clusterRaftProcessHandshake(clusterLink *link, uint16_t type, clusterMsgRaftHandshake *req);
void clusterRaftProcessSnapshotResponse(clusterNode *sender, void *payload, size_t payload_len);
void clusterDelNode(clusterNode *delnode);

#define MY_RAFT_ROLE RAFT_DATA(server.cluster->myself)->role

/* Access Raft protocol-specific state from the cluster. */
#define RAFT_STATE() ((clusterRaftState *)server.cluster->protocol_data)

raftLogEntry *raftLogEntryCreate(uint64_t term, uint64_t index, list *proposals) {
    raftLogEntry *entry = zmalloc(sizeof(raftLogEntry));
    entry->term = term;
    entry->index = index;
    entry->count = listLength(proposals);
    entry->mutations = zmalloc(sizeof(raftKeyValue) * entry->count);

    listIter li;
    listRewind(proposals, &li);
    listNode *ln;
    int i = 0;
    while ((ln = listNext(&li))) {
        raftKeyValue *kv = ln->value;
        entry->mutations[i].key = sdsdup(kv->key);
        entry->mutations[i].value = sdsdup(kv->value);
        i++;
    }
    return entry;
}

void raftLogEntryFree(void *val) {
    raftLogEntry *entry = val;
    for (uint32_t i = 0; i < entry->count; i++) {
        sdsfree(entry->mutations[i].key);
        sdsfree(entry->mutations[i].value);
    }
    zfree(entry->mutations);
    zfree(entry);
}

static const char *raftRoleToString(int role) {
    switch (role) {
    case RAFT_ROLE_FOLLOWER: return "FOLLOWER";
    case RAFT_ROLE_CANDIDATE: return "CANDIDATE";
    case RAFT_ROLE_LEADER: return "LEADER";
    case RAFT_ROLE_JOINING: return "JOINING";
    case RAFT_ROLE_HANDSHAKING: return "HANDSHAKING";
    case RAFT_ROLE_EXTERNAL: return "EXTERNAL";
    default: return "UNKNOWN";
    }
}

static void clusterRaftSetNodeRole(clusterNode *node, int new_role) {
    int old_role = RAFT_DATA(node)->role;
    if (old_role == new_role) return;

    serverLog(LL_NOTICE, "Raft: Update node %.40s role: %s -> %s",
              node->name, raftRoleToString(old_role), raftRoleToString(new_role));
    RAFT_DATA(node)->role = new_role;
}

extern dictType clusterRaftAppliedEntryDictType;

static void clusterRaftPreviousGroupStateCleanup(void) {
    if (RAFT_STATE()->prev_group_state) {
        dictRelease(RAFT_STATE()->prev_group_state->applied_entries);
        zfree(RAFT_STATE()->prev_group_state);
        RAFT_STATE()->prev_group_state = NULL;
    }
}

static void clusterRaftPreviousGroupStateCreate(void) {
    if (RAFT_STATE()->prev_group_state == NULL) {
        RAFT_STATE()->prev_group_state = zcalloc(sizeof(raftBackupState));
        RAFT_STATE()->prev_group_state->applied_entries = RAFT_STATE()->applied_entries;
        RAFT_STATE()->applied_entries = dictCreate(&clusterRaftAppliedEntryDictType);

        RAFT_STATE()->prev_group_state->last_applied_index = RAFT_STATE()->last_applied_index;
        RAFT_STATE()->prev_group_state->last_applied_term = RAFT_STATE()->last_applied_term;
        RAFT_STATE()->prev_group_state->term = RAFT_STATE()->term;
    }
}

static void clusterRaftPreviousGroupStateRestore(void) {
    if (RAFT_STATE()->prev_group_state) {
        dictRelease(RAFT_STATE()->applied_entries);
        RAFT_STATE()->applied_entries = RAFT_STATE()->prev_group_state->applied_entries;
        RAFT_STATE()->last_applied_index = RAFT_STATE()->prev_group_state->last_applied_index;
        RAFT_STATE()->last_applied_term = RAFT_STATE()->prev_group_state->last_applied_term;
        RAFT_STATE()->term = RAFT_STATE()->prev_group_state->term;

        zfree(RAFT_STATE()->prev_group_state);
        RAFT_STATE()->prev_group_state = NULL;

        /* Also become leader */
        clusterRaftSetNodeRole(myself, RAFT_ROLE_LEADER);
        memcpy(RAFT_STATE()->leader_name, myself->name, CLUSTER_NAMELEN);

        /* Move any nodes we learned about to EXTERNAL */
        dictIterator di;
        dictEntry *de;
        dictInitIterator(&di, server.cluster->nodes);
        while ((de = dictNext(&di))) {
            clusterNode *node = dictGetVal(de);
            if (node->flags & CLUSTER_NODE_MYSELF) continue;
            clusterRaftSetNodeRole(node, RAFT_ROLE_EXTERNAL);
        }
    }
}

int raftLogEntryMatch(void *val1, void *val2) {
    raftLogEntry *entry1 = val1;
    raftLogEntry *entry2 = val2;
    return entry1->index == entry2->index && entry1->term == entry2->term;
}

void raftAppliedEntryFree(void *val) {
    raftAppliedEntry *ae = val;
    sdsfree(ae->value);
    zfree(ae);
}

static void clusterRaftAppliedEntryDictEntryDestructor(void *entry) {
    dictEntry *de = entry;
    dictSdsDestructor(dictGetKey(de));
    raftAppliedEntryFree(dictGetVal(de));
    zfree(de);
}

dictType clusterRaftAppliedEntryDictType = {
    .entryGetKey = dictEntryGetKey,
    .hashFunction = dictSdsHash,
    .keyCompare = dictSdsKeyCompare,
    .entryDestructor = clusterRaftAppliedEntryDictEntryDestructor,
};

/* Initialize the Raft state for this node. This will result in this node
 * becoming the leader of a new Raft cluster with just itself.*/
void clusterRaftInit(void) {
    server.cluster->protocol_data = zcalloc(sizeof(clusterRaftState));
    RAFT_STATE()->term = 0;
    memset(RAFT_STATE()->voted_for, 0, CLUSTER_NAMELEN);
    RAFT_STATE()->granted_vote_count = 0;
    RAFT_STATE()->heartbeat_timer = 0;
    RAFT_STATE()->applied_entries = dictCreate(&clusterRaftAppliedEntryDictType);
    RAFT_STATE()->pending_entries = listCreate();
    listSetMatchMethod(RAFT_STATE()->pending_entries, raftLogEntryMatch);
    RAFT_STATE()->nodes_to_pong_once_disabled = listCreate();
    RAFT_STATE()->proposal_retry_timer = 0;
    RAFT_STATE()->join_start_time = 0;

    RAFT_STATE()->enabled = server.cluster_raft_enabled;
}

static void clusterRaftInitLast(void) {
    /* Initialize fields that depend on server.cluster->myself */
    memcpy(RAFT_STATE()->leader_name, server.cluster->myself->name, CLUSTER_NAMELEN);
    clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_LEADER);

    RAFT_DATA(server.cluster->myself)->member_count = 1;

    /* We always begin in a Raft cluster with just ourselves */
    sds my_name_sds = sdsnewlen(server.cluster->myself->name, CLUSTER_NAMELEN);

    /* Also add it to the applied entries so it is included in snapshots */
    list *proposals = listCreate();
    listSetFreeMethod(proposals, freeRaftKeyValue);
    raftKeyValue *kv = zmalloc(sizeof(*kv));
    kv->key = sdsnew("membership");
    kv->value = sdsdup(my_name_sds);
    listAddNodeTail(proposals, kv);
    raftLogEntry *entry = raftLogEntryCreate(0, 1, proposals);
    listRelease(proposals);

    raftAppliedEntry *ae = zmalloc(sizeof(*ae));
    ae->index = entry->index;
    ae->term = entry->term;
    ae->value = sdsdup(entry->mutations[0].value);
    dictAdd(RAFT_STATE()->applied_entries, sdsdup(entry->mutations[0].key), ae);

    RAFT_STATE()->last_applied_index = 1;
    RAFT_STATE()->last_applied_term = 0;

    if (!connectionByType(connTypeOfCluster()->get_type())) {
        serverLog(LL_WARNING, "Missing connection type %s, but it is required for the Cluster bus.",
                  getConnectionTypeName(connTypeOfCluster()->get_type()));
        exit(1);
    }

    int port = defaultClientPort();
    connListener *listener = &server.clistener;
    listener->count = 0;
    listener->bindaddr = server.bindaddr;
    listener->bindaddr_count = server.bindaddr_count;
    listener->port = server.cluster_port ? server.cluster_port : port + CLUSTER_PORT_INCR;
    listener->ct = connTypeOfCluster();
    if (connListen(listener) == C_ERR) {
        /* Note: the following log text is matched by the test suite. */
        serverLog(LL_WARNING, "Failed listening on port %u (cluster), aborting.", listener->port);
        exit(1);
    }

    if (createSocketAcceptHandler(&server.clistener, clusterAcceptHandler) != C_OK) {
        serverPanic("Unrecoverable error creating Cluster socket accept handler.");
    }
}

uint32_t clusterRaftValidateMessageHeader(char *header) {
    clusterRaftHeader *hdr = (clusterRaftHeader *)header;
    if (memcmp(hdr->sig, "RAFT", 4) != 0) return 0;
    return ntohl(hdr->totlen);
}

int clusterRaftProcessMessage(clusterLink *link) {
    clusterRaftHeader *hdr = (clusterRaftHeader *)link->rcvbuf;
    uint16_t type = ntohs(hdr->type);
    void *payload = link->rcvbuf + sizeof(clusterRaftHeader);
    uint32_t totlen = ntohl(hdr->totlen);
    size_t payload_len = totlen - sizeof(clusterRaftHeader);

    clusterNode *sender = link->node;
    if (!sender) {
        if (type != CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REQUEST) {
            serverLog(LL_WARNING, "Raft: Unexpected message type %d from unknown sender", type);
            return 0;
        }
    }

    switch (type) {
    case CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REQUEST:
    case CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REPLY:
        clusterRaftProcessHandshake(link, type, (clusterMsgRaftHandshake *)payload);
        break;
    case CLUSTERMSG_TYPE_RAFT_VOTE_REQUEST:
        clusterRaftProcessVoteRequest(sender, (clusterMsgRaftVoteRequest *)payload);
        break;
    case CLUSTERMSG_TYPE_RAFT_VOTE_RESPONSE:
        clusterRaftProcessVoteResponse(sender, (clusterMsgRaftVoteResponse *)payload);
        break;
    case CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES_ACK:
        clusterRaftProcessAppendEntriesAck(sender, (clusterMsgRaftAppendEntriesAck *)payload);
        break;
    case CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES:
        clusterRaftProcessAppendEntries(sender, (clusterMsgRaftAppendEntries *)payload, payload_len);
        break;
    case CLUSTERMSG_TYPE_RAFT_PROPOSE_ENTRY:
        clusterRaftProcessProposeEntries(link, (clusterMsgRaftProposeEntries *)payload, payload_len);
        break;
    case CLUSTERMSG_TYPE_RAFT_SNAPSHOT_REQUEST:
        clusterRaftProcessSnapshotRequest(link, payload);
        break;
    case CLUSTERMSG_TYPE_RAFT_SNAPSHOT_RESPONSE:
        clusterRaftProcessSnapshotResponse(sender, payload, payload_len);
        break;
    default:
        serverLog(LL_WARNING, "Unknown Raft message type %d", type);
        return 0;
    }
    return 1;
}

clusterMsgSendBlock *createClusterRaftMsgSendBlock(int type, uint32_t payload_len) {
    uint32_t msglen = sizeof(clusterRaftHeader) + payload_len;
    uint32_t blocklen = sizeof(clusterMsgSendBlock) + msglen;
    clusterMsgSendBlock *msgblock = zcalloc(blocklen);
    msgblock->refcount = 1;
    msgblock->totlen = blocklen;
    msgblock->len = msglen;
    server.stat_cluster_links_memory += blocklen;

    clusterRaftHeader *hdr = (clusterRaftHeader *)msgblock->data;
    memcpy(hdr->sig, "RAFT", 4);
    hdr->totlen = htonl(msglen);
    hdr->ver = htons(1);
    hdr->type = htons(type);

    return msgblock;
}

void clusterRaftInitNodeData(clusterNode *node) {
    node->protocol_data = zmalloc(sizeof(clusterNodeRaftData));
    RAFT_DATA(node)->match_index = 0;
    clusterRaftSetNodeRole(node, RAFT_ROLE_HANDSHAKING);
    RAFT_DATA(node)->outbound_link_established = 0;
}

static void clusterRaftFreeNodeData(clusterNode *node) {
    if (node->protocol_data) {
        zfree(node->protocol_data);
        node->protocol_data = NULL;
    }
}

void clusterRaftStateMachine(void) {
    if (server.cluster == NULL || !RAFT_STATE()) return;

    mstime_t now = mstime();

    /* 1. Handle other nodes */
    dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
    dictEntry *de;
    while ((de = dictNext(di)) != NULL) {
        clusterNode *node = dictGetVal(de);
        if (node == server.cluster->myself) continue;
        if (!RAFT_DATA(node)) continue;

        /* Reconnect logic (skip for myself handled above) */
        if (node->link == NULL) {
            mstime_t reconnect_interval = server.cluster_node_timeout / 2;
            if (now - node->outbound_link_attempt_time >= reconnect_interval) {
                node->outbound_link_attempt_time = now;
                serverLog(LL_NOTICE, "Raft: Reconnecting to node %.40s (%s:%d)",
                          node->name, node->ip, node->cport);
                clusterRaftConnectToNode(node);
            }
            continue; /* Cannot do much without a link */
        }

        switch (RAFT_DATA(node)->role) {
        case RAFT_ROLE_HANDSHAKING:
            /* Step 7: Once both inbound and outbound link are tracked, transition to EXTERNAL */
            if (node->link && connGetState(node->link->conn) == CONN_STATE_CONNECTED && node->inbound_link != NULL) {
                clusterRaftSetNodeRole(node, RAFT_ROLE_EXTERNAL);
                node->flags &= ~CLUSTER_NODE_HANDSHAKE;
            }
            break;
        case RAFT_ROLE_EXTERNAL: {
            /* Step 8: Reconciliation */
            uint32_t my_member_count = clusterRaftGetMemberCount();
            uint32_t req_member_count = RAFT_DATA(node)->member_count;
            bool should_join = false;

            if (my_member_count == 1 && req_member_count == 1) {
                /* Both are single-node clusters, use tie-breaker */
                clusterNode *myself = getMyClusterNode();
                if (memcmp(node->name, myself->name, CLUSTER_NAMELEN) > 0) {
                    should_join = true;
                }
            } else if (my_member_count == 1 && req_member_count > 1) {
                should_join = true;
            }

            if (should_join) {
                if (MY_RAFT_ROLE != RAFT_ROLE_JOINING) {
                    serverLog(LL_NOTICE, "Raft: Decided to join cluster of %.40s (members %u)",
                              node->name, req_member_count);
                    clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_JOINING);
                    RAFT_STATE()->join_start_time = now;
                    memcpy(RAFT_STATE()->leader_name, node->name, CLUSTER_NAMELEN);
                }
            }
        } break;
        default:
            /* Other states handled in specific message processors */
            break;
        }
    }
    dictReleaseIterator(di);

    /* 2. Handle myself */
    switch (MY_RAFT_ROLE) {
    case RAFT_ROLE_FOLLOWER:
    case RAFT_ROLE_CANDIDATE:
        if (now > RAFT_STATE()->election_timer) {
            serverLog(LL_NOTICE, "Raft: Starting election for term %llu", (unsigned long long)RAFT_STATE()->term + 1);
            clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_CANDIDATE);
            RAFT_STATE()->term++;
            memcpy(RAFT_STATE()->voted_for, server.cluster->myself->name, CLUSTER_NAMELEN);
            RAFT_STATE()->granted_vote_count = 1;
            RAFT_STATE()->denied_vote_count = 0;
            RAFT_STATE()->election_timer = now + server.cluster_raft_election_timeout + (rand() % 150);
            clusterRaftSendVoteRequests();
        }
        break;
    case RAFT_ROLE_LEADER:
        if (now > RAFT_STATE()->heartbeat_timer) {
            /* Send heartbeats */
            clusterRaftSendAppendEntries();
            RAFT_STATE()->heartbeat_timer = now + server.cluster_raft_heartbeat_interval;
        }
        break;
    case RAFT_ROLE_JOINING:
        /* Check for join timeout */
        if (now - RAFT_STATE()->join_start_time > 10000) { /* 10 seconds timeout */
            serverLog(LL_WARNING, "Raft: Join attempt timed out. Restoring previous group.");
            clusterRaftPreviousGroupStateRestore();

            break;
        }

        if (now > RAFT_STATE()->proposal_retry_timer) {
            clusterNode *leader = clusterLookupNode(RAFT_STATE()->leader_name, CLUSTER_NAMELEN);
            if (leader) {
                if (leader->link) {
                    serverLog(LL_NOTICE, "Raft: Retrying by requesting fresh snapshot from leader %.40s", leader->name);
                    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_SNAPSHOT_REQUEST, sizeof(clusterMsgRaftSnapshotRequest));
                    clusterMsgRaftSnapshotRequest *sn_req = (clusterMsgRaftSnapshotRequest *)((char *)msgblock->data + sizeof(clusterRaftHeader));
                    sn_req->term = htonu64(RAFT_STATE()->term);
                    clusterLinkSendBlock(leader->link, msgblock);
                    clusterMsgSendBlockDecrRefCount(msgblock);
                } else {
                    serverLog(LL_NOTICE, "Raft: Retrying by connecting to leader %.40s", leader->name);
                    clusterRaftConnectToNode(leader);
                }
            }
            RAFT_STATE()->proposal_retry_timer = now + 2000; /* Retry every 2 seconds */
        }
        break;
    }
}


void clusterRaftFree(void) {
    if (RAFT_STATE()) {
        dictRelease(RAFT_STATE()->applied_entries);

        listNode *ln;
        while ((ln = listFirst(RAFT_STATE()->pending_entries))) {
            raftLogEntry *entry = ln->value;
            listDelNode(RAFT_STATE()->pending_entries, ln);
            raftLogEntryFree(entry);
        }
        listRelease(RAFT_STATE()->pending_entries);

        listRelease(RAFT_STATE()->nodes_to_pong_once_disabled);

        zfree(RAFT_STATE());
        server.cluster->protocol_data = NULL;
    }
}

static inline void encodeUint64(char **ptr, uint64_t val) {
    uint64_t n = htonu64(val);
    memcpy(*ptr, &n, sizeof(n));
    *ptr += sizeof(n);
}

static inline void encodeUint32(char **ptr, uint32_t val) {
    uint32_t n = htonl(val);
    memcpy(*ptr, &n, sizeof(n));
    *ptr += sizeof(n);
}

static inline int decodeUint64(char **ptr, char *end, uint64_t *val) {
    if (*ptr + sizeof(uint64_t) > end) return C_ERR;
    memcpy(val, *ptr, sizeof(uint64_t));
    *val = ntohu64(*val);
    *ptr += sizeof(uint64_t);
    return C_OK;
}

static inline int decodeUint32(char **ptr, char *end, uint32_t *val) {
    if (*ptr + sizeof(uint32_t) > end) return C_ERR;
    memcpy(val, *ptr, sizeof(uint32_t));
    *val = ntohl(*val);
    *ptr += sizeof(uint32_t);
    return C_OK;
}

static inline void encodeString(char **ptr, const char *str, uint32_t len) {
    encodeUint32(ptr, len);
    memcpy(*ptr, str, len);
    *ptr += len;
}

static inline sds decodeString(char **ptr, char *end) {
    uint32_t len;
    if (decodeUint32(ptr, end, &len) != C_OK) return NULL;
    if (*ptr + len > end) return NULL;
    sds s = sdsnewlen(*ptr, len);
    *ptr += len;
    return s;
}

size_t clusterRaftComputeSerializedEntrySize(raftLogEntry *entry) {
    size_t size = sizeof(uint64_t) * 2 + sizeof(uint32_t); // index, term, count
    for (uint32_t i = 0; i < entry->count; i++) {
        size += sizeof(uint32_t) * 2 + sdslen(entry->mutations[i].key) + sdslen(entry->mutations[i].value);
    }
    return size;
}

size_t clusterRaftSerializeEntry(raftLogEntry *entry, char *buf) {
    char *initial_buf = buf;

    encodeUint64(&buf, entry->index);
    encodeUint64(&buf, entry->term);
    encodeUint32(&buf, entry->count);
    for (uint32_t i = 0; i < entry->count; i++) {
        encodeString(&buf, entry->mutations[i].key, sdslen(entry->mutations[i].key));
        encodeString(&buf, entry->mutations[i].value, sdslen(entry->mutations[i].value));
    }

    return buf - initial_buf;
}

raftLogEntry *clusterRaftDeserializeEntry(char *cursor, char *end, size_t *consumed_out) {
    char *cursor_start = cursor;

    uint64_t index;
    uint64_t term;
    uint32_t count;
    if (decodeUint64(&cursor, end, &index) != C_OK) return NULL;
    if (decodeUint64(&cursor, end, &term) != C_OK) return NULL;
    if (decodeUint32(&cursor, end, &count) != C_OK) return NULL;

    list *proposals = listCreate();
    listSetFreeMethod(proposals, freeRaftKeyValue);

    for (uint32_t i = 0; i < count; i++) {
        sds key = decodeString(&cursor, end);
        if (!key) {
            listRelease(proposals);
            return NULL;
        }
        sds value = decodeString(&cursor, end);
        if (!value) {
            sdsfree(key);
            listRelease(proposals);
            return NULL;
        }

        raftKeyValue *kv = zmalloc(sizeof(*kv));
        kv->key = key;
        kv->value = value;
        listAddNodeTail(proposals, kv);
    }

    *consumed_out = cursor - cursor_start;

    raftLogEntry *entry = raftLogEntryCreate(term, index, proposals);
    listRelease(proposals);
    return entry;
}

/* Get the latest value in the Raft log. */
raftLogEntry *clusterRaftGetLatestEntry(void) {
    if (listLength(RAFT_STATE()->pending_entries) == 0) {
        static raftLogEntry dummy;
        dummy.index = RAFT_STATE()->last_applied_index;
        dummy.term = RAFT_STATE()->last_applied_term;
        return &dummy;
    }
    return listLast(RAFT_STATE()->pending_entries)->value;
}

void clusterRaftAdvanceTerm(uint32_t new_term) {
    RAFT_STATE()->term = new_term;
    memset(RAFT_STATE()->voted_for, 0, CLUSTER_NAMELEN);
    if (MY_RAFT_ROLE == RAFT_ROLE_JOINING) return;
    if (MY_RAFT_ROLE == RAFT_ROLE_CANDIDATE) {
        serverLog(LL_NOTICE, "Raft: Failing election due to higher term %llu", (unsigned long long)new_term);
    } else if (MY_RAFT_ROLE == RAFT_ROLE_LEADER) {
        serverLog(LL_NOTICE, "Raft: Stepping down to follower, new term %llu", (unsigned long long)new_term);
    }
    clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_FOLLOWER);
}

/* Compare two term-index pairs.
 *
 * Return 1 if (term1, index1) > (term2, index2), -1 if (term1, index1) < (term2, index2), and 0 if
 * they are equal. */
int clusterRaftCompareTermIndexPairs(uint64_t term1, uint64_t index1, uint64_t term2, uint64_t index2) {
    if (term1 > term2) return 1;
    if (term1 < term2) return -1;
    if (index1 > index2) return 1;
    if (index1 < index2) return -1;
    return 0;
}

/* Get the number of committed Raft members (nodes not in HANDSHAKE state). */
int clusterRaftGetMemberCount(void) {
    int count = 0;
    dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
    dictEntry *de;
    while ((de = dictNext(di)) != NULL) {
        clusterNode *node = dictGetVal(de);
        if (!RAFT_DATA(node)) continue;

        int role = RAFT_DATA(node)->role;
        if (node->flags & CLUSTER_NODE_MYSELF ||
            role == RAFT_ROLE_FOLLOWER ||
            role == RAFT_ROLE_LEADER ||
            role == RAFT_ROLE_JOINING) {
            count++;
        }
    }
    dictReleaseIterator(di);
    return count;
}

/* Add a new (uncommitted) entry to the Raft log. Takes ownership of key and value. */
void clusterRaftAddEntry(list *proposals) {
    if (RAFT_STATE() == NULL || MY_RAFT_ROLE != RAFT_ROLE_LEADER) {
        return;
    }
    raftLogEntry *latest_entry = clusterRaftGetLatestEntry();
    uint64_t next_index = latest_entry ? latest_entry->index + 1 : 1;
    raftLogEntry *new_entry = raftLogEntryCreate(RAFT_STATE()->term, next_index, proposals);
    serverLog(LL_NOTICE, "Raft: New pending entry (index=%lu, term=%lu) with %u keys", (unsigned long)new_entry->index, (unsigned long)new_entry->term, new_entry->count);
    listAddNodeTail(RAFT_STATE()->pending_entries, new_entry);

    /* Update node states if this is a membership entry */
    clusterRaftOnAppendEntry(new_entry);

    /* TODO start background IO job to persist the new entry */

    int total_members = clusterRaftGetMemberCount();
    if (total_members <= 1) {
        clusterRaftAdvanceCommitIndexToMajority();
    }

    /* Send the append entries before we go to sleep. */
    RAFT_STATE()->todo_before_sleep |= RAFT_TODO_BROADCAST_APPEND_ENTRIES;
}
void clusterRaftSendHandshakeReply(clusterLink *link, const char *node_name) {
    serverLog(LL_VERBOSE, "Raft: Sending handshake response to %.40s", node_name);

    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REPLY, sizeof(clusterMsgRaftHandshake));
    clusterMsgRaftHandshake *resp = (clusterMsgRaftHandshake *)((char *)msgblock->data + sizeof(clusterRaftHeader));

    memcpy(resp->sender_name, server.cluster->myself->name, CLUSTER_NAMELEN);
    resp->member_count = htonl(clusterRaftGetMemberCount());

    /* Get IP from connection for the responder */
    char ip[NET_IP_STR_LEN] = {0};
    if (nodeIp2String(ip, link, "") == C_OK) {
        memcpy(resp->remote_ip, ip, NET_IP_STR_LEN);
    }

    resp->plaintext_port = htons(server.port);
    resp->tls_port = htons(server.tls_port);
    resp->cluster_port = htons(myself->cport);

    clusterLinkSendBlock(link, msgblock);
    clusterMsgSendBlockDecrRefCount(msgblock);
}

void clusterRaftOnCommitEntry(raftLogEntry *entry) {
    for (uint32_t j = 0; j < entry->count; j++) {
        /* Handle special configs */
        if (strcmp(entry->mutations[j].key, "membership") == 0) {
            int argc = 0;
            sds *splitres = sdssplitlen(entry->mutations[j].value, sdslen(entry->mutations[j].value), " ", 1, &argc);
            if (!splitres) {
                serverLog(LL_WARNING, "Raft: Failed to split membership string: %s", entry->mutations[j].value);
                continue;
            }

            for (int i = 0; i < argc; i++) {
                clusterNode *n = clusterLookupNode(splitres[i], sdslen(splitres[i]));
                if (n && RAFT_DATA(n)->role == RAFT_ROLE_JOINING) {
                    clusterRaftSetNodeRole(n, RAFT_ROLE_FOLLOWER);

                    /* If I was joining do the post-join cleanup */
                    if (n == myself) {
                        RAFT_STATE()->election_timer = mstime() + 1000 + (rand() % 1000);
                        serverLog(LL_NOTICE, "Raft: Joined cluster successfully, transitioned to FOLLOWER");

                        if (RAFT_STATE()->prev_group_state) {
                            serverLog(LL_NOTICE, "Raft: Join successful, clearing backup");
                            clusterRaftPreviousGroupStateCleanup();
                        }
                    }
                }
            }

            sdsfreesplitres(splitres, argc);
        }
    }
}

/* Advance the commit index, applying pending changes if they are now committed. */
void clusterRaftAdvanceCommitIndex(uint64_t commit_index) {
    /* Nothing to do if the commit index is already applied. */
    if (commit_index <= RAFT_STATE()->last_applied_index) return;

    while (RAFT_STATE()->pending_entries->len > 0) {
        listNode *node = listFirst(RAFT_STATE()->pending_entries);
        raftLogEntry *entry = listNodeValue(node);
        if (entry->index > commit_index) break;
        listDelNode(RAFT_STATE()->pending_entries, node);

        bool added_any = false;
        for (uint32_t i = 0; i < entry->count; i++) {
            raftAppliedEntry *ae = zmalloc(sizeof(*ae));
            ae->index = entry->index;
            ae->term = entry->term;
            ae->value = sdsdup(entry->mutations[i].value);
            dictReplace(RAFT_STATE()->applied_entries, sdsdup(entry->mutations[i].key), ae);
            serverLog(LL_NOTICE, "Raft: New applied value for %s (index=%lu, term=%lu): %s", entry->mutations[i].key, (unsigned long)commit_index, (unsigned long)entry->term, entry->mutations[i].value);
            added_any = true;
        }

        if (added_any) {
            RAFT_STATE()->last_applied_index = entry->index;
            RAFT_STATE()->last_applied_term = entry->term;
            clusterRaftOnCommitEntry(entry);
        }
        raftLogEntryFree(entry);
    }

    if (MY_RAFT_ROLE == RAFT_ROLE_LEADER) {
        /* The commit index has advanced, so we need to send AppendEntries to
         * all nodes to update their commit index. */
        // clusterDoBeforeSleep(CLUSTER_TODO_BROADCAST_ALL);
    }
}
void clusterRaftConnectToNode(clusterNode *node) {
    if (node->link) return;
    clusterLink *link = createClusterLink(node);
    link->conn = connCreate(connTypeOfCluster());
    connSetPrivateData(link->conn, link);
    if (connConnect(link->conn, node->ip, node->cport, server.bind_source_addr, 0, clusterLinkConnectHandler) == C_ERR) {
        serverLog(LL_WARNING, "Raft: Failed to initiate connection to %.40s", node->name);
        freeClusterLink(link);
    }
}

void clusterRaftCron(void) {
    /* No work if cluster is not initialized or we are not in a Raft cluster. */
    if (server.cluster == NULL || !RAFT_STATE()) return;

    /* Run state machine periodically */
    clusterRaftStateMachine();
}

/* -----------------------------------------------------------------------------
 * Raft Membership Management
 * -------------------------------------------------------------------------- */


/* -----------------------------------------------------------------------------
 * User Raft Commands
 * -------------------------------------------------------------------------- */

/* User command to get Raft info. Currently just for testing. */
void clusterRaftInfo(client *c) {
    if (!RAFT_STATE()) {
        addReplyError(c, "Raft not initialized");
        return;
    }
    sds info = sdsempty();
    info = sdscatprintf(info, "raft_role:");
    if (MY_RAFT_ROLE == RAFT_ROLE_LEADER) {
        info = sdscatprintf(info, "leader\r\n");
    } else if (MY_RAFT_ROLE == RAFT_ROLE_CANDIDATE) {
        info = sdscatprintf(info, "candidate\r\n");
    } else {
        info = sdscatprintf(info, "follower\r\n");
    }
    info = sdscatprintf(info, "raft_node_id:%.40s\r\n", server.cluster->myself->name);
    info = sdscatprintf(info, "raft_term:%llu\r\n", (unsigned long long)RAFT_STATE()->term);
    info = sdscatprintf(info, "raft_leader:%.40s\r\n", RAFT_STATE()->leader_name);
    info = sdscatprintf(info, "raft_voted_for:%.40s\r\n", RAFT_STATE()->voted_for);
    info = sdscatprintf(info, "raft_applied_key_count:%zu\r\n", dictSize(RAFT_STATE()->applied_entries));
    info = sdscatprintf(info, "raft_pending_queue_size:%zu\r\n", listLength(RAFT_STATE()->pending_entries));
    info = sdscatprintf(info, "raft_applied_index:%llu\r\n", (unsigned long long)RAFT_STATE()->last_applied_index);
    info = sdscatprintf(info, "raft_pending_index:%llu\r\n", (unsigned long long)(listLength(RAFT_STATE()->pending_entries) ? ((raftLogEntry *)RAFT_STATE()->pending_entries->tail->value)->index : 0));
    addReplyVerbatim(c, info, sdslen(info), "txt");
    sdsfree(info);
}

/* User command to get metadata. Currently just for testing. */
void clusterRaftGetMetadata(client *c) {
    if (!RAFT_STATE()) {
        addReplyError(c, "Raft not initialized");
        return;
    }
    if (c->argc != 3) {
        addReplyError(c, "Wrong number of arguments");
        return;
    }
    dictEntry *de = dictFind(RAFT_STATE()->applied_entries, objectGetVal(c->argv[2]));
    if (!de) {
        addReplyError(c, "Metadata not found");
        return;
    }
    addReplyBulkCBuffer(c, dictGetVal(de), sdslen(dictGetVal(de)));
}

/* User command to set metadata. Currently just for testing. */
void clusterRaftSetMetadata(client *c) {
    if (!RAFT_STATE()) {
        addReplyError(c, "Raft not initialized");
        return;
    }
    if (c->argc != 4) {
        addReplyError(c, "Wrong number of arguments");
        return;
    }
    if (MY_RAFT_ROLE != RAFT_ROLE_LEADER) {
        if (RAFT_STATE()->leader_name[0] != '\0') {
            /* Redirect to leader */
            clusterNode *leader = clusterLookupNode(RAFT_STATE()->leader_name, CLUSTER_NAMELEN);
            if (leader) {
                addReplyErrorFormat(c, "TRY_LEADER %.40s %s:%d", leader->name, leader->ip, leader->tcp_port);
            } else {
                addReplyError(c, "Raft leader unknown");
            }
        } else {
            addReplyError(c, "No Raft leader elected");
        }
        return;
    }

    /* We are leader, update metadata */
    list *proposals = listCreate();
    listSetFreeMethod(proposals, freeRaftKeyValue);
    raftKeyValue *kv = zmalloc(sizeof(*kv));
    kv->key = sdsdup(objectGetVal(c->argv[2]));
    kv->value = sdsdup(objectGetVal(c->argv[3]));
    listAddNodeTail(proposals, kv);
    clusterRaftAddEntry(proposals);
    listRelease(proposals);

    /* TODO start background IO job to persist the new entry */

    /* Send the append entries before we go to sleep. */
    // clusterDoBeforeSleep(CLUSTER_TODO_BROADCAST_ALL);
    addReply(c, shared.ok);
}

/* -----------------------------------------------------------------------------
 * Raft Election Implementation
 * -------------------------------------------------------------------------- */

/* Send vote requests to all raft members to elect myself */
void clusterRaftSendVoteRequests(void) {
    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_VOTE_REQUEST, sizeof(clusterMsgRaftVoteRequest));
    clusterMsgRaftVoteRequest *req = (clusterMsgRaftVoteRequest *)((char *)msgblock->data + sizeof(clusterRaftHeader));
    raftLogEntry *latest_entry = clusterRaftGetLatestEntry();
    req->term = htonu64(RAFT_STATE()->term);
    req->last_entry_index = htonu64(latest_entry->index);
    req->last_entry_term = htonu64(latest_entry->term);

    serverLog(LL_VERBOSE, "Raft: Requesting votes for term %llu", (unsigned long long)RAFT_STATE()->term);
    dictIterator di;
    dictInitIterator(&di, server.cluster->nodes);
    dictEntry *de;
    while ((de = dictNext(&di)) != NULL) {
        clusterNode *node = dictGetVal(de);
        if (node->flags & (CLUSTER_NODE_MYSELF | CLUSTER_NODE_HANDSHAKE)) continue;
        if (node->link == NULL) continue;
        if (!RAFT_DATA(node)) continue;
        clusterLinkSendBlock(node->link, msgblock);
    }
    clusterMsgSendBlockDecrRefCount(msgblock);
}

/* Send AppendEntries to all registered Raft members. */
void clusterRaftSendAppendEntries(void) {
    if (!RAFT_STATE() || MY_RAFT_ROLE != RAFT_ROLE_LEADER) return;

    dictIterator di;
    dictInitIterator(&di, server.cluster->nodes);
    dictEntry *de;

    while ((de = dictNext(&di)) != NULL) {
        clusterNode *node = dictGetVal(de);

        if (node->flags & CLUSTER_NODE_MYSELF) continue;
        if (!RAFT_DATA(node)) continue;
        if (node->flags & CLUSTER_NODE_HANDSHAKE || RAFT_DATA(node)->role == RAFT_ROLE_HANDSHAKING) {
            serverLog(LL_NOTICE, "Raft: skipping %.40s because it is in HANDSHAKING state", node->name);
            continue;
        }
        if (RAFT_DATA(node)->role == RAFT_ROLE_EXTERNAL) continue;

        if (node->link == NULL || connGetState(node->link->conn) != CONN_STATE_CONNECTED || !RAFT_DATA(node)->outbound_link_established) {
            serverLog(LL_NOTICE, "Raft: skipping %.40s because link is NULL or not connected or not established", node->name);
            continue;
        }

        /* Find the last log entry matching the previous match index. If the
         * node is lagging, match index may be before our pending entries. */
        uint64_t match_index = RAFT_DATA(node)->match_index;
        listIter li;
        listRewind(RAFT_STATE()->pending_entries, &li);
        listNode *ln;
        listNode *prev_entry = NULL;
        while ((ln = listNext(&li))) {
            raftLogEntry *entry = ln->value;
            if (entry->index > match_index) {
                break;
            }
            prev_entry = ln;
        }

        /* In the case of lag, optimistically send from the first pending entry. */
        listNode *first_entry_to_send = prev_entry ? prev_entry->next : RAFT_STATE()->pending_entries->head;

        /* Compute number of entries to send */
        size_t entries_count = 0;
        size_t total_entries_size = 0;
        ln = first_entry_to_send;
        while (ln) {
            total_entries_size += clusterRaftComputeSerializedEntrySize(ln->value);
            entries_count++;
            ln = ln->next;
        }

        /* Build the AppendEntries message */
        clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(
            CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES,
            sizeof(clusterMsgRaftAppendEntries) + total_entries_size);
        clusterMsgRaftAppendEntries *ext =
            (clusterMsgRaftAppendEntries *)((char *)msgblock->data + sizeof(clusterRaftHeader));
        ext->term = htonu64(RAFT_STATE()->term);
        memcpy(ext->leader_name, server.cluster->myself->name, CLUSTER_NAMELEN);
        ext->prev_log_index = htonu64(match_index);
        if (prev_entry) {
            raftLogEntry *prev_entry_value = prev_entry->value;
            ext->prev_log_term = htonu64(prev_entry_value->term);
            ext->prev_log_index = htonu64(prev_entry_value->index);
        } else {
            ext->prev_log_term = htonu64(RAFT_STATE()->last_applied_term);
            ext->prev_log_index = htonu64(RAFT_STATE()->last_applied_index);
        }
        ext->leader_commit = htonu64(RAFT_STATE()->last_applied_index);
        ext->entries_len = htonu64(entries_count);

        /* Serialize entries */
        char *cursor = ext->entries;
        ln = first_entry_to_send;
        while (ln) {
            cursor += clusterRaftSerializeEntry(ln->value, cursor);
            ln = ln->next;
        }

        /* Send and decrement ref count */
        clusterLinkSendBlock(node->link, msgblock);
        clusterMsgSendBlockDecrRefCount(msgblock);
    }
}

/* Handle a vote request to elect sender. */
void clusterRaftProcessVoteRequest(clusterNode *sender, clusterMsgRaftVoteRequest *req) {
    uint64_t term = ntohu64(req->term);
    bool grant = false;

    /* Handle term increment. */
    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
    }

    uint64_t last_entry_term = ntohu64(req->last_entry_term);
    uint64_t last_entry_index = ntohu64(req->last_entry_index);

    /* Determine if we should vote or not:
     * 1. We must be in the same term.
     * 2. We must not have voted for someone else in this term.
     * 3. The sender must have a value that is at least as up to date as ours. */
    raftLogEntry *local_entry = clusterRaftGetLatestEntry();
    if (term == RAFT_STATE()->term &&
        (RAFT_STATE()->voted_for[0] == '\0' ||
         memcmp(RAFT_STATE()->voted_for, sender->name, CLUSTER_NAMELEN) == 0) &&
        clusterRaftCompareTermIndexPairs(local_entry->term, local_entry->index, last_entry_term, last_entry_index) <= 0) {
        grant = true;
        memcpy(RAFT_STATE()->voted_for, sender->name, CLUSTER_NAMELEN);
        RAFT_STATE()->election_timer = mstime() + 1000 + (rand() % 1000);
        serverLog(LL_VERBOSE, "Raft: Granted vote to %.*s for term %llu", CLUSTER_NAMELEN, sender->name, (unsigned long long)term);
    }

    /* In either case, we respond to help facilitate the vote being decided.
     * Also if our term is higher, this will help catch the candidate up. */
    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_VOTE_RESPONSE, sizeof(clusterMsgRaftVoteResponse));
    clusterMsgRaftVoteResponse *resp = (clusterMsgRaftVoteResponse *)((char *)msgblock->data + sizeof(clusterRaftHeader));
    resp->term = htonu64(RAFT_STATE()->term);
    resp->vote_granted = grant;
    clusterLinkSendBlock(sender->link, msgblock);
    clusterMsgSendBlockDecrRefCount(msgblock);
}

/* Hanlde a vote response to our vote request from the sender. */
void clusterRaftProcessVoteResponse(clusterNode *sender, clusterMsgRaftVoteResponse *resp) {
    uint64_t term = ntohu64(resp->term);
    bool vote_granted = resp->vote_granted;
    UNUSED(sender);

    /* Handle term update. */
    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
        return;
    }

    /* Handle stale response. */
    if (term != RAFT_STATE()->term || MY_RAFT_ROLE != RAFT_ROLE_CANDIDATE) {
        return;
    }

    if (vote_granted) {
        RAFT_STATE()->granted_vote_count++;
    } else {
        RAFT_STATE()->denied_vote_count++;
    }

    int raft_nodes = clusterRaftGetMemberCount();
    int majority = (raft_nodes / 2) + 1;
    if (RAFT_STATE()->granted_vote_count >= majority) {
        serverLog(LL_NOTICE, "Raft: Elected leader for term %llu", (unsigned long long)RAFT_STATE()->term);
        clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_LEADER);
        memcpy(RAFT_STATE()->leader_name, server.cluster->myself->name, CLUSTER_NAMELEN);

        /* Reset other nodes' role to follower if they were leader */
        dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
        dictEntry *de;
        while ((de = dictNext(di)) != NULL) {
            clusterNode *n = dictGetVal(de);
            if (n != server.cluster->myself && RAFT_DATA(n)->role == RAFT_ROLE_LEADER) {
                clusterRaftSetNodeRole(n, RAFT_ROLE_FOLLOWER);
            }
        }
        dictReleaseIterator(di);

        /* Finish the election by sending AppendEntries via PONG to all nodes */
        // clusterDoBeforeSleep(CLUSTER_TODO_BROADCAST_ALL);
    } else if (RAFT_STATE()->denied_vote_count >= majority) {
        serverLog(LL_NOTICE, "Raft: Fast fail election after majority denied votes for term %llu", (unsigned long long)RAFT_STATE()->term);
        clusterRaftSetNodeRole(server.cluster->myself, RAFT_ROLE_FOLLOWER);
    }
}

void clusterRaftProcessHandshake(clusterLink *link, uint16_t type, clusterMsgRaftHandshake *req) {
    char *sender_name = req->sender_name;
    char *remote_ip = req->remote_ip;

    /* IP discovery */
    if (myself->ip[0] == '\0' && remote_ip[0] != '\0') {
        valkey_strlcpy(myself->ip, remote_ip, NET_IP_STR_LEN);
        char *colon = strchr(myself->ip, ':');
        if (colon) *colon = '\0';
        serverLog(LL_NOTICE, "Raft: Discovered my IP: %s", myself->ip);
    }

    if (verifyClusterNodeId(sender_name, CLUSTER_NAMELEN) != C_OK) {
        char hex[CLUSTER_NAMELEN * 2 + 1] = {0};
        for (int i = 0; i < CLUSTER_NAMELEN; i++) {
            snprintf(hex + i * 2, 3, "%02x", (unsigned char)sender_name[i]);
        }
        serverLog(LL_WARNING, "Raft: Received handshake with invalid sender name: %s", hex);
        return;
    }

    clusterNode *sender = clusterLookupNode(sender_name, CLUSTER_NAMELEN);
    if (!sender) {
        sender = createClusterNode(sender_name, CLUSTER_NODE_HANDSHAKE);
        clusterAddNode(sender);
        serverLog(LL_VERBOSE, "Raft: Created handshake node for %.40s", sender_name);
    }

    /* Get IP from connection if not set */
    if (sender->ip[0] == '\0') {
        nodeIp2String(sender->ip, link, "");
        serverLog(LL_VERBOSE, "Raft: Set IP for %.40s to %s from connection", sender_name, sender->ip);
        sender->flags &= ~CLUSTER_NODE_NOADDR;
    }

    /* Update ports */
    sender->tcp_port = ntohs(req->plaintext_port);
    sender->tls_port = ntohs(req->tls_port);
    sender->cport = ntohs(req->cluster_port);

    /* Bind link */
    if (link->node && (link->node->flags & CLUSTER_NODE_HANDSHAKE)) {
        if (link->node != sender) {
            serverLog(LL_NOTICE, "Raft: Moving link from handshake node %.40s to real node %.40s", link->node->name, sender->name);
            clusterNode *old_node = link->node;
            old_node->link = NULL;
            sender->link = link;
            link->node = sender;
            RAFT_DATA(sender)->outbound_link_established = RAFT_DATA(old_node)->outbound_link_established;
            /* Delete the old temporary node manually since clusterDelNode is not safe for Raft nodes */
            sds nodename = sdsnewlen(old_node->name, CLUSTER_NAMELEN);
            dictDelete(server.cluster->nodes, nodename);
            sdsfree(nodename);

            sdsfree(old_node->hostname);
            sdsfree(old_node->human_nodename);
            sdsfree(old_node->availability_zone);
            sdsfree(old_node->announce_client_ipv4);
            sdsfree(old_node->announce_client_ipv6);

            zfree(old_node->protocol_data);
            zfree(old_node);
        } else {
            /* Handshake complete on existing node link */
            serverLog(LL_NOTICE, "Raft: Handshake complete for existing node %.40s", sender->name);
        }
    } else if (!link->node) {
        setClusterNodeToInboundClusterLink(sender, link);
        /* Handshake complete for inbound link */
        serverLog(LL_VERBOSE, "Raft: Handshake complete for inbound link from %.40s", sender->name);

        /* Step 4: Create outbound link if it doesn't exist */
        if (!sender->link) {
            serverLog(LL_NOTICE, "Raft: Creating outbound link to %.40s on receiving handshake request", sender->name);
            clusterRaftConnectToNode(sender);
        }
    }

    /* Store member count for reconciliation */
    RAFT_DATA(sender)->member_count = ntohl(req->member_count);

    /* Update node state in state machine */
    clusterRaftStateMachine();

    /* Respond if we are the receiver of the initial handshake request */
    if (type == CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REQUEST) {
        clusterRaftSendHandshakeReply(link, sender_name);
    } else {
        serverLog(LL_VERBOSE, "Raft: Handshake complete with %.40s", sender_name);
    }
}

void clusterRaftProcessSnapshotRequest(clusterLink *link, void *payload) {
    clusterMsgRaftSnapshotRequest *req = payload;
    uint64_t term = ntohu64(req->term);

    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
    }

    uint32_t count = dictSize(RAFT_STATE()->applied_entries);
    size_t data_size = 0;
    dictIterator *di = dictGetSafeIterator(RAFT_STATE()->applied_entries);
    dictEntry *de;
    while ((de = dictNext(di)) != NULL) {
        sds key = dictGetKey(de);
        raftAppliedEntry *entry = dictGetVal(de);
        /* index, term, count(1), key, value */
        data_size += sizeof(uint64_t) * 2 + sizeof(uint32_t) + sizeof(uint32_t) * 2 + sdslen(key) + sdslen(entry->value);
    }
    dictReleaseIterator(di);

    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_SNAPSHOT_RESPONSE, sizeof(clusterMsgRaftSnapshotResponse) + data_size);
    clusterMsgRaftSnapshotResponse *resp = (clusterMsgRaftSnapshotResponse *)((char *)msgblock->data + sizeof(clusterRaftHeader));
    resp->term = htonu64(RAFT_STATE()->term);
    memcpy(resp->leader_name, RAFT_STATE()->leader_name, CLUSTER_NAMELEN);
    resp->count = htonl(count);

    char *ptr = resp->data;
    di = dictGetSafeIterator(RAFT_STATE()->applied_entries);
    while ((de = dictNext(di)) != NULL) {
        sds key = dictGetKey(de);
        raftAppliedEntry *entry = dictGetVal(de);
        encodeUint64(&ptr, entry->index);
        encodeUint64(&ptr, entry->term);
        encodeUint32(&ptr, 1); // count = 1
        encodeString(&ptr, key, sdslen(key));
        encodeString(&ptr, entry->value, sdslen(entry->value));
    }
    dictReleaseIterator(di);

    clusterLinkSendBlock(link, msgblock);
    clusterMsgSendBlockDecrRefCount(msgblock);
    serverLog(LL_VERBOSE, "Raft: Sent snapshot to %.40s (entries: %u)", clusterLinkGetNodeName(link), count);

    if (link->node && (link->node->flags & CLUSTER_NODE_HANDSHAKE)) {
        link->node->flags &= ~CLUSTER_NODE_HANDSHAKE;
        serverLog(LL_NOTICE, "Raft: Handshake complete for %.40s (cleared handshake flag)", link->node->name);
    }
}

static void freeRaftKeyValue(void *ptr) {
    raftKeyValue *prop = ptr;
    sdsfree(prop->key);
    sdsfree(prop->value);
    zfree(prop);
}

static raftKeyValue *createNodeInfoProposal(clusterNode *node) {
    raftKeyValue *prop = zmalloc(sizeof(*prop));
    prop->key = sdscatprintf(sdsempty(), "node:%.40s", node->name);
    char node_ip[NET_IP_STR_LEN];
    valkey_strlcpy(node_ip, node->ip, NET_IP_STR_LEN);
    prop->value = sdscatprintf(sdsempty(), "%s:%d:%d:%d", node_ip, node->tcp_port, node->tls_port, node->cport);
    return prop;
}

void clusterRaftSendJoinProposal(clusterNode *leader) {
    if (!RAFT_STATE()) return;
    if (MY_RAFT_ROLE != RAFT_ROLE_JOINING) return;
    if (!leader || !leader->link) {
        serverLog(LL_WARNING, "Raft: No link to leader to send join proposal, cannot join");
        return;
    }

    dictEntry *de;
    list *new_proposals = listCreate();
    listSetFreeMethod(new_proposals, (void (*)(void *))freeRaftKeyValue);

    /* Search for myself and leader in the snapshot */
    dictIterator *di_target = dictGetSafeIterator(RAFT_STATE()->applied_entries);
    bool found_myself_addr = false;
    bool found_leader_addr = false;
    while ((de = dictNext(di_target)) != NULL) {
        sds key = dictGetKey(de);
        if (sdslen(key) > sizeof(RAFT_NODE_PREFIX) && memcmp(key, RAFT_NODE_PREFIX, sizeof(RAFT_NODE_PREFIX) - 1) == 0) {
            char *node_id_str = key + sizeof(RAFT_NODE_PREFIX) - 1;
            if (strcmp(node_id_str, myself->name) == 0) found_myself_addr = true;
            if (strcmp(node_id_str, leader->name) == 0) found_leader_addr = true;
        }
    }
    dictReleaseIterator(di_target);

    if (!found_myself_addr) {
        raftKeyValue *myself_proposal = createNodeInfoProposal(myself);
        listAddNodeTail(new_proposals, myself_proposal);
    }
    if (!found_leader_addr) {
        raftKeyValue *leader_proposal = createNodeInfoProposal(leader);
        listAddNodeTail(new_proposals, leader_proposal);
    }

    /* Check that the old group's metadata will cleanly merge */
    dictIterator di;
    dictInitIterator(&di, RAFT_STATE()->prev_group_state->applied_entries);
    while ((de = dictNext(&di)) != NULL) {
        sds key = dictGetKey(de);
        raftAppliedEntry *entry = dictGetVal(de);
        if (strcmp(key, "membership") == 0) continue;

        if (dictFind(RAFT_STATE()->applied_entries, key)) {
            serverLog(LL_NOTICE, "Raft: Key %s conflicts in snapshot. Failing proposal and reverting to previous state", key);
            listRelease(new_proposals);
            clusterRaftPreviousGroupStateRestore();
            return;
        }

        raftKeyValue *clone = zmalloc(sizeof(*clone));
        clone->key = sdsdup(key);
        clone->value = sdsdup(entry->value);
        listAddNodeTail(new_proposals, clone);
    }

    /* Find membership in applied_entries */
    sds mem_key = sdsnew("membership");
    raftAppliedEntry *entry = dictFetchValue(RAFT_STATE()->applied_entries, mem_key);
    sdsfree(mem_key);
    if (!entry) {
        serverLog(LL_WARNING, "Raft: Target membership not found in applied_entries, cannot join");
        listRelease(new_proposals);
        return;
    }
    sds target_membership = entry->value;

    sds merged_membership = sdscat(sdsdup(target_membership), " ");
    merged_membership = sdscatlen(merged_membership, server.cluster->myself->name, CLUSTER_NAMELEN);
    serverLog(LL_NOTICE, "Raft: Created merged_membership of len %zu: '%s'", sdslen(merged_membership), merged_membership);
    raftKeyValue *membership_proposal = zmalloc(sizeof(*membership_proposal));
    membership_proposal->key = sdsnew("membership");
    membership_proposal->value = merged_membership;
    listAddNodeTail(new_proposals, membership_proposal);

    size_t data_size = 0;

    /* Compute the size of the CAS checks. Each existing entry is used as a CAS
     * check */
    dictInitIterator(&di, RAFT_STATE()->prev_group_state->applied_entries);
    while ((de = dictNext(&di)) != NULL) {
        sds key = dictGetKey(de);
        /* expected_index, expected_term, key_len, key */
        data_size += sizeof(uint64_t) + sizeof(uint64_t) + sizeof(uint32_t) + sdslen(key);
    }

    /* Compute the size of the proposals */
    listNode *ln;
    listIter li;
    listRewind(new_proposals, &li);
    while ((ln = listNext(&li)) != NULL) {
        raftKeyValue *entry = ln->value;
        /* key_len, key, value_len, value */
        data_size += sizeof(uint32_t) + sdslen(entry->key) + sizeof(uint32_t) + sdslen(entry->value);
    }

    /* Allocate message */
    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_PROPOSE_ENTRY, sizeof(clusterMsgRaftProposeEntries) + data_size);
    clusterMsgRaftProposeEntries *prop = (clusterMsgRaftProposeEntries *)((char *)msgblock->data + sizeof(clusterRaftHeader));
    prop->term = htonu64(RAFT_STATE()->term);
    prop->num_checks = htonl(dictSize(RAFT_STATE()->prev_group_state->applied_entries));
    prop->num_proposals = htonl(listLength(new_proposals));

    char *ptr = prop->data;

    /* Fill checks */
    dictInitIterator(&di, RAFT_STATE()->prev_group_state->applied_entries);
    while ((de = dictNext(&di)) != NULL) {
        sds key = dictGetKey(de);

        /* The CAS check should be based on the target group's applied entries
         * (that we just checked for conflicts). */
        dictEntry *de_target = dictFind(RAFT_STATE()->applied_entries, key);
        if (!de_target) {
            /* 0 means we expect no previous value. */
            encodeUint64(&ptr, 0);
            encodeUint64(&ptr, 0);
        } else {
            /* Use the target group's values for the CAS check. */
            raftAppliedEntry *target_entry = dictGetVal(de_target);
            encodeUint64(&ptr, target_entry->index);
            encodeUint64(&ptr, target_entry->term);
        }
        encodeString(&ptr, key, sdslen(key));
    }

    /* Fill proposals */
    listRewind(new_proposals, &li);
    while ((ln = listNext(&li)) != NULL) {
        raftKeyValue *entry = ln->value;
        encodeString(&ptr, entry->key, sdslen(entry->key));
        encodeString(&ptr, entry->value, sdslen(entry->value));
    }
    listRelease(new_proposals);

    clusterLinkSendBlock(leader->link, msgblock);
    serverLog(LL_NOTICE, "Raft: Sent join proposal to leader %.40s", leader->name);
    clusterMsgSendBlockDecrRefCount(msgblock);
}

void clusterRaftProcessSnapshotResponse(clusterNode *sender, void *payload, size_t payload_len) {
    clusterMsgRaftSnapshotResponse *resp = payload;
    uint64_t term = ntohu64(resp->term);
    uint32_t count = ntohl(resp->count);

    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
    }

    if (MY_RAFT_ROLE != RAFT_ROLE_JOINING && MY_RAFT_ROLE != RAFT_ROLE_FOLLOWER) {
        serverLog(LL_WARNING, "Raft: Received unexpected snapshot response from %.40s", clusterLinkGetNodeName(sender->link));
        return;
    }

    serverLog(LL_NOTICE, "Raft: Processing snapshot response from %.40s (entries: %u)", clusterLinkGetNodeName(sender->link), count);

    char *cursor = resp->data;
    char *end = (char *)payload + payload_len;

    if (MY_RAFT_ROLE == RAFT_ROLE_JOINING) {
        /* We cache a backup view of the previous group, which will later be
         * used during the join to merge the two groups.
         *
         * This view will also be restored if we fail to join for any reason. */
        clusterRaftPreviousGroupStateCreate();
    }

    dictEmpty(RAFT_STATE()->applied_entries, NULL);
    for (uint32_t i = 0; i < count; i++) {
        size_t consumed;
        raftLogEntry *entry = clusterRaftDeserializeEntry(cursor, end, &consumed);
        if (!entry) {
            serverLog(LL_WARNING, "Raft: Failed to deserialize entry in snapshot response from %.40s", clusterLinkGetNodeName(sender->link));
            raftLogEntryFree(entry);
            return;
        }
        cursor += consumed;
        if (entry->count != 1) {
            serverLog(LL_WARNING, "Raft: Invalid entry count %u in snapshot response from %.40s", entry->count, clusterLinkGetNodeName(sender->link));
            raftLogEntryFree(entry);
            return;
        }

        /* Add directly to new applied_entries */
        raftAppliedEntry *ae = zmalloc(sizeof(*ae));
        ae->index = entry->index;
        ae->term = entry->term;
        ae->value = sdsdup(entry->mutations[0].value);
        if (dictAdd(RAFT_STATE()->applied_entries, sdsdup(entry->mutations[0].key), ae) != DICT_OK) {
            serverLog(LL_WARNING, "Raft: Duplicate key '%s' in snapshot", entry->mutations[0].key);
            raftAppliedEntryFree(ae);
        }

        /* For snapshots, treat each entry as if it were appended, then committed, to ensure both
         * transitions fire. */
        clusterRaftOnAppendEntry(entry);
        clusterRaftOnCommitEntry(entry);

        if (entry->index > RAFT_STATE()->last_applied_index) {
            RAFT_STATE()->last_applied_index = entry->index;
            RAFT_STATE()->last_applied_term = entry->term;
        }
        raftLogEntryFree(entry);
    }

    /* Otherwise, find leader from snapshot response and send a join proposal */
    clusterNode *leader = clusterLookupNode(resp->leader_name, CLUSTER_NAMELEN);
    if (!leader) {
        serverLog(LL_WARNING, "Raft: Unknown leader '%.40s' in snapshot response", resp->leader_name);
        return;
    }
    clusterRaftRecognizeLeader(leader, term);

    /* All done if we aren't joining.*/
    if (MY_RAFT_ROLE == RAFT_ROLE_JOINING) {
        clusterRaftSendJoinProposal(leader);
    }
}

/* -----------------------------------------------------------------------------
 * Raft AppendEntries Implementation
 * -------------------------------------------------------------------------- */


/* Apply a snapshot to the Raft state machine directly (no merge). */
void clusterRaftApplySnapshot(size_t entries_len, char *serialized_snapshot, char *end) {
    char *cursor = serialized_snapshot;
    dictEmpty(RAFT_STATE()->applied_entries, NULL);
    RAFT_STATE()->last_applied_index = 0;
    RAFT_STATE()->last_applied_term = 0;
    while (entries_len > 0) {
        size_t consumed;
        raftLogEntry *entry = clusterRaftDeserializeEntry(cursor, end, &consumed);
        if (!entry) {
            serverLog(LL_WARNING, "Raft: Failed to deserialize entry in apply snapshot");
            break;
        }
        cursor += consumed;
        entries_len--;

        for (uint32_t i = 0; i < entry->count; i++) {
            raftAppliedEntry *ae = zmalloc(sizeof(*ae));
            ae->index = entry->index;
            ae->term = entry->term;
            ae->value = sdsdup(entry->mutations[i].value);
            if (dictAdd(RAFT_STATE()->applied_entries, sdsdup(entry->mutations[i].key), ae) != DICT_OK) {
                serverLog(LL_WARNING, "Raft: Duplicate key '%s' in snapshot", entry->mutations[i].key);
                raftAppliedEntryFree(ae);
            }
        }

        if (entry->index > RAFT_STATE()->last_applied_index) {
            RAFT_STATE()->last_applied_index = entry->index;
            RAFT_STATE()->last_applied_term = entry->term;
        }
        raftLogEntryFree(entry);
    }
}

/* Ack an AppendEntries message from the Raft leader. */
void clusterRaftSendAppendEntriesAck(clusterNode *sender) {
    clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_APPEND_ENTRIES_ACK, sizeof(clusterMsgRaftAppendEntriesAck));
    clusterMsgRaftAppendEntriesAck *ack = (clusterMsgRaftAppendEntriesAck *)((char *)msgblock->data + sizeof(clusterRaftHeader));
    ack->term = htonu64(RAFT_STATE()->term);
    raftLogEntry *latest_entry = clusterRaftGetLatestEntry();
    ack->value_index = htonu64(latest_entry->index);
    ack->value_term = htonu64(latest_entry->term);
    clusterLinkSendBlock(sender->link, msgblock);
    clusterMsgSendBlockDecrRefCount(msgblock);
}

static void clusterRaftRecognizeLeader(clusterNode *sender, uint64_t term) {
    if (RAFT_DATA(sender)->role != RAFT_ROLE_LEADER) {
        serverLog(LL_NOTICE, "Raft: Recognizing %.40s as leader in term %llu", sender->name, (unsigned long long)term);
        clusterRaftSetNodeRole(sender, RAFT_ROLE_LEADER);

        /* Reset other nodes' role to follower if they were leader */
        dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
        dictEntry *de;
        while ((de = dictNext(di)) != NULL) {
            clusterNode *n = dictGetVal(de);
            if (n != sender && RAFT_DATA(n)->role == RAFT_ROLE_LEADER) {
                clusterRaftSetNodeRole(n, RAFT_ROLE_FOLLOWER);
            }
        }
        dictReleaseIterator(di);

        /* Update leader name on failover */
        if (memcmp(RAFT_STATE()->leader_name, sender->name, CLUSTER_NAMELEN) != 0) {
            memcpy(RAFT_STATE()->leader_name, sender->name, CLUSTER_NAMELEN);
        }

        /* Reset the election timer */
        RAFT_STATE()->election_timer = mstime() + 1000 + (rand() % 1000);
    }
}

static void clusterRaftOnAppendEntry(raftLogEntry *entry) {
    for (uint32_t j = 0; j < entry->count; j++) {
        /* Update node states if this is a membership entry */
        if (strncmp(entry->mutations[j].key, "membership", 10) == 0) {
            int prev_count = clusterRaftGetMemberCount();
            int argc = 0;
            sds *splitres = sdssplitlen(entry->mutations[j].value, sdslen(entry->mutations[j].value), " ", 1, &argc);
            if (splitres) {
                for (int i = 0; i < argc; i++) {
                    clusterNode *n = clusterLookupNode(splitres[i], sdslen(splitres[i]));

                    /* Move EXTERNAL nodes to JOINING. Will promote to FOLLOWER once committed. */
                    if (n && RAFT_DATA(n)->role == RAFT_ROLE_EXTERNAL) {
                        clusterRaftSetNodeRole(n, RAFT_ROLE_JOINING);
                    }
                }
                sdsfreesplitres(splitres, argc);
            }
            if (prev_count != clusterRaftGetMemberCount()) {
                /* Notify all EXTERNAL nodes about the new member count. It may
                 * change their joining calculus. */
                dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
                dictEntry *de;
                while ((de = dictNext(di)) != NULL) {
                    clusterNode *n = dictGetVal(de);
                    if (n != myself && RAFT_DATA(n) && RAFT_DATA(n)->role == RAFT_ROLE_EXTERNAL) {
                        if (n->link) {
                            clusterRaftSendHandshakeReply(n->link, n->name);
                        }
                    }
                }
                dictReleaseIterator(di);
            }
        }

        /* Update node metadata immediately if this is a node metadata entry */
        if (strncmp(entry->mutations[j].key, "node:", 5) == 0) {
            char *node_id = entry->mutations[j].key + 5;
            int argc = 0;
            sds *splitres = sdssplitlen(entry->mutations[j].value, sdslen(entry->mutations[j].value), ":", 1, &argc);
            if (splitres && argc == 4) {
                clusterNode *n = clusterLookupNode(node_id, sdslen(entry->mutations[j].key) - 5);
                if (!n) {
                    n = createClusterNode(node_id, CLUSTER_NODE_NOADDR);
                    clusterAddNode(n);
                    serverLog(LL_NOTICE, "Raft: Created node %.40s (noaddr) on appending entry", n->name);
                }

                /* Update address info */
                size_t ip_len = sdslen(splitres[0]);
                if (ip_len < sizeof(n->ip)) {
                    memcpy(n->ip, splitres[0], ip_len);
                    n->ip[ip_len] = '\0';
                }
                n->tcp_port = atoi(splitres[1]);
                n->tls_port = atoi(splitres[2]);
                n->cport = atoi(splitres[3]);
                n->flags &= ~CLUSTER_NODE_NOADDR;

                serverLog(LL_NOTICE, "Raft: Updated metadata for node %.40s: %s:%d:%d:%d",
                          n->name, n->ip, n->tcp_port, n->tls_port, n->cport);

                /* Initiate connection immediately if it doesn't exist */
                if (!(n->flags & CLUSTER_NODE_MYSELF) && n->link == NULL) {
                    serverLog(LL_NOTICE, "Raft: Discovered node metadata for %.40s, initiating connection", n->name);
                    clusterLink *link = createClusterLink(n);
                    link->conn = connCreate(connTypeOfCluster());
                    connSetPrivateData(link->conn, link);
                    if (connConnect(link->conn, n->ip, n->cport, server.bind_source_addr, 0, clusterLinkConnectHandler) == C_ERR) {
                        serverLog(LL_WARNING, "Raft: Failed to initiate connection to %.40s", n->name);
                        freeClusterLink(link);
                    }
                }
            }
            if (splitres) sdsfreesplitres(splitres, argc);
        }
    }
}

/* Process an AppendEntries message from the Raft leader. */
void clusterRaftProcessAppendEntries(clusterNode *sender, clusterMsgRaftAppendEntries *ext, size_t payload_len) {
    if (!RAFT_STATE()) return;
    uint64_t term = ntohu64(ext->term);

    /* Reply, but ignore the AppendEntries if term is smaller. */
    if (term < RAFT_STATE()->term) {
        clusterRaftSendAppendEntriesAck(sender);
        return;
    }

    /* If term is larger, advance term. */
    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
    }

    /* Set a new election timer (we heard from the leader) */
    RAFT_STATE()->election_timer = mstime() + 1000 + (rand() % 1000);

    /* Update leader role */
    clusterRaftRecognizeLeader(sender, term);

    /* Use the prev_log_index and prev_log_term to find a merge base. From the merge base, proceed
     * to match the provided entries against our pending entries until a conflict is found
     * (comparing based on term and index). Where we find a conflict, we truncate our log at the
     * point of conflict and append the new entries. */
    uint64_t prev_log_index = ntohu64(ext->prev_log_index);
    uint64_t prev_log_term = ntohu64(ext->prev_log_term);
    listNode *merge_base = NULL;

    if (prev_log_index != RAFT_STATE()->last_applied_index || prev_log_term != RAFT_STATE()->last_applied_term) {
        raftLogEntry search_entry = {.index = prev_log_index, .term = prev_log_term};
        merge_base = listSearchKey(RAFT_STATE()->pending_entries, &search_entry);
        if (!merge_base) {
            /* We cannot apply if the prev_log_index and term are not found. */
            serverLog(LL_WARNING, "Raft: Lag detected, prev_log_index %llu not found. Requesting snapshot.", (unsigned long long)prev_log_index);

            /* Request snapshot */
            clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_SNAPSHOT_REQUEST, sizeof(clusterMsgRaftSnapshotRequest));
            clusterMsgRaftSnapshotRequest *sn_req = (clusterMsgRaftSnapshotRequest *)((char *)msgblock->data + sizeof(clusterRaftHeader));
            sn_req->term = htonu64(RAFT_STATE()->term);
            clusterLinkSendBlock(sender->link, msgblock);
            clusterMsgSendBlockDecrRefCount(msgblock);

            /* Drop the message (do not send ACK) */
            return;
        }
    }

    /* Check if there are any entries to process */
    uint64_t entries_len = ntohu64(ext->entries_len);
    if (entries_len == 0) {
        /* Empty append entries (heartbeat). Advance commit index and return. */
        uint64_t leader_commit = ntohu64(ext->leader_commit);
        clusterRaftAdvanceCommitIndex(leader_commit);
        return;
    }

    /* Deserialize the proposed entries*/
    char *cursor = ext->entries;
    char *end = (char *)ext + payload_len;
    list *proposed_entries = listCreate();
    listSetFreeMethod(proposed_entries, raftLogEntryFree);
    while (entries_len > 0) {
        size_t consumed;
        raftLogEntry *entry = clusterRaftDeserializeEntry(cursor, end, &consumed);
        if (!entry) {
            serverLog(LL_WARNING, "Raft: Failed to deserialize entry in append entries");
            listRelease(proposed_entries);
            return;
        }
        listAddNodeTail(proposed_entries, entry);
        cursor += consumed;
        entries_len--;
    }

    /* First scan forward until we: a) find a conflict or b) run out of pending entries */
    listNode *ln = merge_base ? merge_base->next : RAFT_STATE()->pending_entries->head;
    while (ln) {
        raftLogEntry *current_entry = ln->value;
        if (listLength(proposed_entries) == 0) break;
        raftLogEntry *proposed_entry = listFirst(proposed_entries)->value;
        if (clusterRaftCompareTermIndexPairs(current_entry->term, current_entry->index, proposed_entry->term, proposed_entry->index) != 0) {
            /* Conflict! Truncate our log. */
            while (ln) {
                listNode *next = ln->next;
                listDelNode(RAFT_STATE()->pending_entries, ln);
                ln = next;
            }
            break;
        }
        /* Otherwise, it is a match, and we can skip this entry. */
        listDelNode(proposed_entries, listFirst(proposed_entries));
        ln = ln->next;
    }

    /* Now we can stitch the remaining entries to the end of our log. */
    listSetFreeMethod(proposed_entries, NULL); /* Don't free them when we move them */
    while (proposed_entries->head) {
        raftLogEntry *proposed_entry = listFirst(proposed_entries)->value;
        listAddNodeTail(RAFT_STATE()->pending_entries, proposed_entry);
        listDelNode(proposed_entries, listFirst(proposed_entries));
        clusterRaftOnAppendEntry(proposed_entry);
    }
    listRelease(proposed_entries);

    /* Now that our pending log should match the leader's, we can advance our commit index. */
    uint64_t leader_commit = ntohu64(ext->leader_commit);
    clusterRaftAdvanceCommitIndex(leader_commit);

    /* Respond to the leader to let it know that we have persisted the entries. */
    clusterRaftSendAppendEntriesAck(sender);
}

static int compare_uint64(const void *a, const void *b) {
    uint64_t va = *(const uint64_t *)a;
    uint64_t vb = *(const uint64_t *)b;
    if (va < vb) return -1;
    if (va > vb) return 1;
    return 0;
}

void clusterRaftAdvanceCommitIndexToMajority(void) {
    if (RAFT_STATE() == NULL) return;
    int raft_nodes = clusterRaftGetMemberCount();
    if (raft_nodes == 0) return;

    uint64_t *match_indices = zmalloc(sizeof(uint64_t) * raft_nodes);
    int count = 0;

    dictIterator *di = dictGetSafeIterator(server.cluster->nodes);
    dictEntry *de;
    while ((de = dictNext(di)) != NULL) {
        clusterNode *node = dictGetVal(de);
        if (node->flags & CLUSTER_NODE_HANDSHAKE) continue;

        if (node == server.cluster->myself) {
            raftLogEntry *latest = clusterRaftGetLatestEntry();
            match_indices[count++] = latest ? latest->index : 0;
        } else {
            match_indices[count++] = RAFT_DATA(node)->match_index;
        }
    }
    dictReleaseIterator(di);

    if (count == 0) {
        zfree(match_indices);
        return;
    }

    qsort(match_indices, count, sizeof(uint64_t), compare_uint64);

    int majority_index = count - (count / 2 + 1);
    uint64_t median_match_index = match_indices[majority_index];

    zfree(match_indices);

    /* If the median match index has advanced, we can commit some entries. */
    clusterRaftAdvanceCommitIndex(median_match_index);
}

/* Process an AppendEntries ACK from a follower. This involves updating the
 * match index and potentially advancing the commit index. */
void clusterRaftProcessAppendEntriesAck(clusterNode *sender, clusterMsgRaftAppendEntriesAck *ack) {
    uint64_t term = ntohu64(ack->term);
    uint64_t value_index = ntohu64(ack->value_index);
    uint64_t value_term = ntohu64(ack->value_term);
    UNUSED(sender);

    /* Ignore non-raft members */
    if (!RAFT_DATA(sender)) return;

    /* Handle term update. */
    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
        return;
    }

    /* Handle stale response. */
    if (term != RAFT_STATE()->term || MY_RAFT_ROLE != RAFT_ROLE_LEADER) {
        return;
    }

    /* Check if there is divergence */
    bool found = false;
    raftLogEntry search_entry = {.term = value_term, .index = value_index};
    if (listSearchKey(RAFT_STATE()->pending_entries, &search_entry) != NULL) {
        found = true;
    } else {
        /* If not pending, it could be applied */
        dictIterator *di = dictGetSafeIterator(RAFT_STATE()->applied_entries);
        dictEntry *de;
        while ((de = dictNext(di)) != NULL) {
            raftLogEntry *entry = dictGetVal(de);
            if (entry->index == value_index && entry->term == value_term) {
                found = true;
                break;
            }
        }
        dictReleaseIterator(di);
    }

    if (!found) {
        /* Divergence detected. Handle this by resetting the node's state. Next AppendEntries will
         * send a full snapshot. */
        RAFT_DATA(sender)->match_index = 0;
        return;
    }

    /* If the match_index is not getting further, just ignore (stale response) */
    if (RAFT_DATA(sender)->match_index > value_index) return;

    /* Update the match index and term */
    RAFT_DATA(sender)->match_index = value_index;

    clusterRaftAdvanceCommitIndexToMajority();
}

/* -----------------------------------------------------------------------------
 * Raft Entry Proposal (Follower -> Leader)
 * -------------------------------------------------------------------------- */

void clusterRaftProcessProposeEntries(clusterLink *link, clusterMsgRaftProposeEntries *prop, size_t payload_len) {
    serverLog(LL_NOTICE, "Raft: Received propose entries from %.40s", clusterLinkGetNodeName(link));
    uint64_t term = ntohu64(prop->term);

    if (term > RAFT_STATE()->term) {
        clusterRaftAdvanceTerm(term);
        return;
    }

    if (term != RAFT_STATE()->term) return;

    if (MY_RAFT_ROLE != RAFT_ROLE_LEADER) {
        return; /* Only LEADER can handle proposals */
    }

    uint32_t num_checks = ntohl(prop->num_checks);
    uint32_t num_proposals = ntohl(prop->num_proposals);

    char *ptr = prop->data;

    /* First pass: Validate all checks */
    char *check_ptr = ptr;
    char *end = (char *)prop + payload_len;
    for (uint32_t i = 0; i < num_checks; i++) {
        uint64_t expected_index;
        uint64_t expected_term;

        if (decodeUint64(&check_ptr, end, &expected_index) != C_OK) return;
        if (decodeUint64(&check_ptr, end, &expected_term) != C_OK) return;
        sds key = decodeString(&check_ptr, end);
        if (!key) return;

        /* Perform check */
        raftLogEntry *existing_entry = NULL;
        dictEntry *de = dictFind(RAFT_STATE()->applied_entries, key);
        if (de) {
            existing_entry = dictGetVal(de);
        }
        /* Also check pending entries */
        listIter iter;
        listRewind(RAFT_STATE()->pending_entries, &iter);
        listNode *ln;
        while ((ln = listNext(&iter))) {
            raftLogEntry *entry = ln->value;
            for (uint32_t j = 0; j < entry->count; j++) {
                if (sdscmp(entry->mutations[j].key, key) == 0) {
                    existing_entry = entry;
                }
            }
        }

        if (!existing_entry && expected_index == 0) {
            /* 0 means key does not exist */
            sdsfree(key);
            continue;
        }

        if (!existing_entry || existing_entry->term != expected_term || existing_entry->index != expected_index) {
            serverLog(LL_WARNING, "Raft: Check failed in batch proposal from %.40s for key '%s': expected index=%llu, term=%llu; existing index=%llu, term=%llu",
                      clusterLinkGetNodeName(link), key,
                      (unsigned long long)expected_index, (unsigned long long)expected_term,
                      existing_entry ? (unsigned long long)existing_entry->index : 0,
                      existing_entry ? (unsigned long long)existing_entry->term : 0);
            sdsfree(key);
            return; // Abort whole batch
        }

        sdsfree(key);
    }

    /* If we reached here, all checks passed. Now apply proposals. */
    ptr = check_ptr;
    list *proposals = listCreate();
    listSetFreeMethod(proposals, freeRaftKeyValue);
    for (uint32_t i = 0; i < num_proposals; i++) {
        raftKeyValue *kv = zmalloc(sizeof(*kv));
        kv->key = decodeString(&ptr, end);
        if (!kv->key) {
            zfree(kv);
            listRelease(proposals);
            return;
        }
        kv->value = decodeString(&ptr, end);
        if (!kv->value) {
            sdsfree(kv->key);
            zfree(kv);
            listRelease(proposals);
            return;
        }
        listAddNodeTail(proposals, kv);
    }

    /* Apply batch proposal */
    clusterRaftAddEntry(proposals);
    listRelease(proposals);
    serverLog(LL_NOTICE, "Raft: Applied batch proposal from %.40s (checks: %u, proposals: %u)", clusterLinkGetNodeName(link), num_checks, num_proposals);
}


static void clusterRaftBeforeSleep(void) {
    if (!RAFT_STATE()) return;
    if (RAFT_STATE()->todo_before_sleep & RAFT_TODO_BROADCAST_APPEND_ENTRIES) {
        serverLog(LL_VERBOSE, "Raft: Broadcasting AppendEntries before sleep");
        clusterRaftSendAppendEntries();
        RAFT_STATE()->todo_before_sleep &= ~RAFT_TODO_BROADCAST_APPEND_ENTRIES;
    }
}
static void clusterRaftHandleServerShutdown(bool auto_failover) {
    UNUSED(auto_failover);
}
static void clusterRaftPostConnect(clusterLink *link) {
    if (link->node) {
        serverLog(LL_VERBOSE, "Raft: Sending handshake to %.40s after connection established", clusterLinkGetNodeName(link));

        clusterMsgSendBlock *msgblock = createClusterRaftMsgSendBlock(CLUSTERMSG_TYPE_RAFT_HANDSHAKE_REQUEST, sizeof(clusterMsgRaftHandshake));
        clusterMsgRaftHandshake *req = (clusterMsgRaftHandshake *)((char *)msgblock->data + sizeof(clusterRaftHeader));

        memcpy(req->sender_name, myself->name, CLUSTER_NAMELEN);
        req->term = htonu64(RAFT_STATE()->term);

        req->member_count = htonl(clusterRaftGetMemberCount());
        memcpy(req->remote_ip, link->node->ip, NET_IP_STR_LEN);

        req->plaintext_port = htons(server.port);
        req->tls_port = htons(server.tls_port);
        req->cluster_port = htons(myself->cport);

        clusterLinkSendBlock(link, msgblock);
        clusterMsgSendBlockDecrRefCount(msgblock);
        RAFT_DATA(link->node)->outbound_link_established = 1;
        clusterRaftStateMachine();
    }
}
static void clusterRaftOnMyselfUpdated(int old_flags) {
    (void)old_flags;
}
static void clusterRaftPropagatePublish(robj *channel, robj *message, int sharded) {
    UNUSED(channel);
    UNUSED(message);
    UNUSED(sharded);
}
static int clusterRaftSendModuleMessage(const char *target, uint64_t module_id, uint8_t type, const char *payload, uint32_t len) {
    UNUSED(target);
    UNUSED(module_id);
    UNUSED(type);
    UNUSED(payload);
    UNUSED(len);
    return 0;
}

static unsigned long clusterRaftGetConnectionsCount(void) {
    return 0;
}
static void clusterRaftResetStats(void) {
}
static sds clusterRaftAppendInfoFields(sds info) {
    if (server.cluster == NULL) return info;

    info = sdscatfmt(info, "cluster_known_nodes:%U\r\n",
                     (unsigned long long)dictSize(server.cluster->nodes));

    const char *role_str = "unknown";
    if (RAFT_STATE()) {
        switch (MY_RAFT_ROLE) {
        case RAFT_ROLE_FOLLOWER: role_str = "follower"; break;
        case RAFT_ROLE_CANDIDATE: role_str = "candidate"; break;
        case RAFT_ROLE_LEADER: role_str = "leader"; break;
        case RAFT_ROLE_JOINING: role_str = "joining"; break;
        }
    }
    info = sdscatfmt(info, "raft_role:%s\r\n", role_str);
    info = sdscatprintf(info, "raft_leader:%.40s\r\n", RAFT_STATE()->leader_name);
    info = sdscatprintf(info, "raft_node_id:%.40s\r\n", myself->name);

    return info;
}
static void clusterRaftGetNodePingPongEpoch(clusterNode *node, long long *ping_sent, long long *pong_received, uint64_t *config_epoch) {
    UNUSED(node);
    *ping_sent = 0;
    *pong_received = 0;
    *config_epoch = 0;
}
static void clusterRaftSetNodePingPongEpoch(clusterNode *node, int ping_active, int pong_active, uint64_t config_epoch) {
    UNUSED(node);
    UNUSED(ping_active);
    UNUSED(pong_active);
    UNUSED(config_epoch);
}
static void clusterRaftSetNodeFailed(clusterNode *node) {
    UNUSED(node);
}
static int clusterRaftGetFailureReportsCount(clusterNode *node) {
    UNUSED(node);
    return 0;
}
static sds clusterRaftAppendVarsLine(sds config) {
    return config;
}
static int clusterRaftParseVarsLine(const char *name, const char *value) {
    UNUSED(name);
    UNUSED(value);
    return C_OK;
}
static void clusterRaftPostLoad(void) {
}
static void clusterRaftSlotChange(slotRange *ranges, int numranges, clusterNode *target, void *ctx, void (*callback)(void *ctx, const char *error)) {
    UNUSED(ranges);
    UNUSED(numranges);
    UNUSED(target);
    UNUSED(ctx);
    UNUSED(callback);
}
static void clusterRaftCancelManualFailover(void) {
}
static void clusterRaftCancelAutomaticFailover(void) {
}
static void clusterRaftForgetNode(const char *node_id, size_t id_len, void *ctx, void (*callback)(void *ctx, const char *error)) {
    UNUSED(node_id);
    UNUSED(id_len);
    UNUSED(ctx);
    UNUSED(callback);
}
static void clusterRaftSetReplicaOf(clusterNode *primary, void *ctx, void (*callback)(void *ctx, const char *error)) {
    (void)primary;
    if (callback) callback(ctx, "Not supported in Raft mode");
}
static void clusterRaftFailover(int force, int takeover, void *ctx, void (*callback)(void *ctx, const char *error)) {
    (void)force;
    (void)takeover;
    if (callback) callback(ctx, "Not supported in Raft mode");
}
static void clusterRaftMeet(const char *ip, int port, int cport, void *ctx, void (*callback)(void *ctx, const char *error)) {
    if (MY_RAFT_ROLE == RAFT_ROLE_JOINING) {
        if (callback) callback(ctx, "Already in process of joining another group");
        return;
    }

    char norm_ip[NET_IP_STR_LEN];
    struct sockaddr_storage sa;
    if (inet_pton(AF_INET, ip, &(((struct sockaddr_in *)&sa)->sin_addr))) {
        sa.ss_family = AF_INET;
    } else if (inet_pton(AF_INET6, ip, &(((struct sockaddr_in6 *)&sa)->sin6_addr))) {
        sa.ss_family = AF_INET6;
    } else {
        if (callback) callback(ctx, "Invalid node address specified");
        return;
    }
    inet_ntop(sa.ss_family, sa.ss_family == AF_INET ? (void *)&(((struct sockaddr_in *)&sa)->sin_addr) : (void *)&(((struct sockaddr_in6 *)&sa)->sin6_addr), norm_ip, NET_IP_STR_LEN);

    clusterNode *n = createClusterNode(NULL, CLUSTER_NODE_HANDSHAKE);
    memcpy(n->ip, norm_ip, sizeof(n->ip));
    if (server.tls_cluster) {
        n->tls_port = port;
    } else {
        n->tcp_port = port;
    }
    n->cport = cport;
    clusterAddNode(n);

    serverLog(LL_VERBOSE, "Raft: Initiating outbound connection to %s:%d", norm_ip, port);

    clusterLink *link = createClusterLink(n);
    link->conn = connCreate(connTypeOfCluster());
    connSetPrivateData(link->conn, link);
    if (connConnect(link->conn, n->ip, n->cport, server.bind_source_addr, 0, clusterLinkConnectHandler) == C_ERR) {
        serverLog(LL_WARNING, "Raft: Failed to connect to %s:%d", n->ip, n->cport);
        freeClusterLink(link);
        if (callback) callback(ctx, "Failed to initiate connection");
        return;
    }

    if (callback) callback(ctx, NULL);
}
static void clusterRaftReset(int hard) {
    (void)hard;
}
static int clusterRaftProtocolSubcommand(client *c) {
    (void)c;
    return 0;
}

void clusterRaftOnLinkFree(clusterLink *link) {
    if (link->node && link->node->link == link) {
        if (RAFT_DATA(link->node)) {
            RAFT_DATA(link->node)->outbound_link_established = 0;
        }
    }
}

clusterBusType clusterRaftBus = {
    .init = clusterRaftInit,
    .initLast = clusterRaftInitLast,
    .cron = clusterRaftCron,
    .beforeSleep = clusterRaftBeforeSleep,
    .handleServerShutdown = clusterRaftHandleServerShutdown,
    .validateMessageHeader = clusterRaftValidateMessageHeader,
    .processMessage = clusterRaftProcessMessage,
    .postConnect = clusterRaftPostConnect,
    .onLinkFree = clusterRaftOnLinkFree,
    .onMyselfUpdated = clusterRaftOnMyselfUpdated,
    .propagatePublish = clusterRaftPropagatePublish,
    .sendModuleMessage = clusterRaftSendModuleMessage,
    .getConnectionsCount = clusterRaftGetConnectionsCount,
    .resetStats = clusterRaftResetStats,
    .appendInfoFields = clusterRaftAppendInfoFields,
    .getFailureReportsCount = clusterRaftGetFailureReportsCount,
    .getNodePingPongEpoch = clusterRaftGetNodePingPongEpoch,
    .setNodePingPongEpoch = clusterRaftSetNodePingPongEpoch,
    .setNodeFailed = clusterRaftSetNodeFailed,
    .appendVarsLine = clusterRaftAppendVarsLine,
    .parseVarsLine = clusterRaftParseVarsLine,
    .postLoad = clusterRaftPostLoad,
    .initNodeData = clusterRaftInitNodeData,
    .freeNodeData = clusterRaftFreeNodeData,
    .slotChange = clusterRaftSlotChange,
    .cancelManualFailover = clusterRaftCancelManualFailover,
    .cancelAutomaticFailover = clusterRaftCancelAutomaticFailover,
    .forgetNode = clusterRaftForgetNode,
    .setReplicaOf = clusterRaftSetReplicaOf,
    .failover = clusterRaftFailover,
    .meet = clusterRaftMeet,
    .resetCluster = clusterRaftReset,
    .protocolSubcommand = clusterRaftProtocolSubcommand,
};

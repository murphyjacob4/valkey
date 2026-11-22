# Cluster Raft Design

## Overview

Cluster Raft is an alternative cluster bus protocol for Valkey that uses
Raft consensus for all cluster metadata changes. It replaces the gossip
protocol's eventually-consistent model with strong consistency.

Enabled via `cluster-protocol raft` (mutually exclusive with gossip).

## Wire Format

Binary header (8 bytes): `"RAFT" + uint32 BE totlen`.
Payload: space-separated text. First token is the message type.
Multi-line messages use `\n` to separate the header line from entry lines.

Messages:

```
HELLO <node-id> <address>
    First message on every outbound link. Identifies the sender.

HI <node-id> <address>
    Immediate reply to HELLO, sent on the same inbound link.
    Identifies the sender and completes the identification handshake.

MEET singleton|cluster
    Sent after HELLO on CLUSTER MEET-initiated connections. Declares
    the sender's cluster status: "singleton" means it's alone and
    "cluster" means that it's in a cluster with other nodes. The
    receiver decides based on its own status (see Cluster Formation
    below).

ADD_ME
    Reply to MEET: "I stepped down to joiner, please add me to your
    cluster." Sent by a singleton that received MEET.

WELCOME
    Reply to MEET: "I'm in a cluster and will add you." Sent by a
    cluster member that received MEET from a singleton. The receiver
    steps down to joiner on receiving WELCOME.

MEET_REJECTED
    Reply to MEET: both sides are already in a non-singleton cluster.
    Merging clusters is not supported. The CLUSTER MEET client
    receives an error.

AE <leader-id> <term> <prev-log-idx> <prev-log-term> <commit> <count>
    AppendEntries. Carries log entries from leader to followers.
    Followed by <count> entry lines: <term> <type> <data>.
    With zero entries, serves as a heartbeat.

AE_ACK <term> <success> <last-log-index> <repl-offset>
    Response to AE. Reports whether entries were accepted, the
    follower's last log index for matchIndex tracking, and the
    node's replication offset.

VOTE_REQ <candidate-id> <term> <last-log-index> <last-log-term>
    RequestVote. Sent by candidates during elections.

VOTE <term> <granted>
    Response to VOTE_REQ. Indicates whether the vote was granted.
    Always sent, even on deny, so the candidate can learn higher terms.

PRE_VOTE_REQ <candidate-id> <term> <last-log-index> <last-log-term>
    Request for speculative election. Sent by pre-candidates before
    incrementing currentTerm. The term is currentTerm+1.

PRE_VOTE <term> <granted>
    Response to PRE_VOTE_REQ. Indicates whether the node would grant
    a real vote in that term.

PROPOSE <entry>
    Forwards a proposal from a follower to the leader. The entry
    uses the same format as log entries (type followed by data).

FORGET_VOTER <node-id> <shard-epoch>
    Sent by a follower or learner to the leader for CLUSTER FORGET
    when the target is currently a voter. The leader chains DEL_VOTER,
    waits for it to commit, and then appends NODE_FORGET (or transfers
    leadership first if the target is the leader itself). Raw
    PROPOSE NODE_FORGET targeting a voter is rejected.

REJECT <reason> <type> <data...>
    Sent by the leader to a proposing follower when append-time
    validation rejects a proposal. <reason> is "conflict" (stale
    shard epoch, retryable), "transfer" (leadership transfer in
    progress), or "rejected" (terminal error).

FAILOVER_PREPARE
    Sent by a replica to its primary to request a coordinated failover.
    The primary pauses writes and replies with FAILOVER_PAUSED. Not a
    raft log entry — just a direct message over the cluster link.

FAILOVER_PAUSED <offset>
    Reply to FAILOVER_PREPARE. Carries the primary's replication offset
    after pausing writes. The replica proposes FAILOVER only after its
    own replication offset reaches this offset.

REPL_OFFSETS <node-id> <offset> [<node-id> <offset> ...]
    Sent by the leader to propagate replication offsets. Broadcast
    periodically (every 10s) and immediately when a replica's offset
    transitions from 0 to non-zero. Also sent before NODE_FAIL to
    provide replicas with sibling offsets for failover ranking.
    Recipients update node->repl_offset for CLUSTER SLOTS/SHARDS
    health reporting.

TIMEOUT_NOW <term>
    Sent by the leader to a follower to trigger immediate election
    (leader transfer). The recipient starts an election without
    waiting for the election timeout. Used during graceful shutdown.

PUBLISH <sharded> <chan_len> <msg_len>
    Propagates a Pub/Sub message to all cluster nodes. The channel
    and message data follow the header fields. <sharded> is 1 for
    shard channel messages, 0 for global.

MODULE <module_id> <type> <len>
    Propagates a module-to-module cluster message. The payload
    (binary, <len> bytes) follows on the next line. Delivered to
    module cluster message receivers.
```

The address string uses the nodes.conf format:
`ip:port@cport[,hostname][,aux=val]*`

## Roles

A new node starts up as leader of its own singleton cluster, meaning a
cluster with only one member. Singleton means that it's alone.

- **Joiner**: A singleton that stepped down to join another cluster.
  Cannot vote, propose, or form a cluster. Waits for AE from the
  leader to receive its NODE_JOIN entry. Reverts to singleton leader
  after 4× cluster-node-timeout if no AE arrives.
- **Learner**: A non-voting member that receives and applies the Raft
  log but is not counted for elections or commit quorum. Learners can
  own slots and act as data primaries or replicas.
- **Follower**: Participates in elections and counts for quorum.
  Promoted from learner by ADD_VOTER after catching up with the log.
- **Pre-candidate**: Runs a pre-vote round without incrementing term.
  Reverts to follower if no quorum is reached within one election timeout
  (see [Election timeout](#election-timeout)).
- **Candidate**: Runs a formal election by sending VOTE_REQ after
  winning a pre-vote round.
- **Leader**: Accepts proposals, replicates log, sends heartbeats.

The Raft leader is independent of the data primary/replica role. Any
node can be the Raft leader.

## Typed Log Entries

Each log entry has a type and a text data field. The entry types and
their data formats:

```
NODE_JOIN <node-id> <address> <learner|voter>
    Add a node to the cluster. Applied when a new node is discovered
    via MEET. The "voter" mode is only allowed as the empty-log
    bootstrap self-join of a singleton; every other node joins as a
    learner so subsequent NODE_JOIN entries never change quorum.

ADD_VOTER <node-id>
    Promote a learner to a voting follower after it has caught up with
    the leader's log. This adds the node to the effective voter set on
    append (and increments the applied voting cluster size on apply).

DEL_VOTER <node-id>
    Demote a voting follower (or the leader itself) to learner. The
    node stays in the cluster and continues receiving AE, but is
    removed from the effective voter set on append.

NODE_FORGET <node-id> <shard-epoch>
    Remove a learner from the cluster (CLUSTER FORGET). Restricted to
    learners so NODE_FORGET never changes the voter set; forgetting a
    voter requires DEL_VOTER first (chained automatically by the
    leader for CLUSTER FORGET). The epoch refers to the leaving node's
    shard and guards against removing a node whose role changed (e.g.,
    promoted to primary via a concurrent FAILOVER).

SLOT_CHANGE <source-node-id-or-dash> <source-epoch> <target-node-id-or-dash> <target-epoch> <range> [<range> ...]
    Assign or remove slot ownership. A dash means "no owner" (delete
    slots). Ranges use the nodes.conf format: "0-5460" or "5461".
    Carries two epochs (source and target shard). Shard epoch is not
    bumped because SLOT_CHANGE only moves slots, it doesn't change shard
    membership or leadership. Two slot migrations touching the same
    shard are safe to apply concurrently as they affect different slots.
    Bumping would serialize them unnecessarily. But validating is still
    needed to catch the case where a slot migration races against a
    failover that invalidated the shard's topology.

SET_REPLICA_OF <replica-id> <source-shard> <source-epoch> <primary-id-or-dash> <target-shard> <target-epoch>
    Set a node as replica of a primary (CLUSTER REPLICATE). A dash as
    primary means promote to primary. It carries two epochs because it
    involves two shards (source and target) and bumps the epoch of both
    shards on apply. A primary that becomes a replica takes its replicas
    along. If the target has become a replica, its primary is used
    instead, if it's still in the target shard.

FAILOVER <replica-id> <primary-id> <shard-id> <shard-epoch>
    The replica takes over the primary's slots and becomes primary.
    The old primary becomes a replica of the new primary. This bumps the
    shard epoch on apply.

NODE_INFO <node-id> <address-string> <flags>
    Update node address and self-set flags. The address-string uses
    the nodes.conf format but excludes shard-id, which is not a
    property of the node but of the shard and is managed by NODE_JOIN
    and SET_REPLICA_OF. Flags is "nofailover" or "noflags". No shard epoch required here
    as it does not create any mutations.

NODE_FAIL <node-id>
    Mark a node as failed. Proposed by the leader when a peer exceeds
    the node timeout without responding to heartbeats. No shard epoch here as it does not change cluster membership or leadership.

NODE_RECOVER <node-id>
    Clear the FAIL flag. Proposed by the leader when it receives
    AE_ACK from a previously failed node.
```

Ranges in SLOT_CHANGE use the same format as nodes.conf: `0-5460` or
`5461`. A dash as source/target-id means "no owner" (delete slots) or "no
primary" (promote to primary).

### Two-state model, pure apply, and append-time validation

Cluster Raft maintains two topology states on every node:

1. **Applied state (`S_a`)**: the cluster topology after applying
   `log[1..lastApplied]` (stored in `server.cluster->nodes`, `slots`,
   `shards`, `size`, and `rs->shard_epochs`, and persisted in the
   snapshot section of `nodes.conf`).
2. **Projected state (`S_p`)**: the topology after folding the entire
   uncommitted log tail onto `S_a`:
   `S_p = fold(apply, S_a, log[lastApplied+1..lastIndex])`.
   `S_p` is updated incrementally on log append and rebuilt from
   `S_a + log[lastApplied+1..lastIndex]` on truncation, snapshot
   install, startup, self-forget, and cluster reset.

**Pure apply:** `apply(S, entry) -> S'` is a total, deterministic
function of `(S, entry)` only. Apply functions never read node-local
volatile state (`rs->leader`, role, links, `match_index`, timers, or
wall clock) and never silently turn committed entries into no-ops.
Local side effects (reconfiguring replication for `myself`, closing
links to a forgotten node, stepping down after a committed self-demotion)
are allowed, but never affect replicated state.

**Append-time validation only:** Before appending any entry (whether
from a local command, a forwarded `PROPOSE`, or a retried proposal after
leader change), the leader validates it against `S_p` (applied state
plus the entire uncommitted tail, including entries inherited from older
terms). Facts not in the log (learner caught up, node failed, link up)
are checked at append time and, where they matter for the outcome,
encoded in the entry (e.g., expected shard epochs). Because proposals
are validated in log order against `S_p`, racing losers are rejected
before append (`REJECT`) rather than committed as no-ops.

**Debug-only apply checks:** Apply-time invariant checks follow Valkey's
standard `enable-debug-assert` (`debugServerAssert`, off by default in
production and enabled in the test harness). When `enable-debug-assert` is
enabled, apply re-runs the validation predicate against `S_a` right before
applying each committed entry and verifies after `raftApplyCommitted()` that
`S_p` matches a fresh rebuild from `S_a` + uncommitted tail and that
`server.cluster->size` equals the applied voter count, aborting via
`debugServerAssert` on any violation. In production (`enable-debug-assert no`),
apply never rejects or skips entries.

## PROPOSE and Leader Validation

Followers forward proposals to the leader using the `PROPOSE` message,
sent on the outbound link to the leader (or `FORGET_VOTER` when
`CLUSTER FORGET` targets a voter). The leader authoritatively validates
every proposal against `S_p` before appending it to the log. Invalid or
stale proposals are rejected immediately with `REJECT <reason> <type> <data...>`
without consuming log indices.

### Proposal retry on leader change

A pending proposal stays in the originator's list until the matching
entry is committed and applied, or until the leader sends a terminal
`REJECT`. Sending `PROPOSE` does not remove it. If the leader dies or a
new leader is elected, the proposal is retried automatically:

- If the follower becomes the new leader, it checks whether the entry is
  already in its uncommitted tail; if not, it re-validates against `S_p`
  and appends it (or rejects/defers on stale epoch).
- If another node becomes leader, the follower forwards the pending
  proposal to the new leader.

Pending proposals expire after 3× `cluster-node-timeout` since last
send (capped at 10× `cluster-node-timeout` overall). If a proposal
expires, the client receives a timeout error.

## Link Identification (HELLO/HI)

HELLO is sent on every new outbound connection. HI is the reply on
the same link. This exchange identifies both sides and occurs on
every connection: initial joins, reconnections, and new links to
nodes learned via AE.

After HI completes, the leader sends AE to bring the peer up to
date. A follower retries any deferred proposals to the leader.

## Cluster Formation (MEET/ADD_ME/WELCOME)

CLUSTER MEET is synchronous from the client's perspective: the command
blocks until the target node has stepped down (can't form a competing
cluster) or until the node is committed in the raft log.

MEET is sent immediately after HELLO on CLUSTER MEET-initiated
connections. The reply is either ADD_ME or WELCOME:

- **MEET → ADD_ME**: The receiver is a singleton leader. It steps
  down to joiner and replies ADD_ME. The sender invites it.
- **MEET → WELCOME**: The receiver is in a cluster (size > 1). It
  replies WELCOME immediately and invites the sender. The sender
  steps down to joiner on receiving WELCOME.

### Unblock conditions for CLUSTER MEET

The client is unblocked when any of these occur:
- **ADD_ME received**: The peer stepped down to joiner — it can't
  form a competing cluster. Safe to proceed with the next MEET.
- **WELCOME received**: We stepped down to joiner — we'll be added
  by the peer's cluster.
- **NODE_JOIN applied** (fallback): When the target node's NODE_JOIN
  entry is applied locally (e.g., for deferred meets forwarded via
  a follower).

### Why early unblock is safe

The blocking requirement prevents disjoint non-singleton clusters
from forming during chained MEET commands (A→B, B→C, C→D). Early
unblock (on ADD_ME/WELCOME) is safe because once a node steps down
to joiner, it cannot:
- Win an election (no voters know it)
- Commit entries (not a leader)
- Form a cluster independently

The worst case on crash is liveness failure (orphaned joiners), not
safety violation (disjoint clusters). Joiners revert to singleton
leader after 4× cluster-node-timeout — intentionally longer than
the proposal expiry (3× cluster-node-timeout) to avoid a race: if
a re-proposed NODE_JOIN commits and AE is sent to the joiner, the
joiner must still be waiting. If it reverts first, it bumps its
term and rejects AE, potentially disrupting the cluster's leader.

### Deferred MEET

When a joiner receives MEET (e.g., in reverse star formation where
multiple nodes MEET the same target), the MEET is deferred until the
joiner promotes to follower (applies its own NODE_JOIN). At that
point, the node has size > 1 and processes deferred meets by sending
WELCOME and inviting the sender.

### Two singletons meeting

```
  Admin                   Node A               Node B
  client               singleton leader     singleton leader
    |                       |                     |
    |--- CLUSTER MEET B --->|                     |
    |                       |--- HELLO ---------->|
    |                       |<------- HI ---------|
    |                       |--- MEET singleton ->|
    |                       |                     |  Step down to joiner
    |                       |<------ ADD_ME ------|
    |<------- OK -----------|                     |
    |                       |                     |
    |             Propose NODE_JOIN(A) + NODE_JOIN(B)
    |             Commit (quorum=1)               |
    |             Apply: size=2                   |
    |                       |                     |
    |                       |--- AE ------------->|  Apply: promote
    |                       |<-- AE_ACK ----------|  to follower
```

### Singleton joining an existing cluster

```
  Admin                   Node A               Node B
  client               singleton leader       in cluster
    |                       |                     |
    |--- CLUSTER MEET B --->|                     |
    |                       |--- HELLO ---------->|
    |                       |<------- HI ---------|
    |                       |--- MEET singleton ->|
    |                       |                     |  size > 1
    |                       |<----- WELCOME ------|  Invites A
    |                       |                     |
    |              Step down to joiner            |
    |<------- OK -----------|                     |
    |                       |                     |  Leader commits
    |                       |                     |  NODE_JOIN(A)
    |                       |<---- AE ------------|
    |                       |                     |
    |              Apply NODE_JOIN(A)             |
    |              promotes A to follower         |

```

### AE suppression during joining

AE and VOTE_REQ are not sent to nodes that aren't in the raft log
yet. This prevents a race where AE
arrives before MEET on the same link, causing the receiver to step
down prematurely and defer the MEET.

### Membership changes (Config-on-append)

Membership and voting rights are separate. `NODE_JOIN ... learner` adds
a node to the replicated topology without changing quorum; only
`ADD_VOTER` and `DEL_VOTER` change the voter set after bootstrap.
`NODE_JOIN ... voter` is permitted only as the empty-log bootstrap
self-join of a singleton, and `NODE_FORGET` may only target a learner.
To forget a voter via `CLUSTER FORGET`, the leader chains `DEL_VOTER`,
waits for it to commit, and then appends `NODE_FORGET`.

| Entry                                | Changes effective voter set |
|--------------------------------------|-----------------------------|
| `NODE_JOIN ... learner`              | no                          |
| `NODE_FORGET` (learner only)         | no                          |
| `NODE_JOIN ... voter` (bootstrap)    | yes (0 → 1)                 |
| `ADD_VOTER`                          | yes (+1 voter)              |
| `DEL_VOTER`                          | yes (-1 voter)              |

Because an entry's voter effect is determined by the entry alone,
non-voting membership changes (`NODE_JOIN ... learner`, `NODE_FORGET`)
can still be pipelined freely while voter changes follow Ongaro's
single-server configuration change rules (§4.1):

1. **Effective voter set `V(S_p)` takes effect on append.** Every node
   uses the voter set of its projected state `S_p` (latest config in the
   log, committed or not) for:
   - `PRE_VOTE` and `VOTE` tallying (deduplicated per voter ID; votes
     count only from members of the counting node's `V(S_p)`),
   - `PRE_VOTE_REQ` and `VOTE_REQ` targets and vote-granting eligibility,
   - leader commit counting and leader quorum freshness checks,
   - leadership transfer target selection, and
   - the single-voter fast-commit path, which requires `V(S_p) == {myself}`
     and a current-term entry (never `size <= 1`).

   `server.cluster->size` remains the applied voter count derived from
   `S_a` (for `CLUSTER INFO` / `CLUSTER NODES`).

2. **At most one uncommitted voter change.** The leader rejects
   `ADD_VOTER` and `DEL_VOTER` while any voter-changing entry exists in
   `log[commit_index+1..lastIndex]`.

3. **New leader commits own-term entry first (Ongaro 2015).** A newly
   elected leader always appends a `NOOP` in its own term and rejects
   `ADD_VOTER` and `DEL_VOTER` until `commit_index > 0` and
   `termAt(commit_index) == current_term`. This guarantees every prior
   configuration is committed before a new configuration is appended,
   preserving quorum intersection across all simultaneously active
   configurations.

4. **Leader self-demotion.** A leader may append `DEL_VOTER` for itself
   as long as `|V(S_p)| > 1`. Once appended, `myself` is no longer in
   `V(S_p)`: the leader keeps replicating without counting its own ack
   or freshness, broadcasts a commit `AE`, and steps down to `learner`
   once the `DEL_VOTER` commits and applies.

5. **Rollback on truncation.** If a follower truncates conflicting
   uncommitted entries on `AE`, `S_p` is rebuilt from `S_a` plus the
   remaining tail and the node's non-leader role (`follower` ↔ `learner`)
   is re-synchronized with `V(S_p)`.

6. **Crash/restart safety.** On startup, `S_p` is rebuilt from the
   persisted snapshot (`S_a`) plus the persisted log tail, and the node's
   role is synchronized with `V(S_p)`. Membership safety does not depend
   on persisting `commit_index` or on apply/persist ordering.

## Failure Detection

The leader tracks `last_ack_time` per peer, updated on every AE_ACK
received. In the leader's cron, if a peer hasn't responded within
`cluster-node-timeout`, the leader proposes a NODE_FAIL entry.

On apply, the FAIL flag is set on the node and slot coverage is
rechecked, transitioning `cluster_state` to `fail` if a node with
slots is down.

When a failed node comes back and sends AE_ACK, the leader proposes
a NODE_RECOVER entry to clear the FAIL flag on all nodes.

### Election timeout

The election timeout is based on `cluster-node-timeout`:
`[T, 2T)` where T = max(cluster-node-timeout, 1000ms). The heartbeat
interval is `election_timeout / 10`, minimum 100ms.

#### Pre-vote and term inflation

Ongaro's dissertation (§9.6) introduces pre-vote to reduce disruption
when a partitioned node rejoins, but it does not spell out the full
election-timeout state machine that production implementations need.
In classic Raft, every election timeout on a follower increments
`currentTerm` and sends RequestVote. A node isolated from the quorum
will therefore bump its term on every timeout even though it can never
win — when it rejoins, its higher term forces the real leader to step
down.

Pre-vote breaks this cycle by separating *connectivity probing* from
*term commitment*. A pre-vote round sends `PRE_VOTE_REQ` with a
*speculative* term of `currentTerm + 1` but does **not** change local
`currentTerm`, `votedFor`, or the on-disk vars line. Only after a
majority grants `PRE_VOTE` does the node call `StartElection()`, which
increments `currentTerm`, votes for itself, and persists the new term
before broadcasting `VOTE_REQ`.

Nodes deny `PRE_VOTE` and `VOTE_REQ` when they still consider the
current leader alive: `last_heartbeat` is younger than one election
timeout. The same log-up-to-date check applies to both message types.

#### Timeout state machine

```
                +----------+
                | FOLLOWER |
                +----------+
                   |    ^
  election timeout |    | pre-vote timeout
                   v    |
              +---------------+
              | PRE_CANDIDATE |
              +---------------+
                   |    ^
   quorum PRE_VOTE |    | election timeout
                   v    |
               +-----------+
               | CANDIDATE |
               +-----------+
                   |
       quorum VOTE |
                   v
               +--------+
               | LEADER |
               +--------+
```

The non-obvious transition is `CANDIDATE -> PRE_CANDIDATE`. After a
split vote, the node has already bumped `currentTerm`; immediately
starting another election would bump it again even if the node cannot
reach a majority. Re-entering pre-vote first confirms that a quorum is
reachable before committing to another term increment.

Pre-vote is an in-memory probe. It uses the speculative term
`currentTerm + 1`, but it does not update or persist `currentTerm` or
`votedFor`. Only `StartElection()` persists a new term and self-vote,
and only after a majority has granted pre-vote.

The leader lease check is shared by pre-vote and real vote requests:
nodes that have heard from the leader within one election timeout deny
both. This keeps a reachable leader stable while still allowing a node
whose pre-vote timed out to fall back to follower and retry later
without inflating its term.

### Backdating on leader election

When a node wins an election, it backdates the old leader's
`last_ack_time` to the time of the last heartbeat received. This
allows the new leader to detect the old leader as failed almost
immediately, without waiting an additional `node_timeout`.

### Multiple simultaneous failures

When the raft leader and another primary fail simultaneously, the
failure detection timelines differ between gossip and raft:

```
Gossip protocol — parallel failure detection:

  Time 0     Leader (L) and Primary (P) both fail
             |
  T          All nodes mark L and P as PFAIL independently
             |
  T+few sec  Gossip propagates PFAIL → FAIL for both L and P
             Replicas of L and P start failover in parallel
             |
  ~T+3s      Both failovers complete

  Total: ~node_timeout + gossip propagation
```

```
Raft protocol — sequential through new leader:

  Time 0     Leader (L) and Primary (P) both fail
             |
  T..2T      Election timeout fires on fastest follower
             New leader (N) elected
             |
  ~T         N backdates L's last_ack_time → proposes NODE_FAIL(L)
             immediately. Replica of L starts failover.
             |
  ~2T        N's last_ack_time for P was set to election time.
             After node_timeout from election, N detects P as failed.
             Proposes NODE_FAIL(P). Replica of P starts failover.

  Total: ~2 * node_timeout for the second failure
```

The gossip protocol detects all failures in parallel after one
`node_timeout`. Raft detects the old leader quickly (backdating) but
other failures take an additional `node_timeout` from the election,
because the new leader has no prior heartbeat history for those nodes.

Note: in gossip, only one failover election can be in progress at a
time (per epoch). When multiple primaries fail simultaneously, their
replicas are staggered using a "failed primary rank" to avoid
collisions. This adds small delays but is still much faster than
raft's sequential detection, since the ranking delays are on the
order of seconds rather than a full `node_timeout`.

### Potential future improvements to simultaneous failure detection

* Heartbeat timestamps in VOTE: To close this gap, voters could include their
  last known `last_ack_time` for each peer in the VOTE response. The new leader
  would use the oldest `last_ack_time` across all voters for each peer, giving
  it a head start on failure detection for all unresponsive nodes — not just the
  old leader. However, this will bloat the heartbeat messages.

* Defer primary failure detection to each shard, using the replication protocol.
  Primaries send PING commands over the replication stream as heartbeats to the
  replicas. If a replica hasn't received one for enough time, it can propose its
  primary as failing to the raft leader.

## Blocking Async Commands

Commands that modify cluster metadata (MEET, ADDSLOTS, REPLICATE,
FORGET, FAILOVER) block the client using `blockClientAsync` before
calling the vtable callback. The callback receives an opaque handle
that wraps the client ID.

When the operation completes (synchronously on the leader for
single-node clusters, or asynchronously after raft commit), the
completion callback looks up the client by ID, sends the reply, and
calls `unblockClientAsync`.

The actual unblock is deferred to `blockedBeforeSleep` (not done
inline from timer or read handlers), matching the pattern used by
modules, WAIT, and all other blocking types. This ensures
`processUnblockedClients` runs in the same event loop iteration.

Key implementation details:
- `call()` leaves `executing_command=1` when a client blocks, so the
  sync/async distinction uses `server.current_client == c` instead.
- `c->duration` is not cleared when blocking (stats are deferred), so
  `updateStatsOnUnblock()` is called before `unblockClient()`.
- `BLOCKED_ASYNC` is allowed for replicated clients (the sync path
  completes immediately inside `call()`).

## Compatibility with CLUSTER SLOTS and CLUSTER SHARDS

`CLUSTER SLOTS` and `CLUSTER SHARDS` report node health and
replication offsets. In gossip, each node's replication offset is
piggybacked on ping/pong messages and stored in `node->repl_offset`.
This is not persisted in nodes.conf — it's purely ephemeral.

The leader learns each follower's replication offset from AE_ACK
messages and updates `node->repl_offset` locally. To propagate
offsets to other nodes, the leader sends REPL_OFFSETS messages. This
is currently done before NODE_FAIL (for failover ranking) and is
planned for when a replica finishes initial sync (offset transitions
from 0 to non-zero).

On the leader, CLUSTER SLOTS and CLUSTER SHARDS show accurate offsets
and health. On followers, remote replicas start with `repl_offset = 0`
(hidden from CLUSTER SLOTS) until the leader broadcasts their real
offset via REPL_OFFSETS. The broadcast is triggered immediately when
a node's offset transitions from 0 to non-zero, and periodically
every 10 seconds.

## Persistence

Raft state is persisted in `nodes.conf`. The file has three sections:

1. **Node lines** — the cluster state snapshot (nodes, slots, replication
   topology) as of `lastApplied`.
2. **Vars line** — `currentTerm`, `lastApplied`, `snapshotTerm`,
   `votedFor`, `raftLeader`.
3. **Log lines** — entries with index > `lastApplied` appended at the end.

Only `currentTerm`, `votedFor`, and the log require persistence for
safety; `commitIndex` is rediscovered from the leader after restart
(Raft paper §5.2, Figure 2).

Log line format:

    log <index> <term> <type> <data>

### Full rewrite

A full rewrite (atomic write to temp file + rename + fsync) is triggered
when:

- `currentTerm` changes (step-down on higher term).
- `votedFor` changes (granting a vote or starting an election).
- An applied entry affects `myself` (SLOT_CHANGE, SET_REPLICA_OF,
  FAILOVER, NODE_JOIN promotion from learner).

A full rewrite updates the snapshot (node lines reflect the current
applied state), updates `lastApplied` in vars, and writes only
unapplied log entries in the tail.

### Append-only

When new log entries arrive (from AE or local proposals), they are
appended to the end of the file with a single batched write + fsync
(deferred to `beforeSleep`). No full rewrite is needed.

**Safety invariant:** The fsync must complete before the AE_ACK reaches
the leader. This is enforced by deferring the success AE_ACK: the AE
handler sets `todo_send_ae_ack` instead of sending immediately, and
`beforeSleep` sends the ACK only after persistence completes. If fsync
is ever moved to a background thread, the ACK must be deferred until
the background fsync completes.

### Startup

On load:

1. Node lines are parsed → applied cluster state (`S_a`) restored (snapshot).
2. Vars line is parsed → `currentTerm`, `votedFor`, `lastApplied` restored.
   `commit_index` is set to `lastApplied`.
3. Log lines are parsed → entries added to the in-memory log.
4. `S_p` is rebuilt from `S_a` plus the persisted log tail, and the node's
   Raft role (`follower` vs `learner`) is synchronized with `V(S_p)`.
5. If the node is a replica, replication is started.

The leader will send AE after reconnection, updating `commit_index`.
Entries between `lastApplied + 1` and the new `commit_index` are then
applied.

### Integrity checks

Each log line includes a CRC64 checksum as its first field:

    log <crc64hex> <index> <term> <type> <data...>

The CRC covers the payload (everything after the checksum field). On
load, each line is validated:

- **CRC matches** → accept the entry (regardless of trailing `\n`)
- **Invalid + no trailing `\n`** → discard (last line, short write from
  crash during append; safe because AE_ACK is sent only after fsync)
- **Invalid + trailing `\n`** → fatal (complete line is corrupted)
- **Index gap between valid entries** → fatal (missing entry)

The snapshot section (node lines + vars) is protected by a separate
`crc` line written between vars and log lines.

After loading, a full rewrite is always scheduled to produce a clean
file (removes any incomplete trailing line).

### File format

The node lines share the same format as the gossip protocol (code
reuse), but the vars and log lines are raft-specific. The file is not
compatible between protocols — switching from gossip to raft (or vice
versa) requires removing nodes.conf.

## Log compaction and snapshots

### Conceptual model

The `nodes.conf` file IS the snapshot. The node lines represent the
fully applied cluster state at `lastApplied`. Entries at or before
`lastApplied` are not stored — only their cumulative effect (the cluster
state) is retained. Entries after `lastApplied` are stored as log lines.

This corresponds to the Raft paper's snapshot mechanism (§7), where:

- **`lastApplied`** = `lastIncludedIndex` (last entry in the snapshot)
- **`snapshotTerm`** = `lastIncludedTerm` (term of that entry)

`snapshotTerm` is needed because the entry at `lastApplied` is no longer
in the log. When the leader sends AE whose previous entry is the one at
`lastApplied`, the follower verifies its term against `snapshotTerm`.

Note: the standard Raft paper persists the full log (or log from the
snapshot point). We don't — we only persist entries after `lastApplied`.
This is why `snapshotTerm` must be explicitly stored in the vars line,
whereas in a textbook implementation it could be read from the log.

Terms start at 1, so a term of 0 always means an unknown entry. A node
refuses to start if `nodes.conf` contains a log entry with term 0, has
`lastApplied` without `snapshotTerm`, or has a `currentTerm` lower than
`snapshotTerm`.

### In-memory log trimming

Each node trims applied entries from its in-memory log to bound memory
usage. It keeps the 64 most recent applied entries, so that slow
followers can catch up through normal AE, and trims in batches when
there are more than 128. The term of the last trimmed entry is
remembered, so a follower can still be checked against the entry just
before the first one in memory.

A follower rejects an AE whose previous entry it doesn't know, and only
appends entries that directly follow its last log entry, so its log
never has gaps. On rejection, the leader steps back, and once it needs
an entry it has trimmed, it sends a snapshot instead.

### InstallSnapshot

When a follower needs entries that the leader has trimmed, the leader
sends `INSTALL_SNAPSHOT` instead of AE. The message contains:

    INSTALL_SNAPSHOT <leader-id> <term> <last-index> <last-term>
    <node line 1>
    <node line 2>
    ...

The follower processes the snapshot by:

1. Checking all node lines before changing anything. If a line is
   invalid, for example because it has an unknown flag, or the sender
   isn't included, the snapshot is rejected with a failed AE_ACK and the
   follower keeps its state.
2. Replacing its cluster state with the node lines: nodes are created or
   updated, and nodes not present in the snapshot are removed.
3. Updating local state for slots whose owner changed, as when applying
   a slot change: completed importing and migrating markers are cleared,
   and keys in slots it no longer owns are deleted.
4. Promoting from joiner to follower if its own NODE_JOIN is included.
5. Setting `lastApplied` and `snapshotTerm` to the snapshot's values,
   clearing the in-memory log (all entries are superseded), and
   recomputing the number of voters (quorum).
6. Scheduling an automatic failover if it is a replica and its primary
   is failed in the snapshot.

Slot migration markers (`[slot->…]` and `[slot-<-…]`) aren't part of the
snapshot, since they are local to a shard and propagated through
replication.

The leader keeps resending the snapshot until the follower acknowledges
that it has installed it, at most every half node timeout. A lost
snapshot is therefore resent, but a slow follower doesn't get one on
every heartbeat.

### No-op entry on election

When a new leader is elected, it appends a no-op entry in its own term.
This serves two purposes (Raft paper §5.4.2, §8):

1. **Commit previous-term entries**: A leader cannot commit entries from
   prior terms by replica counting alone. The no-op in the current term
   carries older entries to commitment.
2. **Establish the new term in the log**: After the no-op is committed,
   `snapshotTerm` equals `currentTerm` in steady state, simplifying
   reasoning about the compaction boundary.

## Shard Epoch

Raft ensures entries are applied in a total order, but ordering alone
is not sufficient to prevent stale mutations from corrupting cluster
state. When concurrent operations target the same shard (e.g., a slot
migration racing with a failover), a committed entry may carry
assumptions about shard topology that are no longer true by the time
it is applied. Without additional application-level state to fence
against these stale updates, the apply logic can produce
inconsistencies — such as moving a slot to a node that no longer owns
the corresponding keys.

A shard-epoch is a per-shard monotonically increasing counter stored
in the raft protocol state. It is bumped each time membership or
leadership of the shard changes. Such entries include the shard's
current epoch at proposal time. Epoch is validated at prepare time
and at apply time. If the epoch has advanced past the value in the entry,
the entry is stale and is ignored.

### Example: slot migration racing with failover

```
1. Slot migration starts: keys transferred from shard A to shard B.
2. Primary of shard A fails. FAILOVER entry is proposed.
3. Migration is rolled back (keys stay on shard A's new primary).
4. SLOT_CHANGE entry (assigning slot to shard B) was proposed before
   the failover and appears after FAILOVER in the log.
5. Without shard-epoch: SLOT_CHANGE applies, slot moves to shard B,
   but keys are on shard A. Data and ownership are out of sync.
6. With shard-epoch: FAILOVER bumped shard A's epoch. SLOT_CHANGE
   carries the old epoch, so it's a no-op. Slot stays on shard A.
```

### Validation

Epoch and topology validation happens authoritatively at **append time on
the leader** against the projected state `S_p` (applied state plus the
whole uncommitted tail). If an epoch is stale, the leader rejects the
proposal immediately with `REJECT conflict <type> <data...>` without
appending to the log, and the proposing node defers and retries with a
fresh epoch once its epoch advances.

At apply time, entries are applied purely and deterministically without
rejection. When `enable-debug-assert` is enabled, apply re-checks the
validation predicate against `S_a` via `debugServerAssert`.

### Retry on stale epoch

Proposals rejected due to a stale shard epoch are automatically retried
with a fresh epoch (up to 5 attempts):

- **SET_REPLICA_OF / NODE_FORGET / FAILOVER (force) / SLOT_CHANGE** —
  the proposal is rebuilt with current epoch(s) and re-submitted.

- **Automatic failover** — if the FAILOVER proposal is rejected, the
  failover is re-scheduled (via `todo_schedule_failover`) as long as
  the primary is still failed. The next attempt uses the current epoch.
  For automatic failover, no cap on retry attempt to avoid leaderless shard.

Only `STALE_SHARD_EPOCH_REJECTION_MSG` triggers retry. Other errors
(format errors, invalid state) are forwarded to the client immediately.

When the leader rejects a forwarded proposal at pre-validation, it sends
a `REJECT <reason> <type> <data...>` message back. The reason is a token:
`conflict` (stale epoch, retryable) or `syntax` (permanent error).

### Entries that don't carry an epoch

- NODE_FAIL / NODE_RECOVER 
- NODE_INFO, NODE_JOIN

## Leader Transfer

On graceful shutdown, the leader sends a `TIMEOUT_NOW` message to the
follower with the highest `match_index`. The message is flushed
synchronously to the socket before shutdown proceeds. The target
immediately starts a real election (skipping pre-vote) without waiting
for the election timeout.
(See Ongaro dissertation §3.10.)

When `CLUSTER FORGET` targets the leader (a voter), the follower sends
`FORGET_VOTER <leader-id> <epoch>` to the leader. The leader validates
forget preconditions against `S_p`, starts a leadership transfer instead
of appending, and replies `REJECT transfer NODE_FORGET ...`. Since the
target skips pre-vote, the leader only sends `TIMEOUT_NOW` once the
target's `match_index` has reached the leader's last log index. If that
doesn't happen within the node timeout, the transfer is abandoned and
the leader stays leader. After sending `TIMEOUT_NOW`, the leader doesn't
append new entries until it steps down or the transfer times out, so the
target's log stays complete for the election. The proposing node keeps
the proposal pending and resends `FORGET_VOTER` to the new leader after
the leader change; the new leader then chains `DEL_VOTER` (after
committing its own-term `NOOP`) followed by `NODE_FORGET`. Otherwise it
times out.

Nodes in handshake, non-voters in `V(S_p)`, and nodes not yet in the
raft log are excluded as transfer targets.

## Future Work

- Automatic learner promotion (promote the first 5 or 7 nodes to voters).
- Chained learner replication.
- Balancing voters over availability zones: the leader can use the
  per-node availability-zone info to add/remove voters so that voters
  are spread across at least 3 zones, letting the cluster survive a
  single zone outage.
- Cluster merging via MEET: when two independently configured clusters
  are joined via CLUSTER MEET, the clusters should merge, either
  atomically or not.

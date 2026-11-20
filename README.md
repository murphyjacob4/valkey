# Raft Cluster Bus (valkey#3856): Lean model, gaps, and assumptions

**Scope:** [#3856](https://github.com/valkey-io/valkey/issues/3856) and all 20 sub-issues, the [design doc](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/design-docs/cluster-raft.md), and the related PRs/issues #3887, #3899, #4094, #4127, #4392–4394. I checked the model against [`src/cluster_raft.c`](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c) on `cluster-v2` @ `f278b08b` (2026-08-12).

**Lean project:** [lean/](lean/README.md). It uses Lean 4.35 core only. `lake build` checks 39 theorems with no `sorry`, and `lake exe explore` runs the bounded searches.

> [!IMPORTANT]
> The model reproduces the code's actual behaviour, not only the plan text, so several findings are **safety bugs in the current branch**. Each one has a short concrete trace that you could turn into a TCL test. I haven't reproduced any of them on a live cluster yet.

## How the model is organised

| Module | Issues covered | Kind of result |
|---|---|---|
| [Quorum.lean](lean/ValkeyRaft/Quorum.lean) | #3866, #3926, #4392, #4393 | General proofs (∀ inputs) |
| [Raft.lean](lean/ValkeyRaft/Raft.lean) + [Traces.lean](lean/ValkeyRaft/Traces.lean) | #3857–#3859, #3866, #3926, #3960, #4392 | Executable model + bounded DFS. Counterexamples are re-checked with `native_decide` |
| [Meta.lean](lean/ValkeyRaft/Meta.lean) | #3863, #3865, #3874, #4069, #3862/#4127 | Apply functions modelled after the C code. Concrete theorems by `decide` |
| [Protocols.lean](lean/ValkeyRaft/Protocols.lean) | #3860, #3861, #3862, #3868, #3869, #4069, proposal expiry | Small state machines, proven by `decide`/`omega` |
| *(no formal content)* | #3864, #3867, #3875, #3411, #3701 | Checked as text only (see §C) |

In `Raft.lean`, every place where the code differs from the Raft paper is a flag whose default is the code's behaviour. This means the same trace can be replayed under "code" and "fixed" settings.

---

## A. Safety violations in the current code

### A1. The AE_ACK `match_index` is the follower's *whole* last index (High)
- **Code:** the follower replies with `raftLogLastIndex()` ([L1696](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1692-L1699)), and the leader stores it as `match_index` ([L1825](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1823-L1826)). Raft requires `prevLogIndex + #entries`. The follower side has the matching deviation: `commit = min(leaderCommit, raftLogLastIndex())` ([L1768](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1766-L1769)).
- **Lean:** [`f1_ack_last_index_loses_committed_entry`](lean/ValkeyRaft/Traces.lean#L26) is an 8-step trace with 5 voters and no crash. A heartbeat ACK from a node with a stale uncommitted entry counts as a match for the new leader's *different* entry at that index. The entry "commits" on 2 of 5 real holders and is then overwritten. [`f1_fixed`](lean/ValkeyRaft/Traces.lean#L30) shows that reporting the verified index closes it. The fixed model found no violation in 295k states at depth 9.

### A2. Config-on-apply plus pipelined voter changes loses committed entries (High). This affects #3926 and #4392.
- **Code:** nothing serialises `ADD_VOTER`/`DEL_VOTER`/voter `NODE_FORGET` ([`clusterRaftProposeVoterChange`](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3747-L3758)).
- **Lean:** [`f2_pipelined_add_voter_loses_committed_entry`](lean/ValkeyRaft/Traces.lean#L50). The voters are {0,1,2}. Two ADD_VOTERs are committed by {0,1}. X is then committed by {0,3,4}, a majority of the new config. Node 1 never learned the commit, still uses {0,1,2}, and wins with {1,2}. **No crash is needed.** The general reason is [`two_step_majorities_can_be_disjoint`](lean/ValkeyRaft/Quorum.lean#L67): configs one step apart always overlap ([`adjacent_majorities_intersect`](lean/ValkeyRaft/Quorum.lean#L46), proven ∀), but configs two steps apart need not.
- **Design-doc claim that is wrong:** "Worst case… the new node is orphaned… No data loss". In fact *any* entry committed after the change can be lost, including SLOT_CHANGE and FAILOVER. The quoted 3→4 and 5→6 examples are also not the real mechanism. Votes are counted only from `nodeIsVoter` peers ([L2036](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L2036)), so a single in-flight change is not unsafe in the way the doc describes.
- **What the plans need:**
  - **#3926:** config-on-append **alone does not fix it**. [`f2b_config_on_append_without_serialisation_unsafe`](lean/ValkeyRaft/Traces.lean#L66) shows the leader using C₂ immediately. The essential rule is to **serialise quorum changes**.
  - **#4392's rule** "only one quorum-changing operation in flight; wait for commit" makes the F2 trace non-executable ([`f2_one_in_flight_blocks_trace`](lean/ValkeyRaft/Traces.lean#L55)). It also finds no violation in a bounded search, under both config-on-apply and config-on-append (see §D). That safety depends on an assumption that needs to be written down: *the AE carrying change k+1 also carries a commit index that covers change k, and the follower applies it before acting on it.*
  - This rule has to apply to **manual** `CLUSTER ADDVOTER/DELVOTER`, `NODE_FORGET` of voters, AZ rebalancing (#4393), and merge-time promotion (#3868), not only to the auto-promoter.

### A3. A restart leaves an empty log tail, and nodes.conf has no lastApplied term (High). This affects #3857, #3858, and #3859.
- **Code:** a full rewrite keeps only entries with index > `lastApplied` ([L3003-L3011](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3001-L3011)), and the vars line has no term for `lastApplied` ([L2948](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L2948-L2963)). With an empty log, `raftLogLastIndex()` and `raftLogLastTerm()` both return 0 ([L1312-L1320](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1312-L1320)).
- **Lean:**
  - [`f3_restart_empty_tail_grants_stale_vote`](lean/ValkeyRaft/Traces.lean#L82): a restarted, fully-applied node votes for a candidate with an empty log.
  - [`f3b_no_install_snapshot_skips_committed_entry`](lean/ValkeyRaft/Traces.lean#L95): persisting the term alone is not enough. `raftLogTermAt()` is 0 for indices that *neither* side holds, so a compacted leader "matches" a lagging follower below its own log start, and the C apply loop silently skips the missing entry ([L1773](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1770-L1774)).
  - [`f3c_full_restart_reuses_indices`](lean/ValkeyRaft/Traces.lean#L117): after a **full-cluster restart**, new entries are appended at index 1 again while `last_applied ≥ 1`. They are never applied, and Log Matching then commits a different history.
- **Fix that was checked:** persist `lastIncluded{Index,Term}`, have `lastIndex/lastTerm/termAt` fall back to it, and implement InstallSnapshot. With this, the model finds no violation (≈1M states, 2 restarts, 3 elections, depth 12). **#3858 is therefore a safety prerequisite, not just an optimisation, and #3859 is not "only tests left".**

### A4. Apply-time non-determinism (High). This affects #4069 and #3866.
Apply must be a pure function of (committed state, entry). Two apply functions read node-local state:
- `DEL_VOTER` rejects if the target equals `rs->leader` *at apply time* ([L3643](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3641-L3646)). [`del_voter_apply_nondeterministic`](lean/ValkeyRaft/Meta.lean#L219) shows that nodes then diverge on `size`, and therefore on quorum.
- `NODE_FORGET` rejects on the forgotten node itself (`node == myself`, [L3675](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3675)) and applies everywhere else ([`node_forget_apply_nondeterministic`](lean/ValkeyRaft/Meta.lean#L228)). The forgotten node keeps itself as a voter, and if it is the leader (#4069) it keeps leading. If its links are accepted, members that have no live leader grant it pre-votes, and *every* member steps down on its higher-term VOTE_REQ ([`forgotten_node_can_disrupt`](lean/ValkeyRaft/Protocols.lean#L116)), because `MaybeStepDown` runs before any membership check ([L1995](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1995)).
- **Gap to document:** "leader may not be removed" belongs in leader pre-validation, not in apply. A removed node must apply its own removal, then step down or reset (Raft §4.2.2), and messages from non-members must be ignored (§4.2.3). #4069's scope should be "leader *removal*", not just "leader transfer". The same applies to `CLUSTER RESET` (raised in #4069).

### A5. Stale-epoch auto-retry defeats the shard-epoch fence (High). This affects #3863 and #3874.
- **Code:** SLOT_CHANGE, NODE_FORGET, FAILOVER, and SET_REPLICA_OF are retried with *refreshed* epochs, up to `PROPOSAL_MAX_RETRIES = 10` ([L892-L898](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L891-L902), [L979-L1068](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L977-L1068)). The doc says 5.
- **Lean:** [`epoch_fences_stale_slot_change`](lean/ValkeyRaft/Meta.lean#L163) confirms the design-doc example works *without* retry. [`auto_retry_defeats_fence`](lean/ValkeyRaft/Meta.lean#L172) shows that with the retry, the slot moves to shard B anyway after the migration was rolled back, which is exactly the outcome the fence exists to prevent. NODE_FORGET's epoch guard is bypassed the same way ([`retry_rebuilds_forget_epoch`](lean/ValkeyRaft/Meta.lean#L184)).
- **Gap to document:** after a stale-epoch rejection, the *originator* has to re-check its semantic preconditions before resubmitting. Is the migration still valid? Is the node still forgettable? Blind epoch refresh is only safe for automatic failover. The retry semantics must be defined per entry type.

### A6. SLOT_CHANGE has no compare-and-swap on the current owner (Medium-High)
- **Code:** apply checks epochs only and reassigns every slot in the range ([L3366-L3404](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3366-L3404)). The proposer sets the source to the owner of the *first* slot only ([L3321](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3321)).
- **Lean:**
  - [`concurrent_same_slot_migrations_both_apply`](lean/ValkeyRaft/Meta.lean#L195): two migrations of the same slot both apply, and the first target **deletes the keys it received** as a "dirty slot".
  - [`concurrent_addslots_both_apply`](lean/ValkeyRaft/Meta.lean#L207) shows the same for ADDSLOTS.
- **Assumption to document or enforce:** the doc says "two slot migrations touching the same shard are safe… as they affect different slots". That is never checked. Not bumping the epoch on SLOT_CHANGE is only sound if apply validates `slots[j] == source` for every slot.

### A7. Duplicated or replayed non-epoch entries (Medium)
- `clusterRaftRetryProposals(1)` runs **on every cron tick** and re-sends every pending proposal. On the leader it re-appends them ([L2385](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L2384-L2385), [L2252](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L2249-L2258)). A leader without quorum accumulates roughly 10 duplicates per second per proposal until it steps down.
- A leader-originated `NODE_FAIL` survives step-down in the pending list. It is then forwarded to the *new* leader, which appends it without checking its own detector.
- [`duplicate_node_fail_not_harmless`](lean/ValkeyRaft/Meta.lean#L239): a NODE_FAIL that lands after NODE_RECOVER marks a healthy primary failed and schedules a failover. The doc's claim "duplicate proposals are harmless because all entry types are idempotent" holds only for epoch-carrying entries ([`duplicate_failover_harmless`](lean/ValkeyRaft/Meta.lean#L244)). NODE_INFO has the same last-writer-wins problem, softened by the 10-second divergence check.

### A8. Shard-level failure detection (#3862 / #4127) (Medium)
- [`mutual_node_fail_both_apply`](lean/ValkeyRaft/Meta.lean#L255): if the primary and replica lose only their link to each other, both NODE_FAILs apply and the shard is marked fully failed while both processes are up.
- [`failed_replica_can_be_promoted`](lean/ValkeyRaft/Meta.lean#L262): FAILOVER apply doesn't check the replica's health.
- [`one_way_partition_inverts_order`](lean/ValkeyRaft/Protocols.lean#L82): the T vs 1.5T asymmetry orders the two detections only for symmetric failures.
- **Gaps:**
  - NODE_FAIL from a shard peer needs proposer validation (proposer not FAIL, still in the shard) or a shard epoch.
  - FAILOVER should require the candidate to be healthy.
  - The plan doesn't say whether the primary must **stop accepting writes** when its replica lease lapses (the PacificA lease). Without that, the split-brain write window is the same as in gossip mode and should be documented.

### A9. Suspected: a restarted follower with a conflicting non-empty tail corrupts the log array (needs a repro)
This one comes from code reading only and is not modelled. After a restart, the in-memory log starts at `lastApplied+1`. If the leader's probe goes below that (because the tail conflicts), `raftLogGet()` returns NULL for low indices. The AE handler then `raftLogAppend`s those indices *after* the stale tail ([L1758-L1759](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1752-L1762)), and the base-offset indexing in `raftLogGet` ([L1296-L1298](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L1291-L1299)) then returns wrong entries. The same InstallSnapshot work as in A3 fixes it.

---

## B. Plan-level gaps and assumptions, by sub-issue

| Issue | Gap / assumption that needs documenting |
|---|---|
| **#3857** Persistence (closed) | (1) The snapshot needs `lastIncluded{Index,Term}` (A3). (2) The leader counts itself in the commit quorum before its own fsync. This is safe only because of event-loop ordering (fsync in `beforeSleep` happens before any ACK can be read), so state that invariant next to the follower-side one. (3) The CRC check is skipped when the parsed CRC is 0 (`expected_crc != 0 &&`, [L3054](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L3054)), so a garbled checksum field disables verification (#3960). |
| **#3858** Snapshots | Required for safety (A3), not only for catch-up. The snapshot must carry node lines, **shard epochs** (today in the config-epoch column), voter/learner flags, and the lastIncluded term. A leader must never send AE below its log start. |
| **#3859** Crash recovery | Not "done except InstallSnapshot": A3/F3c (full-cluster restart) and A9 are open. Also: the joiner revert path bumps the term and sets `voted_for` without `todo_save_config` ([L2334-L2341](https://github.com/valkey-io/valkey/blob/f278b08bc33539998477b67e9da04883801c840d/src/cluster_raft.c#L2334-L2341)). |
| **#3860** Pre-vote (closed) | Proven: an isolated node never inflates its term ([`isolated_never_inflates`](lean/ValkeyRaft/Protocols.lean#L25)). Gap: the tally is a message counter, not a set of voters, and accepts grants from earlier rounds of the same term ([`stale_prevote_double_counted`](lean/ValkeyRaft/Protocols.lean#L40)). This affects liveness and term inflation, not safety. Doc mismatch: "nodes deny VOTE_REQ when they consider the leader alive" is effectively bypassed, because `MaybeStepDown` clears `rs->leader` first. Only PRE_VOTE enforces the lease. |
| **#3861** Step-down (closed) | Old and new leaders can overlap by up to the ACK latency plus clock drift ([`two_leaders_window`](lean/ValkeyRaft/Protocols.lean#L57)). Document that leadership is **not** a read lease (CLUSTER SLOTS/NODES may be stale) and that leader-only decisions such as NODE_FAIL may come from a deposed leader. |
| **#3862 / #4127** Decentralised FD | See A8. Also decide: (a) who monitors **learners** (sushilpaneru1's open point), (b) how the two detectors hand over when a shard goes from 1 to 2 or more nodes, (c) `repl-ping-replica-period` must be lower than the timeout and is overridden. Document that it is overridden. |
| **#3863** Shard epochs (closed) | A5 and A6. Also: `validEpoch` treats `current == 0` as "accept anything", so epochs are never checked on a shard that has only seen SLOT_CHANGE. Document that. |
| **#3864** REPLCONF failover | No formal content. Assumption: a capability handshake (`REPLCONF CAPA`) and coexistence with `FAILOVER_PREPARE`. Define which mechanism wins if both are in flight. |
| **#3865** MIGRATING/IMPORTING (closed) | Keeping these node-local is fine *only if* SLOT_CHANGE checks the owner (A6). Otherwise nothing cluster-wide prevents two migrations of the same slot. |
| **#3866** Learners (closed) | Good separation of membership and voting. Gaps: A2 (voter changes are not serialised) and A4 (DEL_VOTER apply reads `rs->leader`). |
| **#3867** valkey-cli | The sequential-command approach needs the **timeout ⇒ unknown outcome** semantics ([`timeout_but_applied`](lean/ValkeyRaft/Protocols.lean#L227)). The CLI must re-read state before retrying, because the entry may commit after `-TIMEOUT`. |
| **#3868** Merge | (1) A handoff held in memory loses the absorbee's slot map if the absorber leader crashes before committing it ([`volatile_handoff_loses_slot_map`](lean/ValkeyRaft/Protocols.lean#L151)). The absorber must *commit* the handoff before the absorbee dissolves ([`persisted_handoff_safe`](lean/ValkeyRaft/Protocols.lean#L158)). The "cache as pending proposals" variant is equally volatile, because pending proposals are not persisted. (2) Shard epochs from the absorbee are meaningless in the absorber, so define how they map (and A5's refresh would silently accept them). (3) Promotion after the merge must follow A2's serialisation rule. (4) Define the tie-break for "larger cluster wins". |
| **#3869** Sync replication | If the primary starts waiting for the replica only once SYNC is *applied*, acknowledged writes are missing from a "sync" replica ([`late_wait_breaks_invariant`](lean/ValkeyRaft/Protocols.lean#L198)). It must wait from proposal time ([`eager_wait_keeps_invariant`](lean/ValkeyRaft/Protocols.lean#L201)). Also: FAILOVER apply must require the candidate to be in the SYNC set, promotion and demotion must carry and bump the shard epoch, and demotion must commit before the primary acknowledges writes without that replica (PacificA). |
| **#3874** Leader pre-validation | Pre-validation reads committed state only. It cannot replace apply-time validation, but it can host the leader-only rules ("can't DEL_VOTER/FORGET the leader", "one quorum change in flight") that are wrongly placed in apply today (A4). |
| **#3875** ACL/Functions | Undecided. If they go into the Raft log they become entries without epochs, so define conflict and retry semantics up front (A7). |
| **#3926** Config-on-append | Serialisation is the essential part (A2, [`f2b_…`](lean/ValkeyRaft/Traces.lean#L66)). The bounded model also found no violation for config-on-*apply* plus serialisation, so config-on-append is optional for safety if the "AE carries commit and the follower applies immediately" assumption is documented. |
| **#3960** Log CRC (closed) | See #3857 (3). |
| **#4069** Forget the leader | See A4: this is an apply determinism bug, not just a transfer feature. TIMEOUT_NOW does work today, but only because a higher-term VOTE_REQ bypasses the lease. Document that dependency. |
| **#4392** Auto-promotion | Its "one quorum change in flight" invariant is *required*, and it must also cover manual commands (A2). The target must count configured voters (agreed in the thread). An even target is useless for AZ survival ([`four_voters_three_zones_never_survive`](lean/ValkeyRaft/Quorum.lean#L108)). |
| **#4393** AZ balancing | "At least 3 zones" is **not sufficient** ([`three_zones_not_sufficient`](lean/ValkeyRaft/Quorum.lean#L98)). The exact condition is *max voters per zone ≤ ⌊(n−1)/2⌋* ([`survives_iff`](lean/ValkeyRaft/Quorum.lean#L86)). Rebalancing with DEL-then-ADD passes through an unsafe even count ([`rebalance_transient_unsafe`](lean/ValkeyRaft/Quorum.lean#L115)), so prefer ADD-then-DEL. |

## C. Cross-cutting assumptions to write into the design doc
1. **Apply determinism:** an apply function may read only committed replicated state and the entry. It must never read `myself`, `rs->leader`, links, or timers (A4).
2. **Membership changes are serialised.** The next quorum change may start only after the previous one is committed *and* carried, together with its commit index, to any node that receives the next one (A2).
3. **Per-type retry semantics:** each entry type must state whether it is idempotent, whether a stale rejection is retried, and *who* re-checks preconditions (A5, A7).
4. **Proposal outcome:** `-TIMEOUT` means unknown. Pending proposals are in memory only and are lost on restart (#3867, #3868).
5. **Transport:** the model assumes per-link FIFO delivery (TCP), atomic delivery of AE and its ACK, and instantaneous fsync. Message reordering, duplication, and fsync stalls were *not* explored.
6. **Leadership is not a lease** for reads or for failure verdicts (#3861).
7. **Non-members are ignored:** messages from nodes outside the applied config must be dropped (A4).

## D. Bounded verification results

| Scenario (Explore.lean) | Result |
|---|---|
| S1 code, 5 static voters | **Violation** in 8 steps (83k states) → A1 |
| S1 fixed ACK (verified index) | None to depth 9 (295k states) |
| S2 config-on-apply, pipelined ADD_VOTER | **Violation** in 9 steps → A2 |
| S2a config-on-apply + one-in-flight, 1 election | None to depth 10 (746k states) |
| S2b config-on-append, pipelined | **Violation** in 8 steps → A2 |
| S2c config-on-append + one-in-flight, 1 election | None to depth 10 (557k states) |
| S2a2 config-on-apply + one-in-flight, 2 elections | None to depth 11 (6.2M states) |
| S2c2 config-on-append + one-in-flight, 2 elections | None to depth 11 (5.0M states) |
| S3 code restart | **Violation** in 9 steps → A3 |
| S3 + persisted snapshot term, no InstallSnapshot | **Violation** in 9 steps → A3 |
| S3 + snapshot term + InstallSnapshot, 2 restarts, 3 elections | None to depth 12 (1.0M states) |

> [!NOTE]
> "No violation" results are bounded and under-approximate. Failed elections, message reordering, and pre-vote/lease timing aren't explored. Every **violation** is a real, executable trace of the model, and the model's behaviour was read off the C code line by line.

## E. Suggested next steps
1. Turn F1, F2, F3, and F3c into TCL tests on `cluster-v2`. They are short, deterministic traces.
2. Fix A1 (ACK index and follower commit), A3 (snapshot term), and A4 (move the leader checks out of apply). These are small and local.
3. Decide A5 and A6 together. Either SLOT_CHANGE gets an owner check and stale-epoch retries re-check preconditions at the originator, or the doc example is dropped.
4. Add the §C invariants to `design-docs/cluster-raft.md` before #3926, #4392, #4393, and #3868 build on them.

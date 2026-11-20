/-
  Certified counterexamples for the Raft log layer (see `Raft.lean`).

  Each trace was found by the bounded explorer (`lake exe explore`) and is
  re-checked here by evaluation. `native_decide` is used because the safety
  monitor builds diagnostic strings; the traces are short and fully concrete.
-/
import ValkeyRaft.Raft

namespace ValkeyRaft.Traces
open ValkeyRaft.Raft

/-! ## F1. AE_ACK reports the follower's last index (cluster_raft.c:1696, 1825)

5 voters. Leader 0 (term 1) appends X and replicates it to 1 only. Node 2 wins
term 2 (votes of 2,3,4). Its first AE to node 0 is a heartbeat with 0 entries;
node 0's AE_ACK reports `raftLogLastIndex()` = 1 (its stale X), so node 2 sets
`match_index[0] = 1`. Node 2 appends Y at index 1 and replicates to node 1;
counting itself, node 1 and the bogus match of node 0, Y "commits" on 2 of 5
real holders. Node 0 is then elected in term 3 (votes of 0,3,4: its log
`[X@t1]` is as up-to-date as theirs) and overwrites the committed Y. -/
def o1 : Opts := { maxData := 2, maxCrash := 1, maxElect := 2 }
def tr1 : List Act :=
  [.data 0, .repl 0 1, .elect 2, .repl 2 0, .data 2, .repl 2 1, .repl 2 1, .elect 0]

theorem f1_ack_last_index_loses_committed_entry :
    violates o1 (init 5 [0, 1, 2, 3, 4]) tr1 = true := by native_decide

/-- Reporting the verified index (prevLogIndex + #entries) instead closes it. -/
theorem f1_fixed :
    violates { o1 with ackLastIndex := false, followerCommitLast := false }
      (init 5 [0, 1, 2, 3, 4]) tr1 = false := by native_decide

/-! ## F2. Config-on-apply with pipelined ADD_VOTER (#3926, #4392)

Voters {0,1,2}, learners {3,4}. Leader 0 appends ADD_VOTER(3), ADD_VOTER(4)
back-to-back (allowed today: nothing serialises quorum changes). Node 1 acks
both; 0+1 is a majority of the *old* config so both commit and the leader
applies them (size 5). The leader then commits data X with {0,3,4}, a majority
of the *new* config. Node 1 never learned the commit index and still runs
under {0,1,2}; it is elected with votes {1,2} and X is lost. No crash needed.
Note: the design doc's "worst case: new node orphaned, no data loss" is wrong
— any entry committed after the membership change can be lost. -/
def o2 : Opts :=
  { ackLastIndex := false, followerCommitLast := false,
    maxData := 1, maxConfig := 2, maxCrash := 1, maxElect := 1, learners := [3, 4] }
def tr2 : List Act :=
  [.addV 0 3, .addV 0 4, .repl 0 1, .data 0, .repl 0 3, .repl 0 4, .repl 0 3, .repl 0 4, .elect 1]

theorem f2_pipelined_add_voter_loses_committed_entry :
    violates o2 (init 5 [0, 1, 2]) tr2 = true := by native_decide

/-- With "one quorum change in flight" (#4392) the second ADD_VOTER is not
even enabled until the first commits, so this trace is not executable. -/
theorem f2_one_in_flight_blocks_trace :
    replay { o2 with oneConfigInFlight := true } (init 5 [0, 1, 2]) tr2 = none := by native_decide

/-! ## F2b. Config-on-append *alone* does not fix F2 (#3926)

Switching to config-on-append without also serialising membership changes is
still unsafe: with both ADD_VOTERs appended the leader immediately uses the
5-voter config and commits X with {0,3,4}. -/
def tr2b : List Act :=
  [.data 0, .addV 0 3, .addV 0 4, .repl 0 3, .repl 0 4, .repl 0 3, .repl 0 4, .elect 1]

theorem f2b_config_on_append_without_serialisation_unsafe :
    violates { o2 with configOnAppend := true } (init 5 [0, 1, 2]) tr2b = true := by native_decide

/-! ## F3. Restart with an empty log tail (#3857 / #3858 / #3859)

nodes.conf keeps only log entries with index > lastApplied and does not store
the term of entry `lastApplied`. After a restart with everything applied,
`raftLogLastIndex()` and `raftLogLastTerm()` return 0, so the node grants its
vote to *any* candidate (`clusterRaftCanGrantVote`). Here node 1 holds the
committed entries, restarts, and votes node 2 (empty log) into leadership. -/
def o3 : Opts :=
  { ackLastIndex := false, followerCommitLast := false,
    maxData := 2, maxCrash := 1, maxElect := 2, maxRestart := 1 }
def tr3 : List Act :=
  [.data 0, .data 0, .repl 0 1, .repl 0 1, .elect 1, .repl 1 0, .crash 0, .restart 1, .elect 2]

theorem f3_restart_empty_tail_grants_stale_vote :
    violates o3 (init 3 [0, 1, 2]) tr3 = true := by native_decide

/-! ## F3b. Persisting lastIncluded{Index,Term} is necessary but not sufficient

Without InstallSnapshot (#3858) a restarted leader whose log starts after
`lastApplied` cannot bring up a lagging follower. Worse, `raftLogTermAt()` is
0 for indices *neither* node holds, so the AE consistency check "matches" at
an index the leader has compacted: the follower advances commit past entries
it never received (the C apply loop silently skips missing entries). -/
def tr3b : List Act :=
  [.data 0, .data 0, .repl 0 1, .repl 0 1, .elect 1, .repl 1 0, .restart 0, .elect 0, .repl 0 2]

theorem f3b_no_install_snapshot_skips_committed_entry :
    violates { o3 with persistSnapTerm := true } (init 3 [0, 1, 2]) tr3b = true := by native_decide

theorem f3b_fixed_with_install_snapshot :
    violates { o3 with persistSnapTerm := true, installSnapshot := true }
      (init 3 [0, 1, 2]) tr3b = false := by native_decide

/-! ## F3c. Full-cluster restart re-uses log indices

All three nodes restart after everything is applied. Every node now reports
an empty log, a leader is elected, and the next proposals are appended at
index 1, 2, ... again — while `lastApplied` is already ≥ 1 everywhere. The
leader's commit loop ignores indices ≤ its restored commit_index, so the
re-used index 1 is never applied (proposer times out); once index 2 commits,
index 1 is committed by Log Matching with a *different* entry than the one
every node already applied there. A node that later replays the log from
index 1 (new learner) would apply a different history. -/
def o3c : Opts := { o3 with maxRestart := 3, maxData := 3, maxElect := 2 }
def tr3c : List Act :=
  [.data 0, .repl 0 1, .repl 0 2, .repl 0 1, .repl 0 2,
   .restart 0, .restart 1, .restart 2, .elect 0, .data 0, .data 0, .repl 0 1]

theorem f3c_full_restart_reuses_indices :
    violates o3c (init 3 [0, 1, 2]) tr3c = true := by native_decide

end ValkeyRaft.Traces

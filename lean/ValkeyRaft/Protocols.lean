/-
  Small protocol models for the remaining sub-issues of valkey-io/valkey#3856.

  * #3860 pre-vote               (PreVote)
  * #3861 leader step-down       (StepDown)
  * #3862 / #4127 decentralised failure detection (ShardFD)
  * #4069 FORGET of the leader / non-member messages (NonMember)
  * #3868 merging clusters       (Merge)
  * #3869 sync-replication promotion (SyncRepl)
  * proposal expiry semantics    (Expiry)
-/
namespace ValkeyRaft.Protocols

/-! ## PreVote (#3860) -/
namespace PreVote

def quorum (voters : Nat) : Nat := voters / 2 + 1

/-- Pre-vote as designed: term increases only if a quorum of *distinct*
voters (incl. self) grants. An isolated node (`reach + 1 < quorum`) never
inflates its term, for any number of rounds. -/
def round (voters reach term : Nat) : Nat :=
  if reach + 1 ≥ quorum voters then term + 1 else term

theorem isolated_never_inflates (voters reach term k : Nat)
    (h : reach + 1 < quorum voters) :
    (Nat.repeat (round voters reach) k term) = term := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.repeat, ih, round]; omega

/-- Code: `pre_votes_received++` per PRE_VOTE message; responses are accepted
if `msg_term == current_term + 1`, which is the same value in every pre-vote
round of the same term (pre-vote does not bump the term). A delayed grant from
round 1 plus a fresh grant from round 2 by the *same* voter are both counted.
`grants` lists the voter id of every PRE_VOTE grant received in this round. -/
def codeTally (grants : List Nat) : Nat := 1 + grants.length
def distinctTally (grants : List Nat) : Nat := 1 + grants.eraseDups.length

theorem stale_prevote_double_counted :
    let grants := [7, 7]                 -- voter 7: late round-1 reply + round-2 reply
    codeTally grants ≥ quorum 5 ∧ distinctTally grants < quorum 5 := by decide

end PreVote

/-! ## StepDown (#3861) -/
namespace StepDown

/-- A follower last heard the old leader at `h`; its ACK reaches the leader at
`h + d`. The old leader keeps its role until `h + d + T` (fresh-quorum check,
`now - last_ack_time <= node_timeout`). A new leader can be elected once the
followers' election timeout `≥ T` elapsed, i.e. from `h + T`. For any positive
ACK delay there is an interval in which two nodes believe they are leader.
This is harmless for log safety (terms), but it means "I am leader" must not
be used as a read lease (e.g. for CLUSTER SLOTS freshness or for deciding
NODE_FAIL). -/
theorem two_leaders_window (h d T : Nat) (hd : 0 < d) :
    h + T < h + d + T := by omega

end StepDown

/-! ## ShardFD (#3862 / #4127) -/
namespace ShardFD

/-- Discrete-time model. `p2r t` / `r2p t`: whether the primary->replica and
replica->primary directions deliver at tick `t`. Primary times out the replica
after `tp` silent ticks, replica times out the primary after `tr` ticks. -/
def silentFor (link : Nat → Bool) (now : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => !link (now - (k + 1) + 1) && silentFor link now k

def primaryDetects (r2p : Nat → Bool) (tp now : Nat) : Bool := now ≥ tp && silentFor r2p now tp
def replicaDetects (p2r : Nat → Bool) (tr now : Nat) : Bool := now ≥ tr && silentFor p2r now tr

/-- "The primary uses a shorter timeout than the replica" (T vs 1.5T) only
orders the two proposals when both directions fail together. With a one-way
failure (primary->replica lost, replica->primary healthy: e.g. a full
replica-side receive buffer or asymmetric firewall), the replica proposes
NODE_FAIL(primary) and the primary never detects anything. Combined with
`Meta.failed_replica_can_be_promoted` / FAILOVER, the healthy primary is
deposed while still serving writes. -/
theorem one_way_partition_inverts_order :
    let tp := 2; let tr := 3; let now := 4
    let p2r : Nat → Bool := fun t => t < 1     -- lost from tick 1
    let r2p : Nat → Bool := fun _ => true      -- always fine
    replicaDetects p2r tr now = true ∧ primaryDetects r2p tp now = false := by decide

end ShardFD

/-! ## NonMember (#4069, NODE_FORGET) -/
namespace NonMember

/-- Inputs to the PRE_VOTE_REQ / VOTE_REQ handlers as written in
cluster_raft.c:1933-2021. `known` = candidate is in my node table,
`learner` = it is a learner in my view. -/
structure Req where
  known : Bool
  learner : Bool
  higherTerm : Bool
  logOk : Bool
  deriving DecidableEq, Repr

/-- `candidate && nodeIsLearner(candidate)` → deny; an *unknown* (e.g.
forgotten) candidate is not denied. -/
def codeGrantsPreVote (r : Req) : Bool :=
  !(r.known && r.learner) && r.higherTerm && r.logOk

/-- VOTE_REQ: `clusterRaftMaybeStepDown(msg_term)` runs before any
membership check, so any higher-term VOTE_REQ deposes the current leader. -/
def codeStepsDownOnVoteReq (r : Req) : Bool := r.higherTerm

/-- A node removed by NODE_FORGET (it rejects the entry on itself, see
`Meta.node_forget_apply_nondeterministic`) keeps running elections; members
grant it pre-votes and step down on its VOTE_REQ. Raft §4.2.3 requires
ignoring RequestVote from servers outside the current configuration. -/
theorem forgotten_node_can_disrupt :
    let r : Req := { known := false, learner := false, higherTerm := true, logOk := true }
    codeGrantsPreVote r = true ∧ codeStepsDownOnVoteReq r = true := by decide

end NonMember

/-! ## Merge (#3868) -/
namespace Merge

/-- Phases of the proposed "absorber/absorbee" merge (nemtsv's state machine,
MERGE_HANDOFF held in the absorber leader's memory, DISSOLVE committed in the
absorbee). We track where the absorbee's slot map lives. -/
structure S where
  handoffInAbsorberMem : Bool := false   -- MERGE_HANDOFF received & ACKed
  handoffInAbsorberLog : Bool := false   -- proposed + committed in absorber
  absorbeeDissolved : Bool := false      -- DISSOLVE applied: absorbee state reset
  deriving DecidableEq, Repr

inductive A | handoff | dissolve | absorberLeaderCrash | commitBatch
  deriving DecidableEq, Repr

def step (persistBeforeDissolve : Bool) (s : S) : A → S
  | .handoff => { s with handoffInAbsorberMem := true }
  | .dissolve =>
    if persistBeforeDissolve && !s.handoffInAbsorberLog then s   -- must wait
    else if s.handoffInAbsorberMem || s.handoffInAbsorberLog then { s with absorbeeDissolved := true } else s
  | .absorberLeaderCrash => { s with handoffInAbsorberMem := false }
  | .commitBatch => if s.handoffInAbsorberMem then { s with handoffInAbsorberLog := true } else s

def run (p : Bool) (s : S) (as : List A) : S := as.foldl (step p) s

/-- Slot ownership of the absorbee is lost when it has dissolved but its
metadata never reached the absorber's log. -/
def lost (s : S) : Bool := s.absorbeeDissolved && !s.handoffInAbsorberLog && !s.handoffInAbsorberMem

theorem volatile_handoff_loses_slot_map :
    lost (run false {} [.handoff, .dissolve, .absorberLeaderCrash, .commitBatch]) = true := by decide

/-- Requiring the absorber to *commit* the handoff (e.g. MERGE_PREPARE entry)
before the absorbee dissolves prevents the loss on this trace. The same
applies to the alternative "cache entries as local pending proposals"
design: pending proposals are not persisted, so they are equally volatile. -/
theorem persisted_handoff_safe :
    lost (run true {} [.handoff, .dissolve, .absorberLeaderCrash, .commitBatch]) = false := by decide

end Merge

/-! ## SyncRepl (#3869) -/
namespace SyncRepl

structure S where
  primaryOff : Nat := 10
  replicaOff : Nat := 10
  ackedOff : Nat := 10          -- highest offset acknowledged to a client
  syncSet : Bool := false       -- replica in the committed SYNC set
  waitsForReplica : Bool := false  -- primary blocks acks on this replica
  deriving DecidableEq, Repr

inductive A | write | replicate | proposeSync | applySync | failoverToReplica
  deriving DecidableEq, Repr

/-- `eagerWait`: primary starts waiting for the replica as soon as it
*proposes* the promotion (fix), instead of when SYNC is applied (as the
issue's step list reads). -/
def step (eagerWait : Bool) (s : S) : A → S
  | .write =>
    let p := s.primaryOff + 1
    if s.waitsForReplica && s.replicaOff < p then { s with primaryOff := p }      -- not acked yet
    else { s with primaryOff := p, ackedOff := p }
  | .replicate => { s with replicaOff := s.primaryOff,
                           ackedOff := if s.waitsForReplica then s.primaryOff else s.ackedOff }
  | .proposeSync => if eagerWait then { s with waitsForReplica := true } else s
  | .applySync => { s with syncSet := true, waitsForReplica := true }
  | .failoverToReplica => s

/-- PacificA invariant: every SYNC replica holds every acknowledged write. -/
def inv (s : S) : Bool := !s.syncSet || s.replicaOff ≥ s.ackedOff

/-- Primary sees replica caught up (offset 10), proposes SYNC; a write is
acknowledged before the entry is applied; SYNC applies with the replica one
write behind. A FAILOVER to this "sync" replica loses an acknowledged write.
(Also note FAILOVER apply today does not check SYNC membership at all.) -/
theorem late_wait_breaks_invariant :
    inv ((([A.proposeSync, .write, .applySync]).foldl (step false) {})) = false := by decide

theorem eager_wait_keeps_invariant :
    inv ((([A.proposeSync, .write, .applySync]).foldl (step true) {})) = true := by decide

end SyncRepl

/-! ## Expiry -/
namespace Expiry

/-- `clusterRaftCron` expires a pending proposal after 3×node_timeout and
replies `-TIMEOUT` (cluster_raft.c:2367-2380), but the entry may already be in
the leader's log and commit later. The error is therefore "outcome unknown",
not "not applied". -/
structure S where
  inLeaderLog : Bool := false
  clientGotTimeout : Bool := false
  applied : Bool := false
  deriving DecidableEq, Repr

inductive A | appendAtLeader | expire | commitApply
  deriving DecidableEq, Repr

def step (s : S) : A → S
  | .appendAtLeader => { s with inLeaderLog := true }
  | .expire => { s with clientGotTimeout := true }
  | .commitApply => if s.inLeaderLog then { s with applied := true } else s

theorem timeout_but_applied :
    let s := [A.appendAtLeader, .expire, .commitApply].foldl step {}
    s.clientGotTimeout = true ∧ s.applied = true := by decide

end Expiry

end ValkeyRaft.Protocols

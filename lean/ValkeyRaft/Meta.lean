/-
  Model of the *apply functions* of cluster-v2 metadata entries
  (src/cluster_raft.c @ f278b08b): SLOT_CHANGE, FAILOVER, NODE_FORGET,
  DEL_VOTER, NODE_FAIL / NODE_RECOVER, plus the stale-epoch auto-retry of
  `raftRefreshEpochInData` / `clusterRaftRetryProposals`.

  Covers #3863 (shard epochs), #3874 (leader pre-validation), #3865
  (slot-migration states), #4069 (FORGET of leader), #3862/#4127 (shard-level
  failure detection), and the design-doc claim "Duplicate proposals are
  harmless because all entry types are idempotent at apply time".

  Apply functions MUST be deterministic functions of (committed state, entry):
  every node applies the same log and must converge. We model the two pieces of
  node-local context the code consults at apply time (`myself` and
  `rs->leader`) explicitly so that non-determinism becomes visible.
-/
namespace ValkeyRaft.Meta

structure NodeM where
  id : Nat
  shard : Nat
  primary : Bool
  replicaOf : Option Nat
  failed : Bool := false
  voter : Bool := true
  deriving BEq, DecidableEq, Repr

structure Meta where
  nodes : List NodeM
  slots : List (Option Nat)        -- slot -> owning node
  epochs : List Nat                -- shard -> shard epoch (0 = unset)
  size : Nat                       -- server.cluster->size (voters)
  deriving BEq, DecidableEq, Repr

/-- Node-local context consulted by the C apply functions. -/
structure Ctx where
  myself : Nat
  localLeader : Nat                -- rs->leader on this node at apply time
  deriving Repr

inductive Res | ok | stale | rejected
  deriving BEq, DecidableEq, Repr

inductive Entry where
  | slotChange (src : Option Nat) (srcEpoch : Nat) (tgt : Option Nat) (tgtEpoch : Nat) (slots : List Nat)
  | failover (replica primary shard epoch : Nat)
  | nodeForget (n epoch : Nat)
  | delVoter (n : Nat)
  | nodeFail (n : Nat)
  | nodeRecover (n : Nat)
  deriving BEq, DecidableEq, Repr

def node? (m : Meta) (i : Nat) : Option NodeM := m.nodes.find? (·.id == i)
def epochOf (m : Meta) (sh : Nat) : Nat := m.epochs.getD sh 0
def setEpoch (m : Meta) (sh e : Nat) : Meta := { m with epochs := m.epochs.set sh e }
def updNode (m : Meta) (i : Nat) (f : NodeM → NodeM) : Meta :=
  { m with nodes := m.nodes.map (fun n => if n.id == i then f n else n) }

/-- clusterValidateShardEpoch: `current > 0 && epoch != current` is stale. -/
def validEpoch (m : Meta) (sh e : Nat) : Bool :=
  let cur := epochOf m sh
  cur == 0 || e == cur

/-- Side effect we track: keys deleted on `myself` by "dirty slot" cleanup
(`delKeysInSlot` in clusterRaftApplySlotChange). -/
structure Out where
  st : Meta
  res : Res
  deleted : List Nat := []         -- slots whose keys `myself` deleted
  deriving Repr

def apply (c : Ctx) (m : Meta) : Entry → Out
  | .slotChange src se tgt te sl =>
    let srcSh := src.bind (node? m) |>.map (·.shard)
    let tgtSh := tgt.bind (node? m) |>.map (·.shard)
    let ok1 := match srcSh with | some sh => validEpoch m sh se | none => true
    let ok2 := match tgtSh with | some sh => validEpoch m sh te | none => true
    if !(ok1 && ok2) then { st := m, res := .stale } else
    -- NOTE: no check that `src` still owns the slots (code only epoch-checks)
    let del := sl.filter (fun j => m.slots.getD j none == some c.myself && tgt != some c.myself)
    let slots := sl.foldl (fun acc j => acc.set j tgt) m.slots
    { st := { m with slots := slots }, res := .ok, deleted := del }
  | .failover r p sh e =>
    match node? m r, node? m p with
    | some rn, some pn =>
      if pn.shard != sh then { st := m, res := .rejected } else
      if !validEpoch m sh e then { st := m, res := .stale } else
      if rn.primary || !pn.primary || rn.replicaOf != some p then { st := m, res := .rejected } else
      -- NOTE: no check that the promoted replica is healthy (not FAIL)
      let slots := m.slots.map (fun o => if o == some p then some r else o)
      let m := { m with slots := slots }
      let m := updNode m r (fun n => { n with primary := true, replicaOf := none })
      let m := updNode m p (fun n => { n with primary := false, replicaOf := some r, shard := rn.shard })
      { st := setEpoch m sh (e + 1), res := .ok }
    | _, _ => { st := m, res := .rejected }
  | .nodeForget n e =>
    match node? m n with
    | none => { st := m, res := .ok }               -- already forgotten
    | some nn =>
      if n == c.myself then { st := m, res := .rejected }   -- `node == myself` -> reject
      else if !validEpoch m nn.shard e then { st := m, res := .stale }
      else if nn.primary && (m.slots.contains (some n) ||
                m.nodes.any (·.replicaOf == some n)) then { st := m, res := .rejected }
      else
        let m' := { m with nodes := m.nodes.filter (·.id != n),
                           size := if nn.voter && m.size > 0 then m.size - 1 else m.size }
        let cur := epochOf m nn.shard
        { st := setEpoch m' nn.shard (if cur == 0 then 1 else cur + 1), res := .ok }
  | .delVoter n =>
    match node? m n with
    | none => { st := m, res := .rejected }
    | some nn =>
      -- `memcmp(node->name, rs->leader) == 0` -> reject: reads node-local state
      if !nn.voter || m.size ≤ 1 || n == c.localLeader then { st := m, res := .rejected }
      else { st := { updNode m n (fun x => { x with voter := false }) with size := m.size - 1 }, res := .ok }
  | .nodeFail n =>
    if n == c.myself then { st := m, res := .ok }
    else { st := updNode m n (fun x => { x with failed := true }), res := .ok }
  | .nodeRecover n => { st := updNode m n (fun x => { x with failed := false }), res := .ok }

def run (c : Ctx) (m : Meta) : List Entry → Meta
  | [] => m
  | e :: es => run c (apply c m e).st es

/-- `raftRefreshEpochInData`: rebuild a stale proposal with the *current*
epochs of the shards it references (no other precondition is re-checked). -/
def refresh (m : Meta) : Entry → Entry
  | .slotChange src _ tgt _ sl =>
    let se := (src.bind (node? m)).map (fun n => epochOf m n.shard) |>.getD 0
    let te := (tgt.bind (node? m)).map (fun n => epochOf m n.shard) |>.getD 0
    .slotChange src se tgt te sl
  | .failover r p sh _ => .failover r p sh (epochOf m sh)
  | .nodeForget n e => match node? m n with
    | some nn => .nodeForget n (epochOf m nn.shard)
    | none => .nodeForget n e
  | e => e

/-- Apply with the code's automatic stale-epoch retry (up to `k` times). -/
def applyRetry (c : Ctx) (m : Meta) (e : Entry) : Nat → Meta
  | 0 => (apply c m e).st
  | k + 1 =>
    let o := apply c m e
    if o.res == Res.stale then applyRetry c m (refresh m e) k else o.st

/-! ## Fixture: shard 0 = {node 1 primary, node 2 replica}, shard 1 = {node 3},
shard 2 = {node 4}. Slot 0 owned by node 1. All shard epochs = 1. -/

def m0 : Meta :=
  { nodes := [ { id := 1, shard := 0, primary := true,  replicaOf := none },
               { id := 2, shard := 0, primary := false, replicaOf := some 1 },
               { id := 3, shard := 1, primary := true,  replicaOf := none },
               { id := 4, shard := 2, primary := true,  replicaOf := none } ],
    slots := [some 1, some 3, some 4, none],
    epochs := [1, 1, 1],
    size := 4 }

def ctx (me : Nat) : Ctx := { myself := me, localLeader := 0 }

/-! ### #3863: the design-doc example *does* hold without retry -/

/-- Slot migration 0 -> shard 1 races a FAILOVER of shard 0: the stale
SLOT_CHANGE is a no-op and slot 0 stays on shard 0 (now owned by node 2). -/
theorem epoch_fences_stale_slot_change :
    let fo := Entry.failover 2 1 0 1
    let sc := Entry.slotChange (some 1) 1 (some 3) 1 [0]
    (run (ctx 9) m0 [fo, sc]).slots.getD 0 none = some 2 := by decide

/-- ...but with the code's automatic stale-epoch retry (SLOT_CHANGE is in the
retry list, cluster_raft.c:892-897), the SLOT_CHANGE is rebuilt with the new
epoch and re-applied: slot 0 moves to shard 1 anyway. The fence is defeated;
the end state equals having no epochs at all. -/
theorem auto_retry_defeats_fence :
    let fo := Entry.failover 2 1 0 1
    let sc := Entry.slotChange (some 1) 1 (some 3) 1 [0]
    let afterFo := (apply (ctx 9) m0 fo).st
    (applyRetry (ctx 9) afterFo sc 5).slots.getD 0 none = some 3 := by decide

/-- Same for NODE_FORGET: the epoch is meant to "guard against removing a node
whose role changed", yet the retry rebuilds it with the current epoch. Here
node 2 is promoted by FAILOVER and becomes slot owner; NODE_FORGET(2) is
rejected only because of the separate "primary with slots" check, not by the
epoch. Remove that check (e.g. node 2 promoted but slots moved away) and the
retry forgets it. We show the epoch check alone is bypassed: -/
theorem retry_rebuilds_forget_epoch :
    let afterFo := (apply (ctx 9) m0 (.failover 2 1 0 1)).st
    refresh afterFo (.nodeForget 1 1) = .nodeForget 1 2 ∧
    (apply (ctx 9) afterFo (.nodeForget 1 2)).res = .ok := by decide

/-! ### SLOT_CHANGE does not CAS on the current owner -/

/-- Two concurrent migrations of the *same* slot from shard 0 (to shards 1 and
2) carry identical, valid epochs and SLOT_CHANGE does not bump. Both apply;
the second silently overrides the first and node 3 (first target, which
already received the keys) deletes them as a "dirty slot". -/
theorem concurrent_same_slot_migrations_both_apply :
    let a := Entry.slotChange (some 1) 1 (some 3) 1 [0]
    let b := Entry.slotChange (some 1) 1 (some 4) 1 [0]
    let mA := (apply (ctx 3) m0 a).st
    (apply (ctx 3) m0 a).res = .ok ∧
    (apply (ctx 3) mA b).res = .ok ∧
    (apply (ctx 3) mA b).st.slots.getD 0 none = some 4 ∧
    (apply (ctx 3) mA b).deleted = [0] := by decide

/-- Two concurrent ADDSLOTS for unowned slot 3 on different nodes: source is
"-" so only target epochs are checked; both apply and the first owner deletes
its keys when the second applies. -/
theorem concurrent_addslots_both_apply :
    let a := Entry.slotChange none 0 (some 3) 1 [3]
    let b := Entry.slotChange none 0 (some 4) 1 [3]
    let mA := (apply (ctx 3) m0 a).st
    (apply (ctx 3) mA b).res = .ok ∧ (apply (ctx 3) mA b).deleted = [3] := by decide

/-! ### Apply-time non-determinism (#4069, #3866) -/

/-- DEL_VOTER validation reads `rs->leader` at *apply* time
(cluster_raft.c:3643). Two nodes applying the same committed entry from the
same state diverge on `size` (and therefore on quorum) if they disagree on who
the leader is at the moment they apply it. -/
theorem del_voter_apply_nondeterministic :
    let e := Entry.delVoter 2
    (apply { myself := 1, localLeader := 2 } m0 e).st.size = 4 ∧
    (apply { myself := 3, localLeader := 1 } m0 e).st.size = 3 := by decide

/-- NODE_FORGET is rejected on the forgotten node itself (`node == myself`)
but applied everywhere else: the forgotten node keeps itself in the voter set
(size 4) while everyone else has size 3. If the forgotten node is the Raft
leader (#4069) it keeps acting as leader for a membership it is not part of. -/
theorem node_forget_apply_nondeterministic :
    let e := Entry.nodeForget 2 1
    (apply (ctx 2) m0 e).st.size = 4 ∧
    (apply (ctx 1) m0 e).st.size = 3 := by decide

/-! ### "Duplicate proposals are harmless" (design doc §Proposal retry) -/

/-- NODE_FAIL / NODE_RECOVER carry no epoch. A NODE_FAIL that is re-proposed
(pending-proposal retry runs every cron tick and on every leader change,
cluster_raft.c:2385) after the NODE_RECOVER was committed marks a healthy
node failed again; NODE_FAIL apply also schedules a failover on its replicas. -/
theorem duplicate_node_fail_not_harmless :
    let log := [Entry.nodeFail 1, .nodeRecover 1, .nodeFail 1]
    ((run (ctx 9) m0 log).nodes.find? (·.id == 1)).map (·.failed) = some true := by decide

/-- Epoch-carrying FAILOVER *is* idempotent under duplication. -/
theorem duplicate_failover_harmless :
    let e := Entry.failover 2 1 0 1
    let m1 := (apply (ctx 9) m0 e).st
    (apply (ctx 9) m1 e).res = .stale ∧ (apply (ctx 9) m1 e).st = m1 := by decide

/-! ### #3862 / #4127: shard-level failure detection -/

/-- Primary 1 and replica 2 lose connectivity to each other but not to the
Raft leader. Primary proposes NODE_FAIL(2) at T, replica proposes NODE_FAIL(1)
at 1.5T. Neither entry is validated against the proposer's own health, so both
apply and the shard has no healthy member while both processes are up. -/
theorem mutual_node_fail_both_apply :
    let m := run (ctx 9) m0 [.nodeFail 2, .nodeFail 1]
    (m.nodes.filter (fun n => n.shard == 0 && !n.failed)).length = 0 := by decide

/-- ...and the FAILED replica can still win FAILOVER (apply only checks
the replica relation and epoch, not health): the slot ends up owned by a node
marked FAIL. -/
theorem failed_replica_can_be_promoted :
    let m := run (ctx 9) m0 [.nodeFail 2, .nodeFail 1, .failover 2 1 0 1]
    m.slots.getD 0 none = some 2 ∧
      ((m.nodes.find? (·.id == 2)).map (·.failed)) = some true := by decide

end ValkeyRaft.Meta

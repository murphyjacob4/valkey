/-
  Formal state machine specification for Valkey cluster Raft with:
  * Two replicated states: applied state `S_a` and projected state `S_p(i)`
  * Pure, total, deterministic `apply` (no reads of node-local state)
  * Append-time validation only against `S_p` (generic over topology entries)
  * Config-on-append with at most one uncommitted voter change
  * New-leader-commits-own-term-entry-first rule (Ongaro 2015)
  * Vote/ack counting strictly from the effective voter set `(S_p).voters`
  * Truncation = recompute `S_p`; restart from snapshot + persisted tail
  * Only `ADD_VOTER` and `DEL_VOTER` change voters after bootstrap self-join
  * Asynchronous network (delay, reordering, duplication, drop) + crash/restart

  Zero `sorry`, core Lean 4 only (no Mathlib).
-/
import ValkeyRaft.Quorum

namespace ValkeyRaft.ConfigOnAppend

/-! ## 1. Quorum arithmetic for `Nodup` voter lists -/

abbrev IsMajority {α : Type} (v : List α) (p : α → Bool) : Prop :=
  ValkeyRaft.Quorum.IsMajority v p

/-- Two voter lists are *adjacent* if they represent the same voter set or
differ by adding/removing a single distinct voter (single-server change,
Ongaro §4.1). -/
inductive Adjacent {α : Type} [DecidableEq α] : List α → List α → Prop where
  | refl (c : List α) : Adjacent c c
  | addRight {c : List α} {n : α} (hnd : c.Nodup) (hnot : n ∉ c) :
      Adjacent c (c ++ [n])
  | addLeft {c : List α} {n : α} (hnd : c.Nodup) (hnot : n ∉ c) :
      Adjacent (c ++ [n]) c
  | eraseRight {c : List α} {n : α} (hnd : c.Nodup) (hmem : n ∈ c) :
      Adjacent c (c.filter (fun x => decide (x ≠ n)))
  | eraseLeft {c : List α} {n : α} (hnd : c.Nodup) (hmem : n ∈ c) :
      Adjacent (c.filter (fun x => decide (x ≠ n))) c

theorem Adjacent.symm {α : Type} [DecidableEq α] {a b : List α} (h : Adjacent a b) :
    Adjacent b a := by
  cases h with
  | refl => exact .refl _
  | addRight hnd hnot => exact .addLeft hnd hnot
  | addLeft hnd hnot => exact .addRight hnd hnot
  | eraseRight hnd hmem => exact .eraseLeft hnd hmem
  | eraseLeft hnd hmem => exact .eraseRight hnd hmem

theorem filter_len_erase {α : Type} [DecidableEq α] (c : List α) (n : α) (p : α → Bool)
    (hnd : c.Nodup) (hmem : n ∈ c) :
    ((c.filter (fun x => decide (x ≠ n))).filter p).length + (if p n then 1 else 0) =
      (c.filter p).length := by
  induction c with
  | nil => cases hmem
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_not, ht_nd⟩
    rcases List.mem_cons.mp hmem with rfl | ht_mem
    · have hfilt : t.filter (fun x => decide (x ≠ n)) = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        intro hxn; subst hxn; exact ha_not hx
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, hfilt]
      cases hpn : p n <;> simp <;> omega
    · have han : a ≠ n := fun h => ha_not (h ▸ ht_mem)
      have hih := ih ht_nd ht_mem
      have hstep : (a :: t).filter (fun x => decide (x ≠ n)) =
          a :: t.filter (fun x => decide (x ≠ n)) := by
        simp [han]
      rw [hstep]
      cases hpa : p a
      · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte]
        exact hih
      · simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons]
        omega

theorem filter_const_true {α : Type} (l : List α) :
    l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem len_erase_eq {α : Type} [DecidableEq α] (c : List α) (n : α)
    (hnd : c.Nodup) (hmem : n ∈ c) :
    (c.filter (fun x => decide (x ≠ n))).length + 1 = c.length := by
  have h := filter_len_erase c n (fun _ => true) hnd hmem
  rw [filter_const_true, filter_const_true] at h
  simpa using h

theorem majorities_intersect_erase {α : Type} [DecidableEq α] (c : List α) (n : α)
    (p q : α → Bool) (hnd : c.Nodup) (hmem : n ∈ c)
    (hp : IsMajority c p)
    (hq : IsMajority (c.filter (fun x => decide (x ≠ n))) q) :
    ∃ x ∈ c, x ≠ n ∧ p x = true ∧ q x = true := by
  have hlen : (c.filter (fun x => decide (x ≠ n))).length + 1 = c.length :=
    len_erase_eq c n hnd hmem
  have hp' : ((c.filter (fun x => decide (x ≠ n))).filter p).length + (if p n then 1 else 0) =
      (c.filter p).length :=
    filter_len_erase c n p hnd hmem
  have hadd := ValkeyRaft.Quorum.filter_len_add p q (c.filter (fun x => decide (x ≠ n)))
  unfold IsMajority ValkeyRaft.Quorum.IsMajority at hp hq
  have hpos : 0 < ((c.filter (fun x => decide (x ≠ n))).filter (fun x => p x && q x)).length := by
    cases hpn : p n
    · rw [hpn] at hp'; simp only [Bool.false_eq_true, ↓reduceIte] at hp'; omega
    · rw [hpn] at hp'; simp only [↓reduceIte] at hp'; omega
  match hl : (c.filter (fun x => decide (x ≠ n))).filter (fun x => p x && q x), hpos with
  | x :: _, _ =>
    have hx : x ∈ (c.filter (fun x => decide (x ≠ n))).filter (fun x => p x && q x) := by
      rw [hl]; simp
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact ⟨x, hx.1.1, hx.1.2, hx.2.1, hx.2.2⟩

/-- Any two majorities of adjacent configurations intersect in a common voter
belonging to both configurations. -/
theorem adjacent_quorums_intersect {α : Type} [DecidableEq α] {a b : List α}
    (hadj : Adjacent a b) (p q : α → Bool)
    (hp : IsMajority a p) (hq : IsMajority b q) :
    ∃ x, x ∈ a ∧ x ∈ b ∧ p x = true ∧ q x = true := by
  cases hadj with
  | refl =>
    rcases ValkeyRaft.Quorum.majorities_intersect _ p q hp hq with ⟨x, hx, hpx, hqx⟩
    exact ⟨x, hx, hx, hpx, hqx⟩
  | addRight _ _ =>
    rcases ValkeyRaft.Quorum.adjacent_majorities_intersect _ _ p q hp hq with ⟨x, hx, hpx, hqx⟩
    exact ⟨x, hx, List.mem_append_left _ hx, hpx, hqx⟩
  | addLeft _ _ =>
    rcases ValkeyRaft.Quorum.adjacent_majorities_intersect _ _ q p hq hp with ⟨x, hx, hqx, hpx⟩
    exact ⟨x, List.mem_append_left _ hx, hx, hpx, hqx⟩
  | eraseRight hnd hmem =>
    rcases majorities_intersect_erase _ _ p q hnd hmem hp hq with ⟨x, hx, hne, hpx, hqx⟩
    refine ⟨x, hx, ?_, hpx, hqx⟩
    simp [List.mem_filter, hx, hne]
  | eraseLeft hnd hmem =>
    rcases majorities_intersect_erase _ _ q p hnd hmem hq hp with ⟨x, hx, hne, hqx, hpx⟩
    refine ⟨x, ?_, hx, hpx, hqx⟩
    simp [List.mem_filter, hx, hne]

/-! ## 2. Abstract topology state machine & pure total `apply` -/

/-- Generic specification of topology operations (SLOT_CHANGE, FAILOVER,
NODE_FAIL, NODE_RECOVER, etc.). The Raft model is completely parametric over
this interface. -/
structure TopoSpec (NodeId : Type) where
  State : Type
  Op : Type
  initState : State
  /-- Append-time validation predicate against the projected state. -/
  valid : State → List NodeId → List NodeId → Op → Prop
  /-- Checked apply (modeling the debug-only assertion path). -/
  applyOpt : State → Op → Option State
  /-- Core contract lemma: any entry valid w.r.t. state `s` succeeds on apply. -/
  valid_apply : ∀ s members voters op, valid s members voters op →
    ∃ s', applyOpt s op = some s'
  /-- Optional topology precondition for forgetting a learner (e.g. not a
  primary holding slots or replicas). -/
  canForget : State → NodeId → Prop := fun _ _ => True
  /-- Pure topology update on forgetting a learner. -/
  onForget : State → NodeId → State := fun s _ => s

/-- Pure total apply for topology operations. -/
def TopoSpec.applyTotal {NodeId : Type} (T : TopoSpec NodeId)
    (s : T.State) (op : T.Op) : T.State :=
  (T.applyOpt s op).getD s

theorem TopoSpec.valid_applyOpt_eq_total {NodeId : Type} (T : TopoSpec NodeId)
    {s : T.State} {members voters : List NodeId} {op : T.Op}
    (hv : T.valid s members voters op) :
    T.applyOpt s op = some (T.applyTotal s op) := by
  rcases T.valid_apply s members voters op hv with ⟨s', hs'⟩
  simp [TopoSpec.applyTotal, hs']

/-- Replicated cluster state (both `S_a` and `S_p` have this type). -/
structure ClusterState {NodeId : Type} (T : TopoSpec NodeId) where
  members : List NodeId   -- all cluster members (voters ∪ learners)
  voters  : List NodeId   -- voting members (subset of `members`)
  topo    : T.State

def ClusterState.empty {NodeId : Type} (T : TopoSpec NodeId) : ClusterState T :=
  { members := [], voters := [], topo := T.initState }

/-- Well-formedness of a `ClusterState`. -/
def ClusterState.WF {NodeId : Type} {T : TopoSpec NodeId} (S : ClusterState T) : Prop :=
  S.members.Nodup ∧ S.voters.Nodup ∧ (∀ v, v ∈ S.voters → v ∈ S.members)

theorem ClusterState.empty_wf {NodeId : Type} (T : TopoSpec NodeId) :
    (ClusterState.empty T).WF := by
  refine ⟨List.nodup_nil, List.nodup_nil, ?_⟩
  intro v hv; cases hv

/-- Replicated log entry commands. Only `addVoter` and `delVoter` change the
voter set after the singleton bootstrap self-join (Contract §6). -/
inductive Cmd (NodeId : Type) (Op : Type) where
  | noop
  | bootstrapJoin (n : NodeId)    -- NODE_JOIN n voter: empty-log singleton bootstrap only
  | joinLearner   (n : NodeId)    -- NODE_JOIN n learner
  | forgetLearner (n : NodeId)    -- NODE_FORGET n (learners only)
  | addVoter      (n : NodeId)    -- ADD_VOTER n
  | delVoter      (n : NodeId)    -- DEL_VOTER n
  | topo          (op : Op)       -- generic topology entry

/-- Whether a command changes the voter set (readable from the entry alone). -/
def Cmd.isVoterChange {NodeId Op : Type} : Cmd NodeId Op → Bool
  | .bootstrapJoin _ => true
  | .addVoter _ => true
  | .delVoter _ => true
  | _ => false

/-- Append-time validation predicate against a projected `ClusterState`.
Parameterized by the unique cluster bootstrap node `boot`. -/
def validCmd {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) (S : ClusterState T) : Cmd NodeId T.Op → Prop
  | .noop => S.voters ≠ []
  | .bootstrapJoin n => n = boot ∧ S.members = [] ∧ S.voters = []
  | .joinLearner n => S.voters ≠ [] ∧ n ∉ S.members
  | .forgetLearner n => n ∈ S.members ∧ n ∉ S.voters ∧ T.canForget S.topo n
  | .addVoter n => n ∈ S.members ∧ n ∉ S.voters
  | .delVoter n => n ∈ S.voters ∧ S.voters.length > 1
  | .topo op => S.voters ≠ [] ∧ T.valid S.topo S.members S.voters op

/-- Pure, total, deterministic apply function `apply(S, cmd) -> S'`.
Reads ONLY `(S, cmd)` — never `myself`, `rs->leader`, role, links, match_index,
timers, failure flags, or wall clock (Contract §2). -/
def applyCmd {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (S : ClusterState T) : Cmd NodeId T.Op → ClusterState T
  | .noop => S
  | .bootstrapJoin n =>
    { S with members := if n ∈ S.members then S.members else S.members ++ [n],
             voters  := if n ∈ S.voters  then S.voters  else S.voters  ++ [n] }
  | .joinLearner n =>
    { S with members := if n ∈ S.members then S.members else S.members ++ [n] }
  | .forgetLearner n =>
    { S with members := S.members.filter (fun x => decide (x ≠ n)),
             topo    := T.onForget S.topo n }
  | .addVoter n =>
    { S with voters  := if n ∈ S.voters  then S.voters  else S.voters  ++ [n] }
  | .delVoter n =>
    { S with voters  := S.voters.filter (fun x => decide (x ≠ n)) }
  | .topo op =>
    { S with topo    := T.applyTotal S.topo op }

/-- Checked apply (models the debug-only assertion path in Contract §4):
returns `some S'` iff the entry is valid (and topology apply succeeds),
`none` if an assertion would fire. -/
noncomputable def applyChecked {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) (S : ClusterState T) (c : Cmd NodeId T.Op) : Option (ClusterState T) := by
  classical
  exact
    if validCmd boot S c then
      match c with
      | .topo op => (T.applyOpt S.topo op).map (fun t' => { S with topo := t' })
      | _ => some (applyCmd S c)
    else none

/-- Core validity-to-apply theorem: if `validCmd boot S c` holds, then
`applyChecked` NEVER rejects and produces `some (applyCmd S c)`. -/
theorem validCmd_applyChecked {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) (S : ClusterState T) (c : Cmd NodeId T.Op)
    (hv : validCmd boot S c) :
    applyChecked boot S c = some (applyCmd S c) := by
  unfold applyChecked
  simp only [hv, ↓reduceIte]
  cases c with
  | topo op =>
    have hopt := T.valid_applyOpt_eq_total hv.2
    simp [applyCmd, hopt]
  | _ => rfl

/-- Non-voter-changing commands leave `voters` completely unchanged. -/
theorem non_voter_change_preserves_voters {NodeId : Type} [DecidableEq NodeId]
    {T : TopoSpec NodeId} (S : ClusterState T) (c : Cmd NodeId T.Op)
    (h : c.isVoterChange = false) :
    (applyCmd S c).voters = S.voters := by
  cases c <;> simp [Cmd.isVoterChange, applyCmd] at h ⊢

/-- Helper: appending a fresh element preserves `Nodup`. -/
theorem nodup_append_singleton {α : Type} {l : List α} {x : α}
    (hnd : l.Nodup) (hnot : x ∉ l) : (l ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, ?_, ?_⟩
  · simp [List.nodup_cons]
  · intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb; subst hab
    exact hnot ha

/-- Helper: filtering preserves `Nodup`. -/
theorem nodup_filter {α : Type} {l : List α} (p : α → Bool) (hnd : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha, ht⟩
    cases hpa : p a
    · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte]
      exact ih ht
    · simp only [List.filter_cons, hpa, ↓reduceIte, List.nodup_cons, List.mem_filter]
      exact ⟨fun ⟨hmem, _⟩ => ha hmem, ih ht⟩

/-- Every valid command preserves `ClusterState.WF`. -/
theorem validCmd_preserves_wf {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    {boot : NodeId} {S : ClusterState T} {c : Cmd NodeId T.Op}
    (hwf : S.WF) (hv : validCmd boot S c) :
    (applyCmd S c).WF := by
  rcases hwf with ⟨hm, hvnd, hsub⟩
  cases c with
  | noop => exact ⟨hm, hvnd, hsub⟩
  | bootstrapJoin n =>
    rcases hv with ⟨_, hme, hve⟩
    simp [ClusterState.WF, applyCmd, hme, hve]
  | joinLearner n =>
    rcases hv with ⟨_, hnot⟩
    refine ⟨?_, hvnd, ?_⟩
    · simp only [applyCmd, hnot, ↓reduceIte]
      exact nodup_append_singleton hm hnot
    · intro v hvmem
      simp only [applyCmd, hnot, ↓reduceIte]
      exact List.mem_append_left _ (hsub v hvmem)
  | forgetLearner n =>
    rcases hv with ⟨_, hnotv, _⟩
    refine ⟨nodup_filter _ hm, hvnd, ?_⟩
    intro v hvmem
    simp only [applyCmd, List.mem_filter, decide_eq_true_eq]
    refine ⟨hsub v hvmem, ?_⟩
    intro hvn; subst hvn; exact hnotv hvmem
  | addVoter n =>
    rcases hv with ⟨hmem, hnotv⟩
    refine ⟨hm, ?_, ?_⟩
    · simp only [applyCmd, hnotv, ↓reduceIte]
      exact nodup_append_singleton hvnd hnotv
    · intro v hvmem
      simp only [applyCmd, hnotv, ↓reduceIte, List.mem_append, List.mem_singleton] at hvmem
      rcases hvmem with hvmem | rfl
      · exact hsub v hvmem
      · exact hmem
  | delVoter n =>
    refine ⟨hm, nodup_filter _ hvnd, ?_⟩
    intro v hvmem
    simp only [applyCmd, List.mem_filter, decide_eq_true_eq] at hvmem
    exact hsub v hvmem.1
  | topo op =>
    exact ⟨hm, hvnd, hsub⟩

/-- Once `S.voters` is non-empty, every valid command keeps `S.voters` non-empty. -/
theorem validCmd_preserves_voters_nonempty {NodeId : Type} [DecidableEq NodeId]
    {T : TopoSpec NodeId} {boot : NodeId} {S : ClusterState T} {c : Cmd NodeId T.Op}
    (hwf : S.WF) (hne : S.voters ≠ []) (hv : validCmd boot S c) :
    (applyCmd S c).voters ≠ [] := by
  cases c with
  | noop => exact hne
  | bootstrapJoin n => exact absurd hv.2.2 hne
  | joinLearner n => exact hne
  | forgetLearner n => exact hne
  | addVoter n =>
    rcases hv with ⟨_, hnotv⟩
    simp [applyCmd, hnotv]
  | delVoter n =>
    rcases hv with ⟨hmem, hgt⟩
    intro hemp
    have hlen := len_erase_eq S.voters n hwf.2.1 hmem
    simp only [applyCmd] at hemp
    rw [hemp] at hlen
    simp at hlen
    omega
  | topo op => exact hne

/-- Any valid command on a non-empty well-formed state produces an *adjacent*
voter set! (And in particular `bootstrapJoin` is impossible once `S.voters ≠ []`.) -/
theorem validCmd_adjacent_voters {NodeId : Type} [DecidableEq NodeId]
    {T : TopoSpec NodeId} {boot : NodeId} {S : ClusterState T} {c : Cmd NodeId T.Op}
    (hwf : S.WF) (hne : S.voters ≠ []) (hv : validCmd boot S c) :
    Adjacent S.voters (applyCmd S c).voters := by
  cases c with
  | noop => exact .refl _
  | bootstrapJoin n => exact absurd hv.2.2 hne
  | joinLearner n => exact .refl _
  | forgetLearner n => exact .refl _
  | addVoter n =>
    rcases hv with ⟨_, hnotv⟩
    simp only [applyCmd, hnotv, ↓reduceIte]
    exact .addRight hwf.2.1 hnotv
  | delVoter n =>
    rcases hv with ⟨hmem, _⟩
    simp only [applyCmd]
    exact .eraseRight hwf.2.1 hmem
  | topo op => exact .refl _

/-! ## 3. Log entries, folding, and the two replicated states -/

structure Entry (NodeId : Type) (Op : Type) where
  term : Nat
  cmd  : Cmd NodeId Op

/-- Fold a log prefix `L` (1-indexed entries in chronological order) from the
empty initial state. -/
def stateOfLog {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (L : List (Entry NodeId T.Op)) : ClusterState T :=
  L.foldl (fun s e => applyCmd s e.cmd) (ClusterState.empty T)

/-- State at 1-based log index `i` (0 = empty initial state). -/
def stateAt {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (L : List (Entry NodeId T.Op)) (i : Nat) : ClusterState T :=
  stateOfLog (L.take i)

/-- Effective voter set of a full log `L`. -/
def votersOfLog {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (L : List (Entry NodeId T.Op)) : List NodeId :=
  (stateOfLog L).voters

/-- Voter set at 1-based log index `i`. -/
def cfgAt {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (L : List (Entry NodeId T.Op)) (i : Nat) : List NodeId :=
  (stateAt L i).voters

/-- 1-based entry lookup on a full log. -/
def logGet {NodeId Op : Type} (L : List (Entry NodeId Op)) (i : Nat) :
    Option (Entry NodeId Op) :=
  if i == 0 then none else L[i - 1]?

/-- 1-based term lookup on a full log (0 for index 0 or out of bounds). -/
def logTermAt {NodeId Op : Type} (L : List (Entry NodeId Op)) (i : Nat) : Nat :=
  match logGet L i with
  | some e => e.term
  | none => 0

def logLastTerm {NodeId Op : Type} (L : List (Entry NodeId Op)) : Nat :=
  logTermAt L L.length

/-- Up-to-date log comparison (Raft §5.4.1): candidate `(cTerm, cIdx)` is at
least as up-to-date as voter `(vTerm, vIdx)`. -/
def upToDate (cTerm cIdx vTerm vIdx : Nat) : Bool :=
  cTerm > vTerm || (cTerm == vTerm && cIdx ≥ vIdx)

/-- Every entry in `L` is valid w.r.t. the state of its strict prefix. -/
def LogValid {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) (L : List (Entry NodeId T.Op)) : Prop :=
  ∀ (k : Nat) (e : Entry NodeId T.Op),
    1 ≤ k → k ≤ L.length → logGet L k = some e →
    validCmd boot (stateAt L (k - 1)) e.cmd

/-- List prefix relation (`L1` is a prefix of `L2`). -/
def IsPrefix {α : Type} (L1 L2 : List α) : Prop :=
  L1.length ≤ L2.length ∧ L2.take L1.length = L1

/-! ## 4. Per-node runtime state (snapshot + tail, `S_a` vs `S_p`) -/

inductive Role where
  | follower
  | candidate
  | leader
  deriving DecidableEq, Repr

/-- Per-node state. Contains ONLY real runtime fields (no ghost state).
`tail` holds entries for 1-based indices `snapIdx + 1 .. snapIdx + tail.length`. -/
structure Node (NodeId : Type) (T : TopoSpec NodeId) where
  -- Persisted state (survives crash/restart)
  term         : Nat
  votedFor     : Option NodeId
  snapIdx      : Nat
  snapTerm     : Nat
  snapState    : ClusterState T
  tail         : List (Entry NodeId T.Op)
  -- Volatile state (reset on crash/restart; `commit` is NOT assumed persisted)
  role         : Role
  commit       : Nat
  applied      : Nat
  appliedState : ClusterState T     -- S_a: topology after applying log[1..applied]
  votes        : List NodeId        -- candidate only: votes granted in `term`
  matchIdx     : NodeId → Nat       -- leader only: verified match index per peer

def Node.init {NodeId : Type} (T : TopoSpec NodeId) : Node NodeId T :=
  { term         := 0
    votedFor     := none
    snapIdx      := 0
    snapTerm     := 0
    snapState    := ClusterState.empty T
    tail         := []
    role         := .follower
    commit       := 0
    applied      := 0
    appliedState := ClusterState.empty T
    votes        := []
    matchIdx     := fun _ => 0 }

def Node.lastIdx {NodeId : Type} {T : TopoSpec NodeId} (n : Node NodeId T) : Nat :=
  n.snapIdx + n.tail.length

def Node.entryAt {NodeId : Type} {T : TopoSpec NodeId} (n : Node NodeId T) (i : Nat) :
    Option (Entry NodeId T.Op) :=
  if i > n.snapIdx then n.tail[i - n.snapIdx - 1]? else none

def Node.termAt {NodeId : Type} {T : TopoSpec NodeId} (n : Node NodeId T) (i : Nat) : Nat :=
  if i == 0 then 0
  else if i == n.snapIdx then n.snapTerm
  else match n.entryAt i with
       | some e => e.term
       | none => 0

def Node.lastTerm {NodeId : Type} {T : TopoSpec NodeId} (n : Node NodeId T) : Nat :=
  n.termAt n.lastIdx

/-- Projected state `S_p(i)` for any index `i ≥ n.applied`:
`fold(apply, S_a, log[lastApplied+1..i])` (Contract §1). -/
def Node.projectedAt {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (n : Node NodeId T) (i : Nat) : ClusterState T :=
  ((n.tail.drop (n.applied - n.snapIdx)).take (i - n.applied)).foldl
    (fun s e => applyCmd s e.cmd) n.appliedState

/-- Projected state `S_p := S_p(lastIndex)` (Contract §1). -/
def Node.projectedState {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (n : Node NodeId T) : ClusterState T :=
  (n.tail.drop (n.applied - n.snapIdx)).foldl (fun s e => applyCmd s e.cmd) n.appliedState

/-- Equivalent recomputation from `snapState + tail` (used on startup/truncation). -/
def Node.projectedFromSnap {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (n : Node NodeId T) : ClusterState T :=
  n.tail.foldl (fun s e => applyCmd s e.cmd) n.snapState

/-- Effective voter set used for elections, commit counting, and VOTE_REQ targets
(Contract §5): always `(S_p).voters`. -/
def Node.effVoters {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (n : Node NodeId T) : List NodeId :=
  n.projectedState.voters

/-- Whether the node has any uncommitted voter-changing entry in its log tail. -/
def Node.hasUncommittedVoterChange {NodeId : Type} {T : TopoSpec NodeId}
    (n : Node NodeId T) : Bool :=
  (n.tail.drop (n.commit - n.snapIdx)).any (fun e => e.cmd.isVoterChange)

/-- Raft §5.3 Rule 3 log merge: keep matching entries, truncate ONLY on term
conflict, append new suffix. Never truncates when `newEs` is a matching prefix
(safe against delayed/reordered shorter AppendEntries). -/
def mergeFrom {NodeId Op : Type} :
    List (Entry NodeId Op) → List (Entry NodeId Op) → List (Entry NodeId Op)
  | existing, [] => existing
  | [], newEs => newEs
  | ex :: exs, ne :: nes =>
    if ex.term == ne.term then ex :: mergeFrom exs nes
    else ne :: nes

/-! ## 5. Network messages & write-only proof history -/

inductive Msg (NodeId : Type) (T : TopoSpec NodeId) where
  | requestVote (term : Nat) (cand : NodeId) (to : NodeId)
      (lastIdx : Nat) (lastTerm : Nat)
  | voteReply (term : Nat) (fromId : NodeId) (toId : NodeId) (granted : Bool)
  | appendEntries (term : Nat) (leader : NodeId) (prevIdx : Nat) (prevTerm : Nat)
      (entries : List (Entry NodeId T.Op)) (leaderCommit : Nat)
  | appendReply (term : Nat) (fromId : NodeId) (toId : NodeId)
      (success : Bool) (matchIdx : Nat)
  | installSnapshot (term : Nat) (leader : NodeId)
      (snapIdx : Nat) (snapTerm : Nat) (snapState : ClusterState T)

/-- Record of a vote granted by `voter` to `cand` in `term`. -/
structure VoteRec (NodeId : Type) (T : TopoSpec NodeId) where
  term            : Nat
  voter           : NodeId
  cand            : NodeId
  voterLog        : List (Entry NodeId T.Op)
  hadLeaderInTerm : Bool

/-- Record of a leader election victory (or bootstrap at term 1). -/
structure ElectionRec (NodeId : Type) (T : TopoSpec NodeId) where
  term       : Nat
  leader     : NodeId
  elecLog    : List (Entry NodeId T.Op)
  elecCfg    : List NodeId
  elecQuorum : List NodeId

/-- Record of a commit event by `leader` in `term` at index `idx`. -/
structure CommitRec (NodeId : Type) (T : TopoSpec NodeId) where
  term    : Nat
  leader  : NodeId
  idx     : Nat
  log     : List (Entry NodeId T.Op)
  cfg     : List NodeId
  quorum  : List NodeId

/-- Write-only ghost history for invariants and proofs. NEVER read by any
transition guard or runtime state update. -/
structure Hist (NodeId : Type) (T : TopoSpec NodeId) where
  fullLog  : NodeId → List (Entry NodeId T.Op)
  votes    : List (VoteRec NodeId T)
  elected  : List (ElectionRec NodeId T)
  commits  : List (CommitRec NodeId T)
  /-- Every `(term, prefix)` accepted by a node (as leader or via AE/snapshot). -/
  accepted : NodeId → List (Nat × List (Entry NodeId T.Op))
  /-- Origin log of every `installSnapshot` message (proves snapshot = valid committed prefix). -/
  snapLogs : List (Nat × Nat × ClusterState T × List (Entry NodeId T.Op))

def Hist.init {NodeId : Type} (T : TopoSpec NodeId) : Hist NodeId T :=
  { fullLog  := fun _ => []
    votes    := []
    elected  := []
    commits  := []
    accepted := fun _ => []
    snapLogs := [] }

/-- Full system state. `net` is a monotone list of all messages ever sent:
any message in `net` may be delivered 0, 1, or many times in any order
(models delay, reordering, duplication, and message drop). -/
structure System (NodeId : Type) (T : TopoSpec NodeId) where
  nodes : NodeId → Node NodeId T
  net   : List (Msg NodeId T)
  hist  : Hist NodeId T

def System.init {NodeId : Type} (T : TopoSpec NodeId) : System NodeId T :=
  { nodes := fun _ => Node.init T
    net   := []
    hist  := Hist.init T }

def fnUpd {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x

/-! ## 6. Transition functions & `Step` relation -/

section Transitions
variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

def nextBootstrap (boot : NodeId) (s : System NodeId T) : System NodeId T :=
  let e : Entry NodeId T.Op := { term := 1, cmd := .bootstrapJoin boot }
  let n' : Node NodeId T :=
    { s.nodes boot with
      term := 1
      votedFor := some boot
      role := .leader
      tail := [e]
      votes := [boot]
      matchIdx := fun _ => 0 }
  let er : ElectionRec NodeId T :=
    { term := 1, leader := boot, elecLog := [e], elecCfg := [boot], elecQuorum := [boot] }
  let vr : VoteRec NodeId T :=
    { term := 1, voter := boot, cand := boot, voterLog := [], hadLeaderInTerm := false }
  { nodes := fnUpd s.nodes boot n'
    net   := s.net
    hist  :=
      { s.hist with
        fullLog  := fnUpd s.hist.fullLog boot [e]
        votes    := vr :: s.hist.votes
        elected  := er :: s.hist.elected
        accepted := fnUpd s.hist.accepted boot ((1, [e]) :: s.hist.accepted boot) } }

def nextPropose (s : System NodeId T) (l : NodeId) (cmd : Cmd NodeId T.Op) :
    System NodeId T :=
  let n := s.nodes l
  let e : Entry NodeId T.Op := { term := n.term, cmd := cmd }
  let n' := { n with tail := n.tail ++ [e] }
  let full' := s.hist.fullLog l ++ [e]
  { nodes := fnUpd s.nodes l n'
    net   := s.net
    hist  :=
      { s.hist with
        fullLog  := fnUpd s.hist.fullLog l full'
        accepted := fnUpd s.hist.accepted l ((n.term, full') :: s.hist.accepted l) } }

def nextStartElection (s : System NodeId T) (c : NodeId) : System NodeId T :=
  let n := s.nodes c
  let t := n.term + 1
  let n' := { n with term := t, role := .candidate, votedFor := some c,
                     votes := [c], matchIdx := fun _ => 0 }
  let reqs := n.effVoters.map (fun dst =>
    Msg.requestVote t c dst n.lastIdx n.lastTerm)
  let vr : VoteRec NodeId T :=
    { term := t, voter := c, cand := c, voterLog := s.hist.fullLog c,
      hadLeaderInTerm := s.hist.elected.any (fun e => e.term == t) }
  { nodes := fnUpd s.nodes c n'
    net   := reqs ++ s.net
    hist  := { s.hist with votes := vr :: s.hist.votes } }

def nextHandleRequestVote (s : System NodeId T) (v c : NodeId)
    (t cLastIdx cLastTerm : Nat) : System NodeId T :=
  let n := s.nodes v
  let stepped :=
    if t > n.term then { n with term := t, role := .follower, votedFor := none,
                                votes := [], matchIdx := fun _ => 0 }
    else n
  let canGrant :=
    (stepped.votedFor == none || stepped.votedFor == some c) &&
    upToDate cLastTerm cLastIdx stepped.lastTerm stepped.lastIdx
  let n' := if canGrant then { stepped with votedFor := some c } else stepped
  let reply := Msg.voteReply t v c canGrant
  let vr : VoteRec NodeId T :=
    { term := t, voter := v, cand := c, voterLog := s.hist.fullLog v,
      hadLeaderInTerm := s.hist.elected.any (fun e => e.term == t) }
  { nodes := fnUpd s.nodes v n'
    net   := reply :: s.net
    hist  := { s.hist with votes := if canGrant then vr :: s.hist.votes else s.hist.votes } }

def nextHandleVoteReply (s : System NodeId T) (c fromId : NodeId) : System NodeId T :=
  let n := s.nodes c
  let n' := { n with votes := if fromId ∈ n.votes then n.votes else fromId :: n.votes }
  { nodes := fnUpd s.nodes c n'
    net   := s.net
    hist  := s.hist }

def nextBecomeLeader (s : System NodeId T) (c : NodeId) : System NodeId T :=
  let n := s.nodes c
  let n' := { n with role := .leader, matchIdx := fun _ => 0 }
  let er : ElectionRec NodeId T :=
    { term       := n.term
      leader     := c
      elecLog    := s.hist.fullLog c
      elecCfg    := n.effVoters
      elecQuorum := n.effVoters.filter (fun v => decide (v ∈ n.votes)) }
  { nodes := fnUpd s.nodes c n'
    net   := s.net
    hist  := { s.hist with
                 elected  := er :: s.hist.elected
                 accepted := fnUpd s.hist.accepted c
                               ((n.term, s.hist.fullLog c) :: s.hist.accepted c) } }

def nextSendAppendEntries (s : System NodeId T) (l : NodeId) (prevIdx endIdx : Nat) :
    System NodeId T :=
  let n := s.nodes l
  let entries := (n.tail.drop (prevIdx - n.snapIdx)).take (endIdx - prevIdx)
  let msg := Msg.appendEntries n.term l prevIdx (n.termAt prevIdx) entries n.commit
  { nodes := s.nodes
    net   := msg :: s.net
    hist  := s.hist }

def nextHandleAppendEntries (s : System NodeId T) (f l : NodeId)
    (t prevIdx prevTerm leaderCommit : Nat) (entries : List (Entry NodeId T.Op)) :
    System NodeId T :=
  let n := s.nodes f
  let stepped :=
    if t > n.term then { n with term := t, role := .follower, votedFor := none,
                                votes := [], matchIdx := fun _ => 0 }
    else { n with role := .follower, votes := [], matchIdx := fun _ => 0 }
  let ok := decide (stepped.snapIdx ≤ prevIdx ∧ prevIdx ≤ stepped.lastIdx ∧
                    stepped.termAt prevIdx = prevTerm)
  let offset := prevIdx - stepped.snapIdx
  let newTail := stepped.tail.take offset ++ mergeFrom (stepped.tail.drop offset) entries
  let verified := prevIdx + entries.length
  let newCommit := max stepped.commit (min leaderCommit verified)
  let n' := if ok then { stepped with tail := newTail, commit := newCommit } else stepped
  let full' := if ok then
      (s.hist.fullLog f).take prevIdx ++ mergeFrom ((s.hist.fullLog f).drop prevIdx) entries
    else s.hist.fullLog f
  let reply := Msg.appendReply t f l ok (if ok then verified else 0)
  { nodes := fnUpd s.nodes f n'
    net   := reply :: s.net
    hist  :=
      { s.hist with
        fullLog  := fnUpd s.hist.fullLog f full'
        accepted := if ok then
            fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f)
          else s.hist.accepted } }

def nextHandleAppendReply (s : System NodeId T) (l fromId : NodeId) (mIdx : Nat) :
    System NodeId T :=
  let n := s.nodes l
  let n' := { n with matchIdx := fnUpd n.matchIdx fromId (max (n.matchIdx fromId) mIdx) }
  { nodes := fnUpd s.nodes l n'
    net   := s.net
    hist  := s.hist }

def nextAdvanceCommit (s : System NodeId T) (l : NodeId) (k : Nat) : System NodeId T :=
  let n := s.nodes l
  let n' := { n with commit := k }
  let cm : CommitRec NodeId T :=
    { term   := n.term
      leader := l
      idx    := k
      log    := (s.hist.fullLog l).take k
      cfg    := n.effVoters
      quorum := n.effVoters.filter (fun v => decide (v = l ∨ n.matchIdx v ≥ k)) }
  { nodes := fnUpd s.nodes l n'
    net   := s.net
    hist  := { s.hist with commits := cm :: s.hist.commits } }

def nextLeaderStepDown (s : System NodeId T) (l : NodeId) : System NodeId T :=
  let n := s.nodes l
  let n' := { n with role := .follower, matchIdx := fun _ => 0 }
  { nodes := fnUpd s.nodes l n'
    net   := s.net
    hist  := s.hist }

def nextApplyOne (s : System NodeId T) (i : NodeId) (e : Entry NodeId T.Op) :
    System NodeId T :=
  let n := s.nodes i
  let n' := { n with applied := n.applied + 1,
                     appliedState := applyCmd n.appliedState e.cmd }
  { nodes := fnUpd s.nodes i n'
    net   := s.net
    hist  := s.hist }

def nextCompactSnapshot (s : System NodeId T) (i : NodeId) : System NodeId T :=
  let n := s.nodes i
  let n' := { n with
                snapIdx   := n.applied
                snapTerm  := n.termAt n.applied
                snapState := n.appliedState
                tail      := n.tail.drop (n.applied - n.snapIdx) }
  { nodes := fnUpd s.nodes i n'
    net   := s.net
    hist  := s.hist }

def nextSendInstallSnapshot (s : System NodeId T) (l : NodeId) : System NodeId T :=
  let n := s.nodes l
  let msg := Msg.installSnapshot n.term l n.snapIdx n.snapTerm n.snapState
  { nodes := s.nodes
    net   := msg :: s.net
    hist  := { s.hist with
                 snapLogs := (n.snapIdx, n.snapTerm, n.snapState,
                              (s.hist.fullLog l).take n.snapIdx) :: s.hist.snapLogs } }

def nextHandleInstallSnapshot (s : System NodeId T) (f l : NodeId)
    (t sIdx sTerm : Nat) (sState : ClusterState T) (sLog : List (Entry NodeId T.Op)) :
    System NodeId T :=
  let n := s.nodes f
  let stepped :=
    if t > n.term then { n with term := t, role := .follower, votedFor := none,
                                votes := [], matchIdx := fun _ => 0 }
    else { n with role := .follower, votes := [], matchIdx := fun _ => 0 }
  let advance := decide (sIdx > stepped.snapIdx)
  let retain := decide (sIdx ≤ stepped.lastIdx ∧ stepped.termAt sIdx = sTerm)
  let newTail := if retain then stepped.tail.drop (sIdx - stepped.snapIdx) else []
  let newApplied := max stepped.applied sIdx
  let newAppliedState := if stepped.applied < sIdx then sState else stepped.appliedState
  let newCommit := max stepped.commit sIdx
  let n' := if advance then
      { stepped with
          snapIdx := sIdx, snapTerm := sTerm, snapState := sState,
          tail := newTail, applied := newApplied,
          appliedState := newAppliedState, commit := newCommit }
    else stepped
  let full' := if advance then
      if retain then s.hist.fullLog f else sLog
    else s.hist.fullLog f
  let reply := Msg.appendReply t f l true sIdx
  { nodes := fnUpd s.nodes f n'
    net   := reply :: s.net
    hist  :=
      { s.hist with
        fullLog  := fnUpd s.hist.fullLog f full'
        accepted := fnUpd s.hist.accepted f ((t, sLog) :: s.hist.accepted f) } }

def nextCrashRestart (s : System NodeId T) (i : NodeId) : System NodeId T :=
  let n := s.nodes i
  let n' := { n with
                role         := .follower
                commit       := n.snapIdx
                applied      := n.snapIdx
                appliedState := n.snapState
                votes        := []
                matchIdx     := fun _ => 0 }
  { nodes := fnUpd s.nodes i n'
    net   := s.net
    hist  := s.hist }

end Transitions

inductive Step {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) : System NodeId T → System NodeId T → Prop where

  /-- (1) Bootstrap self-join (Contract §6): the unique cluster seed `boot` with
  an empty log (`term = 0, snapIdx = 0, tail = []`) appends
  `NODE_JOIN boot voter` at index 1 in term 1 and becomes singleton leader. -/
  | bootstrapSelfJoin (s : System NodeId T)
      (hEmpty : (s.nodes boot).term = 0 ∧ (s.nodes boot).snapIdx = 0 ∧ (s.nodes boot).tail = []) :
      Step boot s (nextBootstrap boot s)

  /-- (2) Leader proposes and appends a new entry after validating against `S_p`
  (Contract §3, §5). Voter changes additionally require:
  (a) no uncommitted voter change in the log tail (serialization), and
  (b) the leader has already committed an entry from its own term (Ongaro 2015). -/
  | propose (s : System NodeId T) (l : NodeId) (cmd : Cmd NodeId T.Op)
      (hLeader : (s.nodes l).role = .leader)
      (hValid : validCmd boot (s.nodes l).projectedState cmd)
      (hVoterGuard : cmd.isVoterChange = true →
        (s.nodes l).hasUncommittedVoterChange = false ∧
        (s.nodes l).commit > 0 ∧
        (s.nodes l).termAt (s.nodes l).commit = (s.nodes l).term) :
      Step boot s (nextPropose s l cmd)

  /-- (3) Start election: a node in its own effective voter set increments term,
  votes for itself, becomes candidate, and broadcasts `requestVote` to members
  of its effective voter set (Contract §5). -/
  | startElection (s : System NodeId T) (c : NodeId)
      (hVoter : c ∈ (s.nodes c).effVoters) :
      Step boot s (nextStartElection s c)

  /-- (4) Handle `requestVote`: step down on higher term; grant vote iff not yet
  voted for another candidate in `m.term` and candidate's log is at least as
  up-to-date. -/
  | handleRequestVote (s : System NodeId T) (v c : NodeId) (t cLastIdx cLastTerm : Nat)
      (hMsg : Msg.requestVote t c v cLastIdx cLastTerm ∈ s.net)
      (hTerm : t ≥ (s.nodes v).term) :
      Step boot s (nextHandleRequestVote s v c t cLastIdx cLastTerm)

  /-- (5) Candidate receives a granted `voteReply` for its current term. -/
  | handleVoteReply (s : System NodeId T) (c fromId : NodeId) (t : Nat)
      (hMsg : Msg.voteReply t fromId c true ∈ s.net)
      (hCand : (s.nodes c).role = .candidate)
      (hTerm : (s.nodes c).term = t) :
      Step boot s (nextHandleVoteReply s c fromId)

  /-- (6) Candidate becomes leader once it has votes from a majority of its
  *effective* voter set `(S_p).voters` (Contract §5). -/
  | becomeLeader (s : System NodeId T) (c : NodeId)
      (hCand : (s.nodes c).role = .candidate)
      (hQuorum : IsMajority (s.nodes c).effVoters (fun v => decide (v ∈ (s.nodes c).votes))) :
      Step boot s (nextBecomeLeader s c)

  /-- (7) Leader sends `appendEntries` for any valid slice `[prevIdx+1 .. endIdx]`
  of its in-memory tail (`snapIdx ≤ prevIdx ≤ endIdx ≤ lastIdx`). -/
  | sendAppendEntries (s : System NodeId T) (l : NodeId) (prevIdx endIdx : Nat)
      (hLeader : (s.nodes l).role = .leader)
      (hBounds : (s.nodes l).snapIdx ≤ prevIdx ∧ prevIdx ≤ endIdx ∧ endIdx ≤ (s.nodes l).lastIdx) :
      Step boot s (nextSendAppendEntries s l prevIdx endIdx)

  /-- (8) Handle `appendEntries`: step down if needed, check log consistency
  at `prevIdx`, merge entries without truncating matching suffixes, advance
  `commit` to `min(leaderCommit, prevIdx + entries.length)`, reply with verified
  match index (fixing A1). Truncation automatically recomputes `S_p`. -/
  | handleAppendEntries (s : System NodeId T) (f l : NodeId)
      (t prevIdx prevTerm leaderCommit : Nat) (entries : List (Entry NodeId T.Op))
      (hMsg : Msg.appendEntries t l prevIdx prevTerm entries leaderCommit ∈ s.net)
      (hTerm : t > (s.nodes f).term ∨ (t = (s.nodes f).term ∧ (s.nodes f).role ≠ .leader)) :
      Step boot s (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries)

  /-- (9) Leader processes a successful `appendReply` for its current term. -/
  | handleAppendReply (s : System NodeId T) (l fromId : NodeId) (t mIdx : Nat)
      (hMsg : Msg.appendReply t fromId l true mIdx ∈ s.net)
      (hLeader : (s.nodes l).role = .leader)
      (hTerm : (s.nodes l).term = t) :
      Step boot s (nextHandleAppendReply s l fromId mIdx)

  /-- (10) Leader advances `commit` to index `k` of its current term once a
  majority of its *effective* voter set `(S_p).voters` matches `≥ k`.
  Notice: if `l ∉ effVoters l`, `l` is NOT counted; if `effVoters l = [l]`,
  `l` fast-commits by itself (Contract §5). -/
  | advanceCommit (s : System NodeId T) (l : NodeId) (k : Nat)
      (hLeader : (s.nodes l).role = .leader)
      (hBounds : (s.nodes l).commit < k ∧ k ≤ (s.nodes l).lastIdx)
      (hCurTerm : (s.nodes l).termAt k = (s.nodes l).term)
      (hQuorum : IsMajority (s.nodes l).effVoters
        (fun v => decide (v = l ∨ (s.nodes l).matchIdx v ≥ k))) :
      Step boot s (nextAdvanceCommit s l k)

  /-- (11) Leader steps down to follower (covers both stepping down after
  self-removal commits and lease/timeout step-down). -/
  | leaderStepDown (s : System NodeId T) (l : NodeId)
      (hLeader : (s.nodes l).role = .leader) :
      Step boot s (nextLeaderStepDown s l)

  /-- (12) Apply one committed entry (`applied → applied + 1`) using the pure
  total `applyCmd` function (Contract §2). -/
  | applyOne (s : System NodeId T) (i : NodeId) (e : Entry NodeId T.Op)
      (hLt : (s.nodes i).applied < (s.nodes i).commit)
      (hEntry : (s.nodes i).entryAt ((s.nodes i).applied + 1) = some e) :
      Step boot s (nextApplyOne s i e)

  /-- (13) Snapshot compaction (`nodes.conf` full rewrite): compact applied
  prefix into `(snapIdx, snapTerm, snapState)` and keep tail `> applied`. -/
  | compactSnapshot (s : System NodeId T) (i : NodeId)
      (hLt : (s.nodes i).snapIdx < (s.nodes i).applied) :
      Step boot s (nextCompactSnapshot s i)

  /-- (14) Leader sends `installSnapshot` for its current snapshot. -/
  | sendInstallSnapshot (s : System NodeId T) (l : NodeId)
      (hLeader : (s.nodes l).role = .leader)
      (hSnap : (s.nodes l).snapIdx > 0) :
      Step boot s (nextSendInstallSnapshot s l)

  /-- (15) Handle `installSnapshot` (Raft §7): retain tail suffix if snapshot
  matches an existing entry at `sIdx`, otherwise replace log with snapshot.
  Recomputes `S_p` from `snapState + tail`. -/
  | handleInstallSnapshot (s : System NodeId T) (f l : NodeId)
      (t sIdx sTerm : Nat) (sState : ClusterState T) (sLog : List (Entry NodeId T.Op))
      (hMsg : Msg.installSnapshot t l sIdx sTerm sState ∈ s.net)
      (hSnapLog : (sIdx, sTerm, sState, sLog) ∈ s.hist.snapLogs)
      (hTerm : t > (s.nodes f).term ∨ (t = (s.nodes f).term ∧ (s.nodes f).role ≠ .leader)) :
      Step boot s (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog)

  /-- (16) Crash and restart (Contract §5): keep persisted `(term, votedFor,
  snapIdx, snapTerm, snapState, tail)`, reset all volatile state including
  `commit := snapIdx` and `applied := snapIdx` (no dependency on `commit_index`
  persistence). `S_p` is rebuilt from `snapState + tail`. -/
  | crashRestart (s : System NodeId T) (i : NodeId) :
      Step boot s (nextCrashRestart s i)

/-- Multi-step reachability from the empty initial state. -/
inductive Reachable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}
    (boot : NodeId) : System NodeId T → Prop where
  | init : Reachable boot (System.init T)
  | step {s s' : System NodeId T} : Reachable boot s → Step boot s s' → Reachable boot s'

end ValkeyRaft.ConfigOnAppend

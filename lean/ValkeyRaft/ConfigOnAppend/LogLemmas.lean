/-
  Pure lemmas on logs, 1-based indexing, `stateOfLog` / `stateAt` / `cfgAt`,
  `LogValid`, `LogMonotone`, `IsPrefix`, `mergeFrom`, and voter-change indices.

  All proofs are completely general (zero `sorry`, core Lean 4 only).
-/
import ValkeyRaft.ConfigOnAppend.Spec

namespace ValkeyRaft.ConfigOnAppend

set_option linter.unusedSectionVars false

section LogLemmas

variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

/-! ### `fnUpd` helpers -/

@[simp] theorem fnUpd_same {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) :
    fnUpd f k v k = v := by simp [fnUpd]

@[simp] theorem fnUpd_other {α β : Type} [DecidableEq α] (f : α → β) {k x : α} (v : β)
    (h : x ≠ k) : fnUpd f k v x = f x := by simp [fnUpd, h]

/-! ### `IsPrefix` helpers -/

theorem IsPrefix.refl {α : Type} (L : List α) : IsPrefix L L :=
  ⟨Nat.le_refl _, by simp⟩

theorem IsPrefix.trans {α : Type} {A B C : List α}
    (h1 : IsPrefix A B) (h2 : IsPrefix B C) : IsPrefix A C := by
  refine ⟨Nat.le_trans h1.1 h2.1, ?_⟩
  have : C.take A.length = (C.take B.length).take A.length := by
    rw [List.take_take, Nat.min_eq_left h1.1]
  rw [this, h2.2, h1.2]

theorem IsPrefix.take_left {α : Type} (L : List α) (k : Nat) :
    IsPrefix (L.take k) L := by
  refine ⟨by rw [List.length_take]; omega, ?_⟩
  rw [List.length_take]
  by_cases h : k ≤ L.length
  · rw [Nat.min_eq_left h]
  · have h' : L.length ≤ k := by omega
    rw [Nat.min_eq_right h', List.take_length, List.take_of_length_le h']

theorem IsPrefix.append_right {α : Type} (A B : List α) :
    IsPrefix A (A ++ B) := by
  refine ⟨by simp, by simp⟩

theorem IsPrefix.of_take_eq {α : Type} {A B : List α} (hlen : A.length ≤ B.length)
    (htake : B.take A.length = A) : IsPrefix A B := ⟨hlen, htake⟩

theorem IsPrefix.take_eq_of_le {α : Type} {A B : List α} (hp : IsPrefix A B)
    {k : Nat} (hk : k ≤ A.length) : A.take k = B.take k := by
  rw [← hp.2, List.take_take, Nat.min_eq_left hk]

theorem IsPrefix.getElem?_eq {α : Type} {A B : List α} (hp : IsPrefix A B)
    {i : Nat} (hi : i < A.length) : A[i]? = B[i]? := by
  rw [← hp.2]
  simp [hi]

theorem IsPrefix.eq_of_length_eq {α : Type} {A B : List α}
    (hp : IsPrefix A B) (hlen : A.length = B.length) : A = B := by
  have := hp.2
  rw [hlen, List.take_length] at this
  exact this.symm

theorem IsPrefix.nil_left {α : Type} (L : List α) : IsPrefix [] L :=
  ⟨Nat.zero_le _, by simp⟩

theorem IsPrefix.antisymm {α : Type} {A B : List α}
    (h1 : IsPrefix A B) (h2 : IsPrefix B A) : A = B :=
  h1.eq_of_length_eq (Nat.le_antisymm h1.1 h2.1)

/-! ### `logGet`, `logTermAt`, `logLastTerm` -/

theorem logGet_zero {Op : Type} (L : List (Entry NodeId Op)) : logGet L 0 = none := by
  simp [logGet]

theorem logTermAt_zero {Op : Type} (L : List (Entry NodeId Op)) : logTermAt L 0 = 0 := by
  simp [logTermAt, logGet]

theorem logGet_pos {Op : Type} (L : List (Entry NodeId Op)) {k : Nat} (hk : 1 ≤ k) :
    logGet L k = L[k - 1]? := by
  have : (k == 0) = false := by
    cases k with | zero => omega | succ _ => rfl
  simp [logGet, this]

theorem logGet_some_iff {Op : Type} (L : List (Entry NodeId Op)) {k : Nat}
    (h1 : 1 ≤ k) (h2 : k ≤ L.length) :
    ∃ e, logGet L k = some e := by
  rw [logGet_pos L h1]
  have hlt : k - 1 < L.length := by omega
  exact ⟨L[k - 1], List.getElem?_eq_getElem hlt⟩

theorem logGet_take {Op : Type} (L : List (Entry NodeId Op)) {n k : Nat}
    (hk : k ≤ n) : logGet (L.take n) k = logGet L k := by
  cases k with
  | zero => simp [logGet]
  | succ m =>
    rw [logGet_pos _ (by omega), logGet_pos _ (by omega)]
    simp only [Nat.add_sub_cancel]
    have hlt : m < n := by omega
    simp [hlt]

theorem logTermAt_take {Op : Type} (L : List (Entry NodeId Op)) {n k : Nat}
    (hk : k ≤ n) : logTermAt (L.take n) k = logTermAt L k := by
  simp [logTermAt, logGet_take L hk]

theorem logGet_of_prefix {Op : Type} {A B : List (Entry NodeId Op)}
    (hp : IsPrefix A B) {k : Nat} (hk : k ≤ A.length) :
    logGet A k = logGet B k := by
  rw [← hp.2]
  exact logGet_take B hk

theorem logTermAt_of_prefix {Op : Type} {A B : List (Entry NodeId Op)}
    (hp : IsPrefix A B) {k : Nat} (hk : k ≤ A.length) :
    logTermAt A k = logTermAt B k := by
  simp [logTermAt, logGet_of_prefix hp hk]

theorem logGet_append_left {Op : Type} (A B : List (Entry NodeId Op)) {k : Nat}
    (hk : k ≤ A.length) : logGet (A ++ B) k = logGet A k :=
  (logGet_of_prefix (IsPrefix.append_right A B) hk).symm

theorem logTermAt_append_left {Op : Type} (A B : List (Entry NodeId Op)) {k : Nat}
    (hk : k ≤ A.length) : logTermAt (A ++ B) k = logTermAt A k :=
  (logTermAt_of_prefix (IsPrefix.append_right A B) hk).symm

theorem logGet_append_singleton_last {Op : Type} (A : List (Entry NodeId Op))
    (e : Entry NodeId Op) :
    logGet (A ++ [e]) (A.length + 1) = some e := by
  rw [logGet_pos _ (by omega)]
  simp

theorem logTermAt_append_singleton_last {Op : Type} (A : List (Entry NodeId Op))
    (e : Entry NodeId Op) :
    logTermAt (A ++ [e]) (A.length + 1) = e.term := by
  simp [logTermAt, logGet_append_singleton_last]

theorem logLastTerm_append_singleton {Op : Type} (A : List (Entry NodeId Op))
    (e : Entry NodeId Op) :
    logLastTerm (A ++ [e]) = e.term := by
  simp [logLastTerm, logTermAt_append_singleton_last]

theorem logGet_gt_length {Op : Type} (L : List (Entry NodeId Op)) {k : Nat}
    (hk : L.length < k) : logGet L k = none := by
  rw [logGet_pos L (by omega)]
  exact List.getElem?_eq_none (by omega)

theorem logTermAt_gt_length {Op : Type} (L : List (Entry NodeId Op)) {k : Nat}
    (hk : L.length < k) : logTermAt L k = 0 := by
  simp [logTermAt, logGet_gt_length L hk]

theorem logLastTerm_nil {Op : Type} : logLastTerm ([] : List (Entry NodeId Op)) = 0 := by
  simp [logLastTerm, logTermAt, logGet]

theorem logLastTerm_take {Op : Type} (L : List (Entry NodeId Op)) {k : Nat}
    (hk : k ≤ L.length) : logLastTerm (L.take k) = logTermAt L k := by
  unfold logLastTerm
  rw [List.length_take, Nat.min_eq_left hk]
  exact logTermAt_take L (Nat.le_refl k)

theorem take_succ_eq_append {α : Type} (L : List α) {k : Nat} {x : α}
    (h : L[k]? = some x) : L.take (k + 1) = L.take k ++ [x] := by
  induction L generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero =>
      simp at h; subst h; simp
    | succ m =>
      simp only [List.getElem?_cons_succ] at h
      simp [List.take_succ_cons, ih h]

theorem take_eq_append_logGet {Op : Type} (L : List (Entry NodeId Op)) {k : Nat}
    {e : Entry NodeId Op} (h1 : 1 ≤ k) (hg : logGet L k = some e) :
    L.take k = L.take (k - 1) ++ [e] := by
  rw [logGet_pos L h1] at hg
  have h := take_succ_eq_append L hg
  have hk : k - 1 + 1 = k := by omega
  rwa [hk] at h

/-! ### `stateOfLog`, `stateAt`, `cfgAt`, and `foldl` associativity -/

theorem stateOfLog_nil :
    stateOfLog ([] : List (Entry NodeId T.Op)) = ClusterState.empty T := rfl

theorem stateOfLog_append (A B : List (Entry NodeId T.Op)) :
    stateOfLog (A ++ B) = B.foldl (fun s e => applyCmd s e.cmd) (stateOfLog A) := by
  simp [stateOfLog, List.foldl_append]

theorem stateOfLog_append_singleton (A : List (Entry NodeId T.Op)) (e : Entry NodeId T.Op) :
    stateOfLog (A ++ [e]) = applyCmd (stateOfLog A) e.cmd := by
  simp [stateOfLog, List.foldl_append]

theorem stateAt_zero (L : List (Entry NodeId T.Op)) :
    stateAt L 0 = ClusterState.empty T := by
  simp [stateAt, stateOfLog]

theorem stateAt_length (L : List (Entry NodeId T.Op)) :
    stateAt L L.length = stateOfLog L := by
  simp [stateAt]

theorem stateAt_ge_length (L : List (Entry NodeId T.Op)) {k : Nat} (hk : L.length ≤ k) :
    stateAt L k = stateOfLog L := by
  simp [stateAt, List.take_of_length_le hk]

theorem stateAt_take (L : List (Entry NodeId T.Op)) {n k : Nat} (hk : k ≤ n) :
    stateAt (L.take n) k = stateAt L k := by
  simp [stateAt, List.take_take, Nat.min_eq_left hk]

theorem stateAt_of_prefix {A B : List (Entry NodeId T.Op)} (hp : IsPrefix A B)
    {k : Nat} (hk : k ≤ A.length) : stateAt A k = stateAt B k := by
  simp [stateAt, hp.take_eq_of_le hk]

theorem cfgAt_of_prefix {A B : List (Entry NodeId T.Op)} (hp : IsPrefix A B)
    {k : Nat} (hk : k ≤ A.length) : cfgAt A k = cfgAt B k := by
  simp [cfgAt, stateAt_of_prefix hp hk]

theorem stateAt_succ {L : List (Entry NodeId T.Op)} {k : Nat} {e : Entry NodeId T.Op}
    (h1 : 1 ≤ k) (hg : logGet L k = some e) :
    stateAt L k = applyCmd (stateAt L (k - 1)) e.cmd := by
  unfold stateAt
  rw [take_eq_append_logGet L h1 hg, stateOfLog_append_singleton]

theorem cfgAt_succ {L : List (Entry NodeId T.Op)} {k : Nat} {e : Entry NodeId T.Op}
    (h1 : 1 ≤ k) (hg : logGet L k = some e) :
    cfgAt L k = (applyCmd (stateAt L (k - 1)) e.cmd).voters := by
  simp [cfgAt, stateAt_succ h1 hg]

theorem foldl_drop_take_eq {L : List (Entry NodeId T.Op)} {a b : Nat}
    (hab : a ≤ b) :
    ((L.drop a).take (b - a)).foldl (fun s e => applyCmd s e.cmd) (stateAt L a) =
      stateAt L b := by
  have hsplit : L.take b = L.take a ++ (L.drop a).take (b - a) := by
    induction L generalizing a b with
    | nil => simp
    | cons x xs ih =>
      cases a with
      | zero => simp
      | succ a' =>
        cases b with
        | zero => omega
        | succ b' =>
          simp only [List.take_succ_cons, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub,
            List.cons_append]
          congr 1
          exact ih (by omega)
  unfold stateAt
  rw [hsplit, stateOfLog_append]

theorem foldl_drop_eq {L : List (Entry NodeId T.Op)} (a : Nat) :
    (L.drop a).foldl (fun s e => applyCmd s e.cmd) (stateAt L a) = stateOfLog L := by
  have h := stateOfLog_append (L.take a) (L.drop a)
  rw [List.take_append_drop] at h
  exact h.symm

/-! ### `LogValid`, `LogMonotone`, `BootstrapAtOne` -/

/-- Terms in `L` are strictly positive and monotonically non-decreasing. -/
def LogMonotone {Op : Type} (L : List (Entry NodeId Op)) : Prop :=
  (∀ k, 1 ≤ k → k ≤ L.length → logTermAt L k > 0) ∧
  (∀ i j, 1 ≤ i → i ≤ j → j ≤ L.length → logTermAt L i ≤ logTermAt L j)

/-- Entry 1 (whenever `L` is non-empty) is the unique bootstrap self-join at term 1. -/
def BootstrapAtOne {Op : Type} (boot : NodeId) (L : List (Entry NodeId Op)) : Prop :=
  ∀ e, logGet L 1 = some e → e.term = 1 ∧ e.cmd = .bootstrapJoin boot

theorem LogValid.nil (boot : NodeId) : LogValid boot ([] : List (Entry NodeId T.Op)) := by
  intro k e h1 h2; simp at h2; omega

theorem LogMonotone.nil : LogMonotone ([] : List (Entry NodeId T.Op)) := by
  refine ⟨?_, ?_⟩ <;> intro <;> simp <;> omega

theorem BootstrapAtOne.nil (boot : NodeId) :
    BootstrapAtOne boot ([] : List (Entry NodeId T.Op)) := by
  intro e hg; simp [logGet] at hg

theorem LogValid.of_prefix {boot : NodeId} {A B : List (Entry NodeId T.Op)}
    (hp : IsPrefix A B) (hv : LogValid boot B) : LogValid boot A := by
  intro k e h1 h2 hg
  rw [logGet_of_prefix hp h2] at hg
  rw [stateAt_of_prefix hp (by omega)]
  exact hv k e h1 (Nat.le_trans h2 hp.1) hg

theorem LogMonotone.of_prefix {A B : List (Entry NodeId T.Op)}
    (hp : IsPrefix A B) (hm : LogMonotone B) : LogMonotone A := by
  refine ⟨?_, ?_⟩
  · intro k h1 h2
    rw [logTermAt_of_prefix hp h2]
    exact hm.1 k h1 (Nat.le_trans h2 hp.1)
  · intro i j h1 hij hj
    rw [logTermAt_of_prefix hp (Nat.le_trans hij hj), logTermAt_of_prefix hp hj]
    exact hm.2 i j h1 hij (Nat.le_trans hj hp.1)

theorem BootstrapAtOne.of_prefix {boot : NodeId} {A B : List (Entry NodeId T.Op)}
    (hp : IsPrefix A B) (hb : BootstrapAtOne boot B) : BootstrapAtOne boot A := by
  intro e hg
  cases hlen : A.length with
  | zero =>
    rw [List.length_eq_zero_iff] at hlen; subst hlen; simp [logGet] at hg
  | succ m =>
    rw [logGet_of_prefix hp (by omega)] at hg
    exact hb e hg

theorem LogValid.append_singleton {boot : NodeId} {L : List (Entry NodeId T.Op)}
    {e : Entry NodeId T.Op}
    (hv : LogValid boot L) (he : validCmd boot (stateOfLog L) e.cmd) :
    LogValid boot (L ++ [e]) := by
  intro k e' h1 h2 hg
  simp only [List.length_append, List.length_singleton] at h2
  by_cases hlt : k ≤ L.length
  · rw [logGet_append_left L [e] hlt] at hg
    rw [← stateAt_of_prefix (IsPrefix.append_right L [e]) (by omega)]
    exact hv k e' h1 hlt hg
  · have hkeq : k = L.length + 1 := by omega
    subst hkeq
    rw [logGet_append_singleton_last] at hg
    injection hg with heq; subst heq
    have hst : stateAt (L ++ [e]) L.length = stateOfLog L := by
      simp [stateAt]
    simpa [Nat.add_sub_cancel, hst] using he

theorem LogMonotone.append_singleton {L : List (Entry NodeId T.Op)} {e : Entry NodeId T.Op}
    (hm : LogMonotone L) (hpos : e.term > 0) (hle : logLastTerm L ≤ e.term) :
    LogMonotone (L ++ [e]) := by
  refine ⟨?_, ?_⟩
  · intro k h1 h2
    simp only [List.length_append, List.length_singleton] at h2
    by_cases hlt : k ≤ L.length
    · rw [logTermAt_append_left L [e] hlt]; exact hm.1 k h1 hlt
    · have : k = L.length + 1 := by omega
      subst this; rw [logTermAt_append_singleton_last]; exact hpos
  · intro i j h1 hij hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j ≤ L.length
    · rw [logTermAt_append_left L [e] (Nat.le_trans hij hjl),
          logTermAt_append_left L [e] hjl]
      exact hm.2 i j h1 hij hjl
    · have hjeq : j = L.length + 1 := by omega
      subst hjeq
      rw [logTermAt_append_singleton_last]
      by_cases hil : i ≤ L.length
      · rw [logTermAt_append_left L [e] hil]
        have hle' : logTermAt L i ≤ logLastTerm L := hm.2 i L.length h1 hil (Nat.le_refl _)
        omega
      · have hieq : i = L.length + 1 := by omega
        subst hieq; rw [logTermAt_append_singleton_last]; exact Nat.le_refl _

theorem stateAt_wf_of_valid {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) (k : Nat) (hk : k ≤ L.length) :
    (stateAt L k).WF := by
  induction k with
  | zero =>
    rw [stateAt_zero]; exact ClusterState.empty_wf T
  | succ m ih =>
    rcases logGet_some_iff L (by omega) hk with ⟨e, hg⟩
    rw [stateAt_succ (by omega) hg]
    have hwf := ih (by omega)
    have hve := hv (m + 1) e (by omega) hk hg
    simpa [Nat.add_sub_cancel] using validCmd_preserves_wf hwf hve

theorem stateOfLog_wf_of_valid {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) : (stateOfLog L).WF := by
  rw [← stateAt_length]; exact stateAt_wf_of_valid hv L.length (Nat.le_refl _)

theorem voters_nonempty_of_valid_pos {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ L.length) :
    cfgAt L k ≠ [] := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases logGet_some_iff L (by omega) h2 with ⟨e, hg⟩
    have hve := hv (m + 1) e (by omega) h2 hg
    rw [cfgAt_succ (by omega) hg]
    cases m with
    | zero =>
      simp only [Nat.add_sub_cancel, stateAt_zero] at hve ⊢
      cases hc : e.cmd with
      | bootstrapJoin n => simp [applyCmd, ClusterState.empty]
      | noop => simp [hc, validCmd, ClusterState.empty] at hve
      | joinLearner n => simp [hc, validCmd, ClusterState.empty] at hve
      | forgetLearner n => simp [hc, validCmd, ClusterState.empty] at hve
      | addVoter n => simp [hc, validCmd, ClusterState.empty] at hve
      | delVoter n => simp [hc, validCmd, ClusterState.empty] at hve
      | topo op => simp [hc, validCmd, ClusterState.empty] at hve
    | succ m' =>
      have hne := ih (by omega) (by omega)
      have hwf := stateAt_wf_of_valid hv (m' + 1) (by omega)
      simpa [Nat.add_sub_cancel] using validCmd_preserves_voters_nonempty hwf hne hve

/-- Every entry at index `k > 1` in a valid log produces an *adjacent* voter set,
and cannot be `bootstrapJoin`! -/
theorem cfgAt_adjacent_step {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) {k : Nat} (hgt : 1 < k) (hk : k ≤ L.length) :
    Adjacent (cfgAt L (k - 1)) (cfgAt L k) := by
  rcases logGet_some_iff L (by omega) hk with ⟨e, hg⟩
  have hve := hv k e (by omega) hk hg
  have hwf := stateAt_wf_of_valid hv (k - 1) (by omega)
  have hne := voters_nonempty_of_valid_pos hv (k := k - 1) (by omega) (by omega)
  rw [cfgAt_succ (by omega) hg]
  exact validCmd_adjacent_voters hwf hne hve

/-- Contract §6: for any entry at index `k > 1` in a valid log, if it changes
the voter set then it MUST be `addVoter` or `delVoter` (never `bootstrapJoin`,
`joinLearner`, `forgetLearner`, `noop`, or `topo`). -/
theorem only_add_del_change_voters_gt_one {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) {k : Nat} {e : Entry NodeId T.Op}
    (hgt : 1 < k) (hk : k ≤ L.length) (hg : logGet L k = some e)
    (hchg : cfgAt L k ≠ cfgAt L (k - 1)) :
    (∃ n, e.cmd = .addVoter n) ∨ (∃ n, e.cmd = .delVoter n) := by
  have hve := hv k e (by omega) hk hg
  have hne := voters_nonempty_of_valid_pos hv (k := k - 1) (by omega) (by omega)
  rw [cfgAt_succ (by omega) hg] at hchg
  cases hc : e.cmd with
  | addVoter n => exact Or.inl ⟨n, rfl⟩
  | delVoter n => exact Or.inr ⟨n, rfl⟩
  | bootstrapJoin n =>
    simp [hc, validCmd] at hve
    exact absurd hve.2.2 hne
  | noop => simp [hc, applyCmd, cfgAt] at hchg
  | joinLearner n => simp [hc, applyCmd, cfgAt] at hchg
  | forgetLearner n => simp [hc, applyCmd, cfgAt] at hchg
  | topo op => simp [hc, applyCmd, cfgAt] at hchg

/-- If no entry in `(a, b]` is a voter change, then `cfgAt L b = cfgAt L a`. -/
theorem cfgAt_eq_of_no_voter_change {L : List (Entry NodeId T.Op)} {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ L.length)
    (hno : ∀ j e, a < j → j ≤ b → logGet L j = some e → e.cmd.isVoterChange = false) :
    cfgAt L b = cfgAt L a := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hEq : a = m + 1
    · subst hEq; rfl
    · have ham : a ≤ m := by omega
      rcases logGet_some_iff L (by omega) hb with ⟨e, hg⟩
      have hfalse := hno (m + 1) e (by omega) (Nat.le_refl _) hg
      rw [cfgAt_succ (by omega) hg, non_voter_change_preserves_voters _ _ hfalse]
      simpa [Nat.add_sub_cancel, cfgAt] using ih ham (by omega) (fun j e' hj1 hj2 => hno j e' hj1 (by omega))

/-- If there is at most ONE voter change in `(a, b]` (with `1 ≤ a`), then
`cfgAt L a` and `cfgAt L b` are `Adjacent`. -/
theorem cfgAt_adjacent_of_one_voter_change {boot : NodeId} {L : List (Entry NodeId T.Op)}
    (hv : LogValid boot L) {a b k : Nat}
    (ha1 : 1 ≤ a) (hak : a < k) (hkb : k ≤ b) (hb : b ≤ L.length)
    (hno1 : ∀ j e, a < j → j < k → logGet L j = some e → e.cmd.isVoterChange = false)
    (hno2 : ∀ j e, k < j → j ≤ b → logGet L j = some e → e.cmd.isVoterChange = false) :
    Adjacent (cfgAt L a) (cfgAt L b) := by
  have h1 : cfgAt L (k - 1) = cfgAt L a :=
    cfgAt_eq_of_no_voter_change (by omega) (by omega) (fun j e hj1 hj2 => hno1 j e hj1 (by omega))
  have h2 : cfgAt L b = cfgAt L k :=
    cfgAt_eq_of_no_voter_change hkb hb hno2
  rw [← h1, h2]
  exact cfgAt_adjacent_step hv (by omega) (by omega)

/-! ### Latest voter-change index in a log -/

/-- Find the largest 1-based index `≤ k` in `L` that has `isVoterChange = true`
(or `0` if none). -/
def lastVoterChangeUpTo {Op : Type} (L : List (Entry NodeId Op)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    match logGet L (k + 1) with
    | some e => if e.cmd.isVoterChange then k + 1 else lastVoterChangeUpTo L k
    | none => lastVoterChangeUpTo L k

def lastVoterChange {Op : Type} (L : List (Entry NodeId Op)) : Nat :=
  lastVoterChangeUpTo L L.length

theorem lastVoterChangeUpTo_le {Op : Type} (L : List (Entry NodeId Op)) (k : Nat) :
    lastVoterChangeUpTo L k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold lastVoterChangeUpTo
    cases hg : logGet L (m + 1) with
    | none => simp only; omega
    | some e =>
      simp only
      cases hvc : e.cmd.isVoterChange
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [↓reduceIte]; omega

theorem lastVoterChange_le {Op : Type} (L : List (Entry NodeId Op)) :
    lastVoterChange L ≤ L.length :=
  lastVoterChangeUpTo_le L L.length

theorem lastVoterChangeUpTo_is_vc {Op : Type} (L : List (Entry NodeId Op)) (k : Nat)
    (hpos : lastVoterChangeUpTo L k > 0) :
    ∃ e, logGet L (lastVoterChangeUpTo L k) = some e ∧ e.cmd.isVoterChange = true := by
  induction k with
  | zero => simp [lastVoterChangeUpTo] at hpos
  | succ m ih =>
    unfold lastVoterChangeUpTo at hpos ⊢
    cases hg : logGet L (m + 1) with
    | none =>
      simp only [hg] at hpos ⊢; exact ih hpos
    | some e =>
      simp only [hg] at hpos ⊢
      cases hvc : e.cmd.isVoterChange with
      | true =>
        simp only [↓reduceIte]
        exact ⟨e, hg, hvc⟩
      | false =>
        simp only [hvc, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
        exact ih hpos

theorem lastVoterChangeUpTo_none_after {Op : Type} (L : List (Entry NodeId Op)) (k : Nat) :
    ∀ j e, lastVoterChangeUpTo L k < j → j ≤ k → logGet L j = some e →
      e.cmd.isVoterChange = false := by
  induction k with
  | zero => intro j e h1 h2; omega
  | succ m ih =>
    intro j e hj1 hj2 hg
    unfold lastVoterChangeUpTo at hj1
    cases hgm : logGet L (m + 1) with
    | none =>
      simp only [hgm] at hj1
      by_cases hjm : j = m + 1
      · subst hjm; rw [hgm] at hg; cases hg
      · exact ih j e hj1 (by omega) hg
    | some em =>
      simp only [hgm] at hj1
      cases hvc : em.cmd.isVoterChange with
      | true =>
        simp only [hvc, ↓reduceIte] at hj1; omega
      | false =>
        simp only [hvc, Bool.false_eq_true, ↓reduceIte] at hj1
        by_cases hjm : j = m + 1
        · subst hjm; rw [hgm] at hg; injection hg with heq; subst heq; exact hvc
        · exact ih j e hj1 (by omega) hg

theorem lastVoterChangeUpTo_ge_of_vc {Op : Type} (L : List (Entry NodeId Op)) {k j : Nat}
    {e : Entry NodeId Op} (hj : j ≤ k) (hg : logGet L j = some e)
    (hvc : e.cmd.isVoterChange = true) :
    j ≤ lastVoterChangeUpTo L k := by
  by_cases hle : j ≤ lastVoterChangeUpTo L k
  · exact hle
  · have hgt : lastVoterChangeUpTo L k < j := by omega
    have hf := lastVoterChangeUpTo_none_after L k j e hgt hj hg
    rw [hvc] at hf; cases hf

theorem cfgAt_eq_lastVoterChangeUpTo {L : List (Entry NodeId T.Op)} {k : Nat}
    (hk : k ≤ L.length) :
    cfgAt L k = cfgAt L (lastVoterChangeUpTo L k) :=
  cfgAt_eq_of_no_voter_change (lastVoterChangeUpTo_le L k) hk
    (lastVoterChangeUpTo_none_after L k)

theorem votersOfLog_eq_lastVoterChange (L : List (Entry NodeId T.Op)) :
    votersOfLog L = cfgAt L (lastVoterChange L) := by
  have h := cfgAt_eq_lastVoterChangeUpTo (L := L) (Nat.le_refl L.length)
  simpa [cfgAt, stateAt_length, votersOfLog, lastVoterChange] using h

theorem lastVoterChangeUpTo_take {Op : Type} (L : List (Entry NodeId Op)) {n k : Nat}
    (hk : k ≤ n) : lastVoterChangeUpTo (L.take n) k = lastVoterChangeUpTo L k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    simp only [lastVoterChangeUpTo, logGet_take L hk, ih (by omega)]

theorem lastVoterChange_of_prefix_vc {Op : Type} {A B : List (Entry NodeId Op)}
    (hp : IsPrefix A B) {k : Nat} (hk : k ≤ A.length) :
    lastVoterChangeUpTo A k = lastVoterChangeUpTo B k := by
  rw [← hp.2]
  exact lastVoterChangeUpTo_take B hk

/-- First voter-change index strictly greater than `a` and `≤ b` (if any exists). -/
theorem exists_first_voter_change {Op : Type} (L : List (Entry NodeId Op)) {a b : Nat}
    (hex : ∃ j e, a < j ∧ j ≤ b ∧ logGet L j = some e ∧ e.cmd.isVoterChange = true) :
    ∃ k e, a < k ∧ k ≤ b ∧ logGet L k = some e ∧ e.cmd.isVoterChange = true ∧
      (∀ j e', a < j → j < k → logGet L j = some e' → e'.cmd.isVoterChange = false) := by
  induction b with
  | zero =>
    rcases hex with ⟨j, _, h1, h2, _⟩; omega
  | succ m ih =>
    by_cases hprev : ∃ j e, a < j ∧ j ≤ m ∧ logGet L j = some e ∧ e.cmd.isVoterChange = true
    · rcases ih hprev with ⟨k, e, h1, h2, h3, h4, h5⟩
      exact ⟨k, e, h1, by omega, h3, h4, h5⟩
    · rcases hex with ⟨j, e, h1, h2, h3, h4⟩
      have hjeq : j = m + 1 := by
        by_cases heq : j = m + 1
        · exact heq
        · exact absurd ⟨j, e, h1, by omega, h3, h4⟩ hprev
      subst hjeq
      refine ⟨m + 1, e, h1, Nat.le_refl _, h3, h4, ?_⟩
      intro j' e' hj1 hj2 hg'
      cases hvc' : e'.cmd.isVoterChange with
      | false => rfl
      | true => exact absurd ⟨j', e', hj1, by omega, hg', hvc'⟩ hprev

/-! ### `hasUncommittedVoterChange` characterization -/

theorem hasUncommittedVoterChange_false_iff {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hTail : n.tail = L.drop n.snapIdx)
    (hSnapLeCommit : n.snapIdx ≤ n.commit) :
    n.hasUncommittedVoterChange = false ↔
      (∀ j e, n.commit < j → j ≤ L.length → logGet L j = some e → e.cmd.isVoterChange = false) := by
  unfold Node.hasUncommittedVoterChange
  rw [hTail, List.drop_drop]
  have hadd : n.snapIdx + (n.commit - n.snapIdx) = n.commit := by omega
  rw [hadd]
  constructor
  · intro h j e hj1 hj2 hg
    rw [logGet_pos L (by omega)] at hg
    have hmem : e ∈ L.drop n.commit := by
      have hidx : (L.drop n.commit)[j - 1 - n.commit]? = some e := by
        rw [List.getElem?_drop]
        have : n.commit + (j - 1 - n.commit) = j - 1 := by omega
        rw [this]; exact hg
      exact List.mem_of_getElem? hidx
    cases hvc : e.cmd.isVoterChange with
    | false => rfl
    | true =>
      have hany : (L.drop n.commit).any (fun x => x.cmd.isVoterChange) = true :=
        List.any_eq_true.mpr ⟨e, hmem, hvc⟩
      rw [hany] at h; cases h
  · intro hall
    rw [Bool.eq_false_iff]
    intro hany
    rcases List.any_eq_true.mp hany with ⟨e, hmem, hvc⟩
    rcases List.getElem_of_mem hmem with ⟨idx, hlt, heq⟩
    have hlt' : idx < L.length - n.commit := by simpa [List.length_drop] using hlt
    have hget : L[n.commit + idx]? = some e := by
      have hdrop : (L.drop n.commit)[idx] = L[n.commit + idx]'(by omega) :=
        List.getElem_drop
      rw [heq] at hdrop
      rw [List.getElem?_eq_getElem (by omega)]
      exact congrArg some hdrop.symm
    have hg : logGet L (n.commit + idx + 1) = some e := by
      rw [logGet_pos L (by omega)]
      simpa [Nat.add_sub_cancel] using hget
    have hf := hall (n.commit + idx + 1) e (by omega) (by omega) hg
    rw [hvc] at hf; cases hf

/-! ### `Node` sync helpers (`projectedState`, `termAt`, `lastIdx`, `entryAt`) -/

theorem node_lastIdx_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hSnap : n.snapIdx ≤ L.length) (hTail : n.tail = L.drop n.snapIdx) :
    n.lastIdx = L.length := by
  unfold Node.lastIdx
  rw [hTail, List.length_drop]
  omega

theorem node_entryAt_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hTail : n.tail = L.drop n.snapIdx) {k : Nat} (hk : n.snapIdx < k) :
    n.entryAt k = logGet L k := by
  unfold Node.entryAt
  simp only [hk, ↓reduceIte, hTail, List.getElem?_drop]
  rw [logGet_pos L (by omega)]
  congr 1; omega

theorem node_termAt_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hTail : n.tail = L.drop n.snapIdx) (hSnapTerm : n.snapTerm = logTermAt L n.snapIdx)
    {k : Nat} (hk : n.snapIdx ≤ k) :
    n.termAt k = logTermAt L k := by
  unfold Node.termAt
  cases k with
  | zero => simp [logTermAt_zero]
  | succ m =>
    have hnz : (m + 1 == 0) = false := rfl
    rw [hnz]
    simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
    by_cases heq : m + 1 = n.snapIdx
    · simp [heq, hSnapTerm]
    · simp only [heq, ↓reduceIte]
      rw [node_entryAt_eq hTail (by omega)]
      unfold logTermAt
      cases logGet L (m + 1) <;> rfl

theorem node_lastTerm_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hSnap : n.snapIdx ≤ L.length) (hTail : n.tail = L.drop n.snapIdx)
    (hSnapTerm : n.snapTerm = logTermAt L n.snapIdx) :
    n.lastTerm = logLastTerm L := by
  unfold Node.lastTerm logLastTerm
  rw [node_lastIdx_eq hSnap hTail]
  exact node_termAt_eq hTail hSnapTerm hSnap

theorem node_projectedFromSnap_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hTail : n.tail = L.drop n.snapIdx) (hSnapState : n.snapState = stateAt L n.snapIdx) :
    n.projectedFromSnap = stateOfLog L := by
  unfold Node.projectedFromSnap
  rw [hTail, hSnapState]
  exact foldl_drop_eq n.snapIdx

theorem node_projectedState_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hSnapLeApp : n.snapIdx ≤ n.applied)
    (hTail : n.tail = L.drop n.snapIdx)
    (hAppState : n.appliedState = stateAt L n.applied) :
    n.projectedState = stateOfLog L := by
  unfold Node.projectedState
  rw [hTail, List.drop_drop]
  have hadd : n.snapIdx + (n.applied - n.snapIdx) = n.applied := by omega
  rw [hadd, hAppState]
  exact foldl_drop_eq n.applied

theorem node_projectedAt_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hSnapLeApp : n.snapIdx ≤ n.applied)
    (hTail : n.tail = L.drop n.snapIdx)
    (hAppState : n.appliedState = stateAt L n.applied)
    {i : Nat} (hi : n.applied ≤ i) :
    n.projectedAt i = stateAt L i := by
  unfold Node.projectedAt
  rw [hTail, List.drop_drop]
  have hadd : n.snapIdx + (n.applied - n.snapIdx) = n.applied := by omega
  rw [hadd, hAppState]
  exact foldl_drop_take_eq hi

theorem node_effVoters_eq {n : Node NodeId T} {L : List (Entry NodeId T.Op)}
    (hSnapLeApp : n.snapIdx ≤ n.applied)
    (hTail : n.tail = L.drop n.snapIdx)
    (hAppState : n.appliedState = stateAt L n.applied) :
    n.effVoters = votersOfLog L := by
  unfold Node.effVoters votersOfLog
  rw [node_projectedState_eq hSnapLeApp hTail hAppState]

/-! ### `mergeFrom` lemmas (Raft §5.3 Rule 3) -/

theorem mergeFrom_nil_right {Op : Type} (xs : List (Entry NodeId Op)) :
    mergeFrom xs [] = xs := by
  cases xs <;> rfl

theorem mergeFrom_nil_left {Op : Type} (ys : List (Entry NodeId Op)) :
    mergeFrom [] ys = ys := by
  cases ys <;> rfl

theorem mergeFrom_len_ge {Op : Type} (xs ys : List (Entry NodeId Op)) :
    ys.length ≤ (mergeFrom xs ys).length := by
  induction xs generalizing ys with
  | nil => rw [mergeFrom_nil_left]; exact Nat.le_refl _
  | cons x xs ih =>
    cases ys with
    | nil => simp [mergeFrom]
    | cons y ys =>
      unfold mergeFrom
      cases h : (x.term == y.term)
      · simp
      · simp only [↓reduceIte, List.length_cons]
        have := ih ys; omega

/-- Under Log Matching, `mergeFrom xs ys` either equals `xs` (when `ys` is a
prefix of `xs`) or equals `ys` (when they conflict or `ys` extends `xs`). -/
theorem mergeFrom_spec {Op : Type}
    (xs ys : List (Entry NodeId Op))
    (hmatch : ∀ (i : Nat) (h1 : i < xs.length) (h2 : i < ys.length),
      (xs[i]'h1).term = (ys[i]'h2).term → xs.take (i + 1) = ys.take (i + 1)) :
    (mergeFrom xs ys = xs ∧ IsPrefix ys xs) ∨ mergeFrom xs ys = ys := by
  induction xs generalizing ys with
  | nil => exact Or.inr (mergeFrom_nil_left ys)
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inl ⟨rfl, IsPrefix.nil_left _⟩
    | cons y ys =>
      unfold mergeFrom
      by_cases ht : x.term = y.term
      · have hxy : x = y := by
          have h0 := hmatch 0 (by simp) (by simp) ht
          simp at h0; exact h0
        subst hxy
        simp only [beq_self_eq_true, ↓reduceIte]
        have hsub : ∀ (i : Nat) (h1 : i < xs.length) (h2 : i < ys.length),
            (xs[i]'h1).term = (ys[i]'h2).term → xs.take (i + 1) = ys.take (i + 1) := by
          intro i h1 h2 hti
          have h' := hmatch (i + 1) (by simp; omega) (by simp; omega) hti
          simp at h'
          exact h'
        rcases ih ys hsub with ⟨hL, hp⟩ | hR
        · left
          refine ⟨by rw [hL], ?_⟩
          refine ⟨by simp; exact hp.1, ?_⟩
          simp [hp.2]
        · exact Or.inr (by rw [hR])
      · have hne : (x.term == y.term) = false := beq_false_of_ne ht
        simp [hne]

/-- Drop commutativity for `handleAppendEntries`: merging `tail` at `prevIdx - snapIdx`
equals dropping `snapIdx` from merging `fullLog` at `prevIdx`! -/
theorem drop_take_append_merge {Op : Type} (L entries : List (Entry NodeId Op))
    {snapIdx prevIdx : Nat} (hle : snapIdx ≤ prevIdx) (hprev : prevIdx ≤ L.length) :
    (L.take prevIdx ++ mergeFrom (L.drop prevIdx) entries).drop snapIdx =
      (L.drop snapIdx).take (prevIdx - snapIdx) ++
      mergeFrom ((L.drop snapIdx).drop (prevIdx - snapIdx)) entries := by
  rw [List.drop_append]
  have h1 : (L.take prevIdx).drop snapIdx = (L.drop snapIdx).take (prevIdx - snapIdx) := by
    rw [List.drop_take]
  have h2 : (L.drop snapIdx).drop (prevIdx - snapIdx) = L.drop prevIdx := by
    rw [List.drop_drop]; congr 1; omega
  have hlt : (L.take prevIdx).length = prevIdx := by rw [List.length_take]; omega
  rw [h1, h2, hlt]
  have hsub : snapIdx - prevIdx = 0 := by omega
  simp [hsub]

end LogLemmas

end ValkeyRaft.ConfigOnAppend

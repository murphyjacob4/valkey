/-
  Quorum arithmetic for the Raft cluster bus (valkey-io/valkey#3856).

  Covers:
  * #3866 learners / `server.cluster->size` = voters only
  * #3926 config-on-append vs. config-on-apply
  * #4392 automatic learner promotion ("one quorum-changing op in flight")
  * #4393 balancing voters across availability zones

  Everything here is proved for *all* inputs (no bounded checking), except the
  explicit counterexamples, which are closed by `decide`.
-/
namespace ValkeyRaft.Quorum

/-- Majority of a voter list `v` w.r.t. a membership predicate. This matches
`clusterRaftQuorum() = size / 2 + 1` when `v` has no duplicates. -/
abbrev IsMajority {α} (v : List α) (p : α → Bool) : Prop :=
  (v.filter p).length ≥ v.length / 2 + 1

theorem filter_len_add {α} (p q : α → Bool) (v : List α) :
    (v.filter p).length + (v.filter q).length
      ≤ v.length + (v.filter (fun x => p x && q x)).length := by
  induction v with
  | nil => simp
  | cons a t ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

/-- Two majorities of the *same* voter set always intersect (Raft's core
safety argument). Holds for every voter list. -/
theorem majorities_intersect {α} (v : List α) (p q : α → Bool)
    (hp : IsMajority v p) (hq : IsMajority v q) :
    ∃ x ∈ v, p x = true ∧ q x = true := by
  unfold IsMajority at hp hq
  have h := filter_len_add p q v
  have hpos : 0 < (v.filter (fun x => p x && q x)).length := by omega
  match hl : v.filter (fun x => p x && q x), hpos with
  | x :: _, _ =>
    have hx : x ∈ v.filter (fun x => p x && q x) := by rw [hl]; simp
    simp [List.mem_filter] at hx
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- Single-server change (Ongaro §4.1): a majority of `c` and a majority of
`c ++ [n]` always intersect inside `c`. This is the property that makes
ADD_VOTER / DEL_VOTER safe *as long as the two configurations involved are
adjacent*. -/
theorem adjacent_majorities_intersect {α} (c : List α) (n : α) (p q : α → Bool)
    (hp : IsMajority c p) (hq : IsMajority (c ++ [n]) q) :
    ∃ x ∈ c, p x = true ∧ q x = true := by
  unfold IsMajority at hp hq
  simp [List.filter_append] at hq
  have h := filter_len_add p q c
  have hq' : (c.filter q).length + (if q n then 1 else 0) ≥ (c.length + 1) / 2 + 1 := by
    cases hqn : q n <;> simp [hqn, List.filter] at hq ⊢ <;> omega
  have hpos : 0 < (c.filter (fun x => p x && q x)).length := by
    cases hqn : q n <;> simp [hqn] at hq' <;> omega
  match hl : c.filter (fun x => p x && q x), hpos with
  | x :: _, _ =>
    have hx : x ∈ c.filter (fun x => p x && q x) := by rw [hl]; simp
    simp [List.mem_filter] at hx
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- ...but two configurations that are *two* single-server steps apart can
have disjoint majorities. With config-on-apply a lagging follower can still be
operating under `c0` while the leader already commits under `c2`; see
`Raft.lean` (`trace_pipelined_add_voter`) for the concrete committed-entry
loss. Voters 0,1,2 -> add 3 -> add 4. -/
theorem two_step_majorities_can_be_disjoint :
    let c0 := [0, 1, 2]
    let c2 := [0, 1, 2, 3, 4]
    let s0 := [1, 2]        -- majority of c0
    let s2 := [0, 3, 4]     -- majority of c2
    IsMajority c0 (· ∈ s0) ∧ IsMajority c2 (· ∈ s2) ∧
      (∀ x ∈ c0, ¬ (x ∈ s0 ∧ x ∈ s2)) := by
  decide

/-! ### Availability-zone placement (#4393)

`zones` is the number of voters placed in each zone (sum = n). The cluster
survives the loss of any single zone iff every zone holds at most
`(n - 1) / 2` voters. "Spread across at least 3 zones" (the wording in
#4393 and the design doc) is necessary but **not** sufficient.
-/

abbrev survivesZoneLoss (n z : Nat) : Prop := n - z ≥ n / 2 + 1

theorem survives_iff (n z : Nat) (hn : 0 < n) (hz : z ≤ n) :
    survivesZoneLoss n z ↔ z ≤ (n - 1) / 2 := by
  show n - z ≥ n / 2 + 1 ↔ z ≤ (n - 1) / 2
  constructor <;> intro h <;> omega

/-- With 2 zones no placement survives losing a zone. -/
theorem two_zones_never_survive (a b : Nat) :
    ¬ (survivesZoneLoss (a + b) a ∧ survivesZoneLoss (a + b) b) := by
  intro ⟨h1, h2⟩; unfold survivesZoneLoss at h1 h2; omega

/-- 5 voters over 3 zones as 3/1/1 satisfies "at least 3 zones" but does not
survive losing the big zone. -/
theorem three_zones_not_sufficient :
    ¬ survivesZoneLoss 5 3 := by decide

/-- 5 voters as 2/2/1 does survive any single zone loss. -/
theorem five_as_221_ok :
    survivesZoneLoss 5 2 ∧ survivesZoneLoss 5 1 := by decide

/-- An even voter target (e.g. 4) over 3 zones can never survive a zone loss:
some zone must hold ≥ 2 voters and 4 - 2 < 3. Relevant to the auto-promotion
target (#4392) and to transient states during DEL_VOTER/ADD_VOTER rebalancing. -/
theorem four_voters_three_zones_never_survive (a b c : Nat) (h : a + b + c = 4) :
    ¬ (survivesZoneLoss 4 a ∧ survivesZoneLoss 4 b ∧ survivesZoneLoss 4 c) := by
  intro ⟨h1, h2, h3⟩; unfold survivesZoneLoss at h1 h2 h3; omega

/-- Rebalancing by DEL_VOTER-then-ADD_VOTER passes through an even voter count.
From 5 voters (2/2/1) moving one voter from zone A to zone C:
DEL_VOTER first gives 4 voters as 1/2/1 -> losing zone B (2) leaves 2 < 3. -/
theorem rebalance_transient_unsafe : ¬ survivesZoneLoss 4 2 := by decide

end ValkeyRaft.Quorum

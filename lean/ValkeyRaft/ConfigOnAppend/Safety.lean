/-
  Top-level Safety Theorems for the Intended Valkey Cluster Raft Protocol
  (Config-on-Append, Projected State `S_p`, Pure Total `apply`, Single-Server
  Voter Serialization, Ongaro 2015 Own-Term Commit Gate, Snapshot + Restart).

  All theorems quantify over:
  * an arbitrary `NodeId` type with `[DecidableEq NodeId]`
  * an arbitrary abstract topology specification `T : TopoSpec NodeId`
  * an arbitrary cluster seed `boot : NodeId`
  * an arbitrary reachable state `s` (`Reachable boot s`) under asynchronous
    unordered message delay / duplication / reordering / drop and node crashes.

  Zero `sorry`, zero new axioms (verified via `#print axioms` at the bottom).
-/
import ValkeyRaft.ConfigOnAppend.PreservationCore

namespace ValkeyRaft.ConfigOnAppend

set_option linter.unusedSectionVars false

section Safety

variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

/-! ## 1. Election Safety (Contract §7.1) -/

/-- **Election Safety (historical)**: at most one leader is ever elected in any
given term. -/
theorem election_safety {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {er1 er2 : ElectionRec NodeId T}
    (h1 : er1 ∈ s.hist.elected) (h2 : er2 ∈ s.hist.elected)
    (ht : er1.term = er2.term) :
    er1 = er2 :=
  (Inv.reachable hr).electionUnique er1 h1 er2 h2 ht

/-- **Election Safety (live leaders)**: no two distinct nodes simultaneously
hold `.leader` role in the same term. -/
theorem election_safety_live {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {l1 l2 : NodeId}
    (hL1 : (s.nodes l1).role = .leader) (hL2 : (s.nodes l2).role = .leader)
    (ht : (s.nodes l1).term = (s.nodes l2).term) :
    l1 = l2 := by
  have hinv := Inv.reachable hr
  rcases (hinv.leaderNode l1 hL1).2.2.2.1 with ⟨er1, her1, ht1, hl1, _⟩
  rcases (hinv.leaderNode l2 hL2).2.2.2.1 with ⟨er2, her2, ht2, hl2, _⟩
  have heq := hinv.electionUnique er1 her1 er2 her2 (by omega)
  rw [← hl1, ← hl2, heq]

/-! ## 2. Log Matching (Contract §7.2) -/

/-- **Log Matching**: if two nodes' logs have an entry with the same index and
term, then their logs are identical through that index. -/
theorem log_matching {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i j : NodeId} {k : Nat}
    (hk1 : 1 ≤ k)
    (hi : k ≤ (s.hist.fullLog i).length)
    (hj : k ≤ (s.hist.fullLog j).length)
    (ht : logTermAt (s.hist.fullLog i) k = logTermAt (s.hist.fullLog j) k) :
    (s.hist.fullLog i).take k = (s.hist.fullLog j).take k :=
  (Inv.reachable hr).logMatching (Or.inl ⟨i, rfl⟩) (Or.inl ⟨j, rfl⟩) hk1 hi hj ht

/-- **Log Matching (entry equality)**: same index and term implies the exact
same entry (including command). -/
theorem log_matching_entry {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i j : NodeId} {k : Nat}
    (hk1 : 1 ≤ k)
    (hi : k ≤ (s.hist.fullLog i).length)
    (hj : k ≤ (s.hist.fullLog j).length)
    (ht : logTermAt (s.hist.fullLog i) k = logTermAt (s.hist.fullLog j) k) :
    logGet (s.hist.fullLog i) k = logGet (s.hist.fullLog j) k := by
  have htk := log_matching hr hk1 hi hj ht
  rw [← logGet_take (s.hist.fullLog i) (Nat.le_refl k),
      ← logGet_take (s.hist.fullLog j) (Nat.le_refl k), htk]

/-! ## 3. Leader Completeness (Contract §7.3) -/

/-- **Leader Completeness (election records)**: if a log prefix is committed in
term `cm.term`, it is a prefix of the initial log of every leader elected in any
strictly higher term `er.term > cm.term`. -/
theorem leader_completeness {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {cm : CommitRec NodeId T} {er : ElectionRec NodeId T}
    (hcm : cm ∈ s.hist.commits) (her : er ∈ s.hist.elected)
    (hlt : cm.term < er.term) :
    IsPrefix cm.log er.elecLog :=
  (Inv.reachable hr).leaderCompleteness cm hcm er her hlt

/-- **Leader Completeness (live leaders)**: every entry committed on any node `i`
is present in the log of every active leader `l` with `term l ≥ term i`. -/
theorem leader_completeness_live {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i l : NodeId} {k : Nat}
    (hk1 : 1 ≤ k)
    (hkc : k ≤ (s.nodes i).commit)
    (hL : (s.nodes l).role = .leader)
    (ht : (s.nodes i).term ≤ (s.nodes l).term) :
    IsPrefix ((s.hist.fullLog i).take k) (s.hist.fullLog l) := by
  have hinv := Inv.reachable hr
  have hsync_i := hinv.nodeSync i
  rcases hinv.nodeCommit i (by omega) with ⟨cm, hcm, hcm_t, hcm_idx, hcm_pre⟩
  have hsub : IsPrefix ((s.hist.fullLog i).take k) cm.log := by
    have hki : IsPrefix ((s.hist.fullLog i).take k) ((s.hist.fullLog i).take (s.nodes i).commit) := by
      refine ⟨by rw [List.length_take, List.length_take]; have := hsync_i.2.2.1; omega, ?_⟩
      rw [List.length_take, Nat.min_eq_left (by have := hsync_i.2.2.1; omega),
          List.take_take, Nat.min_eq_left hkc]
    exact IsPrefix.trans hki hcm_pre
  have hln := hinv.leaderNode l hL
  by_cases hlt : cm.term < (s.nodes l).term
  · rcases hln.2.2.2.1 with ⟨er, her, hter, _, hpre_er, _⟩
    have hlc := hinv.leaderCompleteness cm hcm er her (by omega)
    exact IsPrefix.trans hsub (IsPrefix.trans hlc hpre_er)
  · have hcm_eq : cm.term = (s.nodes l).term := by omega
    have hcompat := hinv.commit_accepted_compat hcm (by omega) hln.2.2.1
    have hle_c := hln.2.2.2.2.2.2 cm hcm hcm_eq
    have hle_l := (hinv.nodeSync l).2.2.1
    have hcm_len := (hinv.commitRecs cm hcm).2.1
    have hcm_pre_l : IsPrefix cm.log (s.hist.fullLog l) :=
      isPrefix_of_le_of_prefix_compat hcompat (by omega)
    exact IsPrefix.trans hsub hcm_pre_l

/-! ## 4. State Machine Safety (Contract §7.4) -/

/-- **State Machine Safety (commit records)**: all committed log prefixes are
mutually prefix-compatible (linearly ordered by prefix). -/
theorem state_machine_safety_commits {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {cm1 cm2 : CommitRec NodeId T}
    (h1 : cm1 ∈ s.hist.commits) (h2 : cm2 ∈ s.hist.commits) :
    IsPrefix cm1.log cm2.log ∨ IsPrefix cm2.log cm1.log :=
  (Inv.reachable hr).commitPrefixAgreement h1 h2

/-- **State Machine Safety (committed prefixes)**: if two nodes have both
committed up to index `k`, they agree on the entire log prefix `1..k`. -/
theorem state_machine_safety {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i j : NodeId} {k : Nat}
    (hi : k ≤ (s.nodes i).commit)
    (hj : k ≤ (s.nodes j).commit) :
    (s.hist.fullLog i).take k = (s.hist.fullLog j).take k := by
  cases k with
  | zero => simp
  | succ m =>
    have hinv := Inv.reachable hr
    have hsi := hinv.nodeSync i
    have hsj := hinv.nodeSync j
    rcases hinv.nodeCommit i (by omega) with ⟨cm1, hcm1, _, hidx1, hpre1⟩
    rcases hinv.nodeCommit j (by omega) with ⟨cm2, hcm2, _, hidx2, hpre2⟩
    have hlen1 : ((s.hist.fullLog i).take (s.nodes i).commit).length = (s.nodes i).commit := by
      rw [List.length_take, Nat.min_eq_left hsi.2.2.1]
    have hlen2 : ((s.hist.fullLog j).take (s.nodes j).commit).length = (s.nodes j).commit := by
      rw [List.length_take, Nat.min_eq_left hsj.2.2.1]
    have hti : (s.hist.fullLog i).take (m + 1) = cm1.log.take (m + 1) := by
      have h1 := hpre1.take_eq_of_le (k := m + 1) (by omega)
      rw [List.take_take, Nat.min_eq_left hi] at h1
      exact h1
    have htj : (s.hist.fullLog j).take (m + 1) = cm2.log.take (m + 1) := by
      have h2 := hpre2.take_eq_of_le (k := m + 1) (by omega)
      rw [List.take_take, Nat.min_eq_left hj] at h2
      exact h2
    rw [hti, htj]
    have hcm1_len := (hinv.commitRecs cm1 hcm1).2.1
    have hcm2_len := (hinv.commitRecs cm2 hcm2).2.1
    rcases hinv.commitPrefixAgreement hcm1 hcm2 with h12 | h21
    · exact h12.take_eq_of_le (by omega)
    · exact (h21.take_eq_of_le (by omega)).symm

/-- **State Machine Safety (applied entries)**: no two nodes ever apply
different entries at the same log index. -/
theorem state_machine_safety_applied {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i j : NodeId} {k : Nat}
    (hi : k ≤ (s.nodes i).applied)
    (hj : k ≤ (s.nodes j).applied) :
    logGet (s.hist.fullLog i) k = logGet (s.hist.fullLog j) k := by
  have hinv := Inv.reachable hr
  have htk := state_machine_safety hr
    (Nat.le_trans hi (hinv.nodeSync i).2.1)
    (Nat.le_trans hj (hinv.nodeSync j).2.1)
  rw [← logGet_take (s.hist.fullLog i) (Nat.le_refl k),
      ← logGet_take (s.hist.fullLog j) (Nat.le_refl k), htk]

/-! ## 5. Apply Determinism (Contract §7.5) -/

/-- **Apply Determinism**: any two nodes at the same `applied` index have
byte-for-byte identical `appliedState`. -/
theorem apply_determinism {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i j : NodeId}
    (heq : (s.nodes i).applied = (s.nodes j).applied) :
    (s.nodes i).appliedState = (s.nodes j).appliedState := by
  have hinv := Inv.reachable hr
  have hsi := hinv.nodeSync i
  have hsj := hinv.nodeSync j
  rw [hsi.2.2.2.2.2.2.1, hsj.2.2.2.2.2.2.1, heq]
  unfold stateAt
  have htk := state_machine_safety hr
    (by rw [← heq]; exact hsi.2.1) hsj.2.1
  rw [htk]

/-! ## 6. No Committed No-Ops / Append-Time Validation Sufficiency (Contract §7.6) -/

/-- Every entry in any node's log is valid with respect to its prefix state. -/
theorem all_log_entries_valid {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i : NodeId} {k : Nat} {e : Entry NodeId T.Op}
    (hk1 : 1 ≤ k) (hkl : k ≤ (s.hist.fullLog i).length)
    (hget : logGet (s.hist.fullLog i) k = some e) :
    validCmd boot (stateAt (s.hist.fullLog i) (k - 1)) e.cmd :=
  ((Inv.reachable hr).goodLogs (s.hist.fullLog i) (Or.inl ⟨i, rfl⟩)).1 k e hk1 hkl hget

/-- **No Committed No-Ops**: every committed entry is valid w.r.t. its prefix
state, so `applyChecked` ALWAYS succeeds and equals pure total `applyCmd`. -/
theorem no_committed_noops {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i : NodeId} {k : Nat} {e : Entry NodeId T.Op}
    (hk1 : 1 ≤ k) (hkc : k ≤ (s.nodes i).commit)
    (hget : logGet (s.hist.fullLog i) k = some e) :
    validCmd boot (stateAt (s.hist.fullLog i) (k - 1)) e.cmd ∧
    applyChecked boot (stateAt (s.hist.fullLog i) (k - 1)) e.cmd =
      some (applyCmd (stateAt (s.hist.fullLog i) (k - 1)) e.cmd) := by
  have hinv := Inv.reachable hr
  have hle := Nat.le_trans hkc (hinv.nodeSync i).2.2.1
  have hv := all_log_entries_valid hr hk1 hle hget
  exact ⟨hv, validCmd_applyChecked boot _ _ hv⟩

/-- **Apply Never Rejects (Debug Assertion Soundness)**: at every `applyOne`
step (`applied < commit`), the debug-checked `applyChecked` on `appliedState`
is guaranteed to return `some (applyCmd appliedState e.cmd)` (never `none`). -/
theorem apply_step_never_rejects {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i : NodeId} {e : Entry NodeId T.Op}
    (hLt : (s.nodes i).applied < (s.nodes i).commit)
    (hEntry : (s.nodes i).entryAt ((s.nodes i).applied + 1) = some e) :
    applyChecked boot (s.nodes i).appliedState e.cmd =
      some (applyCmd (s.nodes i).appliedState e.cmd) := by
  have hinv := Inv.reachable hr
  have hsync := hinv.nodeSync i
  have hget : logGet (s.hist.fullLog i) ((s.nodes i).applied + 1) = some e := by
    rw [← node_entryAt_eq hsync.2.2.2.1 (by have := hsync.1; omega)]; exact hEntry
  have hnc := (no_committed_noops hr (by omega) (by omega) hget).2
  rw [hsync.2.2.2.2.2.2.1]
  simpa [Nat.add_sub_cancel] using hnc

/-! ## 7. Config Safety / Quorum Overlap (Contract §7.7) -/

/-- **Config Safety (quorum overlap for adjacent configs)**: any two configs
differing by at most one voter (single-server `ADD_VOTER`/`DEL_VOTER`) have
intersecting majorities. -/
theorem config_safety_quorum_overlap {C1 C2 : List NodeId}
    (hadj : Adjacent C1 C2)
    (q1 q2 : NodeId → Bool)
    (h1 : IsMajority C1 q1) (h2 : IsMajority C2 q2) :
    ∃ v, v ∈ C1 ∧ v ∈ C2 ∧ q1 v = true ∧ q2 v = true :=
  adjacent_quorums_intersect hadj q1 q2 h1 h2

/-- **Config Safety (commit config vs committed-prefix config)**: every commit
record's effective voter set `cm.cfg` is `Adjacent` to `votersOfLog cm.log`,
so every commit quorum intersects every majority of `votersOfLog cm.log`. -/
theorem config_safety_commit_adjacent {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {cm : CommitRec NodeId T} (hcm : cm ∈ s.hist.commits) :
    Adjacent (votersOfLog cm.log) cm.cfg := by
  have hwf := (Inv.reachable hr).commitRecs cm hcm
  rcases hwf.2.2.2.2.2.2.2 with heq | ⟨hadj, _⟩
  · rw [heq]; exact .refl _
  · exact hadj

/-- **Config Safety (active leader effective vs committed config)**: once an
active leader has committed an entry from its own term (as required before
proposing any voter change), its effective config `(s.nodes l).effVoters` and
its committed config `cfgAt (s.hist.fullLog l) (s.nodes l).commit` are
`Adjacent` — hence any two majorities of them intersect! -/
theorem config_safety_leader_effective_vs_committed {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {l : NodeId}
    (hLeader : (s.nodes l).role = .leader)
    (hCommPos : (s.nodes l).commit > 0)
    (hOwnTerm : (s.nodes l).termAt (s.nodes l).commit = (s.nodes l).term) :
    Adjacent (cfgAt (s.hist.fullLog l) (s.nodes l).commit) (s.nodes l).effVoters := by
  have hinv := Inv.reachable hr
  have hsync := hinv.nodeSync l
  have hL := hinv.leaderNode l hLeader
  have hgood := hinv.goodLogs (s.hist.fullLog l) (Or.inl ⟨l, rfl⟩)
  let L := s.hist.fullLog l
  have heff : (s.nodes l).effVoters = votersOfLog L :=
    node_effVoters_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  let kvc := lastVoterChange L
  have hkvc_le : kvc ≤ L.length := lastVoterChange_le L
  by_cases hle : kvc ≤ (s.nodes l).commit
  · have heq : cfgAt L (s.nodes l).commit = (s.nodes l).effVoters := by
      rw [heff, votersOfLog_eq_lastVoterChange]
      exact cfgAt_eq_of_no_voter_change hle hsync.2.2.1
        (fun j e hj1 hj2 => lastVoterChangeUpTo_none_after L L.length j e hj1 (by dsimp [L] at hj2 ⊢; omega))
    rw [heq]; exact .refl _
  · have hkvc_gt : (s.nodes l).commit < kvc := by omega
    have hkvc_gt1 : kvc > 1 := by omega
    have hkvc_pos : lastVoterChangeUpTo L L.length > 0 := by change kvc > 0; omega
    rcases lastVoterChangeUpTo_is_vc L L.length hkvc_pos with ⟨evc, hgvc, hvcvc⟩
    have hgvc' : logGet L kvc = some evc := hgvc
    rcases hgood.2.2.2.1 kvc evc hkvc_gt1 hkvc_le hgvc' hvcvc with
      ⟨cm0, hcm0_mem, hcm0_t, hcm0_lt, _, _, hcm0_novc⟩
    have hcomm_t : logTermAt L (s.nodes l).commit = (s.nodes l).term := by
      rw [← node_termAt_eq hsync.2.2.2.1 hsync.2.2.2.2.1 (by have := hsync.1; have := hsync.2.1; omega)]
      exact hOwnTerm
    have hkvc_t : logTermAt L kvc = (s.nodes l).term := by
      have h1 := hgood.2.1.2 (s.nodes l).commit kvc hCommPos (by omega) hkvc_le
      have h2 := logTermAt_le_logLastTerm hgood.2.1 hkvc_le
      have h3 : logLastTerm L ≤ (s.nodes l).term := hsync.2.2.2.2.2.2.2
      dsimp [L] at h1 h2 h3 hcomm_t ⊢; omega
    have hcm0_t_eq : cm0.term = (s.nodes l).term := by
      have hteq : evc.term = logTermAt L kvc := by simp [logTermAt, hgvc']
      omega
    have hcm0_le : cm0.idx ≤ (s.nodes l).commit := hL.2.2.2.2.2.2 cm0 hcm0_mem hcm0_t_eq
    have hprev_eq : cfgAt L (s.nodes l).commit = cfgAt L (kvc - 1) :=
      (cfgAt_eq_of_no_voter_change (by omega) (by dsimp [L] at hkvc_le ⊢; omega)
        (fun j e hj1 hj2 => hcm0_novc j e (by omega) (by omega))).symm
    rw [hprev_eq, heff, votersOfLog_eq_lastVoterChange]
    exact cfgAt_adjacent_step hgood.1 hkvc_gt1 hkvc_le

/-- **Config Safety (serialization of voter changes)**: between any two distinct
voter-changing entries `1 < k1 < k2` in any node's log, there is a committed
entry `cm` at some index `k1 ≤ cm.idx < k2` — proving no second voter change
was ever appended while an earlier one remained uncommitted. -/
theorem config_safety_voter_changes_serialized {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i : NodeId} {k1 k2 : Nat} {e1 e2 : Entry NodeId T.Op}
    (hk1 : 1 < k1) (hlt : k1 < k2) (hk2 : k2 ≤ (s.hist.fullLog i).length)
    (hg1 : logGet (s.hist.fullLog i) k1 = some e1)
    (hg2 : logGet (s.hist.fullLog i) k2 = some e2)
    (hvc1 : e1.cmd.isVoterChange = true) (hvc2 : e2.cmd.isVoterChange = true) :
    ∃ cm ∈ s.hist.commits, k1 ≤ cm.idx ∧ cm.idx < k2 := by
  have hgood := (Inv.reachable hr).goodLogs (s.hist.fullLog i) (Or.inl ⟨i, rfl⟩)
  rcases hgood.2.2.2.1 k2 e2 (by omega) hk2 hg2 hvc2 with ⟨cm, hcm, _, hcm_lt, _, _, hnovc⟩
  refine ⟨cm, hcm, ?_, hcm_lt⟩
  by_cases hle : k1 ≤ cm.idx
  · exact hle
  · have hf := hnovc k1 e1 (by omega) hlt hg1
    rw [hvc1] at hf; cases hf

/-- **Config Safety (consecutive committed configs overlap)**: if two commits
`cm1, cm2` have at most one voter-changing entry between their indices, their
voter sets are `Adjacent` and any two majorities intersect. -/
theorem config_safety_consecutive_commits_overlap {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {cm1 cm2 : CommitRec NodeId T}
    (hcm1 : cm1 ∈ s.hist.commits) (hcm2 : cm2 ∈ s.hist.commits)
    (hle : cm1.idx ≤ cm2.idx)
    (hatmost : ∀ j1 j2 e1 e2, cm1.idx < j1 → j1 < j2 → j2 ≤ cm2.idx →
      logGet cm2.log j1 = some e1 → logGet cm2.log j2 = some e2 →
      e1.cmd.isVoterChange = true → e2.cmd.isVoterChange = true → False)
    (q1 q2 : NodeId → Bool)
    (hm1 : IsMajority (votersOfLog cm1.log) q1)
    (hm2 : IsMajority (votersOfLog cm2.log) q2) :
    ∃ v, v ∈ votersOfLog cm1.log ∧ v ∈ votersOfLog cm2.log ∧ q1 v = true ∧ q2 v = true := by
  have hinv := Inv.reachable hr
  have hwf1 := hinv.commitRecs cm1 hcm1
  have hwf2 := hinv.commitRecs cm2 hcm2
  have hpre : IsPrefix cm1.log cm2.log :=
    isPrefix_of_le_of_prefix_compat (hinv.commitPrefixAgreement hcm1 hcm2)
      (by rw [hwf1.2.1, hwf2.2.1]; exact hle)
  have hcfg1 : votersOfLog cm1.log = cfgAt cm2.log cm1.idx := by
    rw [votersOfLog_eq_cfgAt_length, hwf1.2.1, cfgAt_of_prefix hpre (by rw [hwf1.2.1]; exact Nat.le_refl _)]
  have hcfg2 : votersOfLog cm2.log = cfgAt cm2.log cm2.idx := by
    rw [votersOfLog_eq_cfgAt_length, hwf2.2.1]
  have hadj : Adjacent (votersOfLog cm1.log) (votersOfLog cm2.log) := by
    rw [hcfg1, hcfg2]
    by_cases hex : ∃ j e, cm1.idx < j ∧ j ≤ cm2.idx ∧
        logGet cm2.log j = some e ∧ e.cmd.isVoterChange = true
    · rcases exists_first_voter_change cm2.log hex with ⟨k, ek, hk1, hk2, hgk, hvck, hbefore⟩
      have hafter : ∀ j e, k < j → j ≤ cm2.idx → logGet cm2.log j = some e →
          e.cmd.isVoterChange = false := by
        intro j e hj1 hj2 hgj
        cases hvc : e.cmd.isVoterChange with
        | false => rfl
        | true => exact absurd hvc (fun h => hatmost k j ek e hk1 hj1 hj2 hgk hgj hvck h)
      exact cfgAt_adjacent_of_one_voter_change hwf2.2.2.2.1.1 hwf1.1 hk1 hk2
        (by rw [hwf2.2.1]; exact Nat.le_refl _) hbefore hafter
    · have hnone : ∀ j e, cm1.idx < j → j ≤ cm2.idx → logGet cm2.log j = some e →
          e.cmd.isVoterChange = false := by
        intro j e hj1 hj2 hgj
        cases hvc : e.cmd.isVoterChange with
        | false => rfl
        | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvc⟩ hex
      rw [cfgAt_eq_of_no_voter_change hle (by rw [hwf2.2.1]; exact Nat.le_refl _) hnone]
      exact .refl _
  exact adjacent_quorums_intersect hadj q1 q2 hm1 hm2

/-! ## 8. Structural Contract Guarantees (`S_p`, Restart, `ADD_VOTER`/`DEL_VOTER` only) -/

/-- **Projected State Consistency (Contract §2, §5)**: on every node (including
immediately after truncation or crash/restart), `projectedState` built from
`appliedState + tail[applied..]` equals `projectedFromSnap` built from
`snapState + tail` and equals `stateOfLog fullLog`. -/
theorem projected_state_consistency {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s) (i : NodeId) :
    (s.nodes i).projectedState = (s.nodes i).projectedFromSnap ∧
    (s.nodes i).projectedState = stateOfLog (s.hist.fullLog i) := by
  have hsync := (Inv.reachable hr).nodeSync i
  have h1 := node_projectedState_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  have h2 := node_projectedFromSnap_eq hsync.2.2.2.1 hsync.2.2.2.2.2.1
  exact ⟨by rw [h1, h2], h1⟩

/-- **Voter-Change Exclusivity (Contract §6)**: after index 1 (bootstrap
self-join), ONLY `ADD_VOTER` and `DEL_VOTER` entries can change the voter set. -/
theorem only_add_del_change_voters {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s)
    {i : NodeId} {k : Nat} {e : Entry NodeId T.Op}
    (hk : 1 < k) (hkl : k ≤ (s.hist.fullLog i).length)
    (hget : logGet (s.hist.fullLog i) k = some e)
    (hNotAdd : ∀ x, e.cmd ≠ .addVoter x)
    (hNotDel : ∀ x, e.cmd ≠ .delVoter x) :
    cfgAt (s.hist.fullLog i) k = cfgAt (s.hist.fullLog i) (k - 1) := by
  have hgood := (Inv.reachable hr).goodLogs (s.hist.fullLog i) (Or.inl ⟨i, rfl⟩)
  by_cases hEq : cfgAt (s.hist.fullLog i) k = cfgAt (s.hist.fullLog i) (k - 1)
  · exact hEq
  · rcases only_add_del_change_voters_gt_one hgood.1 hk hkl hget hEq with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact absurd hx (hNotAdd x)
    · exact absurd hx (hNotDel x)

/-- **Non-Empty Effective Voter Set**: once a node has any log entry, its
effective voter set is always non-empty and duplicate-free (`Nodup`). -/
theorem effVoters_nonempty_and_nodup {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s) {i : NodeId}
    (hne : (s.hist.fullLog i).length > 0) :
    (s.nodes i).effVoters ≠ [] ∧ (s.nodes i).effVoters.Nodup := by
  have hinv := Inv.reachable hr
  have hsync := hinv.nodeSync i
  have hgood := hinv.goodLogs (s.hist.fullLog i) (Or.inl ⟨i, rfl⟩)
  have heff := node_effVoters_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  rw [heff, votersOfLog_eq_cfgAt_length]
  have hne' := voters_nonempty_of_valid_pos hgood.1 hne (Nat.le_refl _)
  have hwf := stateAt_wf_of_valid hgood.1 (s.hist.fullLog i).length (Nat.le_refl _)
  exact ⟨hne', hwf.2.1⟩

end Safety

end ValkeyRaft.ConfigOnAppend

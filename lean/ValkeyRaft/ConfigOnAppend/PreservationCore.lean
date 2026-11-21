/-
  Inductive invariant preservation for the 4 core transitions:
  * (6)  `becomeLeader` (via `leader_completeness_step` + `election_safety_step`)
  * (10) `advanceCommit` (via `CommitWF` + `leader_completeness_step`)
  * (8)  `handleAppendEntries` (via `mergeFrom_spec` + `commit_accepted_compat` + `same_term_log_compat`)
  * (15) `handleInstallSnapshot` (via `commitPrefixAgreement` + `same_term_log_compat`)

  Together with `PreservationBasic.lean`, this proves:
  * `Inv.step : Inv boot s → Step boot s s' → Inv boot s'`
  * `Inv.reachable : Reachable boot s → Inv boot s`

  Zero `sorry`, zero new axioms, core Lean 4 only (no Mathlib).
-/
import ValkeyRaft.ConfigOnAppend.PreservationBasic

namespace ValkeyRaft.ConfigOnAppend

set_option linter.unusedSectionVars false

section PreservationCore

variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

/-! ## 1. Small Core Helpers -/

theorem isMajority_filter_mem {α : Type} [DecidableEq α] (cfg : List α) (p : α → Bool)
    (hmaj : IsMajority cfg p) :
    IsMajority cfg (fun v => decide (v ∈ cfg.filter p)) := by
  unfold IsMajority ValkeyRaft.Quorum.IsMajority at hmaj ⊢
  have hfeq : cfg.filter (fun v => decide (v ∈ cfg.filter p)) = cfg.filter p := by
    have haux : ∀ (l : List α), (∀ x ∈ l, x ∈ cfg) →
        l.filter (fun v => decide (v ∈ cfg.filter p)) = l.filter p := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a t ih =>
        have ha : a ∈ cfg := hl a List.mem_cons_self
        have ht := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        have hda : decide (a ∈ cfg.filter p) = p a := by
          cases hpa : p a with
          | true => simp [List.mem_filter, ha, hpa]
          | false => simp [List.mem_filter, hpa]
        simp only [List.filter_cons, hda, ht]
    exact haux cfg (fun _ hx => hx)
  rw [hfeq]; exact hmaj

theorem mergeFrom_eq_left_of_prefix {Op : Type} {xs ys : List (Entry NodeId Op)}
    (hp : IsPrefix ys xs) : mergeFrom xs ys = xs := by
  induction xs generalizing ys with
  | nil =>
    have hlen := hp.1; simp at hlen
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h2 := hp.2
      simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at h2
      have hxy : x = y := h2.1
      subst hxy
      unfold mergeFrom
      simp only [beq_self_eq_true, ↓reduceIte]
      have hsub : IsPrefix ys xs :=
        ⟨by have := hp.1; simp at this; omega, h2.2⟩
      rw [ih hsub]

theorem logLastTerm_take_le {Op : Type} {L : List (Entry NodeId Op)}
    (hmono : LogMonotone L) {n : Nat} (hn : n ≤ L.length) :
    logLastTerm (L.take n) ≤ logLastTerm L := by
  cases n with
  | zero => simp [logLastTerm, logTermAt_zero]
  | succ m =>
    unfold logLastTerm
    rw [List.length_take, Nat.min_eq_left hn, logTermAt_take L (Nat.le_refl _)]
    exact hmono.2 (m + 1) L.length (by omega) hn (Nat.le_refl _)

theorem logTermAt_le_logLastTerm {Op : Type} {L : List (Entry NodeId Op)}
    (hmono : LogMonotone L) {k : Nat} (hk : k ≤ L.length) :
    logTermAt L k ≤ logLastTerm L := by
  cases k with
  | zero => simp [logTermAt_zero]
  | succ m =>
    unfold logLastTerm
    exact hmono.2 (m + 1) L.length (by omega) hk (Nat.le_refl _)

theorem isPrefix_of_le_of_prefix_compat {α : Type} {A B : List α}
    (hcompat : IsPrefix A B ∨ IsPrefix B A) (hle : A.length ≤ B.length) :
    IsPrefix A B := by
  rcases hcompat with hAB | hBA
  · exact hAB
  · have heq : B = A := hBA.eq_of_length_eq (by have := hBA.1; omega)
    rw [heq]; exact IsPrefix.refl _

theorem prefix_compat_of_common_super {α : Type} {A B C : List α}
    (hA : IsPrefix A C) (hB : IsPrefix B C) :
    IsPrefix A B ∨ IsPrefix B A := by
  by_cases hle : A.length ≤ B.length
  · left; refine ⟨hle, ?_⟩
    rw [hB.take_eq_of_le hle, hA.2]
  · right; refine ⟨by omega, ?_⟩
    rw [hA.take_eq_of_le (by omega), hB.2]

theorem prefix_compat_take_left {α : Type} {A B : List α} (k : Nat)
    (h : IsPrefix A B ∨ IsPrefix B A) :
    IsPrefix (A.take k) B ∨ IsPrefix B (A.take k) := by
  rcases h with hAB | hBA
  · exact Or.inl (IsPrefix.trans (IsPrefix.take_left A k) hAB)
  · exact prefix_compat_of_common_super (IsPrefix.take_left A k) hBA

theorem drop_take_eq_take_drop {α : Type} (L : List α) (p n : Nat) :
    (L.take (p + n)).drop p = (L.drop p).take n := by
  rw [List.drop_take]
  congr 1; omega

/-! ## 2. Transition (6): `becomeLeader` -/

theorem Inv.preserve_becomeLeader {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {c : NodeId}
    (hCand : (s.nodes c).role = .candidate)
    (hQuorum : IsMajority (s.nodes c).effVoters (fun v => decide (v ∈ (s.nodes c).votes))) :
    Inv boot (nextBecomeLeader s c) := by
  have hsync := hinv.nodeSync c
  have hc := hinv.candidateNode c hCand
  let n := s.nodes c
  let t := n.term
  let L := s.hist.fullLog c
  let cfg := n.effVoters
  let Q := cfg.filter (fun v => decide (v ∈ n.votes))
  let erNew : ElectionRec NodeId T :=
    { term := t, leader := c, elecLog := L, elecCfg := cfg, elecQuorum := Q }
  have hkn_L : IsKnownLog s L := Or.inl ⟨c, rfl⟩
  have hgood_L : GoodLog boot s L := hinv.goodLogs L hkn_L
  have heff : cfg = votersOfLog L :=
    node_effVoters_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  have hMajQ : IsMajority cfg (fun v => decide (v ∈ Q)) :=
    isMajority_filter_mem cfg (fun v => decide (v ∈ n.votes)) hQuorum
  have hSubQ : ∀ v ∈ Q, v ∈ cfg := fun v hv => (List.mem_filter.mp hv).1
  have hWF_new : ElectionWF boot s erNew :=
    ⟨hc.1, hgood_L, hc.2.2.1, heff, hMajQ, hSubQ⟩
  -- Step 1: Leader Completeness for `erNew` over all commits of term < t (strong induction on term, then idx).
  have hlc_new : ∀ cm ∈ s.hist.commits, cm.term < t → IsPrefix cm.log L := by
    have hstrong : ∀ (boundT : Nat), ∀ cm ∈ s.hist.commits, cm.term < boundT → cm.term < t →
        IsPrefix cm.log L := by
      intro boundT
      induction boundT with
      | zero => intro cm _ hlt; omega
      | succ bt ihT =>
        have hinner : ∀ (boundI : Nat), ∀ cm ∈ s.hist.commits,
            cm.term = bt → cm.idx < boundI → cm.term < t → IsPrefix cm.log L := by
          intro boundI
          induction boundI with
          | zero => intro cm _ _ hlt; omega
          | succ bi ihI =>
            intro cm hcm hcmt hcmi hlt
            refine leader_completeness_step hinv (hinv.commitRecs cm hcm) hWF_new
              ⟨cm.log, Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩)), IsPrefix.refl _⟩ hkn_L hlt
              (fun er' her' h1 _ => hinv.leaderCompleteness cm hcm er' her' h1)
              (fun cm' hcm' hlt' => ?_)
              (fun v hv => ?_)
            · rcases hlt' with hltT | ⟨heqT, hltI⟩
              · exact ihT cm' hcm' (by omega) (by omega)
              · exact ihI cm' hcm' (by omega) (by omega) (by omega)
            · have hv_mem : v ∈ n.votes := by
                have := (List.mem_filter.mp hv).2
                simpa using this
              rcases hc.2.2.2.2 v hv_mem with ⟨vr, hvr, hvrt, hvrv, hvrc, hup⟩
              refine ⟨vr, hvr, hvrt, hvrv, hvrc, hup, Or.inr ?_⟩
              intro er_same her_same hts
              exact hinv.leaderCompleteness cm hcm er_same her_same (by dsimp [erNew, t, n] at hts hlt; omega)
        intro cm hcm hltB hlt
        by_cases heq : cm.term = bt
        · exact hinner (cm.idx + 1) cm hcm heq (by omega) hlt
        · exact ihT cm hcm (by omega) hlt
    intro cm hcm hlt
    exact hstrong (cm.term + 1) cm hcm (by omega) hlt
  -- Step 2: Election Safety — no existing election record can have term = t.
  have hno_same_er : ∀ er ∈ s.hist.elected, er.term ≠ t := by
    intro er her hter
    have hrec := hinv.electionRecs er her
    have her_gt1 : er.term > 1 := by have := hc.1; dsimp [t, n] at hter ⊢; omega
    have hWF_er : ElectionWF boot s er :=
      ⟨her_gt1, hinv.goodLogs er.elecLog (Or.inr (Or.inl ⟨er, her, rfl⟩)),
       (hrec.2.2.2.2.2.2 her_gt1).1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1⟩
    have hv_new : ∀ v ∈ erNew.elecQuorum,
        ∃ vr ∈ s.hist.votes, vr.term = erNew.term ∧ vr.voter = v ∧ vr.cand = erNew.leader := by
      intro v hv
      have hv_mem : v ∈ n.votes := by
        have := (List.mem_filter.mp hv).2; simpa using this
      rcases hc.2.2.2.2 v hv_mem with ⟨vr, hvr, hvrt, hvrv, hvrc, _⟩
      exact ⟨vr, hvr, hvrt, hvrv, hvrc⟩
    have hv_er : ∀ v ∈ er.elecQuorum,
        ∃ vr ∈ s.hist.votes, vr.term = er.term ∧ vr.voter = v ∧ vr.cand = er.leader := by
      intro v hv
      rcases (hrec.2.2.2.2.2.2 her_gt1).2 v hv with ⟨vr, hvr, hvrt, hvrv, hvrc, _, _⟩
      exact ⟨vr, hvr, hvrt, hvrv, hvrc⟩
    have hlead_eq := (election_safety_step hinv hWF_new hWF_er hkn_L
      (Or.inr (Or.inl ⟨er, her, rfl⟩)) hter.symm hlc_new
      (fun cm hcm hlt => hinv.leaderCompleteness cm hcm er her hlt) hv_new hv_er).2
    exact hc.2.2.2.1 er her hter hlead_eq.symm
  -- Step 3: Consequences of `hno_same_er`: no existing commit/vote-hadLeader/entry in term t.
  have hno_same_cm : ∀ cm ∈ s.hist.commits, cm.term ≠ t := by
    intro cm hcm hcmt
    rcases (hinv.commitRecs cm hcm).2.2.2.2.2.2.1 with ⟨er, her, hter, _⟩
    exact hno_same_er er her (by omega)
  have hno_had_leader : ∀ vr ∈ s.hist.votes, vr.term = t → vr.hadLeaderInTerm = false := by
    intro vr hvr hvrt
    cases hhad : vr.hadLeaderInTerm with
    | false => rfl
    | true =>
      rcases (hinv.voteRecs vr hvr).2.2.2.2.2 hhad with ⟨er, her, hter⟩
      exact absurd (by omega) (hno_same_er er her)
  have hno_entry_t : ∀ M k, IsKnownLog s M → 1 ≤ k → k ≤ M.length → logTermAt M k ≠ t := by
    intro M k hkn hk1 hkl htk
    rcases (hinv.goodLogs M hkn).2.2.2.2 k hk1 hkl with ⟨er, her, hter, _⟩
    exact hno_same_er er her (by omega)
  have hkn_eq : ∀ M, IsKnownLog (nextBecomeLeader s c) M ↔ IsKnownLog s M := by
    intro M
    constructor
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · rcases List.mem_cons.mp her with rfl | her'
        · exact hkn_L
        · exact Or.inr (Or.inl ⟨er, her', rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · by_cases hic : i = c
        · rw [hic] at ha; simp only [nextBecomeLeader, fnUpd_same, List.mem_cons] at ha
          rcases ha with heq | ha'
          · injection heq with _ hM; exact hM ▸ hkn_L
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, t', ha'⟩))))
        · simp only [nextBecomeLeader, fnUpd_other _ _ hic] at ha
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨er, List.mem_cons_of_mem _ her, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ?_⟩))))
        by_cases hic : i = c
        · rw [hic] at ha ⊢; simp only [nextBecomeLeader, fnUpd_same, List.mem_cons]; exact Or.inr ha
        · simp only [nextBecomeLeader, fnUpd_other _ _ hic]; exact ha
  have hacc_mono : ∀ v p, p ∈ s.hist.accepted v → p ∈ (nextBecomeLeader s c).hist.accepted v := by
    intro v p hp
    dsimp only [nextBecomeLeader]
    by_cases hvc : v = c
    · rw [hvc] at hp ⊢; simp only [fnUpd_same, List.mem_cons]; exact Or.inr hp
    · simp only [fnUpd_other _ _ hvc]; exact hp
  have hterm_all : ∀ x, ((nextBecomeLeader s c).nodes x).term = (s.nodes x).term := fun x => by
    by_cases hx : x = c
    · rw [hx]; simp [nextBecomeLeader]
    · simp [nextBecomeLeader, hx]
  have hvf_all : ∀ x, ((nextBecomeLeader s c).nodes x).votedFor = (s.nodes x).votedFor := fun x => by
    by_cases hx : x = c
    · rw [hx]; simp [nextBecomeLeader]
    · simp [nextBecomeLeader, hx]
  refine
    { nodeSync := fun i => by
        by_cases hi : i = c
        · rw [hi]; simpa [nextBecomeLeader] using hsync
        · simpa [nextBecomeLeader, hi] using hinv.nodeSync i
      leaderNode := fun l hL => by
        by_cases hl : l = c
        · rw [hl]
          simp only [nextBecomeLeader, fnUpd_same]
          refine ⟨by have := hc.1; omega, hc.2.1, List.mem_cons_self, ?_, ?_, ?_, ?_⟩
          · refine ⟨erNew, List.mem_cons_self, rfl, rfl, IsPrefix.refl _, ?_⟩
            intro j hj1 hj2; dsimp [erNew, L] at hj1; omega
          · intro v hv; simp at hv
          · intro hcpos htc
            exact absurd htc (hno_entry_t L n.commit hkn_L hcpos hsync.2.2.1)
          · intro cm hcm hcmt
            exact absurd hcmt (hno_same_cm cm hcm)
        · simp only [nextBecomeLeader, fnUpd_other _ _ hl] at hL ⊢
          have hln := hinv.leaderNode l hL
          refine ⟨hln.1, hln.2.1, hln.2.2.1, ?_, ?_, hln.2.2.2.2.2.1, hln.2.2.2.2.2.2⟩
          · rcases hln.2.2.2.1 with ⟨er, her, hrest⟩
            exact ⟨er, List.mem_cons_of_mem _ her, hrest⟩
          · intro v hv
            rcases hln.2.2.2.2.1 v hv with ⟨hle, ha⟩
            exact ⟨hle, hacc_mono v _ ha⟩
      candidateNode := fun x hx => by
        by_cases hxc : x = c
        · rw [hxc] at hx; simp [nextBecomeLeader] at hx
        · simp only [nextBecomeLeader, fnUpd_other _ _ hxc] at hx ⊢
          have hcx := hinv.candidateNode x hx
          refine ⟨hcx.1, hcx.2.1, hcx.2.2.1, ?_, hcx.2.2.2.2⟩
          intro er her hter
          rcases List.mem_cons.mp her with rfl | her'
          · exact Ne.symm hxc
          · exact hcx.2.2.2.1 er her' hter
      votedForRec := fun i cand h => by
        rw [hterm_all i]; rw [hvf_all i] at h; exact hinv.votedForRec i cand h
      nodeCommit := fun i hi => by
        by_cases h : i = c
        · rw [h] at hi ⊢; simpa [nextBecomeLeader] using hinv.nodeCommit c (by simpa [nextBecomeLeader] using hi)
        · simpa [nextBecomeLeader, h] using hinv.nodeCommit i (by simpa [nextBecomeLeader, h] using hi)
      nodeSnap := fun i hi => by
        by_cases h : i = c
        · rw [h] at hi ⊢; simpa [nextBecomeLeader] using hinv.nodeSnap c (by simpa [nextBecomeLeader] using hi)
        · simpa [nextBecomeLeader, h] using hinv.nodeSnap i (by simpa [nextBecomeLeader, h] using hi)
      goodLogs := fun M hkn =>
        GoodLog.mono (s := s) (s' := nextBecomeLeader s c)
          (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) (hinv.goodLogs M ((hkn_eq M).mp hkn))
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix L1 L2 i1 i2 ((hkn_eq L1).mp h1) ((hkn_eq L2).mp h2)
      leaderMaxTerm := fun l M k hL hkn hk1 hkl ht => by
        by_cases hl : l = c
        · rw [hl] at ht
          simp only [nextBecomeLeader, fnUpd_same] at ht
          exact absurd ht (hno_entry_t M k ((hkn_eq M).mp hkn) hk1 hkl)
        · simp only [nextBecomeLeader, fnUpd_other _ _ hl] at hL ht ⊢
          exact hinv.leaderMaxTerm l M k hL ((hkn_eq M).mp hkn) hk1 hkl ht
      voteRecs := fun vr hvr => by
        have hv := hinv.voteRecs vr hvr
        rw [hterm_all boot, hterm_all vr.voter, hterm_all vr.cand, hvf_all vr.voter]
        refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, fun hhad => ?_⟩
        rcases hv.2.2.2.2.2 hhad with ⟨er, her, hter⟩
        exact ⟨er, List.mem_cons_of_mem _ her, hter⟩
      voteUnique := hinv.voteUnique
      electionUnique := fun er1 h1 er2 h2 ht => by
        rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
        · rfl
        · exact absurd ht.symm (hno_same_er er2 h2')
        · exact absurd ht (hno_same_er er1 h1')
        · exact hinv.electionUnique er1 h1' er2 h2' ht
      electionRecs := fun er her => by
        rcases List.mem_cons.mp her with rfl | her'
        · refine ⟨by have := hc.1; dsimp [erNew, t, n]; omega,
            by rw [hterm_all c]; exact Nat.le_refl _,
            heff, hMajQ, hSubQ,
            fun h1 => by have := hc.1; dsimp [erNew, t, n] at h1; omega,
            fun _ => ⟨hc.2.2.1, fun v hv => ?_⟩⟩
          have hv_mem : v ∈ n.votes := by
            have := (List.mem_filter.mp hv).2; simpa using this
          rcases hc.2.2.2.2 v hv_mem with ⟨vr, hvr, hvrt, hvrv, hvrc, hup⟩
          exact ⟨vr, hvr, hvrt, hvrv, hvrc, hno_had_leader vr hvr hvrt, hup⟩
        · have hr := hinv.electionRecs er her'
          rw [hterm_all er.leader]; exact hr
      acceptedRecs := fun i t' La ha => by
        by_cases hi : i = c
        · rw [hi] at ha ⊢
          simp only [nextBecomeLeader, fnUpd_same, List.mem_cons] at ha ⊢
          rcases ha with heq | ha'
          · injection heq with ht' hLa; subst ht'; subst hLa
            exact ⟨by have := hc.1; omega, Nat.le_refl _,
              ⟨erNew, Or.inl rfl, rfl, Or.inl (IsPrefix.refl _)⟩,
              fun P hP => Or.inl hP⟩
          · have h := hinv.acceptedRecs c t' La ha'
            refine ⟨h.1, h.2.1, ?_, ?_⟩
            · rcases h.2.2.1 with ⟨er, her, hrest⟩
              exact ⟨er, Or.inr her, hrest⟩
            · intro P hP
              rcases h.2.2.2 P hP with hpre | ⟨er, her, hrest⟩
              · exact Or.inl hpre
              · exact Or.inr ⟨er, Or.inr her, hrest⟩
        · simp only [nextBecomeLeader, fnUpd_other _ _ hi] at ha ⊢
          have h := hinv.acceptedRecs i t' La ha
          refine ⟨h.1, h.2.1, ?_, ?_⟩
          · rcases h.2.2.1 with ⟨er, her, hrest⟩
            exact ⟨er, List.mem_cons_of_mem _ her, hrest⟩
          · intro P hP
            rcases h.2.2.2 P hP with hpre | ⟨er, her, hrest⟩
            · exact Or.inl hpre
            · exact Or.inr ⟨er, List.mem_cons_of_mem _ her, hrest⟩
      acceptedBeforeVote := fun vr hvr t' La ha hlt P hP => by
        have hv_old : (t', La) ∈ s.hist.accepted vr.voter := by
          by_cases hvc : vr.voter = c
          · rw [hvc] at ha
            simp only [nextBecomeLeader, fnUpd_same, List.mem_cons] at ha
            rcases ha with heq | ha'
            · injection heq with ht' _; subst ht'
              have := (hinv.voteRecs vr hvr).2.2.1; rw [hvc] at this; omega
            · rwa [hvc]
          · simp only [nextBecomeLeader, fnUpd_other _ _ hvc] at ha; exact ha
        rcases hinv.acceptedBeforeVote vr hvr t' La hv_old hlt P hP with hpre | ⟨er, her, hrest⟩
        · exact Or.inl hpre
        · exact Or.inr ⟨er, List.mem_cons_of_mem _ her, hrest⟩
      commitRecs := fun cm hcm =>
        CommitWF.mono (s := s) (s' := nextBecomeLeader s c)
          (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) hacc_mono
          (hinv.commitRecs cm hcm)
      leaderCompleteness := fun cm hcm er her hlt => by
        rcases List.mem_cons.mp her with rfl | her'
        · exact hlc_new cm hcm hlt
        · exact hinv.leaderCompleteness cm hcm er her' hlt
      reqVoteMsg := fun t' x v ci ct hm => by
        have h := hinv.reqVoteMsg t' x v ci ct hm
        refine ⟨h.1, by rw [hterm_all boot]; exact h.2.1, by rw [hterm_all x]; exact h.2.2.1, ?_⟩
        intro ht' hC
        by_cases hx : x = c
        · rw [hx] at hC; simp [nextBecomeLeader] at hC
        · simp only [nextBecomeLeader, fnUpd_other _ _ hx] at ht' hC
          exact h.2.2.2 ht' hC
      voteReplyMsg := fun t' f to hm => by
        rcases hinv.voteReplyMsg t' f to hm with ⟨vr, hvr, h1, h2, h3, h4⟩
        refine ⟨vr, hvr, h1, h2, h3, ?_⟩
        intro ht' hC
        by_cases hto : to = c
        · rw [hto] at hC; simp [nextBecomeLeader] at hC
        · simp only [nextBecomeLeader, fnUpd_other _ _ hto] at ht' hC
          exact h4 ht' hC
      aeMsg := fun t' l pi pt es lc hm => by
        rcases hinv.aeMsg t' l pi pt es lc hm with ⟨Lae, hacc, h1, h2, h3, h4, ⟨er, her, h5⟩, h6, h7⟩
        refine ⟨Lae, hacc_mono l _ hacc, h1, h2, h3, h4,
          ⟨er, List.mem_cons_of_mem _ her, h5⟩, h6, ?_⟩
        intro hL ht'
        by_cases hl : l = c
        · rw [hl] at ht'; simp only [nextBecomeLeader, fnUpd_same] at ht'
          have h5t := h5.1; exact absurd (by dsimp [t, n]; omega) (hno_same_er er her)
        · simp only [nextBecomeLeader, fnUpd_other _ _ hl] at hL ht'
          exact h7 hL ht'
      aeReplyMsg := fun t' f to mi hm hpos => by
        rcases hinv.aeReplyMsg t' f to mi hm hpos with ⟨Lack, h1, h2, ⟨er, her, h3⟩, h4⟩
        refine ⟨Lack, h1, hacc_mono f _ h2, ⟨er, List.mem_cons_of_mem _ her, h3⟩, ?_⟩
        intro hL ht'
        by_cases hto : to = c
        · rw [hto] at ht'; simp only [nextBecomeLeader, fnUpd_same] at ht'
          have h3t := h3.1; exact absurd (by dsimp [t, n]; omega) (hno_same_er er her)
        · simp only [nextBecomeLeader, fnUpd_other _ _ hto] at hL ht'
          exact h4 hL ht'
      snapMsg := fun t' l si st ss hm => by
        rcases hinv.snapMsg t' l si st ss hm with ⟨h1, h2, ⟨er, her, h3⟩⟩
        exact ⟨h1, h2, ⟨er, List.mem_cons_of_mem _ her, h3⟩⟩
      snapLogRecs := hinv.snapLogRecs }

/-! ## 3. Transition (10): `advanceCommit` -/

theorem Inv.preserve_advanceCommit {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l : NodeId} {k : Nat}
    (hLeader : (s.nodes l).role = .leader)
    (hBounds : (s.nodes l).commit < k ∧ k ≤ (s.nodes l).lastIdx)
    (hCurTerm : (s.nodes l).termAt k = (s.nodes l).term)
    (hQuorum : IsMajority (s.nodes l).effVoters
      (fun v => decide (v = l ∨ (s.nodes l).matchIdx v ≥ k))) :
    Inv boot (nextAdvanceCommit s l k) := by
  have hsync := hinv.nodeSync l
  have hL := hinv.leaderNode l hLeader
  let n := s.nodes l
  let t := n.term
  let L := s.hist.fullLog l
  let cfg := n.effVoters
  let Q := cfg.filter (fun v => decide (v = l ∨ n.matchIdx v ≥ k))
  let cmNew : CommitRec NodeId T :=
    { term := t, leader := l, idx := k, log := L.take k, cfg := cfg, quorum := Q }
  have hsnap_le_L : n.snapIdx ≤ L.length := by
    have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; dsimp [n, L]; omega
  have hlast_eq : n.lastIdx = L.length := node_lastIdx_eq hsnap_le_L hsync.2.2.2.1
  have hk_le_L : k ≤ L.length := by rw [← hlast_eq]; exact hBounds.2
  have hk_pos : k > 0 := by have := hBounds.1; omega
  have hsnap_le_k : n.snapIdx ≤ k := by
    have := hsync.1; have := hsync.2.1; have := hBounds.1; dsimp [n]; omega
  have hlog_t_k : logTermAt L k = t := by
    rw [← node_termAt_eq hsync.2.2.2.1 hsync.2.2.2.2.1 hsnap_le_k]; exact hCurTerm
  have hkn_L : IsKnownLog s L := Or.inl ⟨l, rfl⟩
  have hgood_L : GoodLog boot s L := hinv.goodLogs L hkn_L
  have heff : cfg = votersOfLog L :=
    node_effVoters_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  have hMajQ : IsMajority cfg (fun v => decide (v ∈ Q)) :=
    isMajority_filter_mem cfg (fun v => decide (v = l ∨ n.matchIdx v ≥ k)) hQuorum
  -- Step 1: Prove `CommitWF boot s cmNew`.
  have hcmNew_wf : CommitWF boot s cmNew := by
    refine ⟨hk_pos, by simp [cmNew, List.length_take, Nat.min_eq_left hk_le_L], ?_, ?_, hMajQ, ?_, ?_, ?_⟩
    · -- logLastTerm (L.take k) = t
      dsimp only [cmNew]
      unfold logLastTerm
      rw [List.length_take, Nat.min_eq_left hk_le_L, logTermAt_take L (Nat.le_refl k)]
      exact hlog_t_k
    · -- GoodLog boot s (L.take k)
      exact GoodLog.of_prefix (IsPrefix.take_left L k) hgood_L
    · -- Every voter in Q accepted some La containing L.take k in term t
      intro v hv
      have hmem := List.mem_filter.mp hv
      refine ⟨hmem.1, ?_⟩
      have hdisj : v = l ∨ n.matchIdx v ≥ k := by simpa using hmem.2
      rcases hdisj with rfl | hge
      · exact ⟨L, hL.2.2.1, IsPrefix.take_left L k⟩
      · rcases hL.2.2.2.2.1 v (by dsimp [n] at hge; omega) with ⟨hle, hacc⟩
        refine ⟨L.take (n.matchIdx v), hacc, ?_⟩
        refine ⟨by rw [List.length_take, List.length_take]; omega, ?_⟩
        rw [List.length_take, Nat.min_eq_left hk_le_L, List.take_take, Nat.min_eq_left hge]
    · -- Leader election record for term t
      rcases hL.2.2.2.1 with ⟨er, her, hter, hlead, hpre_er, hext_er⟩
      have her_le_k : er.elecLog.length ≤ k := by
        by_cases h1 : er.term = 1
        · have hb := (hinv.electionRecs er her).2.2.2.2.2.1 h1
          rw [hb.2.1]; simp; omega
        · have hgt : er.term > 1 := by have := (hinv.electionRecs er her).1; omega
          have hlt := ((hinv.electionRecs er her).2.2.2.2.2.2 hgt).1
          by_cases hle : er.elecLog.length ≤ k
          · exact hle
          · have hlt_k : k ≤ er.elecLog.length := by omega
            have ht_er : logTermAt er.elecLog k = t := by
              rw [logTermAt_of_prefix hpre_er hlt_k]; exact hlog_t_k
            have hmono_er := (hinv.goodLogs er.elecLog (Or.inr (Or.inl ⟨er, her, rfl⟩))).2.1
            have hle_last := logTermAt_le_logLastTerm hmono_er hlt_k
            dsimp [t, n] at ht_er hter; omega
      refine ⟨er, her, hter, hlead, ?_, ?_⟩
      · refine ⟨by dsimp [cmNew]; rw [List.length_take, Nat.min_eq_left hk_le_L]; exact her_le_k, ?_⟩
        dsimp [cmNew]; rw [List.take_take, Nat.min_eq_left her_le_k]; exact hpre_er.2
      · intro j hj1 hj2
        dsimp [cmNew] at hj2 ⊢
        rw [logTermAt_take L hj2]
        exact hext_er j hj1 (by dsimp [L] at hk_le_L; omega)
    · -- Config condition: either cfg = votersOfLog (L.take k) or uncommitted voter change after k
      let kvc := lastVoterChange L
      have hkvc_le : kvc ≤ L.length := lastVoterChange_le L
      by_cases hle_vc : kvc ≤ k
      · left
        dsimp only [cmNew]
        rw [heff, votersOfLog_eq_lastVoterChange, votersOfLog_eq_cfgAt_length]
        rw [List.length_take, Nat.min_eq_left hk_le_L, cfgAt_take_eq L (Nat.le_refl k)]
        exact (cfgAt_eq_of_no_voter_change hle_vc hk_le_L
          (fun j e hj1 hj2 => lastVoterChangeUpTo_none_after L L.length j e hj1 (by omega))).symm
      · right
        have hkvc_gt_k : k < kvc := by omega
        have hkvc_gt1 : kvc > 1 := by omega
        have hkvc_pos : lastVoterChangeUpTo L L.length > 0 := by change kvc > 0; omega
        rcases lastVoterChangeUpTo_is_vc L L.length hkvc_pos with ⟨evc, hgvc, hvcvc⟩
        have hgvc' : logGet L kvc = some evc := hgvc
        rcases hgood_L.2.2.2.1 kvc evc hkvc_gt1 hkvc_le hgvc' hvcvc with
          ⟨cm0, hcm0_mem, hcm0_t, hcm0_lt, hcm0_pre, hcm0_cfg, hcm0_novc⟩
        have hkvc_t : logTermAt L kvc = t := by
          have h1 := hgood_L.2.1.2 k kvc hk_pos (by omega) hkvc_le
          have h2 := logTermAt_le_logLastTerm hgood_L.2.1 hkvc_le
          have h3 : logLastTerm L ≤ t := hsync.2.2.2.2.2.2.2
          omega
        have hcm0_t_eq : cm0.term = t := by
          have hteq : evc.term = logTermAt L kvc := by simp [logTermAt, hgvc']
          omega
        have hcm0_le_comm : cm0.idx ≤ n.commit := hL.2.2.2.2.2.2 cm0 hcm0_mem hcm0_t_eq
        have hcm0_lt_k : cm0.idx < k := by have := hBounds.1; dsimp [n] at hcm0_le_comm; omega
        have hcm0_len : cm0.log.length = cm0.idx := (hinv.commitRecs cm0 hcm0_mem).2.1
        have hcm0_pre_k : IsPrefix cm0.log (L.take k) := by
          have hsub : IsPrefix cm0.log L := IsPrefix.trans hcm0_pre (IsPrefix.take_left L (kvc - 1))
          refine ⟨by rw [List.length_take, Nat.min_eq_left hk_le_L, hcm0_len]; omega, ?_⟩
          rw [List.take_take, Nat.min_eq_left (by omega)]
          exact hsub.2
        have hvoters_eq : votersOfLog (L.take k) = cfgAt L (kvc - 1) := by
          rw [votersOfLog_eq_cfgAt_length, List.length_take, Nat.min_eq_left hk_le_L,
              cfgAt_take_eq L (Nat.le_refl k)]
          exact (cfgAt_eq_of_no_voter_change (by omega) (by omega)
            (fun j e hj1 hj2 => hcm0_novc j e (by omega) (by omega))).symm
        have hcm0_cfg_eq : cm0.cfg = votersOfLog (L.take k) := by
          rw [hcm0_cfg, votersOfLog_eq_cfgAt_length, hcm0_len,
              cfgAt_of_prefix hcm0_pre_k (by omega), cfgAt_take_eq L (by omega),
              votersOfLog_eq_cfgAt_length, List.length_take, Nat.min_eq_left hk_le_L,
              cfgAt_take_eq L (Nat.le_refl k)]
          exact (cfgAt_eq_of_no_voter_change (by omega) hk_le_L
            (fun j e hj1 hj2 => hcm0_novc j e hj1 (by omega))).symm
        have hadj : Adjacent cfg (votersOfLog (L.take k)) := by
          rw [heff, votersOfLog_eq_lastVoterChange, hvoters_eq]
          exact (cfgAt_adjacent_step hgood_L.1 hkvc_gt1 hkvc_le).symm
        refine ⟨hadj.symm, cm0, hcm0_mem, hcm0_t_eq, hcm0_lt_k, hcm0_pre_k, hcm0_cfg_eq, ?_⟩
        intro j ej hj1 hj2 hgj
        dsimp [cmNew] at hj1 hj2 hgj
        rw [logGet_take L hj2] at hgj
        exact hcm0_novc j ej hj1 (by omega) hgj
  -- Step 2: Prove Leader Completeness for `cmNew` against every `er ∈ s.hist.elected` with `t < er.term`.
  have hlc_new : ∀ er ∈ s.hist.elected, t < er.term → IsPrefix cmNew.log er.elecLog := by
    have hstrong : ∀ (bound : Nat), ∀ er ∈ s.hist.elected, er.term < bound → t < er.term →
        IsPrefix cmNew.log er.elecLog := by
      intro bound
      induction bound with
      | zero => intro er _ hlt; omega
      | succ b ih =>
        intro er her hltb hlt
        have hrec := hinv.electionRecs er her
        have her_gt1 : er.term > 1 := by have := hL.1; dsimp [t, n] at hlt; omega
        have hWF_er : ElectionWF boot s er :=
          ⟨her_gt1, hinv.goodLogs er.elecLog (Or.inr (Or.inl ⟨er, her, rfl⟩)),
           (hrec.2.2.2.2.2.2 her_gt1).1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1⟩
        refine leader_completeness_step hinv hcmNew_wf hWF_er
          ⟨L, hkn_L, IsPrefix.take_left L k⟩ (Or.inr (Or.inl ⟨er, her, rfl⟩)) hlt
          (fun er' her' h1 h2 => ih er' her' (by omega) h1)
          (fun cm' hcm' hlt' => ?_)
          (fun v hv => ?_)
        · have hcm'_lt : cm'.term < er.term := by
            rcases hlt' with h1 | ⟨h2, _⟩ <;> (dsimp [cmNew, t, n] at *; omega)
          exact hinv.leaderCompleteness cm' hcm' er her hcm'_lt
        · rcases (hrec.2.2.2.2.2.2 her_gt1).2 v hv with ⟨vr, hvr, h1, h2, h3, h4, h5⟩
          exact ⟨vr, hvr, h1, h2, h3, h5, Or.inl h4⟩
    intro er her hlt
    exact hstrong (er.term + 1) er her (by omega) hlt
  -- Step 3: Known-log prefix characterization & monotonicity helpers.
  have hkn_sub : ∀ M, IsKnownLog (nextAdvanceCommit s l k) M →
      ∃ M0, IsKnownLog s M0 ∧ IsPrefix M M0 := by
    intro M h
    rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
    · exact ⟨M, Or.inl ⟨i, hi⟩, IsPrefix.refl _⟩
    · exact ⟨er.elecLog, Or.inr (Or.inl ⟨er, her, rfl⟩), IsPrefix.refl _⟩
    · rcases List.mem_cons.mp hcm with rfl | hcm'
      · exact ⟨L, hkn_L, IsPrefix.take_left L k⟩
      · exact ⟨cm.log, Or.inr (Or.inr (Or.inl ⟨cm, hcm', rfl⟩)), IsPrefix.refl _⟩
    · exact ⟨vr.voterLog, Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩))), IsPrefix.refl _⟩
    · exact ⟨p.2.2.2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))), IsPrefix.refl _⟩
    · exact ⟨M, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩)))), IsPrefix.refl _⟩
  have hterm_all : ∀ x, ((nextAdvanceCommit s l k).nodes x).term = (s.nodes x).term := fun x => by
    by_cases hx : x = l
    · rw [hx]; simp [nextAdvanceCommit]
    · simp [nextAdvanceCommit, hx]
  have hvf_all : ∀ x, ((nextAdvanceCommit s l k).nodes x).votedFor = (s.nodes x).votedFor := fun x => by
    by_cases hx : x = l
    · rw [hx]; simp [nextAdvanceCommit]
    · simp [nextAdvanceCommit, hx]
  have hrole_all : ∀ x, ((nextAdvanceCommit s l k).nodes x).role = (s.nodes x).role := fun x => by
    by_cases hx : x = l
    · rw [hx]; simp [nextAdvanceCommit]
    · simp [nextAdvanceCommit, hx]
  refine
    { nodeSync := fun i => by
        by_cases hi : i = l
        · rw [hi]; simp only [nextAdvanceCommit, fnUpd_same]
          exact ⟨hsync.1, by have := hsync.2.1; have := hBounds.1; omega, hk_le_L,
            hsync.2.2.2.1, hsync.2.2.2.2.1, hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.2.1, hsync.2.2.2.2.2.2.2⟩
        · simpa [nextAdvanceCommit, hi] using hinv.nodeSync i
      leaderNode := fun l' hL' => by
        by_cases hl' : l' = l
        · rw [hl']
          simp only [nextAdvanceCommit, fnUpd_same]
          refine ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, ?_, ?_⟩
          · intro _ _
            refine ⟨cmNew, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
            intro hnv
            have hno_after := (hasUncommittedVoterChange_false_iff
              (n := { s.nodes l with commit := k }) hsync.2.2.2.1 hsnap_le_k).mp hnv
            dsimp only [cmNew]
            rw [heff, votersOfLog_eq_cfgAt_length, votersOfLog_eq_cfgAt_length,
                List.length_take, Nat.min_eq_left hk_le_L, cfgAt_take_eq L (Nat.le_refl k)]
            exact cfgAt_eq_of_no_voter_change hk_le_L (Nat.le_refl _) hno_after
          · intro cm hcm hcmt
            rcases List.mem_cons.mp hcm with rfl | hcm'
            · exact Nat.le_refl _
            · have := hL.2.2.2.2.2.2 cm hcm' hcmt; have := hBounds.1; omega
        · simp only [nextAdvanceCommit, fnUpd_other _ _ hl'] at hL' ⊢
          have hln := hinv.leaderNode l' hL'
          refine ⟨hln.1, hln.2.1, hln.2.2.1, hln.2.2.2.1, hln.2.2.2.2.1, ?_, ?_⟩
          · intro hc htc
            rcases hln.2.2.2.2.2.1 hc htc with ⟨cm, hcm, hrest⟩
            exact ⟨cm, List.mem_cons_of_mem _ hcm, hrest⟩
          · intro cm hcm hcmt
            rcases List.mem_cons.mp hcm with rfl | hcm'
            · rcases hln.2.2.2.1 with ⟨er', her', hter', hlead', _⟩
              rcases hL.2.2.2.1 with ⟨er, her, hter, hlead, _⟩
              have heq := hinv.electionUnique er' her' er her (by dsimp [cmNew, t, n] at hcmt; omega)
              have hll' : l' = l := by rw [← hlead', ← hlead, heq]
              exact absurd hll' hl'
            · exact hln.2.2.2.2.2.2 cm hcm' hcmt
      candidateNode := fun c hc => by
        rw [hrole_all c] at hc
        by_cases hcl : c = l
        · rw [hcl, hLeader] at hc; cases hc
        · simp only [nextAdvanceCommit, fnUpd_other _ _ hcl]
          exact hinv.candidateNode c hc
      votedForRec := fun i cand h => by
        rw [hterm_all i]; rw [hvf_all i] at h; exact hinv.votedForRec i cand h
      nodeCommit := fun i hi => by
        by_cases hil : i = l
        · rw [hil]; simp only [nextAdvanceCommit, fnUpd_same]
          exact ⟨cmNew, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, IsPrefix.refl _⟩
        · simp only [nextAdvanceCommit, fnUpd_other _ _ hil] at hi ⊢
          rcases hinv.nodeCommit i hi with ⟨cm, hcm, hrest⟩
          exact ⟨cm, List.mem_cons_of_mem _ hcm, hrest⟩
      nodeSnap := fun i hi => by
        by_cases hil : i = l
        · rw [hil] at hi ⊢; simp only [nextAdvanceCommit, fnUpd_same] at hi ⊢
          rcases hinv.nodeSnap l hi with ⟨cm, hcm, hrest⟩
          exact ⟨cm, List.mem_cons_of_mem _ hcm, hrest⟩
        · simp only [nextAdvanceCommit, fnUpd_other _ _ hil] at hi ⊢
          rcases hinv.nodeSnap i hi with ⟨cm, hcm, hrest⟩
          exact ⟨cm, List.mem_cons_of_mem _ hcm, hrest⟩
      goodLogs := fun M hkn => by
        rcases hkn_sub M hkn with ⟨M0, hM0, hpre⟩
        exact (GoodLog.of_prefix hpre (hinv.goodLogs M0 hM0)).mono
          (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix_sub (hkn_sub L1 h1) (hkn_sub L2 h2)
      leaderMaxTerm := fun l' M j hL' hkn hj1 hjl ht => by
        rw [hrole_all l'] at hL'; rw [hterm_all l'] at ht
        rcases hkn_sub M hkn with ⟨M0, hM0, hpre⟩
        rw [logTermAt_of_prefix hpre hjl] at ht
        rcases hinv.leaderMaxTerm l' M0 j hL' hM0 hj1 (Nat.le_trans hjl hpre.1) ht with ⟨hle, htk⟩
        exact ⟨hle, by rw [hpre.take_eq_of_le hjl]; exact htk⟩
      voteRecs := fun vr hvr => by
        have hv := hinv.voteRecs vr hvr
        rw [hterm_all boot, hterm_all vr.voter, hterm_all vr.cand, hvf_all vr.voter]
        exact hv
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        rw [hterm_all er.leader]; exact hr
      acceptedRecs := fun i t' La ha => by
        have h := hinv.acceptedRecs i t' La ha
        rw [hterm_all i]; exact h
      acceptedBeforeVote := hinv.acceptedBeforeVote
      commitRecs := fun cm hcm => by
        rcases List.mem_cons.mp hcm with rfl | hcm'
        · exact CommitWF.mono (s := s) (s' := nextAdvanceCommit s l k)
            (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (fun _ _ h => h) hcmNew_wf
        · exact CommitWF.mono (s := s) (s' := nextAdvanceCommit s l k)
            (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (fun _ _ h => h)
            (hinv.commitRecs cm hcm')
      leaderCompleteness := fun cm hcm er her hlt => by
        rcases List.mem_cons.mp hcm with rfl | hcm'
        · exact hlc_new er her hlt
        · exact hinv.leaderCompleteness cm hcm' er her hlt
      reqVoteMsg := fun t' x v ci ct hm => by
        have h := hinv.reqVoteMsg t' x v ci ct hm
        rw [hterm_all boot, hterm_all x, hrole_all x]; exact h
      voteReplyMsg := fun t' f to hm => by
        rcases hinv.voteReplyMsg t' f to hm with ⟨vr, h1, h2, h3, h4, h5⟩
        refine ⟨vr, h1, h2, h3, h4, ?_⟩
        rw [hterm_all to, hrole_all to]; exact h5
      aeMsg := fun t' l' pi pt es lc hm => by
        rcases hinv.aeMsg t' l' pi pt es lc hm with ⟨Lae, h1, h2, h3, h4, h5, h6, h7, h8⟩
        refine ⟨Lae, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
        · intro hlc
          rcases h7 hlc with ⟨hle, cm, hcm, hrest⟩
          exact ⟨hle, cm, List.mem_cons_of_mem _ hcm, hrest⟩
        · rw [hrole_all l', hterm_all l']; exact h8
      aeReplyMsg := fun t' f to mi hm hpos => by
        rcases hinv.aeReplyMsg t' f to mi hm hpos with ⟨Lack, h1, h2, h3, h4⟩
        refine ⟨Lack, h1, h2, h3, ?_⟩
        rw [hrole_all to, hterm_all to]; exact h4
      snapMsg := fun t' l' si st ss hm => by
        rcases hinv.snapMsg t' l' si st ss hm with ⟨h1, ⟨sLog, hs1, cm, hcm, hs2⟩, h3⟩
        exact ⟨h1, ⟨sLog, hs1, cm, List.mem_cons_of_mem _ hcm, hs2⟩, h3⟩
      snapLogRecs := fun si st ss sl hm => by
        rcases hinv.snapLogRecs si st ss sl hm with ⟨h1, h2, h3, h4, ⟨cm, hcm, h5⟩⟩
        exact ⟨h1, h2, h3, h4, ⟨cm, List.mem_cons_of_mem _ hcm, h5⟩⟩ }

/-! ## 4. Transition (8): `handleAppendEntries` -/

theorem Inv.preserve_handleAppendEntries {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {f l : NodeId} {t prevIdx prevTerm leaderCommit : Nat}
    {entries : List (Entry NodeId T.Op)}
    (hMsg : Msg.appendEntries t l prevIdx prevTerm entries leaderCommit ∈ s.net)
    (hTerm : t > (s.nodes f).term ∨ (t = (s.nodes f).term ∧ (s.nodes f).role ≠ .leader)) :
    Inv boot (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries) := by
  rcases hinv.aeMsg t l prevIdx prevTerm entries leaderCommit hMsg with
    ⟨Lae, hLae_acc, hLae_len, hLae_prevT, hLae_entries, hLae_lastT,
     ⟨erAe, herAe_mem, herAe_t, herAe_lead, herAe_pre⟩, hLae_comm, hLae_leadPre⟩
  have hLae_rec := hinv.acceptedRecs l t Lae hLae_acc
  have ht_pos : t > 0 := hLae_rec.1
  have hLae_ext : IsPrefix Lae erAe.elecLog ∨
      (IsPrefix erAe.elecLog Lae ∧ ∀ j, erAe.elecLog.length < j → j ≤ Lae.length → logTermAt Lae j = t) := by
    rcases hLae_rec.2.2.1 with ⟨er1, her1, hter1, hext1⟩
    have heq := hinv.electionUnique er1 her1 erAe herAe_mem (by omega)
    subst heq; exact hext1
  have hkn_Lae : IsKnownLog s Lae := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, t, hLae_acc⟩))))
  have hgood_Lae : GoodLog boot s Lae := hinv.goodLogs Lae hkn_Lae
  have hsync := hinv.nodeSync f
  let n := s.nodes f
  let Lf := s.hist.fullLog f
  have hkn_Lf : IsKnownLog s Lf := Or.inl ⟨f, rfl⟩
  have ht_ge : t ≥ n.term := by rcases hTerm with h | ⟨h, _⟩ <;> (dsimp [n]; omega)
  have hsnap_le_Lf : n.snapIdx ≤ Lf.length := by
    have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; dsimp [n, Lf]; omega
  have happ_le_Lf : n.applied ≤ Lf.length := by
    have := hsync.2.1; have := hsync.2.2.1; dsimp [n, Lf]; omega
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
      Lf.take prevIdx ++ mergeFrom (Lf.drop prevIdx) entries
    else Lf
  let Lae_v := Lae.take verified
  have hLae_v_len : Lae_v.length = verified := by
    dsimp [Lae_v, verified]; rw [List.length_take, Nat.min_eq_left hLae_len]
  have hstep_term : stepped.term = t := by
    dsimp [stepped]
    by_cases hgt : t > n.term
    · simp [hgt]
    · simp [hgt]; omega
  have hstep_role : stepped.role = .follower := by
    dsimp [stepped]; split <;> rfl
  have hstep_fields : stepped.snapIdx = n.snapIdx ∧ stepped.applied = n.applied ∧
      stepped.commit = n.commit ∧ stepped.tail = n.tail ∧ stepped.snapTerm = n.snapTerm ∧
      stepped.snapState = n.snapState ∧ stepped.appliedState = n.appliedState := by
    dsimp [stepped]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hn'_term : n'.term = t := by dsimp [n']; split <;> exact hstep_term
  have hn'_role : n'.role = .follower := by dsimp [n']; split <;> exact hstep_role
  have hn'_vf : n'.votedFor = stepped.votedFor := by dsimp [n']; split <;> rfl
  have hn'_snap : n'.snapIdx = n.snapIdx ∧ n'.snapTerm = n.snapTerm ∧
      n'.snapState = n.snapState ∧ n'.applied = n.applied ∧ n'.appliedState = n.appliedState := by
    dsimp [n']; split <;> exact ⟨hstep_fields.1, hstep_fields.2.2.2.2.1,
      hstep_fields.2.2.2.2.2.1, hstep_fields.2.1, hstep_fields.2.2.2.2.2.2⟩
  have hstep_lastIdx : stepped.lastIdx = Lf.length :=
    node_lastIdx_eq (by rw [hstep_fields.1]; exact hsnap_le_Lf)
      (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
  have hstep_termAt : ∀ k, n.snapIdx ≤ k → stepped.termAt k = logTermAt Lf k := fun k hk =>
    node_termAt_eq (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
      (by rw [hstep_fields.2.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.2.1)
      (by rw [hstep_fields.1]; exact hk)
  -- Core characterization of `full'` when `ok = true`.
  have hok_char : ok = true →
      (n.snapIdx ≤ prevIdx ∧ prevIdx ≤ Lf.length ∧ logTermAt Lf prevIdx = prevTerm) ∧
      (Lf.take prevIdx = Lae.take prevIdx) ∧
      (entries = Lae_v.drop prevIdx) ∧
      ((full' = Lf ∧ IsPrefix Lae_v Lf) ∨ full' = Lae_v) ∧
      (full'.take verified = Lae_v) ∧
      (IsPrefix Lae_v full') ∧
      (n.commit ≤ full'.length ∧ full'.take n.commit = Lf.take n.commit) ∧
      (logLastTerm full' ≤ t) ∧
      (full' ≠ Lf → ¬ IsPrefix Lae_v Lf) := by
    intro hok
    have hcond : stepped.snapIdx ≤ prevIdx ∧ prevIdx ≤ stepped.lastIdx ∧
        stepped.termAt prevIdx = prevTerm := by
      dsimp [ok] at hok; exact of_decide_eq_true hok
    have hsnap_prev : n.snapIdx ≤ prevIdx := by rw [← hstep_fields.1]; exact hcond.1
    have hprev_len : prevIdx ≤ Lf.length := by rw [← hstep_lastIdx]; exact hcond.2.1
    have hprev_t : logTermAt Lf prevIdx = prevTerm := by
      rw [← hstep_termAt prevIdx hsnap_prev]; exact hcond.2.2
    have htake_prev : Lf.take prevIdx = Lae.take prevIdx := by
      cases prevIdx with
      | zero => simp
      | succ pm =>
        exact hinv.sameTermPrefix Lf Lae (pm + 1) (pm + 1) hkn_Lf hkn_Lae
          (by omega) hprev_len (by omega) (by omega) (by omega) (Nat.le_refl _)
    have hentries_eq : entries = Lae_v.drop prevIdx := by
      dsimp [Lae_v, verified]
      rw [drop_take_eq_take_drop, hLae_entries]
    have hmatch : ∀ (i : Nat) (h1 : i < (Lf.drop prevIdx).length) (h2 : i < entries.length),
        ((Lf.drop prevIdx)[i]'h1).term = (entries[i]'h2).term →
        (Lf.drop prevIdx).take (i + 1) = entries.take (i + 1) := by
      intro i h1 h2 hti
      have h1' : prevIdx + i < Lf.length := by rw [List.length_drop] at h1; omega
      have h2' : prevIdx + i < Lae.length := by omega
      have hterm_f : logTermAt Lf (prevIdx + i + 1) = ((Lf.drop prevIdx)[i]'h1).term := by
        rw [logTermAt, logGet_pos Lf (by omega), Nat.add_sub_cancel, List.getElem?_eq_getElem h1']
        simp [List.getElem_drop]
      have hterm_ae : logTermAt Lae (prevIdx + i + 1) = (entries[i]'h2).term := by
        have he_get : (entries[i]'h2) = Lae[prevIdx + i]'h2' := by
          have : entries[i]? = some (Lae[prevIdx + i]'h2') := by
            rw [hentries_eq]; dsimp [Lae_v, verified]
            rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem h2']
          rw [List.getElem?_eq_getElem h2] at this; injection this
        rw [he_get, logTermAt, logGet_pos Lae (by omega), Nat.add_sub_cancel,
            List.getElem?_eq_getElem h2']
      have htk := hinv.sameTermPrefix Lf Lae (prevIdx + i + 1) (prevIdx + i + 1)
        hkn_Lf hkn_Lae (by omega) (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _)
      have hdrop_tk : (Lf.take (prevIdx + (i + 1))).drop prevIdx =
          (Lae.take (prevIdx + (i + 1))).drop prevIdx := by
        have : prevIdx + (i + 1) = prevIdx + i + 1 := by omega
        rw [this, htk]
      rw [drop_take_eq_take_drop, drop_take_eq_take_drop] at hdrop_tk
      rw [hdrop_tk, ← hLae_entries, List.take_take, Nat.min_eq_left (by omega)]
    have hmerge := mergeFrom_spec (Lf.drop prevIdx) entries hmatch
    have hfull_def : full' = Lf.take prevIdx ++ mergeFrom (Lf.drop prevIdx) entries := by
      dsimp [full']; simp [hok]
    have hLae_v_split : Lf.take prevIdx ++ entries = Lae_v := by
      rw [htake_prev, hentries_eq]
      dsimp [Lae_v, verified]
      have : Lae.take prevIdx = (Lae.take (prevIdx + entries.length)).take prevIdx := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [this, List.take_append_drop]
    have hcases : (full' = Lf ∧ IsPrefix Lae_v Lf) ∨ full' = Lae_v := by
      rcases hmerge with ⟨hleft, hpre_ent⟩ | hright
      · left
        have hfeq : full' = Lf := by rw [hfull_def, hleft, List.take_append_drop]
        refine ⟨hfeq, ?_⟩
        rw [← hLae_v_split]
        refine ⟨by rw [List.length_append, List.length_take, Nat.min_eq_left hprev_len]
                   have := hpre_ent.1; rw [List.length_drop] at this; omega, ?_⟩
        rw [List.length_append, List.length_take, Nat.min_eq_left hprev_len]
        have hlen_ent : entries.length ≤ Lf.length - prevIdx := by
          have := hpre_ent.1; rwa [List.length_drop] at this
        have hsplit_Lf : Lf.take (prevIdx + entries.length) =
            Lf.take prevIdx ++ (Lf.drop prevIdx).take entries.length := by
          have h1 : (Lf.take (prevIdx + entries.length)).take prevIdx = Lf.take prevIdx := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          have h2 : (Lf.take (prevIdx + entries.length)).drop prevIdx = (Lf.drop prevIdx).take entries.length :=
            drop_take_eq_take_drop Lf prevIdx entries.length
          rw [← h1, ← h2, List.take_append_drop]
        rw [hsplit_Lf, hpre_ent.2]
      · right; rw [hfull_def, hright, hLae_v_split]
    have hnot_pre_of_ne : full' ≠ Lf → ¬ IsPrefix Lae_v Lf := by
      intro hne hpre
      have hpre_ent : IsPrefix entries (Lf.drop prevIdx) := by
        rw [hentries_eq]
        refine ⟨by rw [List.length_drop, List.length_drop, hLae_v_len]; have := hpre.1; rw [hLae_v_len] at this; omega, ?_⟩
        rw [List.length_drop, hLae_v_len, ← drop_take_eq_take_drop,
            show prevIdx + (verified - prevIdx) = verified by dsimp [verified]; omega,
            ← hLae_v_len, hpre.2]
      have hfeq : full' = Lf := by
        rw [hfull_def, mergeFrom_eq_left_of_prefix hpre_ent, List.take_append_drop]
      exact hne hfeq
    have hpre_v_full : IsPrefix Lae_v full' := by
      rcases hcases with ⟨hfeq, hpre⟩ | hfeq
      · rwa [hfeq]
      · rw [hfeq]; exact IsPrefix.refl _
    have htake_v : full'.take verified = Lae_v := by
      rw [← hLae_v_len]; exact hpre_v_full.2
    have hcomm_pres : n.commit ≤ full'.length ∧ full'.take n.commit = Lf.take n.commit := by
      by_cases hfeq : full' = Lf
      · rw [hfeq]; exact ⟨hsync.2.2.1, rfl⟩
      · have hfull_v : full' = Lae_v := by
          rcases hcases with ⟨h1, _⟩ | h2
          · exact absurd h1 hfeq
          · exact h2
        by_cases hc0 : n.commit = 0
        · rw [hc0]; simp
        · rcases hinv.nodeCommit f (by dsimp [n] at hc0; omega) with ⟨cm, hcm, hcm_t, hcm_idx, hcm_pre⟩
          have hcompat_cm := hinv.commit_accepted_compat hcm (by dsimp [n] at ht_ge; omega) hLae_acc
          have hcompat_v : IsPrefix cm.log Lae_v ∨ IsPrefix Lae_v cm.log :=
            (prefix_compat_take_left verified hcompat_cm.symm).symm
          have hcompat_c : IsPrefix (Lf.take n.commit) Lae_v ∨ IsPrefix Lae_v (Lf.take n.commit) := by
            rcases hcompat_v with h1 | h2
            · exact Or.inl (IsPrefix.trans hcm_pre h1)
            · exact prefix_compat_of_common_super hcm_pre h2
          have hlt_v : n.commit ≤ verified := by
            by_cases hle : n.commit ≤ verified
            · exact hle
            · have hpre_vc : IsPrefix Lae_v (Lf.take n.commit) :=
                isPrefix_of_le_of_prefix_compat hcompat_c.symm
                  (by rw [hLae_v_len, List.length_take, Nat.min_eq_left hsync.2.2.1]; dsimp [n] at *; omega)
              exact absurd (IsPrefix.trans hpre_vc (IsPrefix.take_left Lf n.commit))
                (hnot_pre_of_ne hfeq)
          have hpre_cv : IsPrefix (Lf.take n.commit) Lae_v :=
            isPrefix_of_le_of_prefix_compat hcompat_c
              (by rw [hLae_v_len, List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hlt_v)
          rw [hfull_v]
          refine ⟨by rw [hLae_v_len]; exact hlt_v, ?_⟩
          have h2 := hpre_cv.2
          rw [List.length_take, Nat.min_eq_left hsync.2.2.1] at h2
          exact h2
    have hlast_t : logLastTerm full' ≤ t := by
      rcases hcases with ⟨hfeq, _⟩ | hfeq
      · rw [hfeq]; have := hsync.2.2.2.2.2.2.2; dsimp [Lf, n] at *; omega
      · rw [hfeq]
        have h1 := logLastTerm_take_le hgood_Lae.2.1 hLae_len
        dsimp [Lae_v, verified]; omega
    exact ⟨⟨hsnap_prev, hprev_len, hprev_t⟩, htake_prev, hentries_eq, hcases,
           htake_v, hpre_v_full, hcomm_pres, hlast_t, hnot_pre_of_ne⟩
  -- Known logs in `s'` are all prefixes of known logs in `s`.
  have hkn_sub : ∀ M, IsKnownLog (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries) M →
      ∃ M0, IsKnownLog s M0 ∧ IsPrefix M M0 := by
    intro M h
    rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
    · by_cases hif : i = f
      · rw [hif] at hi; simp only [nextHandleAppendEntries, fnUpd_same] at hi
        change M = full' at hi; subst hi
        cases hok : ok with
        | false =>
          have : full' = Lf := by dsimp [full']; simp [hok]
          rw [this]; exact ⟨Lf, hkn_Lf, IsPrefix.refl _⟩
        | true =>
          rcases (hok_char hok).2.2.2.1 with ⟨hfeq, _⟩ | hfeq
          · rw [hfeq]; exact ⟨Lf, hkn_Lf, IsPrefix.refl _⟩
          · rw [hfeq]; exact ⟨Lae, hkn_Lae, IsPrefix.take_left Lae verified⟩
      · simp only [nextHandleAppendEntries, fnUpd_other _ _ hif] at hi
        exact ⟨M, Or.inl ⟨i, hi⟩, IsPrefix.refl _⟩
    · exact ⟨er.elecLog, Or.inr (Or.inl ⟨er, her, rfl⟩), IsPrefix.refl _⟩
    · exact ⟨cm.log, Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩)), IsPrefix.refl _⟩
    · exact ⟨vr.voterLog, Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩))), IsPrefix.refl _⟩
    · exact ⟨p.2.2.2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))), IsPrefix.refl _⟩
    · dsimp only [nextHandleAppendEntries] at ha
      cases hok : ok with
      | false =>
        have ha' : (t', M) ∈ s.hist.accepted i := by
          change (t', M) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) i at ha
          rw [hok] at ha; simpa using ha
        exact ⟨M, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha'⟩)))), IsPrefix.refl _⟩
      | true =>
        have ha' : (t', M) ∈ fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) i := by
          change (t', M) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) i at ha
          rw [hok] at ha; simpa using ha
        by_cases hif : i = f
        · rw [hif, fnUpd_same, List.mem_cons] at ha'
          rcases ha' with heq | ha''
          · injection heq with _ hM
            rw [hM, (hok_char hok).2.2.2.2.1]
            exact ⟨Lae, hkn_Lae, IsPrefix.take_left Lae verified⟩
          · exact ⟨M, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, t', ha''⟩)))), IsPrefix.refl _⟩
        · rw [fnUpd_other _ _ hif] at ha'
          exact ⟨M, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha'⟩)))), IsPrefix.refl _⟩
  have hacc_mono : ∀ v p, p ∈ s.hist.accepted v →
      p ∈ (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries).hist.accepted v := by
    intro v p hp
    change p ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) v
    cases hok : ok with
    | false => simpa using hp
    | true =>
      simp only [↓reduceIte]
      by_cases hvf : v = f
      · rw [hvf] at hp ⊢; simp only [fnUpd_same, List.mem_cons]; exact Or.inr hp
      · simp only [fnUpd_other _ _ hvf]; exact hp
  have hnodes_f : (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries).nodes f = n' := by
    simp only [nextHandleAppendEntries, fnUpd_same, n', ok, newTail, newCommit, offset, verified, stepped, n]
  have hfull_f : (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries).hist.fullLog f = full' := by
    simp only [nextHandleAppendEntries, fnUpd_same, full', ok, stepped, Lf, n]
  -- Helper: when `full' ≠ Lf`, any prefix `P` of `(t_a, La) ∈ accepted f` that was a prefix of `Lf`
  -- but is NOT a prefix of `full'` has `t_a < t` and `¬ IsPrefix P erAe.elecLog`.
  have htrunc_witness : ∀ (t_a : Nat) (La P : List (Entry NodeId T.Op)),
      ok = true → full' ≠ Lf → (t_a, La) ∈ s.hist.accepted f → IsPrefix P La →
      IsPrefix P Lf → ¬ IsPrefix P full' →
      t_a < erAe.term ∧ erAe.term ≤ t ∧ ¬ IsPrefix P erAe.elecLog := by
    intro t_a La P hok hne ha hPLa hPLf hnotP
    have hch := hok_char hok
    have hfull_v : full' = Lae_v := by
      rcases hch.2.2.2.1 with ⟨h1, _⟩ | h2
      · exact absurd h1 hne
      · exact h2
    have hta_le : t_a ≤ n.term := (hinv.acceptedRecs f t_a La ha).2.1
    have hta_lt : t_a < t := by
      by_cases hlt : t_a < t
      · exact hlt
      · have heq : t_a = t := by omega
        rcases (hinv.acceptedRecs f t_a La ha).2.2.1 with ⟨er1, her1, hter1, hLa_ext⟩
        have her_eq := hinv.electionUnique er1 her1 erAe herAe_mem (by omega)
        subst er1
        have hLa_ext' : IsPrefix La erAe.elecLog ∨
            (IsPrefix erAe.elecLog La ∧ ∀ j, erAe.elecLog.length < j → j ≤ La.length → logTermAt La j = t) := by
          simpa [heq] using hLa_ext
        have hcompat := hinv.same_term_log_compat
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, t_a, ha⟩))))) hkn_Lae hLa_ext' hLae_ext
        have hcompat_P : IsPrefix P Lae ∨ IsPrefix Lae P := by
          rcases hcompat with h1 | h2
          · exact Or.inl (IsPrefix.trans hPLa h1)
          · exact prefix_compat_of_common_super hPLa h2
        have hcompat_Pv : IsPrefix P Lae_v ∨ IsPrefix Lae_v P :=
          (prefix_compat_take_left verified hcompat_P.symm).symm
        rcases hcompat_Pv with h1 | h2
        · rw [hfull_v] at hnotP; exact absurd h1 hnotP
        · exact absurd (IsPrefix.trans h2 hPLf) (hch.2.2.2.2.2.2.2.2 hne)
    have hnot_er : ¬ IsPrefix P erAe.elecLog := by
      intro hPer
      have hPLae : IsPrefix P Lae := IsPrefix.trans hPer herAe_pre
      have hcompat_Pv : IsPrefix P Lae_v ∨ IsPrefix Lae_v P :=
        prefix_compat_of_common_super hPLae (IsPrefix.take_left Lae verified)
      rcases hcompat_Pv with h1 | h2
      · rw [hfull_v] at hnotP; exact absurd h1 hnotP
      · exact absurd (IsPrefix.trans h2 hPLf) (hch.2.2.2.2.2.2.2.2 hne)
    exact ⟨by omega, by omega, hnot_er⟩
  refine
    { nodeSync := fun i => by
        by_cases hif : i = f
        · rw [hif, hnodes_f, hfull_f]
          cases hok : ok with
          | false =>
            have hn'_eq : n' = stepped := by dsimp [n']; simp [hok]
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hok]
            rw [hn'_eq, hfull'_eq]
            dsimp only
            rw [hstep_term, hstep_fields.1, hstep_fields.2.1,
                hstep_fields.2.2.1, hstep_fields.2.2.2.1, hstep_fields.2.2.2.2.1,
                hstep_fields.2.2.2.2.2.1, hstep_fields.2.2.2.2.2.2]
            exact ⟨hsync.1, hsync.2.1, hsync.2.2.1, hsync.2.2.2.1, hsync.2.2.2.2.1,
              hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.2.1, by have := hsync.2.2.2.2.2.2.2; dsimp [Lf, n] at *; omega⟩
          | true =>
            have hch := hok_char hok
            have htail_eq : n'.tail = full'.drop n'.snapIdx := by
              rw [hn'_snap.1]
              have hnt : n'.tail = newTail := by dsimp [n']; simp [hok]
              have hft : full' = Lf.take prevIdx ++ mergeFrom (Lf.drop prevIdx) entries := by
                dsimp [full']; simp [hok]
              rw [hnt, hft, drop_take_append_merge Lf entries hch.1.1 hch.1.2.1]
              dsimp [newTail, offset]
              rw [hstep_fields.2.2.2.1, hstep_fields.1, hsync.2.2.2.1]
            have hcomm_eq : n'.commit = max n.commit (min leaderCommit verified) := by
              dsimp [n', newCommit]; simp [hok, hstep_fields.2.2.1]
            have hcomm_le : n'.commit ≤ full'.length := by
              rw [hcomm_eq]
              have h1 := hch.2.2.2.2.2.2.1.1
              have h2 : verified ≤ full'.length := by
                have := hch.2.2.2.2.2.1.1; rwa [hLae_v_len] at this
              omega
            have hpre_comm : IsPrefix (Lf.take n.commit) full' := by
              refine ⟨by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hch.2.2.2.2.2.2.1.1, ?_⟩
              rw [List.length_take, Nat.min_eq_left hsync.2.2.1, hch.2.2.2.2.2.2.1.2]
            dsimp only
            refine ⟨by rw [hn'_snap.1, hn'_snap.2.2.2.1]; exact hsync.1,
                    by rw [hn'_snap.2.2.2.1, hcomm_eq]; have := hsync.2.1; dsimp [n]; omega,
                    hcomm_le, htail_eq, ?_, ?_, ?_, by rw [hn'_term]; exact hch.2.2.2.2.2.2.2.1⟩
            · rw [hn'_snap.1, hn'_snap.2.1, hsync.2.2.2.2.1]
              have hle : n.snapIdx ≤ n.commit := by have := hsync.1; have := hsync.2.1; dsimp [n]; omega
              rw [← logTermAt_take Lf hle, logTermAt_of_prefix hpre_comm (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hle)]
            · rw [hn'_snap.1, hn'_snap.2.2.1, hsync.2.2.2.2.2.1]
              have hle : n.snapIdx ≤ n.commit := by have := hsync.1; have := hsync.2.1; dsimp [n]; omega
              rw [← stateAt_of_prefix (IsPrefix.take_left Lf n.commit) (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hle),
                  stateAt_of_prefix hpre_comm (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hle)]
            · rw [hn'_snap.2.2.2.1, hn'_snap.2.2.2.2, hsync.2.2.2.2.2.2.1]
              have hle : n.applied ≤ n.commit := hsync.2.1
              rw [← stateAt_of_prefix (IsPrefix.take_left Lf n.commit) (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hle),
                  stateAt_of_prefix hpre_comm (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; exact hle)]
        · simpa [nextHandleAppendEntries, hif] using hinv.nodeSync i
      leaderNode := fun l' hL' => by
        by_cases hl' : l' = f
        · rw [hl', hnodes_f, hn'_role] at hL'; cases hL'
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hl'] at hL' ⊢
          have hln := hinv.leaderNode l' hL'
          refine ⟨hln.1, hln.2.1, hacc_mono l' _ hln.2.2.1, hln.2.2.2.1, ?_,
            hln.2.2.2.2.2.1, hln.2.2.2.2.2.2⟩
          intro v hv
          rcases hln.2.2.2.2.1 v hv with ⟨hle, ha⟩
          exact ⟨hle, hacc_mono v _ ha⟩
      candidateNode := fun c hc => by
        by_cases hcf : c = f
        · rw [hcf, hnodes_f, hn'_role] at hc; cases hc
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hcf] at hc ⊢
          exact hinv.candidateNode c hc
      votedForRec := fun i cand hcand => by
        by_cases hif : i = f
        · rw [hif] at hcand ⊢; rw [hnodes_f] at hcand ⊢; rw [hn'_vf] at hcand; rw [hn'_term]
          by_cases hgt : t > n.term
          · dsimp [stepped] at hcand; simp [hgt] at hcand
          · have hteq : t = n.term := by omega
            have hvf_eq : stepped.votedFor = n.votedFor := by dsimp [stepped]; simp [hgt]
            rw [hvf_eq] at hcand
            rw [hteq]; exact hinv.votedForRec f cand hcand
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hif] at hcand ⊢
          exact hinv.votedForRec i cand hcand
      nodeCommit := fun i hi => by
        by_cases hif : i = f
        · rw [hif] at hi ⊢; rw [hnodes_f] at hi ⊢; rw [hfull_f, hn'_term]
          cases hok : ok with
          | false =>
            have hn'_eq : n' = stepped := by dsimp [n']; simp [hok]
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hok]
            rw [hn'_eq, hstep_fields.2.2.1] at hi ⊢
            rw [hfull'_eq]
            rcases hinv.nodeCommit f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
            exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
          | true =>
            have hch := hok_char hok
            have hcomm_eq : n'.commit = max n.commit (min leaderCommit verified) := by
              dsimp [n', newCommit]; simp [hok, hstep_fields.2.2.1]
            rw [hcomm_eq] at hi ⊢
            by_cases hle : min leaderCommit verified ≤ n.commit
            · rw [Nat.max_eq_left hle] at hi ⊢
              rw [hch.2.2.2.2.2.2.1.2]
              rcases hinv.nodeCommit f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
              exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
            · rw [Nat.max_eq_right (by omega)] at hi ⊢
              have hlc_pos : leaderCommit > 0 := by omega
              rcases hLae_comm hlc_pos with ⟨hlc_le, cm, hcm, hcmt, hge, hpre⟩
              have hmin_lc : min leaderCommit verified ≤ leaderCommit := Nat.min_le_left _ _
              have hmin_v : min leaderCommit verified ≤ verified := Nat.min_le_right _ _
              refine ⟨cm, hcm, hcmt, by omega, ?_⟩
              have hsub : full'.take (min leaderCommit verified) =
                  (Lae.take leaderCommit).take (min leaderCommit verified) := by
                have h1 : full'.take (min leaderCommit verified) =
                    (full'.take verified).take (min leaderCommit verified) := by
                  rw [List.take_take, Nat.min_eq_left hmin_v]
                rw [h1, hch.2.2.2.2.1]; dsimp [Lae_v]
                rw [List.take_take, List.take_take, Nat.min_eq_left hmin_v, Nat.min_eq_left hmin_lc]
              rw [hsub]
              exact IsPrefix.trans (IsPrefix.take_left (Lae.take leaderCommit) _) hpre
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hif] at hi ⊢
          exact hinv.nodeCommit i hi
      nodeSnap := fun i hi => by
        by_cases hif : i = f
        · rw [hif] at hi ⊢; rw [hnodes_f, hn'_snap.1] at hi ⊢; rw [hfull_f, hn'_term]
          have htake_snap : full'.take n.snapIdx = Lf.take n.snapIdx := by
            cases hok : ok with
            | false =>
              have : full' = Lf := by dsimp [full']; simp [hok]
              rw [this]
            | true =>
              have hch := hok_char hok
              have hle : n.snapIdx ≤ n.commit := by have := hsync.1; have := hsync.2.1; dsimp [n]; omega
              rw [← Nat.min_eq_left hle, ← List.take_take, hch.2.2.2.2.2.2.1.2,
                  List.take_take, Nat.min_eq_left hle]
          rw [htake_snap]
          rcases hinv.nodeSnap f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
          exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hif] at hi ⊢
          exact hinv.nodeSnap i hi
      goodLogs := fun M hkn => by
        rcases hkn_sub M hkn with ⟨M0, hM0, hpre⟩
        exact GoodLog.of_prefix hpre (hinv.goodLogs M0 hM0)
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix_sub (hkn_sub L1 h1) (hkn_sub L2 h2)
      leaderMaxTerm := fun l' M j hL' hkn hj1 hjl ht => by
        by_cases hl' : l' = f
        · rw [hl', hnodes_f, hn'_role] at hL'; cases hL'
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hl'] at hL' ht ⊢
          rcases hkn_sub M hkn with ⟨M0, hM0, hpre⟩
          rw [logTermAt_of_prefix hpre hjl] at ht
          rcases hinv.leaderMaxTerm l' M0 j hL' hM0 hj1 (Nat.le_trans hjl hpre.1) ht with ⟨hle, htk⟩
          exact ⟨hle, by rw [hpre.take_eq_of_le hjl]; exact htk⟩
      voteRecs := fun vr hvr => by
        have hv := hinv.voteRecs vr hvr
        refine ⟨hv.1, ?_, ?_, ?_, ?_, hv.2.2.2.2.2⟩
        · by_cases hb : boot = f
          · rw [hb, hnodes_f, hn'_term]; have := hv.2.1; rw [hb] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hb]; exact hv.2.1
        · by_cases hvf : vr.voter = f
          · rw [hvf, hnodes_f, hn'_term]; have := hv.2.2.1; rw [hvf] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hvf]; exact hv.2.2.1
        · by_cases hcf : vr.cand = f
          · rw [hcf, hnodes_f, hn'_term]; have := hv.2.2.2.1; rw [hcf] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hcf]; exact hv.2.2.2.1
        · by_cases hvf : vr.voter = f
          · rw [hvf, hnodes_f, hn'_term, hn'_vf]
            intro hteq
            have hle : vr.term ≤ (s.nodes f).term := by have := hv.2.2.1; rwa [hvf] at this
            have hft : (s.nodes f).term = vr.term :=
              Nat.le_antisymm (hteq ▸ ht_ge) hle
            have hngt : ¬ t > n.term := fun hgt => Nat.lt_irrefl _ (by
              have h1 : (s.nodes f).term < t := hgt
              rw [hft, hteq] at h1; exact h1)
            have hvfeq : stepped.votedFor = n.votedFor := by dsimp [stepped]; simp [hngt]
            rw [hvfeq]
            have hres := hv.2.2.2.2.1 (by rw [hvf]; exact hft)
            rwa [hvf] at hres
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hvf]; exact hv.2.2.2.2.1
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        refine ⟨hr.1, ?_, hr.2.2⟩
        by_cases hl' : er.leader = f
        · rw [hl', hnodes_f, hn'_term]; have := hr.2.1; rw [hl'] at this; dsimp [n] at ht_ge; omega
        · simp only [nextHandleAppendEntries, fnUpd_other _ _ hl']; exact hr.2.1
      acceptedRecs := fun i t' La ha => by
        by_cases hif : i = f
        · rw [hif] at ha ⊢
          rw [hnodes_f, hfull_f, hn'_term]
          cases hok : ok with
          | false =>
            have ha' : (t', La) ∈ s.hist.accepted f := by
              change (t', La) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) f at ha
              rw [hok] at ha; simpa using ha
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hok]
            rw [hfull'_eq]
            have h := hinv.acceptedRecs f t' La ha'
            refine ⟨h.1, by dsimp [n] at ht_ge; omega, h.2.2.1, fun P hP => ?_⟩
            rcases h.2.2.2 P hP with hp | ⟨er, her, h1, h2, h3⟩
            · exact Or.inl hp
            · exact Or.inr ⟨er, her, h1, by dsimp [n] at ht_ge; omega, h3⟩
          | true =>
            have hch := hok_char hok
            have ha' : (t', La) ∈ (t, full'.take verified) :: s.hist.accepted f := by
              change (t', La) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) f at ha
              rw [hok] at ha; simp only [↓reduceIte, fnUpd_same] at ha; exact ha
            rcases List.mem_cons.mp ha' with heq | ha''
            · injection heq with ht' hLa; subst ht'; subst hLa
              rw [hch.2.2.2.2.1]
              refine ⟨ht_pos, Nat.le_refl _,
                ⟨erAe, herAe_mem, herAe_t, termExt_of_prefix (IsPrefix.take_left Lae verified) hLae_ext⟩,
                fun P hP => Or.inl (IsPrefix.trans hP hch.2.2.2.2.2.1)⟩
            · have h := hinv.acceptedRecs f t' La ha''
              refine ⟨h.1, by dsimp [n] at ht_ge; omega, h.2.2.1, fun P hP => ?_⟩
              rcases h.2.2.2 P hP with hp | ⟨er, her, h1, h2, h3⟩
              · by_cases hPf : IsPrefix P full'
                · exact Or.inl hPf
                · have hne : full' ≠ Lf := fun heq => hPf (heq ▸ hp)
                  rcases htrunc_witness t' La P hok hne ha'' hP hp hPf with ⟨w1, w2, w3⟩
                  exact Or.inr ⟨erAe, herAe_mem, w1, w2, w3⟩
              · exact Or.inr ⟨er, her, h1, by dsimp [n] at ht_ge; omega, h3⟩
        · have ha' : (t', La) ∈ s.hist.accepted i := by
            change (t', La) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) i at ha
            cases hok : ok with
            | false => rw [hok] at ha; simpa using ha
            | true => rw [hok] at ha; simp only [↓reduceIte, fnUpd_other _ _ hif] at ha; exact ha
          simp only [nextHandleAppendEntries, fnUpd_other _ _ hif]
          exact hinv.acceptedRecs i t' La ha'
      acceptedBeforeVote := fun vr hvr t' La ha hlt P hP => by
        have ha_old : (t', La) ∈ s.hist.accepted vr.voter := by
          change (t', La) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) vr.voter at ha
          cases hok : ok with
          | false => rw [hok] at ha; simpa using ha
          | true =>
            rw [hok] at ha; simp only [↓reduceIte] at ha
            by_cases hvf : vr.voter = f
            · rw [hvf, fnUpd_same, List.mem_cons] at ha
              rcases ha with heq | ha'
              · injection heq with ht' _; subst ht'
                have := (hinv.voteRecs vr hvr).2.2.1; rw [hvf] at this; dsimp [n] at ht_ge; omega
              · rwa [hvf]
            · rw [fnUpd_other _ _ hvf] at ha; exact ha
        exact hinv.acceptedBeforeVote vr hvr t' La ha_old hlt P hP
      commitRecs := fun cm hcm =>
        CommitWF.mono (s := s) (s' := nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries)
          (fun _ h => h) (fun _ h => h) hacc_mono (hinv.commitRecs cm hcm)
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t' x v ci ct hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · have h := hinv.reqVoteMsg t' x v ci ct hm'
          refine ⟨h.1, ?_, ?_, ?_⟩
          · by_cases hb : boot = f
            · rw [hb, hnodes_f, hn'_term]; have := h.2.1; rw [hb] at this; dsimp [n] at ht_ge; omega
            · simp only [nextHandleAppendEntries, fnUpd_other _ _ hb]; exact h.2.1
          · by_cases hx : x = f
            · rw [hx, hnodes_f, hn'_term]; have := h.2.2.1; rw [hx] at this; dsimp [n] at ht_ge; omega
            · simp only [nextHandleAppendEntries, fnUpd_other _ _ hx]; exact h.2.2.1
          · by_cases hx : x = f
            · rw [hx, hnodes_f, hn'_role]; intro _ hC; cases hC
            · simp only [nextHandleAppendEntries, fnUpd_other _ _ hx]; exact h.2.2.2
      voteReplyMsg := fun t' fromId toId hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.voteReplyMsg t' fromId toId hm' with ⟨vr, h1, h2, h3, h4, h5⟩
          refine ⟨vr, h1, h2, h3, h4, ?_⟩
          by_cases hto : toId = f
          · rw [hto, hnodes_f, hn'_role]; intro _ hC; cases hC
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hto]; exact h5
      aeMsg := fun t' l' pi pt es lc hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.aeMsg t' l' pi pt es lc hm' with ⟨Lae', h1, h2, h3, h4, h5, h6, h7, h8⟩
          refine ⟨Lae', hacc_mono l' _ h1, h2, h3, h4, h5, h6, h7, ?_⟩
          by_cases hl' : l' = f
          · rw [hl', hnodes_f, hn'_role]; intro hL'; cases hL'
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hl']; exact h8
      aeReplyMsg := fun t' fromId toId mi hm hpos => by
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with ht' hf' hl' hok' hmi'
          subst t'; subst fromId; subst toId
          have hok : ok = true := hok'.symm
          have hmi_eq : mi = verified := by
            change mi = (if ok then verified else 0) at hmi'
            rw [hmi', hok]; rfl
          have hch := hok_char hok
          refine ⟨Lae_v, by rw [hmi_eq]; exact hLae_v_len, ?_,
            ⟨erAe, herAe_mem, herAe_t, herAe_lead⟩, ?_⟩
          · change (t, Lae_v) ∈ (if ok then fnUpd s.hist.accepted f ((t, full'.take verified) :: s.hist.accepted f) else s.hist.accepted) f
            rw [hok]; simp only [↓reduceIte, fnUpd_same, hch.2.2.2.2.1]; exact List.mem_cons_self
          · intro hL' htL
            by_cases hlf : l = f
            · have hnl : (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries).nodes l = n' := by
                simp only [nextHandleAppendEntries, hlf, fnUpd_same, n', ok, newTail, newCommit, offset, verified, stepped, n]
              rw [hnl, hn'_role] at hL'; cases hL'
            · simp only [nextHandleAppendEntries, fnUpd_other _ _ hlf] at hL' htL ⊢
              exact IsPrefix.trans (IsPrefix.take_left Lae verified) (hLae_leadPre hL' htL)
        · rcases hinv.aeReplyMsg t' fromId toId mi hm' hpos with ⟨Lack, h1, h2, h3, h4⟩
          refine ⟨Lack, h1, hacc_mono fromId _ h2, h3, ?_⟩
          by_cases hto : toId = f
          · rw [hto, hnodes_f, hn'_role]; intro hL'; cases hL'
          · simp only [nextHandleAppendEntries, fnUpd_other _ _ hto]; exact h4
      snapMsg := fun t' l' si st ss hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.snapMsg t' l' si st ss hm'
      snapLogRecs := hinv.snapLogRecs }

/-! ## 5. Transition (15): `handleInstallSnapshot` -/

theorem Inv.preserve_handleInstallSnapshot {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {f l : NodeId} {t sIdx sTerm : Nat} {sState : ClusterState T}
    {sLog : List (Entry NodeId T.Op)}
    (hMsg : Msg.installSnapshot t l sIdx sTerm sState ∈ s.net)
    (hSnapLog : (sIdx, sTerm, sState, sLog) ∈ s.hist.snapLogs)
    (hTerm : t > (s.nodes f).term ∨ (t = (s.nodes f).term ∧ (s.nodes f).role ≠ .leader)) :
    Inv boot (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog) := by
  rcases hinv.snapMsg t l sIdx sTerm sState hMsg with
    ⟨hsIdx_pos, ⟨_, _, cmSn, hcmSn_mem, hcmSn_t, hcmSn_idx, _⟩,
     ⟨erSn, herSn_mem, herSn_t, herSn_lead⟩⟩
  rcases hinv.snapLogRecs sIdx sTerm sState sLog hSnapLog with
    ⟨_, hsLog_len, hsLog_lastT_eq, hsLog_state, ⟨cmS, hcmS_mem, hcmS_idx, hcmS_pre⟩⟩
  have hsLog_term : logTermAt sLog sIdx = sTerm := by
    rw [← hsLog_len]; exact hsLog_lastT_eq
  have ht_pos : t > 0 := by have := (hinv.electionRecs erSn herSn_mem).1; omega
  have hcmSn_wf := hinv.commitRecs cmSn hcmSn_mem
  have hcmSn_len : cmSn.log.length = cmSn.idx := hcmSn_wf.2.1
  -- `sLog` is a prefix of `cmSn.log` (and therefore has term ≤ t and term-ext w.r.t. `erSn`).
  have hsLog_pre_cmSn : IsPrefix sLog cmSn.log := by
    have hcompat := hinv.commitPrefixAgreement hcmS_mem hcmSn_mem
    rcases hcompat with h1 | h2
    · exact IsPrefix.trans hcmS_pre h1
    · exact isPrefix_of_le_of_prefix_compat (prefix_compat_of_common_super hcmS_pre h2)
        (by omega)
  have hsLog_lastT : logLastTerm sLog ≤ t := by
    have h1 : logLastTerm sLog ≤ logLastTerm cmSn.log := by
      rw [← hsLog_pre_cmSn.2]
      exact logLastTerm_take_le hcmSn_wf.2.2.2.1.2.1 (by omega)
    have h2 : logLastTerm cmSn.log = cmSn.term := hcmSn_wf.2.2.1
    omega
  have hsLog_ext : IsPrefix sLog erSn.elecLog ∨
      (IsPrefix erSn.elecLog sLog ∧ ∀ j, erSn.elecLog.length < j → j ≤ sLog.length → logTermAt sLog j = t) := by
    by_cases hlt : cmSn.term < t
    · exact Or.inl (IsPrefix.trans hsLog_pre_cmSn (hinv.leaderCompleteness cmSn hcmSn_mem erSn herSn_mem (by omega)))
    · have heq : cmSn.term = t := by omega
      rcases hcmSn_wf.2.2.2.2.2.2.1 with ⟨er1, her1, hter1, _, hpre1, hext1⟩
      have her_eq := hinv.electionUnique er1 her1 erSn herSn_mem (by omega)
      subst her_eq
      exact termExt_of_prefix hsLog_pre_cmSn
        (Or.inr ⟨hpre1, fun j hj1 hj2 => by rw [← heq]; exact hext1 j hj1 (by omega)⟩)
  have hkn_sLog : IsKnownLog s sLog :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(sIdx, sTerm, sState, sLog), hSnapLog, rfl⟩))))
  have hsync := hinv.nodeSync f
  let n := s.nodes f
  let Lf := s.hist.fullLog f
  have hkn_Lf : IsKnownLog s Lf := Or.inl ⟨f, rfl⟩
  have ht_ge : t ≥ n.term := by rcases hTerm with h | ⟨h, _⟩ <;> (dsimp [n]; omega)
  have hsnap_le_Lf : n.snapIdx ≤ Lf.length := by
    have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; dsimp [n, Lf]; omega
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
  let full' := if advance then if retain then Lf else sLog else Lf
  have hstep_term : stepped.term = t := by
    dsimp [stepped]
    by_cases hgt : t > n.term
    · simp [hgt]
    · simp [hgt]; omega
  have hstep_role : stepped.role = .follower := by
    dsimp [stepped]; split <;> rfl
  have hstep_fields : stepped.snapIdx = n.snapIdx ∧ stepped.applied = n.applied ∧
      stepped.commit = n.commit ∧ stepped.tail = n.tail ∧ stepped.snapTerm = n.snapTerm ∧
      stepped.snapState = n.snapState ∧ stepped.appliedState = n.appliedState := by
    dsimp [stepped]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hn'_term : n'.term = t := by dsimp [n']; split <;> exact hstep_term
  have hn'_role : n'.role = .follower := by dsimp [n']; split <;> exact hstep_role
  have hn'_vf : n'.votedFor = stepped.votedFor := by dsimp [n']; split <;> rfl
  have hstep_lastIdx : stepped.lastIdx = Lf.length :=
    node_lastIdx_eq (by rw [hstep_fields.1]; exact hsnap_le_Lf)
      (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
  have hstep_termAt : ∀ k, n.snapIdx ≤ k → stepped.termAt k = logTermAt Lf k := fun k hk =>
    node_termAt_eq (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
      (by rw [hstep_fields.2.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.2.1)
      (by rw [hstep_fields.1]; exact hk)
  -- Key facts about the 3 branches (`advance = false`, `advance = true ∧ retain = true`, `advance = true ∧ retain = false`):
  have hpre_if_le_commit : sIdx ≤ n.commit → IsPrefix sLog Lf := by
    intro hle
    rcases hinv.nodeCommit f (by dsimp [n] at hle; omega) with ⟨cmf, hcmf, _, hcmf_idx, hcmf_pre⟩
    have hcompat := hinv.commitPrefixAgreement hcmf hcmSn_mem
    have hsLog_cmf : IsPrefix sLog cmf.log :=
      isPrefix_of_le_of_prefix_compat
        (by rcases hcompat with h1 | h2
            · exact prefix_compat_of_common_super hsLog_pre_cmSn h1
            · exact Or.inl (IsPrefix.trans hsLog_pre_cmSn h2))
        (by have := (hinv.commitRecs cmf hcmf).2.1; dsimp [n] at hle; omega)
    have hsLog_take : IsPrefix sLog (Lf.take n.commit) :=
      isPrefix_of_le_of_prefix_compat (prefix_compat_of_common_super hsLog_cmf hcmf_pre)
        (by rw [List.length_take, Nat.min_eq_left hsync.2.2.1]; dsimp [n] at hle; omega)
    exact IsPrefix.trans hsLog_take (IsPrefix.take_left Lf n.commit)
  have hretain_true_pre : advance = true → retain = true → IsPrefix sLog Lf := by
    intro hadv hret
    have hgt : sIdx > n.snapIdx := by
      dsimp [advance] at hadv; rw [hstep_fields.1] at hadv; exact of_decide_eq_true hadv
    have hcond : sIdx ≤ Lf.length ∧ logTermAt Lf sIdx = sTerm := by
      dsimp [retain] at hret
      have hc := of_decide_eq_true hret
      rw [hstep_lastIdx, hstep_termAt sIdx (by omega)] at hc
      exact hc
    have htk := hinv.sameTermPrefix sLog Lf sIdx sIdx hkn_sLog hkn_Lf
      hsIdx_pos (by omega) hsIdx_pos hcond.1 (by omega) (Nat.le_refl _)
    refine ⟨by omega, ?_⟩
    rw [hsLog_len, ← htk, ← hsLog_len, List.take_length]
  have hretain_false_not_pre : advance = true → retain = false → ¬ IsPrefix sLog Lf := by
    intro hadv hret hpre
    have hgt : sIdx > n.snapIdx := by
      dsimp [advance] at hadv; rw [hstep_fields.1] at hadv; exact of_decide_eq_true hadv
    have hlen : sIdx ≤ Lf.length := by have := hpre.1; omega
    have htm : logTermAt Lf sIdx = sTerm := by
      rw [← logTermAt_of_prefix hpre (by omega)]; exact hsLog_term
    have hret_t : retain = true := by
      dsimp [retain]
      rw [decide_eq_true_eq, hstep_lastIdx, hstep_termAt sIdx (by omega)]
      exact ⟨hlen, htm⟩
    rw [hret] at hret_t; cases hret_t
  have hretain_false_lt : advance = true → retain = false → n.commit < sIdx := by
    intro hadv hret
    by_cases hlt : n.commit < sIdx
    · exact hlt
    · exact absurd (hpre_if_le_commit (by omega)) (hretain_false_not_pre hadv hret)
  have hsLog_pre_full' : IsPrefix sLog full' := by
    cases hadv : advance with
    | false =>
      have hle : sIdx ≤ n.snapIdx := by
        dsimp [advance] at hadv; rw [hstep_fields.1] at hadv
        have := of_decide_eq_false hadv; omega
      have hfeq : full' = Lf := by dsimp [full']; simp [hadv]
      rw [hfeq]
      exact hpre_if_le_commit (by have := hsync.1; have := hsync.2.1; dsimp [n] at *; omega)
    | true =>
      cases hret : retain with
      | true =>
        have hfeq : full' = Lf := by dsimp [full']; simp [hadv, hret]
        rw [hfeq]; exact hretain_true_pre hadv hret
      | false =>
        have hfeq : full' = sLog := by dsimp [full']; simp [hadv, hret]
        rw [hfeq]; exact IsPrefix.refl _
  -- Every known log in `s'` is already a known log in `s`.
  have hkn_imp : ∀ M, IsKnownLog (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog) M → IsKnownLog s M := by
    intro M h
    rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
    · by_cases hif : i = f
      · rw [hif] at hi; simp only [nextHandleInstallSnapshot, fnUpd_same] at hi
        change M = full' at hi; subst hi
        cases hadv : advance with
        | false =>
          have hfeq : full' = Lf := by dsimp [full']; simp [hadv]
          rw [hfeq]; exact hkn_Lf
        | true =>
          cases hret : retain with
          | true =>
            have hfeq : full' = Lf := by dsimp [full']; simp [hadv, hret]
            rw [hfeq]; exact hkn_Lf
          | false =>
            have hfeq : full' = sLog := by dsimp [full']; simp [hadv, hret]
            rw [hfeq]; exact hkn_sLog
      · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at hi
        exact Or.inl ⟨i, hi⟩
    · exact Or.inr (Or.inl ⟨er, her, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
    · by_cases hif : i = f
      · rw [hif] at ha; simp only [nextHandleInstallSnapshot, fnUpd_same, List.mem_cons] at ha
        rcases ha with heq | ha'
        · injection heq with _ hM; exact hM ▸ hkn_sLog
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, t', ha'⟩))))
      · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
  have hacc_mono : ∀ v p, p ∈ s.hist.accepted v →
      p ∈ (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog).hist.accepted v := by
    intro v p hp
    dsimp only [nextHandleInstallSnapshot]
    by_cases hvf : v = f
    · rw [hvf] at hp ⊢; simp only [fnUpd_same, List.mem_cons]; exact Or.inr hp
    · simp only [fnUpd_other _ _ hvf]; exact hp
  have hnodes_f : (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog).nodes f = n' := by
    simp only [nextHandleInstallSnapshot, fnUpd_same, n', advance, retain, newTail, newApplied,
      newAppliedState, newCommit, stepped, n]
  have hfull_f : (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog).hist.fullLog f = full' := by
    simp only [nextHandleInstallSnapshot, fnUpd_same, full', advance, retain, stepped, Lf, n]
  -- Truncation witness when `advance = true ∧ retain = false` (`full' = sLog`).
  have htrunc_witness : ∀ (t_a : Nat) (La P : List (Entry NodeId T.Op)),
      advance = true → retain = false → (t_a, La) ∈ s.hist.accepted f → IsPrefix P La →
      IsPrefix P Lf → ¬ IsPrefix P sLog →
      t_a < erSn.term ∧ erSn.term ≤ t ∧ ¬ IsPrefix P erSn.elecLog := by
    intro t_a La P hadv hret ha hPLa hPLf hnotP
    have hnot_sLog : ¬ IsPrefix sLog Lf := hretain_false_not_pre hadv hret
    have hta_le : t_a ≤ n.term := (hinv.acceptedRecs f t_a La ha).2.1
    have hta_lt : t_a < t := by
      by_cases hlt : t_a < t
      · exact hlt
      · have heq : t_a = t := by omega
        rcases (hinv.acceptedRecs f t_a La ha).2.2.1 with ⟨er1, her1, hter1, hLa_ext⟩
        have her_eq := hinv.electionUnique er1 her1 erSn herSn_mem (by omega)
        subst er1
        have hLa_ext' : IsPrefix La erSn.elecLog ∨
            (IsPrefix erSn.elecLog La ∧ ∀ j, erSn.elecLog.length < j → j ≤ La.length → logTermAt La j = t) := by
          simpa [heq] using hLa_ext
        have hcompat := hinv.same_term_log_compat
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, t_a, ha⟩))))) hkn_sLog hLa_ext' hsLog_ext
        have hcompat_P : IsPrefix P sLog ∨ IsPrefix sLog P := by
          rcases hcompat with h1 | h2
          · exact Or.inl (IsPrefix.trans hPLa h1)
          · exact prefix_compat_of_common_super hPLa h2
        rcases hcompat_P with h1 | h2
        · exact absurd h1 hnotP
        · exact absurd (IsPrefix.trans h2 hPLf) hnot_sLog
    have hnot_er : ¬ IsPrefix P erSn.elecLog := by
      intro hPer
      have hcompat_er : IsPrefix sLog erSn.elecLog ∨ IsPrefix erSn.elecLog sLog := by
        rcases hsLog_ext with h1 | ⟨h2, _⟩
        · exact Or.inl h1
        · exact Or.inr h2
      have hcompat_P : IsPrefix P sLog ∨ IsPrefix sLog P := by
        rcases hcompat_er with h1 | h2
        · exact prefix_compat_of_common_super hPer h1
        · exact Or.inl (IsPrefix.trans hPer h2)
      rcases hcompat_P with h1 | h2
      · exact absurd h1 hnotP
      · exact absurd (IsPrefix.trans h2 hPLf) hnot_sLog
    exact ⟨by omega, by omega, hnot_er⟩
  refine
    { nodeSync := fun i => by
        by_cases hif : i = f
        · rw [hif, hnodes_f, hfull_f]
          cases hadv : advance with
          | false =>
            have hn'_eq : n' = stepped := by dsimp [n']; simp [hadv]
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hadv]
            rw [hn'_eq, hfull'_eq]
            dsimp only
            rw [hstep_term, hstep_fields.1, hstep_fields.2.1,
                hstep_fields.2.2.1, hstep_fields.2.2.2.1, hstep_fields.2.2.2.2.1,
                hstep_fields.2.2.2.2.2.1, hstep_fields.2.2.2.2.2.2]
            exact ⟨hsync.1, hsync.2.1, hsync.2.2.1, hsync.2.2.2.1, hsync.2.2.2.2.1,
              hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.2.1, by have := hsync.2.2.2.2.2.2.2; dsimp [Lf, n] at *; omega⟩
          | true =>
            have hgt_snap : sIdx > n.snapIdx := by
              dsimp [advance] at hadv; rw [hstep_fields.1] at hadv; exact of_decide_eq_true hadv
            cases hret : retain with
            | true =>
              have hpre_sL : IsPrefix sLog Lf := hretain_true_pre hadv hret
              have hsIdx_le_Lf : sIdx ≤ Lf.length := by have := hpre_sL.1; omega
              have hfeq : full' = Lf := by dsimp [full']; simp [hadv, hret]
              rw [hfeq]
              dsimp only
              rw [hn'_term]
              have hfields : n'.snapIdx = sIdx ∧ n'.snapTerm = sTerm ∧ n'.snapState = sState ∧
                  n'.tail = n.tail.drop (sIdx - n.snapIdx) ∧
                  n'.applied = max n.applied sIdx ∧
                  n'.appliedState = (if n.applied < sIdx then sState else n.appliedState) ∧
                  n'.commit = max n.commit sIdx := by
                dsimp [n', newTail, newApplied, newAppliedState, newCommit]
                simp [hadv, hret, hstep_fields.1, hstep_fields.2.1, hstep_fields.2.2.1,
                      hstep_fields.2.2.2.1, hstep_fields.2.2.2.2.2.2]
              rw [hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
                  hfields.2.2.2.2.1, hfields.2.2.2.2.2.1, hfields.2.2.2.2.2.2]
              have htail' : n.tail.drop (sIdx - n.snapIdx) = Lf.drop sIdx := by
                rw [hsync.2.2.2.1, List.drop_drop]
                congr 1; dsimp [n] at hgt_snap ⊢; omega
              have hsterm' : sTerm = logTermAt Lf sIdx := by
                rw [← logTermAt_of_prefix hpre_sL (by omega)]; exact hsLog_term.symm
              have hsstate' : sState = stateAt Lf sIdx := by
                rw [← stateAt_of_prefix hpre_sL (by omega), ← hsLog_len, stateAt_length]; exact hsLog_state.symm
              have hcomm_le_Lf : n.commit ≤ Lf.length := hsync.2.2.1
              refine ⟨by omega, by have := hsync.2.1; dsimp [n]; omega, by omega,
                      htail', hsterm', hsstate', ?_, by have := hsync.2.2.2.2.2.2.2; dsimp [Lf, n] at *; omega⟩
              by_cases halt : n.applied < sIdx
              · simp only [halt, ↓reduceIte, Nat.max_eq_right (by omega : n.applied ≤ sIdx)]; exact hsstate'
              · simp only [halt, ↓reduceIte, Nat.max_eq_left (by omega : sIdx ≤ n.applied)]
                exact hsync.2.2.2.2.2.2.1
            | false =>
              have hcomm_lt : n.commit < sIdx := hretain_false_lt hadv hret
              have happ_lt : n.applied < sIdx := by have := hsync.2.1; dsimp [n] at *; omega
              have hfeq : full' = sLog := by dsimp [full']; simp [hadv, hret]
              rw [hfeq]
              dsimp only
              rw [hn'_term]
              have hfields : n'.snapIdx = sIdx ∧ n'.snapTerm = sTerm ∧ n'.snapState = sState ∧
                  n'.tail = [] ∧ n'.applied = sIdx ∧ n'.appliedState = sState ∧ n'.commit = sIdx := by
                dsimp [n', newTail, newApplied, newAppliedState, newCommit]
                simp [hadv, hret, hstep_fields.2.1, hstep_fields.2.2.1, happ_lt,
                      Nat.max_eq_right (by omega : n.applied ≤ sIdx),
                      Nat.max_eq_right (by omega : n.commit ≤ sIdx)]
              rw [hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
                  hfields.2.2.2.2.1, hfields.2.2.2.2.2.1, hfields.2.2.2.2.2.2]
              have hdrop_nil : sLog.drop sIdx = [] := by
                rw [List.drop_eq_nil_iff]; omega
              have hsstate' : sState = stateAt sLog sIdx := by
                rw [← hsLog_len, stateAt_length]; exact hsLog_state.symm
              exact ⟨Nat.le_refl _, Nat.le_refl _, by omega, hdrop_nil.symm,
                hsLog_term.symm, hsstate', hsstate', hsLog_lastT⟩
        · simpa [nextHandleInstallSnapshot, hif] using hinv.nodeSync i
      leaderNode := fun l' hL' => by
        by_cases hl' : l' = f
        · rw [hl', hnodes_f, hn'_role] at hL'; cases hL'
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hl'] at hL' ⊢
          have hln := hinv.leaderNode l' hL'
          refine ⟨hln.1, hln.2.1, hln.2.2.1, hln.2.2.2.1, ?_,
            hln.2.2.2.2.2.1, hln.2.2.2.2.2.2⟩
          intro v hv
          rcases hln.2.2.2.2.1 v hv with ⟨hle, ha⟩
          exact ⟨hle, hacc_mono v _ ha⟩
      candidateNode := fun c hc => by
        by_cases hcf : c = f
        · rw [hcf, hnodes_f, hn'_role] at hc; cases hc
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hcf] at hc ⊢
          exact hinv.candidateNode c hc
      votedForRec := fun i cand hcand => by
        by_cases hif : i = f
        · rw [hif] at hcand ⊢; rw [hnodes_f] at hcand ⊢; rw [hn'_vf] at hcand; rw [hn'_term]
          by_cases hgt : t > n.term
          · dsimp [stepped] at hcand; simp [hgt] at hcand
          · have hteq : t = n.term := by omega
            have hvf_eq : stepped.votedFor = n.votedFor := by dsimp [stepped]; simp [hgt]
            rw [hvf_eq] at hcand
            rw [hteq]; exact hinv.votedForRec f cand hcand
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at hcand ⊢
          exact hinv.votedForRec i cand hcand
      nodeCommit := fun i hi => by
        by_cases hif : i = f
        · rw [hif] at hi ⊢; rw [hnodes_f] at hi ⊢; rw [hfull_f, hn'_term]
          cases hadv : advance with
          | false =>
            have hn'_eq : n' = stepped := by dsimp [n']; simp [hadv]
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hadv]
            rw [hn'_eq, hstep_fields.2.2.1] at hi ⊢
            rw [hfull'_eq]
            rcases hinv.nodeCommit f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
            exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
          | true =>
            have hcomm_eq : n'.commit = max n.commit sIdx := by
              dsimp [n', newCommit]; simp [hadv, hstep_fields.2.2.1]
            rw [hcomm_eq] at hi ⊢
            cases hret : retain with
            | true =>
              have hfeq : full' = Lf := by dsimp [full']; simp [hadv, hret]
              rw [hfeq]
              by_cases hle : sIdx ≤ n.commit
              · rw [Nat.max_eq_left hle] at hi ⊢
                rcases hinv.nodeCommit f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
                exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
              · rw [Nat.max_eq_right (by omega)]
                have hpre_sL := hretain_true_pre hadv hret
                have htk : Lf.take sIdx = sLog := by rw [← hsLog_len]; exact hpre_sL.2
                rw [htk]; exact ⟨cmSn, hcmSn_mem, hcmSn_t, hcmSn_idx, hsLog_pre_cmSn⟩
            | false =>
              have hcomm_lt := hretain_false_lt hadv hret
              have hfeq : full' = sLog := by dsimp [full']; simp [hadv, hret]
              rw [hfeq, Nat.max_eq_right (by omega)]
              have htk : sLog.take sIdx = sLog := by rw [← hsLog_len, List.take_length]
              rw [htk]
              exact ⟨cmSn, hcmSn_mem, hcmSn_t, hcmSn_idx, hsLog_pre_cmSn⟩
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at hi ⊢
          exact hinv.nodeCommit i hi
      nodeSnap := fun i hi => by
        by_cases hif : i = f
        · rw [hif] at hi ⊢; rw [hnodes_f] at hi ⊢; rw [hfull_f, hn'_term]
          cases hadv : advance with
          | false =>
            have hn'_eq : n' = stepped := by dsimp [n']; simp [hadv]
            have hfull'_eq : full' = Lf := by dsimp [full']; simp [hadv]
            rw [hn'_eq, hstep_fields.1] at hi ⊢
            rw [hfull'_eq]
            rcases hinv.nodeSnap f hi with ⟨cm, hcm, hcmt, hge, hpre⟩
            exact ⟨cm, hcm, by dsimp [n] at ht_ge; omega, hge, hpre⟩
          | true =>
            have hsnap_eq : n'.snapIdx = sIdx := by dsimp [n']; simp [hadv]
            rw [hsnap_eq]
            have htk : full'.take sIdx = sLog := by rw [← hsLog_len]; exact hsLog_pre_full'.2
            rw [htk]
            exact ⟨cmSn, hcmSn_mem, hcmSn_t, hcmSn_idx, hsLog_pre_cmSn⟩
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at hi ⊢
          exact hinv.nodeSnap i hi
      goodLogs := fun M hkn => hinv.goodLogs M (hkn_imp M hkn)
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix L1 L2 i1 i2 (hkn_imp L1 h1) (hkn_imp L2 h2)
      leaderMaxTerm := fun l' M j hL' hkn hj1 hjl ht => by
        by_cases hl' : l' = f
        · rw [hl', hnodes_f, hn'_role] at hL'; cases hL'
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hl'] at hL' ht ⊢
          exact hinv.leaderMaxTerm l' M j hL' (hkn_imp M hkn) hj1 hjl ht
      voteRecs := fun vr hvr => by
        have hv := hinv.voteRecs vr hvr
        refine ⟨hv.1, ?_, ?_, ?_, ?_, hv.2.2.2.2.2⟩
        · by_cases hb : boot = f
          · rw [hb, hnodes_f, hn'_term]; have := hv.2.1; rw [hb] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hb]; exact hv.2.1
        · by_cases hvf : vr.voter = f
          · rw [hvf, hnodes_f, hn'_term]; have := hv.2.2.1; rw [hvf] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hvf]; exact hv.2.2.1
        · by_cases hcf : vr.cand = f
          · rw [hcf, hnodes_f, hn'_term]; have := hv.2.2.2.1; rw [hcf] at this; dsimp [n] at ht_ge; omega
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hcf]; exact hv.2.2.2.1
        · by_cases hvf : vr.voter = f
          · rw [hvf, hnodes_f, hn'_term, hn'_vf]
            intro hteq
            have hle : vr.term ≤ (s.nodes f).term := by have := hv.2.2.1; rwa [hvf] at this
            have hft : (s.nodes f).term = vr.term :=
              Nat.le_antisymm (hteq ▸ ht_ge) hle
            have hngt : ¬ t > n.term := fun hgt => Nat.lt_irrefl _ (by
              have h1 : (s.nodes f).term < t := hgt
              rw [hft, hteq] at h1; exact h1)
            have hvfeq : stepped.votedFor = n.votedFor := by dsimp [stepped]; simp [hngt]
            rw [hvfeq]
            have hres := hv.2.2.2.2.1 (by rw [hvf]; exact hft)
            rwa [hvf] at hres
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hvf]; exact hv.2.2.2.2.1
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        refine ⟨hr.1, ?_, hr.2.2⟩
        by_cases hl' : er.leader = f
        · rw [hl', hnodes_f, hn'_term]; have := hr.2.1; rw [hl'] at this; dsimp [n] at ht_ge; omega
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hl']; exact hr.2.1
      acceptedRecs := fun i t' La ha => by
        by_cases hif : i = f
        · rw [hif] at ha ⊢
          rw [hnodes_f, hfull_f, hn'_term]
          simp only [nextHandleInstallSnapshot, fnUpd_same, List.mem_cons] at ha
          rcases ha with heq | ha'
          · injection heq with ht' hLa; subst ht'; subst hLa
            exact ⟨ht_pos, Nat.le_refl _, ⟨erSn, herSn_mem, herSn_t, hsLog_ext⟩,
              fun P hP => Or.inl (IsPrefix.trans hP hsLog_pre_full')⟩
          · have h := hinv.acceptedRecs f t' La ha'
            refine ⟨h.1, by dsimp [n] at ht_ge; omega, h.2.2.1, fun P hP => ?_⟩
            rcases h.2.2.2 P hP with hp | ⟨er, her, h1, h2, h3⟩
            · cases hadv : advance with
              | false =>
                have : full' = Lf := by dsimp [full']; simp [hadv]
                rw [this]; exact Or.inl hp
              | true =>
                cases hret : retain with
                | true =>
                  have : full' = Lf := by dsimp [full']; simp [hadv, hret]
                  rw [this]; exact Or.inl hp
                | false =>
                  have hfeq : full' = sLog := by dsimp [full']; simp [hadv, hret]
                  rw [hfeq]
                  by_cases hPs : IsPrefix P sLog
                  · exact Or.inl hPs
                  · rcases htrunc_witness t' La P hadv hret ha' hP hp hPs with ⟨w1, w2, w3⟩
                    exact Or.inr ⟨erSn, herSn_mem, w1, w2, w3⟩
            · exact Or.inr ⟨er, her, h1, by dsimp [n] at ht_ge; omega, h3⟩
        · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hif] at ha ⊢
          exact hinv.acceptedRecs i t' La ha
      acceptedBeforeVote := fun vr hvr t' La ha hlt P hP => by
        have ha_old : (t', La) ∈ s.hist.accepted vr.voter := by
          by_cases hvf : vr.voter = f
          · rw [hvf] at ha
            simp only [nextHandleInstallSnapshot, fnUpd_same, List.mem_cons] at ha
            rcases ha with heq | ha'
            · injection heq with ht' _; subst ht'
              have := (hinv.voteRecs vr hvr).2.2.1; rw [hvf] at this; dsimp [n] at ht_ge; omega
            · rwa [hvf]
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hvf] at ha; exact ha
        exact hinv.acceptedBeforeVote vr hvr t' La ha_old hlt P hP
      commitRecs := fun cm hcm =>
        CommitWF.mono (s := s) (s' := nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog)
          (fun _ h => h) (fun _ h => h) hacc_mono (hinv.commitRecs cm hcm)
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t' x v ci ct hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · have h := hinv.reqVoteMsg t' x v ci ct hm'
          refine ⟨h.1, ?_, ?_, ?_⟩
          · by_cases hb : boot = f
            · rw [hb, hnodes_f, hn'_term]; have := h.2.1; rw [hb] at this; dsimp [n] at ht_ge; omega
            · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hb]; exact h.2.1
          · by_cases hx : x = f
            · rw [hx, hnodes_f, hn'_term]; have := h.2.2.1; rw [hx] at this; dsimp [n] at ht_ge; omega
            · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hx]; exact h.2.2.1
          · by_cases hx : x = f
            · rw [hx, hnodes_f, hn'_role]; intro _ hC; cases hC
            · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hx]; exact h.2.2.2
      voteReplyMsg := fun t' fromId toId hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.voteReplyMsg t' fromId toId hm' with ⟨vr, h1, h2, h3, h4, h5⟩
          refine ⟨vr, h1, h2, h3, h4, ?_⟩
          by_cases hto : toId = f
          · rw [hto, hnodes_f, hn'_role]; intro _ hC; cases hC
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hto]; exact h5
      aeMsg := fun t' l' pi pt es lc hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.aeMsg t' l' pi pt es lc hm' with ⟨Lae', h1, h2, h3, h4, h5, h6, h7, h8⟩
          refine ⟨Lae', hacc_mono l' _ h1, h2, h3, h4, h5, h6, h7, ?_⟩
          by_cases hl' : l' = f
          · rw [hl', hnodes_f, hn'_role]; intro hL'; cases hL'
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hl']; exact h8
      aeReplyMsg := fun t' fromId toId mi hm hpos => by
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with ht' hf' hl' hmi'
          subst t'; subst fromId; subst toId; subst mi
          refine ⟨sLog, hsLog_len, ?_, ⟨erSn, herSn_mem, herSn_t, herSn_lead⟩, ?_⟩
          · simp only [nextHandleInstallSnapshot, fnUpd_same, List.mem_cons]; exact Or.inl trivial
          · intro hL' htL
            by_cases hlf : l = f
            · have hnl : (nextHandleInstallSnapshot s f l t sIdx sTerm sState sLog).nodes l = n' := by
                simp only [nextHandleInstallSnapshot, hlf, fnUpd_same, n', advance, retain,
                  newTail, newApplied, newAppliedState, newCommit, stepped, n]
              rw [hnl, hn'_role] at hL'; cases hL'
            · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hlf] at hL' htL ⊢
              have hln := hinv.leaderNode l hL'
              have hcompat := hinv.commit_accepted_compat hcmSn_mem (by omega)
                (by rw [htL] at hln; exact hln.2.2.1)
              have hle_l : sIdx ≤ (s.hist.fullLog l).length := by
                by_cases hlt : cmSn.term < t
                · rcases hln.2.2.2.1 with ⟨erL, herL, hterL, _, hpre_erL, _⟩
                  have hlc := hinv.leaderCompleteness cmSn hcmSn_mem erL herL (by omega)
                  have h1 := hlc.1; have h2 := hpre_erL.1; omega
                · have hcm_eq_l : cmSn.term = (s.nodes l).term := by omega
                  have hle_c := hln.2.2.2.2.2.2 cmSn hcmSn_mem hcm_eq_l
                  have hle_len := (hinv.nodeSync l).2.2.1
                  omega
              exact isPrefix_of_le_of_prefix_compat
                (by rcases hcompat with h1 | h2
                    · exact Or.inl (IsPrefix.trans hsLog_pre_cmSn h1)
                    · exact prefix_compat_of_common_super hsLog_pre_cmSn h2)
                (by omega)
        · rcases hinv.aeReplyMsg t' fromId toId mi hm' hpos with ⟨Lack, h1, h2, h3, h4⟩
          refine ⟨Lack, h1, hacc_mono fromId _ h2, h3, ?_⟩
          by_cases hto : toId = f
          · rw [hto, hnodes_f, hn'_role]; intro hL'; cases hL'
          · simp only [nextHandleInstallSnapshot, fnUpd_other _ _ hto]; exact h4
      snapMsg := fun t' l' si st ss hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.snapMsg t' l' si st ss hm'
      snapLogRecs := hinv.snapLogRecs }

/-! ## 6. Master Inductive Preservation Theorem (`Inv.step` & `Inv.reachable`) -/

/-- Every transition preserves the inductive invariant `Inv`. -/
theorem Inv.step {boot : NodeId} {s s' : System NodeId T}
    (hinv : Inv boot s) (hstep : Step boot s s') : Inv boot s' := by
  cases hstep with
  | bootstrapSelfJoin hEmpty =>
    exact hinv.preserve_bootstrapSelfJoin hEmpty
  | propose _ _ hLeader hValid hVoterGuard =>
    exact hinv.preserve_propose hLeader hValid hVoterGuard
  | startElection _ hVoter =>
    exact hinv.preserve_startElection hVoter
  | handleRequestVote _ _ _ _ _ hMsg hTerm =>
    exact hinv.preserve_handleRequestVote hMsg hTerm
  | handleVoteReply _ _ _ hMsg hCand hTerm =>
    exact hinv.preserve_handleVoteReply hMsg hCand hTerm
  | becomeLeader _ hCand hQuorum =>
    exact hinv.preserve_becomeLeader hCand hQuorum
  | sendAppendEntries _ _ _ hLeader hBounds =>
    exact hinv.preserve_sendAppendEntries hLeader hBounds
  | handleAppendEntries _ _ _ _ _ _ _ hMsg hTerm =>
    exact hinv.preserve_handleAppendEntries hMsg hTerm
  | handleAppendReply _ _ _ _ hMsg hLeader hTerm =>
    exact hinv.preserve_handleAppendReply hMsg hLeader hTerm
  | advanceCommit _ _ hLeader hBounds hCurTerm hQuorum =>
    exact hinv.preserve_advanceCommit hLeader hBounds hCurTerm hQuorum
  | leaderStepDown _ hLeader =>
    exact hinv.preserve_leaderStepDown hLeader
  | applyOne _ _ hLt hEntry =>
    exact hinv.preserve_applyOne hLt hEntry
  | compactSnapshot _ hLt =>
    exact hinv.preserve_compactSnapshot hLt
  | sendInstallSnapshot _ hLeader hSnap =>
    exact hinv.preserve_sendInstallSnapshot hLeader hSnap
  | handleInstallSnapshot _ _ _ _ _ _ _ hMsg hSnapLog hTerm =>
    exact hinv.preserve_handleInstallSnapshot hMsg hSnapLog hTerm
  | crashRestart i =>
    exact hinv.preserve_crashRestart i

/-- Every reachable state satisfies the full inductive invariant `Inv`. -/
theorem Inv.reachable {boot : NodeId} {s : System NodeId T}
    (hr : Reachable boot s) : Inv boot s := by
  induction hr with
  | init => exact Inv.init boot
  | step _ hstep ih => exact ih.step hstep

end PreservationCore

end ValkeyRaft.ConfigOnAppend


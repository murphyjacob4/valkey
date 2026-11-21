/-
  Inductive invariant preservation for 12 of the 16 transitions:
  * Monotonicity helpers (`GoodLog.mono`, `CommitWF.mono`, `boot_term_zero_empty`)
  * `Inv.of_local_node_upd` generic frame lemma for local single-node updates
  * `handleVoteReply`, `handleAppendReply`, `leaderStepDown`, `applyOne`,
    `compactSnapshot`, `crashRestart`, `sendAppendEntries`, `sendInstallSnapshot`,
    `bootstrapSelfJoin`, `startElection`, `handleRequestVote`, `propose`.

  Zero `sorry`, core Lean 4 only (no Mathlib).
-/
import ValkeyRaft.ConfigOnAppend.Invariants

namespace ValkeyRaft.ConfigOnAppend

set_option linter.unusedSectionVars false

section PreservationBasic

variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

/-! ## 1. Monotonicity & Bootstrap-Empty Helpers -/

theorem ConfigParent.mono {s s' : System NodeId T} {L : List (Entry NodeId T.Op)}
    (hc : ∀ cm, cm ∈ s.hist.commits → cm ∈ s'.hist.commits)
    (h : ConfigParent s L) : ConfigParent s' L := by
  intro k e h1 h2 hg hvc
  rcases h k e h1 h2 hg hvc with ⟨cm, hmem, hrest⟩
  exact ⟨cm, hc cm hmem, hrest⟩

theorem EntryExtendsLeader.mono {s s' : System NodeId T} {L : List (Entry NodeId T.Op)}
    (he : ∀ er, er ∈ s.hist.elected → er ∈ s'.hist.elected)
    (h : EntryExtendsLeader s L) : EntryExtendsLeader s' L := by
  intro k h1 h2
  rcases h k h1 h2 with ⟨er, hmem, hrest⟩
  exact ⟨er, he er hmem, hrest⟩

theorem GoodLog.mono {boot : NodeId} {s s' : System NodeId T} {L : List (Entry NodeId T.Op)}
    (hc : ∀ cm, cm ∈ s.hist.commits → cm ∈ s'.hist.commits)
    (he : ∀ er, er ∈ s.hist.elected → er ∈ s'.hist.elected)
    (h : GoodLog boot s L) : GoodLog boot s' L :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.mono hc, h.2.2.2.2.mono he⟩

theorem GoodLog.of_prefix {boot : NodeId} {s : System NodeId T}
    {A B : List (Entry NodeId T.Op)} (hp : IsPrefix A B) (h : GoodLog boot s B) :
    GoodLog boot s A := by
  refine ⟨h.1.of_prefix hp, h.2.1.of_prefix hp, h.2.2.1.of_prefix hp, ?_, ?_⟩
  · intro k e h1 h2 hg hvc
    rw [logGet_of_prefix hp h2] at hg
    rcases h.2.2.2.1 k e h1 (Nat.le_trans h2 hp.1) hg hvc with
      ⟨cm, hmem, ht, hlt, hpre, hcfg, hnovc⟩
    refine ⟨cm, hmem, ht, hlt, ?_, hcfg, ?_⟩
    · rw [hp.take_eq_of_le (by omega)]; exact hpre
    · intro j e' hj1 hj2 hgj
      rw [logGet_of_prefix hp (by omega)] at hgj
      exact hnovc j e' hj1 hj2 hgj
  · intro k h1 h2
    rcases h.2.2.2.2 k h1 (Nat.le_trans h2 hp.1) with ⟨er, hmem, ht, hpre⟩
    refine ⟨er, hmem, ?_, ?_⟩
    · rw [logTermAt_of_prefix hp h2]; exact ht
    · rw [hp.take_eq_of_le h2]; exact hpre

theorem CommitWF.mono {boot : NodeId} {s s' : System NodeId T} {cm : CommitRec NodeId T}
    (hc : ∀ c, c ∈ s.hist.commits → c ∈ s'.hist.commits)
    (he : ∀ e, e ∈ s.hist.elected → e ∈ s'.hist.elected)
    (ha : ∀ v p, p ∈ s.hist.accepted v → p ∈ s'.hist.accepted v)
    (h : CommitWF boot s cm) : CommitWF boot s' cm := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.mono hc he, h.2.2.2.2.1, ?_, ?_, ?_⟩
  · intro v hv
    rcases h.2.2.2.2.2.1 v hv with ⟨hmem, La, hacc, hpre⟩
    exact ⟨hmem, La, ha v _ hacc, hpre⟩
  · rcases h.2.2.2.2.2.2.1 with ⟨er, hmem, hrest⟩
    exact ⟨er, he er hmem, hrest⟩
  · rcases h.2.2.2.2.2.2.2 with hL | ⟨hadj, cm0, hmem, hrest⟩
    · exact Or.inl hL
    · exact Or.inr ⟨hadj, cm0, hc cm0 hmem, hrest⟩

theorem Inv.boot_term_pos_of_elected {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {er : ElectionRec NodeId T} (her : er ∈ s.hist.elected) :
    (s.nodes boot).term ≥ 1 := by
  have hr := hinv.electionRecs er her
  by_cases h1 : er.term = 1
  · have hb := hr.2.2.2.2.2.1 h1
    have hge := hr.2.1
    rw [hb.1, h1] at hge; exact hge
  · have hgt : er.term > 1 := by have := hr.1; omega
    have hkn : IsKnownLog s er.elecLog := Or.inr (Or.inl ⟨er, her, rfl⟩)
    have hgood := hinv.goodLogs er.elecLog hkn
    have hwf : ElectionWF boot s er :=
      ⟨hgt, hgood, (hr.2.2.2.2.2.2 hgt).1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1⟩
    have hne := electionLog_nonempty hwf
    rcases logGet_some_iff er.elecLog (by omega) hne with ⟨e1, hg1⟩
    have hb1 := hgood.2.2.1 e1 hg1
    rcases hgood.2.2.2.2 1 (by omega) hne with ⟨er1, her1, ht1, _⟩
    have ht1_eq : er1.term = 1 := by simp [logTermAt, hg1, hb1.1] at ht1; exact ht1
    have hr1 := hinv.electionRecs er1 her1
    have hb1' := hr1.2.2.2.2.2.1 ht1_eq
    have hge := hr1.2.1
    rw [hb1'.1, ht1_eq] at hge; exact hge

theorem Inv.boot_term_zero_empty {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    (h0 : (s.nodes boot).term = 0) :
    s.hist.elected = [] ∧
    s.hist.commits = [] ∧
    s.hist.votes = [] ∧
    s.hist.snapLogs = [] ∧
    (∀ L, IsKnownLog s L → L = []) ∧
    (∀ i, s.hist.accepted i = []) := by
  have he : s.hist.elected = [] := by
    cases h : s.hist.elected with
    | nil => rfl
    | cons er _ =>
      have hge := hinv.boot_term_pos_of_elected (er := er) (by rw [h]; simp)
      omega
  have hc : s.hist.commits = [] := by
    cases h : s.hist.commits with
    | nil => rfl
    | cons cm _ =>
      rcases (hinv.commitRecs cm (by rw [h]; simp)).2.2.2.2.2.2.1 with ⟨er, her, _⟩
      rw [he] at her; cases her
  have hv : s.hist.votes = [] := by
    cases h : s.hist.votes with
    | nil => rfl
    | cons vr _ =>
      have := (hinv.voteRecs vr (by rw [h]; simp)).2.1
      omega
  have hs : s.hist.snapLogs = [] := by
    cases h : s.hist.snapLogs with
    | nil => rfl
    | cons p _ =>
      rcases p with ⟨sIdx, sTerm, sState, sLog⟩
      rcases (hinv.snapLogRecs sIdx sTerm sState sLog (by rw [h]; simp)).2.2.2.2 with ⟨cm, hcm, _⟩
      rw [hc] at hcm; cases hcm
  have hlog : ∀ L, IsKnownLog s L → L = [] := by
    intro L hkn
    cases hL : L with
    | nil => rfl
    | cons _ _ =>
      have hgood := hinv.goodLogs L hkn
      rcases hgood.2.2.2.2 1 (by omega) (by rw [hL]; simp) with ⟨er, her, _⟩
      rw [he] at her; cases her
  have hacc : ∀ i, s.hist.accepted i = [] := by
    intro i
    cases h : s.hist.accepted i with
    | nil => rfl
    | cons p _ =>
      rcases (hinv.acceptedRecs i p.1 p.2 (by rw [h]; simp)).2.2.1 with ⟨er, her, _⟩
      rw [he] at her; cases her
  exact ⟨he, hc, hv, hs, hlog, hacc⟩

/-! ## 2. Frame lemma for local single-node updates (hist & net & term & votedFor unchanged) -/

theorem Inv.of_local_node_upd {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    (i : NodeId) (n' : Node NodeId T)
    (hTerm : n'.term = (s.nodes i).term)
    (hVotedFor : n'.votedFor = (s.nodes i).votedFor)
    (hNoNewLeader : n'.role = .leader → (s.nodes i).role = .leader)
    (hNoNewCand : n'.role = .candidate → (s.nodes i).role = .candidate)
    (hSync :
      let L := s.hist.fullLog i
      n'.snapIdx ≤ n'.applied ∧
      n'.applied ≤ n'.commit ∧
      n'.commit ≤ L.length ∧
      n'.tail = L.drop n'.snapIdx ∧
      n'.snapTerm = logTermAt L n'.snapIdx ∧
      n'.snapState = stateAt L n'.snapIdx ∧
      n'.appliedState = stateAt L n'.applied ∧
      logLastTerm L ≤ n'.term)
    (hLead : n'.role = .leader →
      n'.term > 0 ∧
      n'.votedFor = some i ∧
      (n'.term, s.hist.fullLog i) ∈ s.hist.accepted i ∧
      (∃ er ∈ s.hist.elected,
        er.term = n'.term ∧ er.leader = i ∧
        IsPrefix er.elecLog (s.hist.fullLog i) ∧
        (∀ j, er.elecLog.length < j → j ≤ (s.hist.fullLog i).length →
          logTermAt (s.hist.fullLog i) j = n'.term)) ∧
      (∀ v, n'.matchIdx v > 0 →
        n'.matchIdx v ≤ (s.hist.fullLog i).length ∧
        (n'.term, (s.hist.fullLog i).take (n'.matchIdx v)) ∈ s.hist.accepted v) ∧
      (n'.commit > 0 → logTermAt (s.hist.fullLog i) n'.commit = n'.term →
        ∃ cm ∈ s.hist.commits,
          cm.term = n'.term ∧ cm.idx = n'.commit ∧
          cm.log = (s.hist.fullLog i).take n'.commit ∧
          (n'.hasUncommittedVoterChange = false → cm.cfg = votersOfLog cm.log)) ∧
      (∀ cm ∈ s.hist.commits, cm.term = n'.term → cm.idx ≤ n'.commit))
    (hCand : n'.role = .candidate →
      n'.term > 1 ∧
      n'.votedFor = some i ∧
      logLastTerm (s.hist.fullLog i) < n'.term ∧
      (∀ er ∈ s.hist.elected, er.term = n'.term → er.leader ≠ i) ∧
      (∀ v ∈ n'.votes,
        ∃ vr ∈ s.hist.votes,
          vr.term = n'.term ∧ vr.voter = v ∧ vr.cand = i ∧
          upToDate (logLastTerm (s.hist.fullLog i)) (s.hist.fullLog i).length
                   (logLastTerm vr.voterLog) vr.voterLog.length = true))
    (hComm : n'.commit > 0 →
      ∃ cm ∈ s.hist.commits, cm.term ≤ n'.term ∧ cm.idx ≥ n'.commit ∧
        IsPrefix ((s.hist.fullLog i).take n'.commit) cm.log)
    (hSnap : n'.snapIdx > 0 →
      ∃ cm ∈ s.hist.commits, cm.term ≤ n'.term ∧ cm.idx ≥ n'.snapIdx ∧
        IsPrefix ((s.hist.fullLog i).take n'.snapIdx) cm.log) :
    Inv boot { nodes := fnUpd s.nodes i n', net := s.net, hist := s.hist } := by
  have hterm_all : ∀ x, (fnUpd s.nodes i n' x).term = (s.nodes x).term := fun x => by
    by_cases hx : x = i
    · rw [hx, fnUpd_same, hTerm]
    · rw [fnUpd_other _ _ hx]
  have hvf_all : ∀ x, (fnUpd s.nodes i n' x).votedFor = (s.nodes x).votedFor := fun x => by
    by_cases hx : x = i
    · rw [hx, fnUpd_same, hVotedFor]
    · rw [fnUpd_other _ _ hx]
  refine
    { nodeSync := fun x => by
        by_cases hx : x = i
        · rw [hx]; simpa [fnUpd_same] using hSync
        · simpa [fnUpd_other _ _ hx] using hinv.nodeSync x
      leaderNode := fun l hL => by
        by_cases hl : l = i
        · rw [hl] at hL ⊢; simpa [fnUpd_same] using hLead (by simpa [fnUpd_same] using hL)
        · simp only [fnUpd_other _ _ hl] at hL ⊢; exact hinv.leaderNode l hL
      candidateNode := fun c hC => by
        by_cases hc : c = i
        · rw [hc] at hC ⊢; simpa [fnUpd_same] using hCand (by simpa [fnUpd_same] using hC)
        · simp only [fnUpd_other _ _ hc] at hC ⊢; exact hinv.candidateNode c hC
      votedForRec := fun x c h => by
        rw [hterm_all x]; rw [hvf_all x] at h; exact hinv.votedForRec x c h
      nodeCommit := fun x hx => by
        by_cases hxi : x = i
        · rw [hxi] at hx ⊢; simpa [fnUpd_same] using hComm (by simpa [fnUpd_same] using hx)
        · simp only [fnUpd_other _ _ hxi] at hx ⊢; exact hinv.nodeCommit x hx
      nodeSnap := fun x hx => by
        by_cases hxi : x = i
        · rw [hxi] at hx ⊢; simpa [fnUpd_same] using hSnap (by simpa [fnUpd_same] using hx)
        · simp only [fnUpd_other _ _ hxi] at hx ⊢; exact hinv.nodeSnap x hx
      goodLogs := hinv.goodLogs
      sameTermPrefix := hinv.sameTermPrefix
      leaderMaxTerm := fun l L k hL hkn hk1 hkl ht => by
        rw [hterm_all l] at ht
        have hL0 : (s.nodes l).role = .leader := by
          by_cases hl : l = i
          · rw [hl] at hL ⊢; exact hNoNewLeader (by simpa [fnUpd_same] using hL)
          · simp only [fnUpd_other _ _ hl] at hL; exact hL
        exact hinv.leaderMaxTerm l L k hL0 hkn hk1 hkl ht
      voteRecs := fun vr hvr => by
        have hv := hinv.voteRecs vr hvr
        rw [hterm_all boot, hterm_all vr.voter, hterm_all vr.cand, hvf_all vr.voter]
        exact hv
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        rw [hterm_all er.leader]; exact hr
      acceptedRecs := fun x t La ha => by
        have h := hinv.acceptedRecs x t La ha
        rw [hterm_all x]; exact h
      acceptedBeforeVote := hinv.acceptedBeforeVote
      commitRecs := hinv.commitRecs
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t x v ci ct hm => by
        have h := hinv.reqVoteMsg t x v ci ct hm
        refine ⟨h.1, by rw [hterm_all boot]; exact h.2.1, by rw [hterm_all x]; exact h.2.2.1, ?_⟩
        intro ht hC
        rw [hterm_all x] at ht
        have hC0 : (s.nodes x).role = .candidate := by
          by_cases hx : x = i
          · rw [hx] at hC ⊢; exact hNoNewCand (by simpa [fnUpd_same] using hC)
          · simp only [fnUpd_other _ _ hx] at hC; exact hC
        exact h.2.2.2 ht hC0
      voteReplyMsg := fun t f to hm => by
        rcases hinv.voteReplyMsg t f to hm with ⟨vr, hvr, h1, h2, h3, h4⟩
        refine ⟨vr, hvr, h1, h2, h3, ?_⟩
        intro ht hC
        rw [hterm_all to] at ht
        have hC0 : (s.nodes to).role = .candidate := by
          by_cases hx : to = i
          · rw [hx] at hC ⊢; exact hNoNewCand (by simpa [fnUpd_same] using hC)
          · simp only [fnUpd_other _ _ hx] at hC; exact hC
        exact h4 ht hC0
      aeMsg := fun t l pi pt es lc hm => by
        rcases hinv.aeMsg t l pi pt es lc hm with ⟨Lae, h1, h2, h3, h4, h5, h6, h7, h8⟩
        refine ⟨Lae, h1, h2, h3, h4, h5, h6, h7, ?_⟩
        intro hL ht
        rw [hterm_all l] at ht
        have hL0 : (s.nodes l).role = .leader := by
          by_cases hl : l = i
          · rw [hl] at hL ⊢; exact hNoNewLeader (by simpa [fnUpd_same] using hL)
          · simp only [fnUpd_other _ _ hl] at hL; exact hL
        exact h8 hL0 ht
      aeReplyMsg := fun t f to mi hm hpos => by
        rcases hinv.aeReplyMsg t f to mi hm hpos with ⟨Lack, h1, h2, h3, h4⟩
        refine ⟨Lack, h1, h2, h3, ?_⟩
        intro hL ht
        rw [hterm_all to] at ht
        have hL0 : (s.nodes to).role = .leader := by
          by_cases hl : to = i
          · rw [hl] at hL ⊢; exact hNoNewLeader (by simpa [fnUpd_same] using hL)
          · simp only [fnUpd_other _ _ hl] at hL; exact hL
        exact h4 hL0 ht
      snapMsg := hinv.snapMsg
      snapLogRecs := hinv.snapLogRecs }

/-! ## 3. Six local transitions via `Inv.of_local_node_upd` -/

/-- (5) `handleVoteReply` -/
theorem Inv.preserve_handleVoteReply {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {c fromId : NodeId} {t : Nat}
    (hMsg : Msg.voteReply t fromId c true ∈ s.net)
    (hCand : (s.nodes c).role = .candidate)
    (hTerm : (s.nodes c).term = t) :
    Inv boot (nextHandleVoteReply s c fromId) := by
  rcases hinv.voteReplyMsg t fromId c hMsg with ⟨vr, hvr_m, hvr_t, hvr_v, hvr_c, hvr_up⟩
  have hup := hvr_up hTerm hCand
  have hc := hinv.candidateNode c hCand
  refine hinv.of_local_node_upd c _ rfl rfl (fun h => by rw [hCand] at h; cases h) (fun _ => hCand)
    (hinv.nodeSync c) (fun h => by rw [hCand] at h; cases h) ?_ (hinv.nodeCommit c) (hinv.nodeSnap c)
  intro _
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun v hv => ?_⟩
  dsimp only at hv
  split at hv
  · exact hc.2.2.2.2 v hv
  · rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨vr, hvr_m, by dsimp only; omega, hvr_v, hvr_c, hup⟩
    · exact hc.2.2.2.2 v hv'

/-- (9) `handleAppendReply` -/
theorem Inv.preserve_handleAppendReply {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l fromId : NodeId} {t mIdx : Nat}
    (hMsg : Msg.appendReply t fromId l true mIdx ∈ s.net)
    (hLeader : (s.nodes l).role = .leader)
    (hTerm : (s.nodes l).term = t) :
    Inv boot (nextHandleAppendReply s l fromId mIdx) := by
  have hln := hinv.leaderNode l hLeader
  refine hinv.of_local_node_upd l _ rfl rfl (fun _ => hLeader) (fun h => by rw [hLeader] at h; cases h)
    (hinv.nodeSync l) ?_ (fun h => by rw [hLeader] at h; cases h) (hinv.nodeCommit l) (hinv.nodeSnap l)
  intro _
  refine ⟨hln.1, hln.2.1, hln.2.2.1, hln.2.2.2.1, ?_, hln.2.2.2.2.2.1, hln.2.2.2.2.2.2⟩
  intro v hv
  by_cases hvf : v = fromId
  · rw [hvf] at hv ⊢
    simp only [fnUpd_same] at hv ⊢
    by_cases hle : mIdx ≤ (s.nodes l).matchIdx fromId
    · rw [Nat.max_eq_left hle] at hv ⊢; exact hln.2.2.2.2.1 fromId hv
    · rw [Nat.max_eq_right (by omega)] at hv ⊢
      rcases hinv.aeReplyMsg t fromId l mIdx hMsg hv with ⟨Lack, hlen, hacc, _, hpre⟩
      have hpre' := hpre hLeader hTerm
      refine ⟨by have := hpre'.1; omega, ?_⟩
      have htake : (s.hist.fullLog l).take mIdx = Lack := by rw [← hlen]; exact hpre'.2
      rw [hTerm, htake]; exact hacc
  · simp only [fnUpd_other _ _ hvf] at hv ⊢
    exact hln.2.2.2.2.1 v hv

/-- (11) `leaderStepDown` -/
theorem Inv.preserve_leaderStepDown {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l : NodeId} (_hLeader : (s.nodes l).role = .leader) :
    Inv boot (nextLeaderStepDown s l) :=
  hinv.of_local_node_upd l _ rfl rfl (fun h => by cases h) (fun h => by cases h)
    (hinv.nodeSync l) (fun h => by cases h) (fun h => by cases h)
    (hinv.nodeCommit l) (hinv.nodeSnap l)

/-- (12) `applyOne` -/
theorem Inv.preserve_applyOne {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {i : NodeId} {e : Entry NodeId T.Op}
    (hLt : (s.nodes i).applied < (s.nodes i).commit)
    (hEntry : (s.nodes i).entryAt ((s.nodes i).applied + 1) = some e) :
    Inv boot (nextApplyOne s i e) := by
  have hsync := hinv.nodeSync i
  have hget : logGet (s.hist.fullLog i) ((s.nodes i).applied + 1) = some e := by
    rw [← node_entryAt_eq hsync.2.2.2.1 (by have := hsync.1; omega)]; exact hEntry
  have happ' : applyCmd (s.nodes i).appliedState e.cmd =
      stateAt (s.hist.fullLog i) ((s.nodes i).applied + 1) := by
    rw [hsync.2.2.2.2.2.2.1, stateAt_succ (by omega) hget, Nat.add_sub_cancel]
  exact hinv.of_local_node_upd i _ rfl rfl id id
    ⟨by dsimp only; have := hsync.1; omega, by dsimp only; omega, hsync.2.2.1, hsync.2.2.2.1,
     hsync.2.2.2.2.1, hsync.2.2.2.2.2.1, happ', hsync.2.2.2.2.2.2.2⟩
    (fun hL => hinv.leaderNode i hL)
    (fun hC => hinv.candidateNode i hC)
    (hinv.nodeCommit i) (hinv.nodeSnap i)

/-- (13) `compactSnapshot` -/
theorem Inv.preserve_compactSnapshot {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {i : NodeId} (hLt : (s.nodes i).snapIdx < (s.nodes i).applied) :
    Inv boot (nextCompactSnapshot s i) := by
  have hsync := hinv.nodeSync i
  have htail' : (s.nodes i).tail.drop ((s.nodes i).applied - (s.nodes i).snapIdx) =
      (s.hist.fullLog i).drop (s.nodes i).applied := by
    rw [hsync.2.2.2.1, List.drop_drop]
    have : (s.nodes i).snapIdx + ((s.nodes i).applied - (s.nodes i).snapIdx) = (s.nodes i).applied := by omega
    rw [this]
  have hsterm' : (s.nodes i).termAt (s.nodes i).applied =
      logTermAt (s.hist.fullLog i) (s.nodes i).applied :=
    node_termAt_eq hsync.2.2.2.1 hsync.2.2.2.2.1 hsync.1
  have hnovc_eq :
      (({ s.nodes i with
           snapIdx := (s.nodes i).applied, snapTerm := (s.nodes i).termAt (s.nodes i).applied,
           snapState := (s.nodes i).appliedState,
           tail := (s.nodes i).tail.drop ((s.nodes i).applied - (s.nodes i).snapIdx) } : Node NodeId T)).hasUncommittedVoterChange =
      (s.nodes i).hasUncommittedVoterChange := by
    unfold Node.hasUncommittedVoterChange
    dsimp only
    rw [htail', hsync.2.2.2.1, List.drop_drop, List.drop_drop]
    have h1 : (s.nodes i).applied + ((s.nodes i).commit - (s.nodes i).applied) = (s.nodes i).commit := by
      have := hsync.2.1; omega
    have h2 : (s.nodes i).snapIdx + ((s.nodes i).commit - (s.nodes i).snapIdx) = (s.nodes i).commit := by
      have := hsync.2.1; omega
    rw [h1, h2]
  refine hinv.of_local_node_upd i _ rfl rfl id id
    ⟨Nat.le_refl _, hsync.2.1, hsync.2.2.1, htail', hsterm',
     hsync.2.2.2.2.2.2.1, hsync.2.2.2.2.2.2.1, hsync.2.2.2.2.2.2.2⟩
    ?_ (fun hC => hinv.candidateNode i hC) (hinv.nodeCommit i) ?_
  · intro hL
    have hln := hinv.leaderNode i hL
    refine ⟨hln.1, hln.2.1, hln.2.2.1, hln.2.2.2.1, hln.2.2.2.2.1, ?_, hln.2.2.2.2.2.2⟩
    intro hc htc
    rcases hln.2.2.2.2.2.1 hc htc with ⟨cm, h1, h2, h3, h4, h5⟩
    exact ⟨cm, h1, h2, h3, h4, fun hnv => h5 (by rwa [hnovc_eq] at hnv)⟩
  · intro happ_pos
    have hle_comm : (s.nodes i).applied ≤ (s.nodes i).commit := hsync.2.1
    have hle_len : (s.nodes i).commit ≤ (s.hist.fullLog i).length := hsync.2.2.1
    rcases hinv.nodeCommit i (by dsimp only at happ_pos; omega) with ⟨cm, hcm, hcm_t, hge, hpre⟩
    refine ⟨cm, hcm, hcm_t, by dsimp only; omega, ?_⟩
    have hsub : IsPrefix ((s.hist.fullLog i).take (s.nodes i).applied)
        ((s.hist.fullLog i).take (s.nodes i).commit) := by
      refine ⟨by rw [List.length_take, List.length_take]; omega, ?_⟩
      rw [List.length_take, Nat.min_eq_left (by omega), List.take_take, Nat.min_eq_left hle_comm]
    exact IsPrefix.trans hsub hpre

/-- (16) `crashRestart` -/
theorem Inv.preserve_crashRestart {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    (i : NodeId) :
    Inv boot (nextCrashRestart s i) := by
  have hsync := hinv.nodeSync i
  exact hinv.of_local_node_upd i _ rfl rfl (fun h => by cases h) (fun h => by cases h)
    ⟨Nat.le_refl _, Nat.le_refl _, by dsimp only; have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; omega,
     hsync.2.2.2.1, hsync.2.2.2.2.1, hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.2.2⟩
    (fun h => by cases h) (fun h => by cases h)
    (hinv.nodeSnap i) (hinv.nodeSnap i)

/-! ## 4. Send transitions (`sendAppendEntries`, `sendInstallSnapshot`) -/

/-- (7) `sendAppendEntries` -/
theorem Inv.preserve_sendAppendEntries {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l : NodeId} {prevIdx endIdx : Nat}
    (hLeader : (s.nodes l).role = .leader)
    (hBounds : (s.nodes l).snapIdx ≤ prevIdx ∧ prevIdx ≤ endIdx ∧ endIdx ≤ (s.nodes l).lastIdx) :
    Inv boot (nextSendAppendEntries s l prevIdx endIdx) := by
  have hsync := hinv.nodeSync l
  have hL := hinv.leaderNode l hLeader
  have hlast : (s.nodes l).lastIdx = (s.hist.fullLog l).length :=
    node_lastIdx_eq (by omega) hsync.2.2.2.1
  have htermAt : (s.nodes l).termAt prevIdx = logTermAt (s.hist.fullLog l) prevIdx :=
    node_termAt_eq hsync.2.2.2.1 hsync.2.2.2.2.1 hBounds.1
  have hentries : ((s.nodes l).tail.drop (prevIdx - (s.nodes l).snapIdx)).take (endIdx - prevIdx) =
      ((s.hist.fullLog l).drop prevIdx).take (endIdx - prevIdx) := by
    rw [hsync.2.2.2.1, List.drop_drop]
    have : (s.nodes l).snapIdx + (prevIdx - (s.nodes l).snapIdx) = prevIdx := by omega
    rw [this]
  have helen : (((s.hist.fullLog l).drop prevIdx).take (endIdx - prevIdx)).length = endIdx - prevIdx := by
    rw [List.length_take, List.length_drop]; omega
  refine
    { nodeSync := hinv.nodeSync
      leaderNode := hinv.leaderNode
      candidateNode := hinv.candidateNode
      votedForRec := hinv.votedForRec
      nodeCommit := hinv.nodeCommit
      nodeSnap := hinv.nodeSnap
      goodLogs := hinv.goodLogs
      sameTermPrefix := hinv.sameTermPrefix
      leaderMaxTerm := hinv.leaderMaxTerm
      voteRecs := hinv.voteRecs
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := hinv.electionRecs
      acceptedRecs := hinv.acceptedRecs
      acceptedBeforeVote := hinv.acceptedBeforeVote
      commitRecs := hinv.commitRecs
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t c v ci ct hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.reqVoteMsg t c v ci ct hm'
      voteReplyMsg := fun t f to hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.voteReplyMsg t f to hm'
      aeMsg := fun t l' pi pt es lc hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with ht hl hpi hpt hes hlc
          subst ht; subst l'; subst pi; subst pt; subst es; subst lc
          refine ⟨s.hist.fullLog l, hL.2.2.1, ?_, htermAt.symm, ?_, hsync.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
          · rw [hentries, helen]; omega
          · rw [hentries, helen]
          · rcases hL.2.2.2.1 with ⟨er, h1, h2, h3, h4, _⟩
            exact ⟨er, h1, h2, h3, h4⟩
          · intro hpos
            exact ⟨hsync.2.2.1, hinv.nodeCommit l hpos⟩
          · intro _ _; exact IsPrefix.refl _
        · exact hinv.aeMsg t l' pi pt es lc hm'
      aeReplyMsg := fun t f to mi hm hpos => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.aeReplyMsg t f to mi hm' hpos
      snapMsg := fun t l' si st ss hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.snapMsg t l' si st ss hm'
      snapLogRecs := hinv.snapLogRecs }

/-- (14) `sendInstallSnapshot` -/
theorem Inv.preserve_sendInstallSnapshot {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l : NodeId} (hLeader : (s.nodes l).role = .leader) (hSnap : (s.nodes l).snapIdx > 0) :
    Inv boot (nextSendInstallSnapshot s l) := by
  have hsync := hinv.nodeSync l
  have hL := hinv.leaderNode l hLeader
  let sLog := (s.hist.fullLog l).take (s.nodes l).snapIdx
  have hkn_sLog_pre : IsPrefix sLog (s.hist.fullLog l) := IsPrefix.take_left _ _
  have hkn_l : IsKnownLog s (s.hist.fullLog l) := Or.inl ⟨l, rfl⟩
  have hkn_new : ∀ L, IsKnownLog (nextSendInstallSnapshot s l) L → IsKnownLog s L ∨ L = sLog := by
    intro L h
    rcases h with ⟨i, h⟩ | ⟨er, h, rfl⟩ | ⟨cm, h, rfl⟩ | ⟨vr, h, rfl⟩ | ⟨p, h, rfl⟩ | ⟨i, t, h⟩
    · exact Or.inl (Or.inl ⟨i, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨er, h, rfl⟩))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨cm, h, rfl⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, h, rfl⟩))))
    · rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, h', rfl⟩)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t, h⟩)))))
  refine
    { nodeSync := hinv.nodeSync
      leaderNode := hinv.leaderNode
      candidateNode := hinv.candidateNode
      votedForRec := hinv.votedForRec
      nodeCommit := hinv.nodeCommit
      nodeSnap := hinv.nodeSnap
      goodLogs := fun L hkn => by
        rcases hkn_new L hkn with h | rfl
        · exact hinv.goodLogs L h
        · exact (hinv.goodLogs (s.hist.fullLog l) hkn_l).of_prefix hkn_sLog_pre
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 hi1 hl1 hi2 hl2 ht hle => by
        rcases hkn_new L1 h1 with ho1 | rfl <;> rcases hkn_new L2 h2 with ho2 | rfl
        · exact hinv.sameTermPrefix L1 L2 i1 i2 ho1 ho2 hi1 hl1 hi2 hl2 ht hle
        · rw [hkn_sLog_pre.take_eq_of_le (by omega)]
          exact hinv.sameTermPrefix L1 (s.hist.fullLog l) i1 i2 ho1 hkn_l hi1 hl1 hi2
            (Nat.le_trans hl2 hkn_sLog_pre.1) (by rw [← logTermAt_of_prefix hkn_sLog_pre hl2]; exact ht) hle
        · rw [hkn_sLog_pre.take_eq_of_le hl1]
          exact hinv.sameTermPrefix (s.hist.fullLog l) L2 i1 i2 hkn_l ho2 hi1
            (Nat.le_trans hl1 hkn_sLog_pre.1) hi2 hl2 (by rw [← logTermAt_of_prefix hkn_sLog_pre hl1]; exact ht) hle
        · rfl
      leaderMaxTerm := fun l' L k hL' hkn hk1 hkl ht => by
        rcases hkn_new L hkn with ho | rfl
        · exact hinv.leaderMaxTerm l' L k hL' ho hk1 hkl ht
        · rw [hkn_sLog_pre.take_eq_of_le hkl]
          exact hinv.leaderMaxTerm l' (s.hist.fullLog l) k hL' hkn_l hk1
            (Nat.le_trans hkl hkn_sLog_pre.1) (by rw [← logTermAt_of_prefix hkn_sLog_pre hkl]; exact ht)
      voteRecs := hinv.voteRecs
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := hinv.electionRecs
      acceptedRecs := hinv.acceptedRecs
      acceptedBeforeVote := hinv.acceptedBeforeVote
      commitRecs := hinv.commitRecs
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t c v ci ct hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.reqVoteMsg t c v ci ct hm'
      voteReplyMsg := fun t f to hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.voteReplyMsg t f to hm'
      aeMsg := fun t l' pi pt es lc hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.aeMsg t l' pi pt es lc hm'
      aeReplyMsg := fun t f to mi hm hpos => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.aeReplyMsg t f to mi hm' hpos
      snapMsg := fun t l' si st ss hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with ht hl hsi hst hss
          subst ht; subst l'; subst si; subst st; subst ss
          refine ⟨hSnap, ⟨sLog, by simp [nextSendInstallSnapshot, sLog], hinv.nodeSnap l hSnap⟩, ?_⟩
          rcases hL.2.2.2.1 with ⟨er, h1, h2, h3, _⟩
          exact ⟨er, h1, h2, h3⟩
        · rcases hinv.snapMsg t l' si st ss hm' with ⟨h1, ⟨sl, hsl, hcm⟩, h3⟩
          exact ⟨h1, ⟨sl, List.mem_cons_of_mem _ hsl, hcm⟩, h3⟩
      snapLogRecs := fun si st ss sl hmem => by
        rcases List.mem_cons.mp hmem with heq | hm'
        · simp only [Prod.mk.injEq] at heq
          rcases heq with ⟨h1, h2, h3, h4⟩
          subst h1; subst h2; subst h3; subst h4
          rcases hinv.nodeSnap l hSnap with ⟨cm, hcm, _, hge, hpre⟩
          refine ⟨hSnap, by rw [List.length_take]; have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; omega,
            ?_, ?_, cm, hcm, hge, hpre⟩
          · rw [logLastTerm_take _ (by have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; omega)]
            exact hsync.2.2.2.2.1.symm
          · exact hsync.2.2.2.2.2.1.symm
        · exact hinv.snapLogRecs si st ss sl hm' }

/-! ## 5. `bootstrapSelfJoin`, `startElection`, `handleRequestVote`, `propose` -/

/-- (1) `bootstrapSelfJoin` -/
theorem Inv.preserve_bootstrapSelfJoin {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    (hEmpty : (s.nodes boot).term = 0 ∧ (s.nodes boot).snapIdx = 0 ∧ (s.nodes boot).tail = []) :
    Inv boot (nextBootstrap boot s) := by
  rcases hinv.boot_term_zero_empty hEmpty.1 with ⟨he, hc, hv, hs, hlog, hacc⟩
  let e : Entry NodeId T.Op := { term := 1, cmd := .bootstrapJoin boot }
  have hsync_b := hinv.nodeSync boot
  have hfull_b : s.hist.fullLog boot = [] := hlog _ (Or.inl ⟨boot, rfl⟩)
  have hcomm_b : (s.nodes boot).commit = 0 := by have := hsync_b.2.2.1; rw [hfull_b] at this; simp at this; omega
  have happ_b : (s.nodes boot).applied = 0 := by omega
  have hkn_new : ∀ L, IsKnownLog (nextBootstrap boot s) L → L = [] ∨ L = [e] := by
    intro L h
    rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t, ha⟩
    · by_cases hib : i = boot
      · rw [hib] at hi; simp [nextBootstrap] at hi; exact Or.inr hi
      · simp [nextBootstrap, hib] at hi; exact Or.inl (hi ▸ hlog _ (Or.inl ⟨i, rfl⟩))
    · simp only [nextBootstrap, he, List.mem_singleton] at her; subst her; exact Or.inr rfl
    · simp only [nextBootstrap, hc] at hcm; cases hcm
    · simp only [nextBootstrap, hv, List.mem_singleton] at hvr; subst hvr; exact Or.inl rfl
    · simp only [nextBootstrap, hs] at hp; cases hp
    · by_cases hib : i = boot
      · rw [hib] at ha; simp only [nextBootstrap, fnUpd_same, hacc, List.mem_singleton] at ha
        injection ha with _ hL; exact Or.inr hL
      · simp only [nextBootstrap, fnUpd_other _ _ hib, hacc] at ha; cases ha
  have hgood_e : GoodLog boot (nextBootstrap boot s) [e] := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k e' h1 h2 hg
      have hkeq : k = 1 := by simp at h2; omega
      subst hkeq; simp [logGet, e] at hg; subst hg
      simp [validCmd, stateAt_zero, ClusterState.empty]
    · refine ⟨?_, ?_⟩
      · intro k h1 h2; have : k = 1 := by simp at h2; omega
        subst this; simp [logTermAt, logGet, e]
      · intro i j h1 hij hj; have hi : i = 1 := by simp at hj; omega
        have hj' : j = 1 := by simp at hj; omega
        subst hi; subst hj'; exact Nat.le_refl _
    · intro e' hg; simp [logGet, e] at hg; subst hg; exact ⟨rfl, rfl⟩
    · intro k e' h1 h2; simp at h2; omega
    · intro k h1 h2
      have hk : k = 1 := by simp at h2; omega
      subst hk
      refine ⟨{ term := 1, leader := boot, elecLog := [e], elecCfg := [boot], elecQuorum := [boot] },
        by simp [nextBootstrap, e], by simp [logTermAt, logGet, e], ?_⟩
      simp [IsPrefix]
  have hgood_nil : GoodLog boot (nextBootstrap boot s) [] :=
    ⟨LogValid.nil boot, LogMonotone.nil, BootstrapAtOne.nil boot,
     fun k _ _ h2 => by simp at h2; omega, fun k _ h2 => by simp at h2; omega⟩
  refine
    { nodeSync := fun i => by
        by_cases hib : i = boot
        · rw [hib]
          simp only [nextBootstrap, fnUpd_same, hEmpty.2.1, hcomm_b, happ_b]
          exact ⟨Nat.le_refl _, Nat.le_refl _, by simp, rfl,
            by rw [hsync_b.2.2.2.2.1, hEmpty.2.1]; simp [logTermAt_zero],
            by rw [hsync_b.2.2.2.2.2.1, hEmpty.2.1]; simp [stateAt_zero],
            by rw [hsync_b.2.2.2.2.2.2.1, happ_b]; simp [stateAt_zero],
            by simp [logLastTerm, logTermAt, logGet]⟩
        · simpa [nextBootstrap, hib] using hinv.nodeSync i
      leaderNode := fun l hL => by
        by_cases hlb : l = boot
        · rw [hlb]
          simp only [nextBootstrap, fnUpd_same]
          refine ⟨by omega, trivial, by simp, ?_, ?_, ?_, ?_⟩
          · refine ⟨{ term := 1, leader := boot, elecLog := [e], elecCfg := [boot], elecQuorum := [boot] },
              by simp [e], rfl, rfl, IsPrefix.refl _, ?_⟩
            intro j hj1 hj2; simp at hj1 hj2; omega
          · intro v hv; simp at hv
          · intro hpos; rw [hcomm_b] at hpos; omega
          · intro cm hcm; rw [hc] at hcm; cases hcm
        · simp only [nextBootstrap, fnUpd_other _ _ hlb] at hL
          rcases (hinv.leaderNode l hL).2.2.2.1 with ⟨er, her, _⟩
          rw [he] at her; cases her
      candidateNode := fun c hc => by
        by_cases hcb : c = boot
        · rw [hcb] at hc; simp [nextBootstrap] at hc
        · simp only [nextBootstrap, fnUpd_other _ _ hcb] at hc
          have hvf := (hinv.candidateNode c hc).2.1
          rcases (hinv.votedForRec c c hvf).2 with ⟨vr, hvr, _⟩
          rw [hv] at hvr; cases hvr
      votedForRec := fun i c hc => by
        by_cases hib : i = boot
        · rw [hib] at hc ⊢
          simp only [nextBootstrap, fnUpd_same] at hc ⊢
          injection hc with hcb; subst hcb
          exact ⟨by omega, _, List.mem_cons_self, rfl, rfl, rfl⟩
        · simp only [nextBootstrap, fnUpd_other _ _ hib] at hc
          rcases (hinv.votedForRec i c hc).2 with ⟨vr, hvr, _⟩
          rw [hv] at hvr; cases hvr
      nodeCommit := fun i hi => by
        by_cases hib : i = boot
        · rw [hib] at hi; simp [nextBootstrap, hcomm_b] at hi
        · simp only [nextBootstrap, fnUpd_other _ _ hib] at hi
          rcases hinv.nodeCommit i hi with ⟨cm, hcm, _⟩
          rw [hc] at hcm; cases hcm
      nodeSnap := fun i hi => by
        by_cases hib : i = boot
        · rw [hib] at hi; simp [nextBootstrap, hEmpty.2.1] at hi
        · simp only [nextBootstrap, fnUpd_other _ _ hib] at hi
          rcases hinv.nodeSnap i hi with ⟨cm, hcm, _⟩
          rw [hc] at hcm; cases hcm
      goodLogs := fun L hkn => by
        rcases hkn_new L hkn with rfl | rfl
        · exact hgood_nil
        · exact hgood_e
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 hi1 hl1 hi2 hl2 ht hle => by
        rcases hkn_new L1 h1 with rfl | rfl
        · simp at hl1; omega
        · rcases hkn_new L2 h2 with rfl | rfl
          · simp at hl2; omega
          · rfl
      leaderMaxTerm := fun l L k hL hkn hk1 hkl ht => by
        by_cases hlb : l = boot
        · rw [hlb]
          rcases hkn_new L hkn with rfl | rfl
          · simp at hkl; omega
          · simp [nextBootstrap, e] at hkl ⊢; omega
        · simp only [nextBootstrap, fnUpd_other _ _ hlb] at hL
          rcases (hinv.leaderNode l hL).2.2.2.1 with ⟨er, her, _⟩
          rw [he] at her; cases her
      voteRecs := fun vr hvr => by
        simp only [nextBootstrap, hv, List.mem_singleton] at hvr
        subst hvr
        simp [nextBootstrap]
      voteUnique := fun vr1 h1 vr2 h2 => by
        simp only [nextBootstrap, hv, List.mem_singleton] at h1 h2
        subst h1; subst h2; intro _ _; rfl
      electionUnique := fun er1 h1 er2 h2 => by
        simp only [nextBootstrap, he, List.mem_singleton] at h1 h2
        subst h1; subst h2; intro _; rfl
      electionRecs := fun er her => by
        simp only [nextBootstrap, he, List.mem_singleton] at her
        subst her
        simp only [nextBootstrap, fnUpd_same]
        refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
        · simp [votersOfLog, stateOfLog, applyCmd, ClusterState.empty]
        · unfold IsMajority ValkeyRaft.Quorum.IsMajority; simp
        · intro v hv; exact hv
        · intro _; exact ⟨trivial, trivial, trivial⟩
        · intro hgt; omega
      acceptedRecs := fun i t La ha => by
        by_cases hib : i = boot
        · rw [hib] at ha ⊢
          simp only [nextBootstrap, fnUpd_same, hacc, List.mem_singleton] at ha
          injection ha with ht hLa; subst ht; subst hLa
          refine ⟨by omega, by simp [nextBootstrap],
            ⟨{ term := 1, leader := boot, elecLog := [e], elecCfg := [boot], elecQuorum := [boot] },
              by simp [nextBootstrap, e], rfl, Or.inl (IsPrefix.refl _)⟩,
            fun P hP => Or.inl (by simp [nextBootstrap]; exact hP)⟩
        · simp only [nextBootstrap, fnUpd_other _ _ hib, hacc] at ha; cases ha
      acceptedBeforeVote := fun vr hvr t La ha hlt => by
        simp only [nextBootstrap, hv, List.mem_singleton] at hvr; subst hvr
        simp only [nextBootstrap, fnUpd_same, hacc, List.mem_singleton] at ha
        injection ha with ht _; subst ht; dsimp only at hlt; omega
      commitRecs := fun cm hcm => by simp only [nextBootstrap, hc] at hcm; cases hcm
      leaderCompleteness := fun cm hcm => by simp only [nextBootstrap, hc] at hcm; cases hcm
      reqVoteMsg := fun t c v ci ct hm => by
        have := (hinv.reqVoteMsg t c v ci ct hm).2.1; omega
      voteReplyMsg := fun t f to hm => by
        rcases hinv.voteReplyMsg t f to hm with ⟨vr, hvr, _⟩; rw [hv] at hvr; cases hvr
      aeMsg := fun t l pi pt es lc hm => by
        rcases hinv.aeMsg t l pi pt es lc hm with ⟨_, _, _, _, _, _, ⟨er, her, _⟩, _⟩
        rw [he] at her; cases her
      aeReplyMsg := fun t f to mi hm hpos => by
        rcases hinv.aeReplyMsg t f to mi hm hpos with ⟨_, _, _, ⟨er, her, _⟩, _⟩
        rw [he] at her; cases her
      snapMsg := fun t l si st ss hm => by
        rcases (hinv.snapMsg t l si st ss hm).2.2 with ⟨er, her, _⟩
        rw [he] at her; cases her
      snapLogRecs := fun si st ss sl hm => by simp only [nextBootstrap, hs] at hm; cases hm }

/-- (3) `startElection` -/
theorem Inv.preserve_startElection {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {c : NodeId} (hVoter : c ∈ (s.nodes c).effVoters) :
    Inv boot (nextStartElection s c) := by
  have hsync := hinv.nodeSync c
  have hkn_c : IsKnownLog s (s.hist.fullLog c) := Or.inl ⟨c, rfl⟩
  have hgood_c := hinv.goodLogs (s.hist.fullLog c) hkn_c
  have heff : (s.nodes c).effVoters = votersOfLog (s.hist.fullLog c) :=
    node_effVoters_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  have hne_c : (s.hist.fullLog c).length > 0 := by
    cases hl : s.hist.fullLog c with
    | nil =>
      rw [heff, hl] at hVoter
      simp [votersOfLog, stateOfLog, ClusterState.empty] at hVoter
    | cons _ _ => simp
  have hboot_pos : (s.nodes boot).term ≥ 1 := by
    rcases hgood_c.2.2.2.2 1 (by omega) hne_c with ⟨er, her, _⟩
    exact hinv.boot_term_pos_of_elected her
  have hc_term_pos : (s.nodes c).term ≥ 1 := by
    have h1 := hgood_c.2.1.1 (s.hist.fullLog c).length (by omega) (Nat.le_refl _)
    have h2 := hsync.2.2.2.2.2.2.2
    unfold logLastTerm at h2; omega
  let t := (s.nodes c).term + 1
  have ht_gt1 : t > 1 := by omega
  have hkn_eq : ∀ L, IsKnownLog (nextStartElection s c) L ↔ IsKnownLog s L := by
    intro L
    constructor
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨er, her, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · rcases List.mem_cons.mp hvr with rfl | hvr'
        · exact hkn_c
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr', rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨er, her, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, List.mem_cons_of_mem _ hvr, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
  have hno_old_vote : ∀ vr ∈ s.hist.votes, vr.voter = c → vr.term < t := by
    intro vr hvr hv
    have := (hinv.voteRecs vr hvr).2.2.1; rw [hv] at this; omega
  have hno_old_er : ∀ er ∈ s.hist.elected, er.leader = c → er.term < t := by
    intro er her hl
    have := (hinv.electionRecs er her).2.1; rw [hl] at this; omega
  have hlastIdx : (s.nodes c).lastIdx = (s.hist.fullLog c).length :=
    node_lastIdx_eq (by omega) hsync.2.2.2.1
  have hlastTerm : (s.nodes c).lastTerm = logLastTerm (s.hist.fullLog c) :=
    node_lastTerm_eq (by omega) hsync.2.2.2.1 hsync.2.2.2.2.1
  refine
    { nodeSync := fun i => by
        by_cases hi : i = c
        · rw [hi]; simp only [nextStartElection, fnUpd_same]
          exact ⟨hsync.1, hsync.2.1, hsync.2.2.1, hsync.2.2.2.1, hsync.2.2.2.2.1,
            hsync.2.2.2.2.2.1, hsync.2.2.2.2.2.2.1, by omega⟩
        · simpa [nextStartElection, hi] using hinv.nodeSync i
      leaderNode := fun l hL => by
        by_cases hl : l = c
        · rw [hl] at hL; simp [nextStartElection] at hL
        · simp only [nextStartElection, fnUpd_other _ _ hl] at hL ⊢
          exact hinv.leaderNode l hL
      candidateNode := fun x hx => by
        by_cases hxc : x = c
        · rw [hxc]
          simp only [nextStartElection, fnUpd_same]
          have hlt_c : logLastTerm (s.hist.fullLog c) < (s.nodes c).term + 1 := by
            have := hsync.2.2.2.2.2.2.2; omega
          refine ⟨ht_gt1, trivial, hlt_c, ?_, ?_⟩
          · intro er her hter hlead
            have := hno_old_er er her hlead; omega
          · intro v hv
            simp only [List.mem_singleton] at hv; subst hv
            refine ⟨_, List.mem_cons_self, rfl, rfl, rfl, ?_⟩
            simp [upToDate]
        · simp only [nextStartElection, fnUpd_other _ _ hxc] at hx ⊢
          have hc := hinv.candidateNode x hx
          refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun v hv => ?_⟩
          rcases hc.2.2.2.2 v hv with ⟨vr, hvr, hrest⟩
          exact ⟨vr, List.mem_cons_of_mem _ hvr, hrest⟩
      votedForRec := fun i cand hcand => by
        by_cases hi : i = c
        · rw [hi] at hcand ⊢
          simp only [nextStartElection, fnUpd_same] at hcand ⊢
          injection hcand with heq; subst heq
          exact ⟨by omega, _, List.mem_cons_self, rfl, rfl, rfl⟩
        · simp only [nextStartElection, fnUpd_other _ _ hi] at hcand ⊢
          rcases hinv.votedForRec i cand hcand with ⟨hp, vr, hvr, hrest⟩
          exact ⟨hp, vr, List.mem_cons_of_mem _ hvr, hrest⟩
      nodeCommit := fun i hi => by
        by_cases h : i = c
        · rw [h] at hi ⊢; simp only [nextStartElection, fnUpd_same] at hi ⊢
          rcases hinv.nodeCommit c hi with ⟨cm, hcm, ht, hge, hpre⟩
          exact ⟨cm, hcm, by omega, hge, hpre⟩
        · simp only [nextStartElection, fnUpd_other _ _ h] at hi ⊢
          exact hinv.nodeCommit i hi
      nodeSnap := fun i hi => by
        by_cases h : i = c
        · rw [h] at hi ⊢; simp only [nextStartElection, fnUpd_same] at hi ⊢
          rcases hinv.nodeSnap c hi with ⟨cm, hcm, ht, hge, hpre⟩
          exact ⟨cm, hcm, by omega, hge, hpre⟩
        · simp only [nextStartElection, fnUpd_other _ _ h] at hi ⊢
          exact hinv.nodeSnap i hi
      goodLogs := fun L hkn => hinv.goodLogs L ((hkn_eq L).mp hkn)
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix L1 L2 i1 i2 ((hkn_eq L1).mp h1) ((hkn_eq L2).mp h2)
      leaderMaxTerm := fun l L k hL hkn => by
        by_cases hl : l = c
        · rw [hl] at hL; simp [nextStartElection] at hL
        · simp only [nextStartElection, fnUpd_other _ _ hl] at hL ⊢
          exact hinv.leaderMaxTerm l L k hL ((hkn_eq L).mp hkn)
      voteRecs := fun vr hvr => by
        rcases List.mem_cons.mp hvr with rfl | hvr'
        · refine ⟨by dsimp; omega, ?_, by simp [nextStartElection], by simp [nextStartElection],
            by simp [nextStartElection], ?_⟩
          · by_cases hb : boot = c
            · rw [hb]; simp [nextStartElection]
            · simp [nextStartElection, hb]; exact hboot_pos
          · intro hhad
            rcases List.any_eq_true.mp hhad with ⟨er, her, hteq⟩
            exact ⟨er, her, beq_iff_eq.mp hteq⟩
        · have hv := hinv.voteRecs vr hvr'
          refine ⟨hv.1, ?_, ?_, ?_, ?_, hv.2.2.2.2.2⟩
          · by_cases hb : boot = c
            · rw [hb]; simp [nextStartElection]
            · simp [nextStartElection, hb]; exact hv.2.1
          · by_cases hvc : vr.voter = c
            · rw [hvc]; simp [nextStartElection]; have := hv.2.2.1; rw [hvc] at this; omega
            · simp [nextStartElection, hvc, hv.2.2.1]
          · by_cases hcc : vr.cand = c
            · rw [hcc]; simp [nextStartElection]; have := hv.2.2.2.1; rw [hcc] at this; omega
            · simp [nextStartElection, hcc, hv.2.2.2.1]
          · by_cases hvc : vr.voter = c
            · rw [hvc]; have := hno_old_vote vr hvr' hvc; simp [nextStartElection]; omega
            · simp only [nextStartElection, fnUpd_other _ _ hvc]; exact hv.2.2.2.2.1
      voteUnique := fun vr1 h1 vr2 h2 ht hv => by
        rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
        · rfl
        · have := hno_old_vote vr2 h2' hv.symm; dsimp at ht; omega
        · have := hno_old_vote vr1 h1' hv; dsimp at ht; omega
        · exact hinv.voteUnique vr1 h1' vr2 h2' ht hv
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        refine ⟨hr.1, ?_, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, ?_⟩
        · by_cases hl : er.leader = c
          · rw [hl]; simp [nextStartElection]; have := hr.2.1; rw [hl] at this; omega
          · simp [nextStartElection, hl, hr.2.1]
        · intro hgt
          rcases hr.2.2.2.2.2.2 hgt with ⟨hlt, hall⟩
          refine ⟨hlt, fun v hv => ?_⟩
          rcases hall v hv with ⟨vr, hvr, hrest⟩
          exact ⟨vr, List.mem_cons_of_mem _ hvr, hrest⟩
      acceptedRecs := fun i t' La ha => by
        have h := hinv.acceptedRecs i t' La ha
        refine ⟨h.1, ?_, h.2.2.1, ?_⟩
        · by_cases hi : i = c
          · rw [hi]; simp [nextStartElection]; have := h.2.1; rw [hi] at this; omega
          · simp [nextStartElection, hi, h.2.1]
        · intro P hP
          rcases h.2.2.2 P hP with hpre | ⟨er, her, h1, h2, h3⟩
          · exact Or.inl hpre
          · refine Or.inr ⟨er, her, h1, ?_, h3⟩
            by_cases hi : i = c
            · rw [hi]; simp [nextStartElection]; rw [hi] at h2; omega
            · simp [nextStartElection, hi, h2]
      acceptedBeforeVote := fun vr hvr t' La ha hlt P hP => by
        rcases List.mem_cons.mp hvr with rfl | hvr'
        · rcases (hinv.acceptedRecs c t' La ha).2.2.2 P hP with hpre | ⟨er, her, h1, h2, h3⟩
          · exact Or.inl hpre
          · exact Or.inr ⟨er, her, h1, Or.inl (by dsimp; omega), h3⟩
        · exact hinv.acceptedBeforeVote vr hvr' t' La ha hlt P hP
      commitRecs := hinv.commitRecs
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t' x v ci ct hm => by
        rcases List.mem_append.mp hm with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨dst, _, heq⟩
          injection heq with ht' hx hv hci hct
          subst ht'; subst hx; subst hv; subst hci; subst hct
          refine ⟨ht_gt1, ?_, by simp [nextStartElection], ?_⟩
          · by_cases hb : boot = c
            · rw [hb]; simp [nextStartElection]
            · simp [nextStartElection, hb]; exact hboot_pos
          · intro _ _; exact ⟨hlastIdx.symm, hlastTerm.symm⟩
        · have h := hinv.reqVoteMsg t' x v ci ct hold
          refine ⟨h.1, ?_, ?_, ?_⟩
          · by_cases hb : boot = c
            · rw [hb]; simp [nextStartElection]
            · simp [nextStartElection, hb]; exact h.2.1
          · by_cases hx : x = c
            · rw [hx]; simp [nextStartElection]; have := h.2.2.1; rw [hx] at this; omega
            · simp [nextStartElection, hx, h.2.2.1]
          · by_cases hx : x = c
            · rw [hx]; simp [nextStartElection]; intro hte; have := h.2.2.1; rw [hx] at this; omega
            · simp only [nextStartElection, fnUpd_other _ _ hx]; exact h.2.2.2
      voteReplyMsg := fun t' f to hm => by
        rcases List.mem_append.mp hm with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨_, _, heq⟩; cases heq
        · rcases hinv.voteReplyMsg t' f to hold with ⟨vr, hvr, h1, h2, h3, h4⟩
          refine ⟨vr, List.mem_cons_of_mem _ hvr, h1, h2, h3, ?_⟩
          by_cases hto : to = c
          · rw [hto]
            have hcand_le := (hinv.voteRecs vr hvr).2.2.2.1
            rw [h3, hto, h1] at hcand_le
            simp only [nextStartElection, fnUpd_same]
            intro hteq; omega
          · simp only [nextStartElection, fnUpd_other _ _ hto]; exact h4
      aeMsg := fun t' l pi pt es lc hm => by
        rcases List.mem_append.mp hm with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨_, _, heq⟩; cases heq
        · rcases hinv.aeMsg t' l pi pt es lc hold with ⟨Lae, h1, h2, h3, h4, h5, h6, h7, h8⟩
          refine ⟨Lae, h1, h2, h3, h4, h5, h6, h7, ?_⟩
          by_cases hl : l = c
          · rw [hl]; simp [nextStartElection]
          · simp [nextStartElection, hl]; exact h8
      aeReplyMsg := fun t' f to mi hm hpos => by
        rcases List.mem_append.mp hm with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨_, _, heq⟩; cases heq
        · rcases hinv.aeReplyMsg t' f to mi hold hpos with ⟨Lack, h1, h2, h3, h4⟩
          refine ⟨Lack, h1, h2, h3, ?_⟩
          by_cases hto : to = c
          · rw [hto]; simp [nextStartElection]
          · simp [nextStartElection, hto]; exact h4
      snapMsg := fun t' l si st ss hm => by
        rcases List.mem_append.mp hm with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨_, _, heq⟩; cases heq
        · exact hinv.snapMsg t' l si st ss hold
      snapLogRecs := hinv.snapLogRecs }

/-- (4) `handleRequestVote` -/
theorem Inv.preserve_handleRequestVote {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {v c : NodeId} {t cLastIdx cLastTerm : Nat}
    (hMsg : Msg.requestVote t c v cLastIdx cLastTerm ∈ s.net)
    (hTerm : t ≥ (s.nodes v).term) :
    Inv boot (nextHandleRequestVote s v c t cLastIdx cLastTerm) := by
  have hrv := hinv.reqVoteMsg t c v cLastIdx cLastTerm hMsg
  have hsync := hinv.nodeSync v
  have hkn_v : IsKnownLog s (s.hist.fullLog v) := Or.inl ⟨v, rfl⟩
  let n := s.nodes v
  let stepped :=
    if t > n.term then { n with term := t, role := .follower, votedFor := none,
                                votes := [], matchIdx := fun _ => 0 }
    else n
  let canGrant :=
    (stepped.votedFor == none || stepped.votedFor == some c) &&
    upToDate cLastTerm cLastIdx stepped.lastTerm stepped.lastIdx
  let n' := if canGrant then { stepped with votedFor := some c } else stepped
  let vrNew : VoteRec NodeId T :=
    { term := t, voter := v, cand := c, voterLog := s.hist.fullLog v,
      hadLeaderInTerm := s.hist.elected.any (fun e => e.term == t) }
  have hstep_term : stepped.term = t := by
    dsimp [stepped]
    by_cases hgt : t > (s.nodes v).term
    · simp [n, hgt]
    · simp [n, hgt]; omega
  have hn'_term : n'.term = t := by dsimp [n']; split <;> exact hstep_term
  have hstep_fields : stepped.snapIdx = n.snapIdx ∧ stepped.applied = n.applied ∧
      stepped.commit = n.commit ∧ stepped.tail = n.tail ∧ stepped.snapTerm = n.snapTerm ∧
      stepped.snapState = n.snapState ∧ stepped.appliedState = n.appliedState := by
    dsimp [stepped]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hn'_fields : n'.snapIdx = n.snapIdx ∧ n'.applied = n.applied ∧
      n'.commit = n.commit ∧ n'.tail = n.tail ∧ n'.snapTerm = n.snapTerm ∧
      n'.snapState = n.snapState ∧ n'.appliedState = n.appliedState := by
    dsimp [n']; split <;> exact hstep_fields
  have hsnap_le_len : (s.nodes v).snapIdx ≤ (s.hist.fullLog v).length := by
    have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; omega
  have hstep_lastIdx : stepped.lastIdx = (s.hist.fullLog v).length :=
    node_lastIdx_eq (by rw [hstep_fields.1]; exact hsnap_le_len)
      (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
  have hstep_lastTerm : stepped.lastTerm = logLastTerm (s.hist.fullLog v) :=
    node_lastTerm_eq (by rw [hstep_fields.1]; exact hsnap_le_len)
      (by rw [hstep_fields.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.1)
      (by rw [hstep_fields.2.2.2.2.1, hstep_fields.1]; exact hsync.2.2.2.2.1)
  have hvr_mono : ∀ vr, vr ∈ s.hist.votes →
      vr ∈ (nextHandleRequestVote s v c t cLastIdx cLastTerm).hist.votes := by
    intro vr hvr
    change vr ∈ (if canGrant then vrNew :: s.hist.votes else s.hist.votes)
    cases hcg : canGrant <;> simp [hvr]
  have hvr_cases : ∀ vr, vr ∈ (nextHandleRequestVote s v c t cLastIdx cLastTerm).hist.votes →
      (canGrant = true ∧ vr = vrNew) ∨ vr ∈ s.hist.votes := by
    intro vr hvr
    change vr ∈ (if canGrant then vrNew :: s.hist.votes else s.hist.votes) at hvr
    cases hcg : canGrant with
    | true =>
      rw [hcg] at hvr; simp only [↓reduceIte, List.mem_cons] at hvr
      rcases hvr with rfl | hvr'; exact Or.inl ⟨rfl, rfl⟩; exact Or.inr hvr'
    | false =>
      rw [hcg] at hvr; simp only [Bool.false_eq_true, ↓reduceIte] at hvr
      exact Or.inr hvr
  have hkn_eq : ∀ L, IsKnownLog (nextHandleRequestVote s v c t cLastIdx cLastTerm) L ↔ IsKnownLog s L := by
    intro L
    constructor
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨er, her, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · rcases hvr_cases vr hvr with ⟨_, rfl⟩ | hvr'
        · exact hkn_v
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr', rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
    · intro h
      rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t', ha⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨er, her, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr_mono vr hvr, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t', ha⟩))))
  have hn'_eq : (nextHandleRequestVote s v c t cLastIdx cLastTerm).nodes v = n' := by
    simp [nextHandleRequestVote, n', canGrant, stepped, n]
  have hgrant_imp : canGrant = true →
      (∀ vr ∈ s.hist.votes, vr.term = t → vr.voter = v → vr.cand = c) ∧
      upToDate cLastTerm cLastIdx (logLastTerm (s.hist.fullLog v)) (s.hist.fullLog v).length = true := by
    intro hcg
    dsimp [canGrant] at hcg
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcg
    have hup : upToDate cLastTerm cLastIdx (logLastTerm (s.hist.fullLog v)) (s.hist.fullLog v).length = true := by
      have h2 := hcg.2; rwa [hstep_lastTerm, hstep_lastIdx] at h2
    refine ⟨?_, hup⟩
    intro vr hvr hvt hvv
    have hvrec := hinv.voteRecs vr hvr
    by_cases hgt : t > n.term
    · have := hvrec.2.2.1; rw [hvv] at this; dsimp [n] at hgt; omega
    · have hteq : n.term = t := by dsimp [n] at hgt ⊢; omega
      have hvf := hvrec.2.2.2.2.1 (by rw [hvv]; dsimp [n] at hteq; omega)
      have hstep_eq : stepped = n := by dsimp [stepped]; simp [hgt]
      rw [hstep_eq] at hcg
      rw [hvv] at hvf
      rcases hcg.1 with hnone | hsome
      · rw [hnone] at hvf; cases hvf
      · rw [hsome] at hvf; injection hvf with heq; exact heq.symm
  have hupd_vf_eq : ∀ (m : Node NodeId T) (x : NodeId),
      m.votedFor = some x → { m with votedFor := some x } = m := by
    intro m x hm; cases m; dsimp at hm; subst hm; rfl
  have hrole_unchanged : (n'.role = .leader → t = n.term ∧ n' = n) ∧
      (n'.role = .candidate → t = n.term ∧ n' = n) := by
    constructor
    · intro hL
      have hngt : ¬ t > n.term := by
        intro hgt; dsimp [n', stepped] at hL; simp [hgt] at hL; split at hL <;> simp at hL
      have hteq : t = n.term := by dsimp [n] at hngt ⊢; omega
      have hst : stepped = n := by dsimp [stepped]; simp [hngt]
      have hLn : n.role = .leader := by dsimp [n'] at hL; rw [hst] at hL; split at hL <;> exact hL
      have hvfn : n.votedFor = some v := (hinv.leaderNode v hLn).2.1
      refine ⟨hteq, ?_⟩
      dsimp [n']; rw [hst]
      split
      · rename_i hcg
        dsimp [canGrant] at hcg; rw [hst, hvfn] at hcg
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.some.injEq] at hcg
        rcases hcg.1 with hno | hvc
        · cases hno
        · exact hupd_vf_eq n c (by rw [hvfn, hvc])
      · rfl
    · intro hC
      have hngt : ¬ t > n.term := by
        intro hgt; dsimp [n', stepped] at hC; simp [hgt] at hC; split at hC <;> simp at hC
      have hteq : t = n.term := by dsimp [n] at hngt ⊢; omega
      have hst : stepped = n := by dsimp [stepped]; simp [hngt]
      have hCn : n.role = .candidate := by dsimp [n'] at hC; rw [hst] at hC; split at hC <;> exact hC
      have hvfn : n.votedFor = some v := (hinv.candidateNode v hCn).2.1
      refine ⟨hteq, ?_⟩
      dsimp [n']; rw [hst]
      split
      · rename_i hcg
        dsimp [canGrant] at hcg; rw [hst, hvfn] at hcg
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.some.injEq] at hcg
        rcases hcg.1 with hno | hvc
        · cases hno
        · exact hupd_vf_eq n c (by rw [hvfn, hvc])
      · rfl
  refine
    { nodeSync := fun i => by
        by_cases hi : i = v
        · rw [hi, hn'_eq]
          simp only [nextHandleRequestVote]
          exact ⟨by rw [hn'_fields.1, hn'_fields.2.1]; exact hsync.1,
                 by rw [hn'_fields.2.1, hn'_fields.2.2.1]; exact hsync.2.1,
                 by rw [hn'_fields.2.2.1]; exact hsync.2.2.1,
                 by rw [hn'_fields.2.2.2.1, hn'_fields.1]; exact hsync.2.2.2.1,
                 by rw [hn'_fields.2.2.2.2.1, hn'_fields.1]; exact hsync.2.2.2.2.1,
                 by rw [hn'_fields.2.2.2.2.2.1, hn'_fields.1]; exact hsync.2.2.2.2.2.1,
                 by rw [hn'_fields.2.2.2.2.2.2, hn'_fields.2.1]; exact hsync.2.2.2.2.2.2.1,
                 by rw [hn'_term]; have := hsync.2.2.2.2.2.2.2; omega⟩
        · simpa [nextHandleRequestVote, hi] using hinv.nodeSync i
      leaderNode := fun l hL => by
        by_cases hl : l = v
        · rw [hl] at hL ⊢; rw [hn'_eq] at hL ⊢
          have ⟨_, heqn⟩ := hrole_unchanged.1 hL
          rw [heqn] at hL ⊢
          simpa [nextHandleRequestVote] using hinv.leaderNode v hL
        · simp only [nextHandleRequestVote, fnUpd_other _ _ hl] at hL ⊢
          exact hinv.leaderNode l hL
      candidateNode := fun x hx => by
        by_cases hxv : x = v
        · rw [hxv] at hx ⊢; rw [hn'_eq] at hx ⊢
          have ⟨_, heqn⟩ := hrole_unchanged.2 hx
          rw [heqn] at hx ⊢
          have hc := hinv.candidateNode v hx
          refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun w hw => ?_⟩
          rcases hc.2.2.2.2 w hw with ⟨vr, hvr, hrest⟩
          exact ⟨vr, hvr_mono vr hvr, hrest⟩
        · simp only [nextHandleRequestVote, fnUpd_other _ _ hxv] at hx ⊢
          have hc := hinv.candidateNode x hx
          refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun w hw => ?_⟩
          rcases hc.2.2.2.2 w hw with ⟨vr, hvr, hrest⟩
          exact ⟨vr, hvr_mono vr hvr, hrest⟩
      votedForRec := fun i cand hcand => by
        by_cases hi : i = v
        · rw [hi] at hcand ⊢; rw [hn'_eq] at hcand ⊢; rw [hn'_term]
          dsimp [n'] at hcand
          cases hcg : canGrant with
          | true =>
            rw [hcg] at hcand; simp only [↓reduceIte] at hcand
            injection hcand with heq; subst heq
            refine ⟨by omega, vrNew, ?_, rfl, rfl, rfl⟩
            dsimp [nextHandleRequestVote]
            change vrNew ∈ (if canGrant then vrNew :: s.hist.votes else s.hist.votes)
            rw [hcg]; simp
          | false =>
            rw [hcg] at hcand; simp only [Bool.false_eq_true, ↓reduceIte] at hcand
            by_cases hgt : t > n.term
            · dsimp [stepped] at hcand; simp [hgt] at hcand
            · have hteq : t = (s.nodes v).term := by dsimp [n] at hgt; omega
              dsimp [stepped] at hcand; simp [hgt] at hcand
              rcases hinv.votedForRec v cand hcand with ⟨hp, vr, hvr, ht', hv', hc'⟩
              exact ⟨by omega, vr, hvr_mono vr hvr, by omega, hv', hc'⟩
        · simp only [nextHandleRequestVote, fnUpd_other _ _ hi] at hcand ⊢
          rcases hinv.votedForRec i cand hcand with ⟨hp, vr, hvr, hrest⟩
          exact ⟨hp, vr, hvr_mono vr hvr, hrest⟩
      nodeCommit := fun i hi => by
        by_cases h : i = v
        · rw [h] at hi ⊢; rw [hn'_eq, hn'_fields.2.2.1] at hi ⊢; rw [hn'_term]
          rcases hinv.nodeCommit v hi with ⟨cm, hcm, ht, hge, hpre⟩
          exact ⟨cm, hcm, by omega, hge, hpre⟩
        · simp only [nextHandleRequestVote, fnUpd_other _ _ h] at hi ⊢
          exact hinv.nodeCommit i hi
      nodeSnap := fun i hi => by
        by_cases h : i = v
        · rw [h] at hi ⊢; rw [hn'_eq, hn'_fields.1] at hi ⊢; rw [hn'_term]
          rcases hinv.nodeSnap v hi with ⟨cm, hcm, ht, hge, hpre⟩
          exact ⟨cm, hcm, by omega, hge, hpre⟩
        · simp only [nextHandleRequestVote, fnUpd_other _ _ h] at hi ⊢
          exact hinv.nodeSnap i hi
      goodLogs := fun L hkn => hinv.goodLogs L ((hkn_eq L).mp hkn)
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 =>
        hinv.sameTermPrefix L1 L2 i1 i2 ((hkn_eq L1).mp h1) ((hkn_eq L2).mp h2)
      leaderMaxTerm := fun l L k hL hkn => by
        by_cases hl : l = v
        · rw [hl] at hL ⊢; rw [hn'_eq] at hL ⊢
          have ⟨_, heqn⟩ := hrole_unchanged.1 hL
          rw [heqn] at hL ⊢
          exact hinv.leaderMaxTerm v L k hL ((hkn_eq L).mp hkn)
        · simp only [nextHandleRequestVote, fnUpd_other _ _ hl] at hL ⊢
          exact hinv.leaderMaxTerm l L k hL ((hkn_eq L).mp hkn)
      voteRecs := fun vr hvr => by
        rcases hvr_cases vr hvr with ⟨hcg, rfl⟩ | hvr'
        · dsimp only [vrNew]
          refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
          · by_cases hb : boot = v
            · rw [hb, hn'_eq, hn'_term]; omega
            · simp [nextHandleRequestVote, hb]; exact hrv.2.1
          · rw [hn'_eq, hn'_term]; exact Nat.le_refl _
          · by_cases hcv : c = v
            · have hnc : (nextHandleRequestVote s v c t cLastIdx cLastTerm).nodes c = n' := by
                simp only [nextHandleRequestVote, hcv, fnUpd_same, n', canGrant, stepped, n]
              rw [hnc, hn'_term]; exact Nat.le_refl _
            · simp only [nextHandleRequestVote, fnUpd_other _ _ hcv]; exact hrv.2.2.1
          · intro _; rw [hn'_eq]; dsimp [n']; rw [hcg]; rfl
          · intro hhad
            rcases List.any_eq_true.mp hhad with ⟨er, her, hteq⟩
            exact ⟨er, her, beq_iff_eq.mp hteq⟩
        · have hv := hinv.voteRecs vr hvr'
          refine ⟨hv.1, ?_, ?_, ?_, ?_, hv.2.2.2.2.2⟩
          · by_cases hb : boot = v
            · rw [hb, hn'_eq, hn'_term]; have := hv.2.1; rw [hb] at this; omega
            · simp [nextHandleRequestVote, hb, hv.2.1]
          · by_cases hvv : vr.voter = v
            · rw [hvv, hn'_eq, hn'_term]; have := hv.2.2.1; rw [hvv] at this; omega
            · simp [nextHandleRequestVote, hvv, hv.2.2.1]
          · by_cases hcv : vr.cand = v
            · rw [hcv, hn'_eq, hn'_term]; have := hv.2.2.2.1; rw [hcv] at this; omega
            · simp [nextHandleRequestVote, hcv, hv.2.2.2.1]
          · by_cases hvv : vr.voter = v
            · rw [hvv, hn'_eq, hn'_term]
              intro hteq
              have hle : vr.term ≤ n.term := by have := hv.2.2.1; rwa [hvv] at this
              have hne_gt : ¬ t > n.term := by omega
              have hstep_eq : stepped = n := by dsimp [stepped]; simp [hne_gt]
              have hvf := hv.2.2.2.2.1 (by rw [hvv]; dsimp [n] at hle hne_gt; omega)
              rw [hvv] at hvf
              dsimp [n']; rw [hstep_eq]
              cases hcg : canGrant with
              | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hvf
              | true =>
                simp only [↓reduceIte]
                have hcand_eq := (hgrant_imp hcg).1 vr hvr' hteq.symm hvv
                rw [hcand_eq]
            · simp only [nextHandleRequestVote, fnUpd_other _ _ hvv]; exact hv.2.2.2.2.1
      voteUnique := fun vr1 h1 vr2 h2 ht hv => by
        rcases hvr_cases vr1 h1 with ⟨hcg, rfl⟩ | h1' <;> rcases hvr_cases vr2 h2 with ⟨hcg2, rfl⟩ | h2'
        · rfl
        · exact ((hgrant_imp hcg).1 vr2 h2' ht.symm hv.symm).symm
        · exact (hgrant_imp hcg2).1 vr1 h1' ht hv
        · exact hinv.voteUnique vr1 h1' vr2 h2' ht hv
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        refine ⟨hr.1, ?_, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, ?_⟩
        · by_cases hl : er.leader = v
          · rw [hl, hn'_eq, hn'_term]; have := hr.2.1; rw [hl] at this; omega
          · simp [nextHandleRequestVote, hl, hr.2.1]
        · intro hgt
          rcases hr.2.2.2.2.2.2 hgt with ⟨hlt, hall⟩
          refine ⟨hlt, fun w hw => ?_⟩
          rcases hall w hw with ⟨vr, hvr, hrest⟩
          exact ⟨vr, hvr_mono vr hvr, hrest⟩
      acceptedRecs := fun i t' La ha => by
        have h := hinv.acceptedRecs i t' La ha
        refine ⟨h.1, ?_, h.2.2.1, ?_⟩
        · by_cases hi : i = v
          · rw [hi, hn'_eq, hn'_term]; have := h.2.1; rw [hi] at this; omega
          · simp [nextHandleRequestVote, hi, h.2.1]
        · intro P hP
          rcases h.2.2.2 P hP with hpre | ⟨er, her, h1, h2, h3⟩
          · exact Or.inl hpre
          · refine Or.inr ⟨er, her, h1, ?_, h3⟩
            by_cases hi : i = v
            · rw [hi, hn'_eq, hn'_term]; rw [hi] at h2; omega
            · simp [nextHandleRequestVote, hi, h2]
      acceptedBeforeVote := fun vr hvr t' La ha hlt P hP => by
        rcases hvr_cases vr hvr with ⟨_, rfl⟩ | hvr'
        · rcases (hinv.acceptedRecs v t' La ha).2.2.2 P hP with hpre | ⟨er, her, h1, h2, h3⟩
          · exact Or.inl hpre
          · refine Or.inr ⟨er, her, h1, ?_, h3⟩
            by_cases hlt' : er.term < t
            · exact Or.inl hlt'
            · have heq' : er.term = t := by omega
              refine Or.inr ⟨heq', ?_⟩
              exact List.any_eq_true.mpr ⟨er, her, by simp [heq']⟩
        · exact hinv.acceptedBeforeVote vr hvr' t' La ha hlt P hP
      commitRecs := hinv.commitRecs
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t' x dst ci ct hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · have h := hinv.reqVoteMsg t' x dst ci ct hm'
          refine ⟨h.1, ?_, ?_, ?_⟩
          · by_cases hb : boot = v
            · rw [hb, hn'_eq, hn'_term]; have := h.2.1; rw [hb] at this; omega
            · simp [nextHandleRequestVote, hb, h.2.1]
          · by_cases hx : x = v
            · rw [hx, hn'_eq, hn'_term]; have := h.2.2.1; rw [hx] at this; omega
            · simp [nextHandleRequestVote, hx, h.2.2.1]
          · by_cases hx : x = v
            · rw [hx, hn'_eq]
              intro ht' hC
              have ⟨_, heqn⟩ := hrole_unchanged.2 hC
              rw [heqn] at ht' hC
              have hres := h.2.2.2 (by rw [hx]; exact ht') (by rw [hx]; exact hC)
              rw [hx] at hres; exact hres
            · simp [nextHandleRequestVote, hx]; exact h.2.2.2
      voteReplyMsg := fun t' f to hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with ht' hf hto hcg
          subst t'; subst f; subst to
          have hcg' : canGrant = true := hcg.symm
          refine ⟨vrNew, ?_, rfl, rfl, rfl, ?_⟩
          · dsimp [nextHandleRequestVote]
            change vrNew ∈ (if canGrant then vrNew :: s.hist.votes else s.hist.votes)
            rw [hcg']; simp
          · intro htC hroleC
            have hct_eq : (s.nodes c).term = t ∧ (s.nodes c).role = .candidate := by
              by_cases hcv : c = v
              · have hnc : (nextHandleRequestVote s v c t cLastIdx cLastTerm).nodes c = n' := by
                  simp only [nextHandleRequestVote, hcv, fnUpd_same, n', canGrant, stepped, n]
                rw [hnc] at htC hroleC
                have ⟨_, heqn⟩ := hrole_unchanged.2 hroleC
                rw [heqn] at htC hroleC; rw [hcv]; exact ⟨htC, hroleC⟩
              · simp [nextHandleRequestVote, hcv] at htC hroleC; exact ⟨htC, hroleC⟩
            rcases hrv.2.2.2 hct_eq.1 hct_eq.2 with ⟨hclen, hclt⟩
            dsimp only [nextHandleRequestVote, vrNew]
            rw [hclen, hclt]
            exact (hgrant_imp hcg').2
        · rcases hinv.voteReplyMsg t' f to hm' with ⟨vr, hvr, h1, h2, h3, h4⟩
          refine ⟨vr, hvr_mono vr hvr, h1, h2, h3, ?_⟩
          by_cases hto : to = v
          · rw [hto, hn'_eq]
            intro htC hroleC
            have ⟨_, heqn⟩ := hrole_unchanged.2 hroleC
            rw [heqn] at htC hroleC
            have hres := h4 (by rw [hto]; exact htC) (by rw [hto]; exact hroleC)
            rw [hto] at hres; exact hres
          · simp [nextHandleRequestVote, hto]; exact h4
      aeMsg := fun t' l pi pt es lc hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.aeMsg t' l pi pt es lc hm' with ⟨Lae, h1, h2, h3, h4, h5, h6, h7, h8⟩
          refine ⟨Lae, h1, h2, h3, h4, h5, h6, h7, ?_⟩
          by_cases hl : l = v
          · rw [hl, hn'_eq]
            intro hL ht'
            have ⟨_, heqn⟩ := hrole_unchanged.1 hL
            rw [heqn] at hL ht'
            have hres := h8 (by rw [hl]; exact hL) (by rw [hl]; exact ht')
            rw [hl] at hres; exact hres
          · simp [nextHandleRequestVote, hl]; exact h8
      aeReplyMsg := fun t' f to mi hm hpos => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · rcases hinv.aeReplyMsg t' f to mi hm' hpos with ⟨Lack, h1, h2, h3, h4⟩
          refine ⟨Lack, h1, h2, h3, ?_⟩
          by_cases hto : to = v
          · rw [hto, hn'_eq]
            intro hL ht'
            have ⟨_, heqn⟩ := hrole_unchanged.1 hL
            rw [heqn] at hL ht'
            have hres := h4 (by rw [hto]; exact hL) (by rw [hto]; exact ht')
            rw [hto] at hres; exact hres
          · simp [nextHandleRequestVote, hto]; exact h4
      snapMsg := fun t' l si st ss hm => by
        rcases List.mem_cons.mp hm with heq | hm'
        · cases heq
        · exact hinv.snapMsg t' l si st ss hm'
      snapLogRecs := hinv.snapLogRecs }

/-- (2) `propose` -/
theorem Inv.preserve_propose {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {l : NodeId} {cmd : Cmd NodeId T.Op}
    (hLeader : (s.nodes l).role = .leader)
    (hValid : validCmd boot (s.nodes l).projectedState cmd)
    (hVoterGuard : cmd.isVoterChange = true →
      (s.nodes l).hasUncommittedVoterChange = false ∧
      (s.nodes l).commit > 0 ∧
      (s.nodes l).termAt (s.nodes l).commit = (s.nodes l).term) :
    Inv boot (nextPropose s l cmd) := by
  have hsync := hinv.nodeSync l
  have hL := hinv.leaderNode l hLeader
  have hkn_l : IsKnownLog s (s.hist.fullLog l) := Or.inl ⟨l, rfl⟩
  have hgood_l := hinv.goodLogs (s.hist.fullLog l) hkn_l
  let e : Entry NodeId T.Op := { term := (s.nodes l).term, cmd := cmd }
  let L := s.hist.fullLog l
  let L' := L ++ [e]
  have hproj : (s.nodes l).projectedState = stateOfLog L :=
    node_projectedState_eq hsync.1 hsync.2.2.2.1 hsync.2.2.2.2.2.2.1
  have hValid' : validCmd boot (stateOfLog L) e.cmd := by rwa [← hproj]
  have hpre_L : IsPrefix L L' := IsPrefix.append_right L [e]
  have hL_ne : L.length > 0 := by
    dsimp only [L]
    rcases hL.2.2.2.1 with ⟨er, her, _, _, hpre_er, _⟩
    have hrec := hinv.electionRecs er her
    by_cases h1 : er.term = 1
    · have hb := hrec.2.2.2.2.2.1 h1
      have := hpre_er.1; rw [hb.2.1] at this; simp at this; omega
    · have hgt : er.term > 1 := by have := hrec.1; omega
      have hwf : ElectionWF boot s er :=
        ⟨hgt, hinv.goodLogs _ (Or.inr (Or.inl ⟨er, her, rfl⟩)), (hrec.2.2.2.2.2.2 hgt).1,
         hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1⟩
      have hne := electionLog_nonempty hwf
      have := hpre_er.1; omega
  have hgood_L' : GoodLog boot (nextPropose s l cmd) L' := by
    refine ⟨hgood_l.1.append_singleton hValid', hgood_l.2.1.append_singleton hL.1 hsync.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
    · intro e1 hg1
      rw [logGet_append_left L [e] hL_ne] at hg1
      exact hgood_l.2.2.1 e1 hg1
    · intro k ek h1 h2 hg hvc
      simp only [L', List.length_append, List.length_singleton] at h2
      by_cases hle : k ≤ L.length
      · rw [logGet_append_left L [e] hle] at hg
        rcases hgood_l.2.2.2.1 k ek h1 hle hg hvc with ⟨cm, hcm, ht, hlt, hpre, hcfg, hnovc⟩
        refine ⟨cm, hcm, ht, hlt, ?_, hcfg, ?_⟩
        · rw [← hpre_L.take_eq_of_le (by omega)]; exact hpre
        · intro j ej hj1 hj2 hgj
          rw [logGet_append_left L [e] (by omega)] at hgj
          exact hnovc j ej hj1 hj2 hgj
      · have hkeq : k = L.length + 1 := by omega
        subst hkeq
        rw [logGet_append_singleton_last] at hg
        injection hg with heq; subst heq
        rcases hVoterGuard hvc with ⟨hnovc_b, hcomm_pos, hcomm_t⟩
        have hcomm_log_t : logTermAt L (s.nodes l).commit = (s.nodes l).term := by
          rw [← node_termAt_eq hsync.2.2.2.1 hsync.2.2.2.2.1 (by omega)]; exact hcomm_t
        rcases hL.2.2.2.2.2.1 hcomm_pos hcomm_log_t with ⟨cm, hcm, hcm_t, hcm_idx, hcm_log, hcm_cfg⟩
        have hnovc_all := (hasUncommittedVoterChange_false_iff hsync.2.2.2.1 (by omega)).mp hnovc_b
        have hlen_c : (s.nodes l).commit ≤ L.length := hsync.2.2.1
        refine ⟨cm, hcm, hcm_t, by omega, ?_, hcm_cfg hnovc_b, ?_⟩
        · have htk : L'.take (L.length + 1 - 1) = L := by simp [L']
          rw [htk, hcm_log]
          exact IsPrefix.take_left L (s.nodes l).commit
        · intro j ej hj1 hj2 hgj
          rw [logGet_append_left L [e] (by omega)] at hgj
          exact hnovc_all j ej (by omega) (by dsimp only [L] at hj2; omega) hgj
    · intro k hk1 hk2
      simp only [L', List.length_append, List.length_singleton] at hk2
      by_cases hle : k ≤ L.length
      · rw [logTermAt_append_left L [e] hle, ← hpre_L.take_eq_of_le hle]
        exact hgood_l.2.2.2.2 k hk1 hle
      · have hkeq : k = L.length + 1 := by omega
        subst hkeq
        rw [logTermAt_append_singleton_last]
        rcases hL.2.2.2.1 with ⟨er, her, hter, _, hpre_er, _⟩
        refine ⟨er, her, hter, ?_⟩
        have htk : L'.take (L.length + 1) = L' := by
          dsimp only [L']; rw [List.take_of_length_le]; simp
        rw [htk]
        exact IsPrefix.trans hpre_er hpre_L
  have hkn_new : ∀ M, IsKnownLog (nextPropose s l cmd) M → IsKnownLog s M ∨ M = L' := by
    intro M h
    rcases h with ⟨i, hi⟩ | ⟨er, her, rfl⟩ | ⟨cm, hcm, rfl⟩ | ⟨vr, hvr, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨i, t, ha⟩
    · by_cases hil : i = l
      · rw [hil] at hi; simp [nextPropose] at hi; exact Or.inr hi
      · simp [nextPropose, hil] at hi; exact Or.inl (Or.inl ⟨i, hi⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨er, her, rfl⟩))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr, rfl⟩))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))))
    · by_cases hil : i = l
      · rw [hil] at ha; simp only [nextPropose, fnUpd_same, List.mem_cons] at ha
        rcases ha with heq | ha'
        · injection heq with _ hM; exact Or.inr hM
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, t, ha'⟩)))))
      · simp only [nextPropose, fnUpd_other _ _ hil] at ha
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t, ha⟩)))))
  have huniq_lead : ∀ l', (s.nodes l').role = .leader → (s.nodes l').term = (s.nodes l).term → l' = l := by
    intro l' hL' ht'
    rcases (hinv.leaderNode l' hL').2.2.2.1 with ⟨er', her', hter', hlead', _⟩
    rcases hL.2.2.2.1 with ⟨er, her, hter, hlead, _⟩
    have heq := hinv.electionUnique er' her' er her (by omega)
    rw [← hlead', ← hlead, heq]
  have hsnap_le_L : (s.nodes l).snapIdx ≤ L.length := by
    have := hsync.1; have := hsync.2.1; have := hsync.2.2.1; dsimp only [L]; omega
  have happ_le_L : (s.nodes l).applied ≤ L.length := by
    have := hsync.2.1; have := hsync.2.2.1; dsimp only [L]; omega
  have hcomm_le_L : (s.nodes l).commit ≤ L.length := hsync.2.2.1
  have htail' : (s.nodes l).tail ++ [e] = L'.drop (s.nodes l).snapIdx := by
    dsimp only [L', L]
    rw [hsync.2.2.2.1, List.drop_append]
    have hsub : (s.nodes l).snapIdx - (s.hist.fullLog l).length = 0 := by
      dsimp only [L] at hsnap_le_L; omega
    simp [hsub]
  refine
    { nodeSync := fun i => by
        by_cases hil : i = l
        · rw [hil]
          simp only [nextPropose, fnUpd_same]
          refine ⟨hsync.1, hsync.2.1, by simp; omega, htail',
            by rw [logTermAt_append_left L [e] hsnap_le_L]; exact hsync.2.2.2.2.1,
            by rw [← stateAt_of_prefix hpre_L hsnap_le_L]; exact hsync.2.2.2.2.2.1,
            by rw [← stateAt_of_prefix hpre_L happ_le_L]; exact hsync.2.2.2.2.2.2.1,
            by rw [logLastTerm_append_singleton]; exact Nat.le_refl _⟩
        · simpa [nextPropose, hil] using hinv.nodeSync i
      leaderNode := fun l' hL' => by
        by_cases hl' : l' = l
        · rw [hl']
          simp only [nextPropose, fnUpd_same]
          refine ⟨hL.1, hL.2.1, by simp, ?_, ?_, ?_, hL.2.2.2.2.2.2⟩
          · rcases hL.2.2.2.1 with ⟨er, her, ht, hlead, hpre, hext⟩
            refine ⟨er, her, ht, hlead, IsPrefix.trans hpre hpre_L, ?_⟩
            intro j hj1 hj2
            simp only [List.length_append, List.length_singleton] at hj2
            by_cases hjl : j ≤ (s.hist.fullLog l).length
            · rw [logTermAt_append_left L [e] hjl]; exact hext j hj1 hjl
            · have : j = (s.hist.fullLog l).length + 1 := by omega
              subst this; rw [logTermAt_append_singleton_last]
          · intro v hv
            rcases hL.2.2.2.2.1 v hv with ⟨hle, hacc⟩
            refine ⟨by simp; omega, ?_⟩
            rw [← hpre_L.take_eq_of_le hle]
            by_cases hvl : v = l
            · rw [hvl] at hacc ⊢; simp only [fnUpd_same, List.mem_cons]; exact Or.inr hacc
            · simp only [fnUpd_other _ _ hvl]; exact hacc
          · intro hc htc
            rw [logTermAt_append_left L [e] hcomm_le_L] at htc
            rcases hL.2.2.2.2.2.1 hc htc with ⟨cm, hcm, h1, h2, h3, h4⟩
            refine ⟨cm, hcm, h1, h2, by rw [← hpre_L.take_eq_of_le hcomm_le_L]; exact h3, ?_⟩
            intro hnv
            have hnv_old : (s.nodes l).hasUncommittedVoterChange = false := by
              rw [hasUncommittedVoterChange_false_iff hsync.2.2.2.1 (by have := hsync.1; have := hsync.2.1; omega)]
              have hnv_new := (hasUncommittedVoterChange_false_iff htail' (by dsimp only; have := hsync.1; have := hsync.2.1; omega)).mp hnv
              intro j ej hj1 hj2 hgj
              exact hnv_new j ej hj1 (by dsimp only [L', L] at *; simp; omega)
                (by rw [logGet_append_left L [e] hj2]; exact hgj)
            exact h4 hnv_old
        · simp only [nextPropose, fnUpd_other _ _ hl'] at hL' ⊢
          have hln := hinv.leaderNode l' hL'
          refine ⟨hln.1, hln.2.1, ?_, hln.2.2.2.1, ?_, hln.2.2.2.2.2.1, hln.2.2.2.2.2.2⟩
          · simp [hln.2.2.1]
          · intro v hv
            rcases hln.2.2.2.2.1 v hv with ⟨hle, hacc⟩
            refine ⟨hle, ?_⟩
            by_cases hvl : v = l
            · rw [hvl] at hacc ⊢; simp [hacc]
            · simp [hvl, hacc]
      candidateNode := fun c hc => by
        by_cases hcl : c = l
        · rw [hcl] at hc; simp [nextPropose, hLeader] at hc
        · simp only [nextPropose, fnUpd_other _ _ hcl] at hc ⊢
          exact hinv.candidateNode c hc
      votedForRec := fun i c hc => by
        by_cases hi : i = l
        · rw [hi] at hc ⊢; simpa [nextPropose] using hinv.votedForRec l c (by simpa [nextPropose] using hc)
        · simpa [nextPropose, hi] using hinv.votedForRec i c (by simpa [nextPropose, hi] using hc)
      nodeCommit := fun i hi => by
        by_cases hi' : i = l
        · rw [hi'] at hi ⊢
          simp only [nextPropose, fnUpd_same] at hi ⊢
          rw [← hpre_L.take_eq_of_le hsync.2.2.1]
          exact hinv.nodeCommit l hi
        · simpa [nextPropose, hi'] using hinv.nodeCommit i (by simpa [nextPropose, hi'] using hi)
      nodeSnap := fun i hi => by
        by_cases hi' : i = l
        · rw [hi'] at hi ⊢
          simp only [nextPropose, fnUpd_same] at hi ⊢
          rw [← hpre_L.take_eq_of_le hsnap_le_L]
          exact hinv.nodeSnap l hi
        · simpa [nextPropose, hi'] using hinv.nodeSnap i (by simpa [nextPropose, hi'] using hi)
      goodLogs := fun M hkn => by
        rcases hkn_new M hkn with ho | rfl
        · exact hinv.goodLogs M ho
        · exact hgood_L'
      sameTermPrefix := fun L1 L2 i1 i2 h1 h2 hi1 hl1 hi2 hl2 ht hle => by
        rcases hkn_new L1 h1 with ho1 | rfl <;> rcases hkn_new L2 h2 with ho2 | rfl
        · exact hinv.sameTermPrefix L1 L2 i1 i2 ho1 ho2 hi1 hl1 hi2 hl2 ht hle
        · simp only [L', List.length_append, List.length_singleton] at hl2
          by_cases h2l : i2 ≤ L.length
          · rw [logTermAt_append_left L [e] h2l] at ht
            rw [← hpre_L.take_eq_of_le (by omega)]
            exact hinv.sameTermPrefix L1 L i1 i2 ho1 hkn_l hi1 hl1 hi2 h2l ht hle
          · have hi2_eq : i2 = L.length + 1 := by omega
            subst hi2_eq
            rw [logTermAt_append_singleton_last] at ht
            rcases hinv.leaderMaxTerm l L1 i1 hLeader ho1 hi1 hl1 ht with ⟨hle_l, htake_l⟩
            rw [← hpre_L.take_eq_of_le hle_l]; exact htake_l
        · simp only [L', List.length_append, List.length_singleton] at hl1
          by_cases h1l : i1 ≤ L.length
          · rw [logTermAt_append_left L [e] h1l] at ht
            rw [← hpre_L.take_eq_of_le h1l]
            exact hinv.sameTermPrefix L L2 i1 i2 hkn_l ho2 hi1 h1l hi2 hl2 ht hle
          · have hi1_eq : i1 = L.length + 1 := by omega
            subst hi1_eq
            rw [logTermAt_append_singleton_last] at ht
            rcases hinv.leaderMaxTerm l L2 i2 hLeader ho2 hi2 hl2 ht.symm with ⟨hle_l, _⟩
            dsimp only [L] at hle; omega
        · rfl
      leaderMaxTerm := fun l' M k hL' hkn hk1 hkl ht => by
        by_cases hl' : l' = l
        · rw [hl'] at hL' ht ⊢
          simp only [nextPropose, fnUpd_same] at hL' ht ⊢
          rcases hkn_new M hkn with ho | rfl
          · rcases hinv.leaderMaxTerm l M k hLeader ho hk1 hkl ht with ⟨hle, htake⟩
            refine ⟨by simp; omega, ?_⟩
            rw [← hpre_L.take_eq_of_le hle]; exact htake
          · exact ⟨hkl, rfl⟩
        · simp only [nextPropose, fnUpd_other _ _ hl'] at hL' ht ⊢
          rcases hkn_new M hkn with ho | rfl
          · exact hinv.leaderMaxTerm l' M k hL' ho hk1 hkl ht
          · simp only [L', List.length_append, List.length_singleton] at hkl
            by_cases hkl' : k ≤ L.length
            · rw [logTermAt_append_left L [e] hkl'] at ht
              rw [← hpre_L.take_eq_of_le hkl']
              exact hinv.leaderMaxTerm l' L k hL' hkn_l hk1 hkl' ht
            · have hk_eq : k = L.length + 1 := by omega
              subst hk_eq
              rw [logTermAt_append_singleton_last] at ht
              exact absurd (huniq_lead l' hL' ht.symm) hl'
      voteRecs := fun vr h => by
        have hv := hinv.voteRecs vr h
        refine ⟨hv.1, ?_, ?_, ?_, ?_, hv.2.2.2.2.2⟩
        · by_cases hb : boot = l
          · rw [hb]; simp [nextPropose]; have := hv.2.1; rwa [hb] at this
          · simp [nextPropose, hb, hv.2.1]
        · by_cases hv' : vr.voter = l
          · rw [hv']; simp [nextPropose]; have := hv.2.2.1; rwa [hv'] at this
          · simp [nextPropose, hv', hv.2.2.1]
        · by_cases hc' : vr.cand = l
          · rw [hc']; simp [nextPropose]; have := hv.2.2.2.1; rwa [hc'] at this
          · simp [nextPropose, hc', hv.2.2.2.1]
        · by_cases hv' : vr.voter = l
          · rw [hv']; simp only [nextPropose, fnUpd_same]; have := hv.2.2.2.2.1; rwa [hv'] at this
          · simp only [nextPropose, fnUpd_other _ _ hv']; exact hv.2.2.2.2.1
      voteUnique := hinv.voteUnique
      electionUnique := hinv.electionUnique
      electionRecs := fun er her => by
        have hr := hinv.electionRecs er her
        refine ⟨hr.1, ?_, hr.2.2⟩
        by_cases h : er.leader = l
        · rw [h]; simp [nextPropose]; have := hr.2.1; rwa [h] at this
        · simp [nextPropose, h, hr.2.1]
      acceptedRecs := fun i t La ha => by
        by_cases hi : i = l
        · rw [hi] at ha ⊢
          simp only [nextPropose, fnUpd_same, List.mem_cons] at ha ⊢
          rcases ha with heq | ha'
          · injection heq with ht hLa; subst ht; subst hLa
            rcases hL.2.2.2.1 with ⟨er, her, hter, _, hpre_er, hext_er⟩
            refine ⟨hL.1, Nat.le_refl _, ⟨er, her, hter, Or.inr ⟨IsPrefix.trans hpre_er hpre_L, ?_⟩⟩,
              fun P hP => Or.inl hP⟩
            intro j hj1 hj2
            simp only [List.length_append, List.length_singleton] at hj2
            by_cases hjl : j ≤ (s.hist.fullLog l).length
            · rw [logTermAt_append_left L [e] hjl]; exact hext_er j hj1 hjl
            · have : j = (s.hist.fullLog l).length + 1 := by omega
              subst this; rw [logTermAt_append_singleton_last]
          · have h := hinv.acceptedRecs l t La ha'
            refine ⟨h.1, h.2.1, h.2.2.1, fun P hP => ?_⟩
            rcases h.2.2.2 P hP with hpre | hrest
            · exact Or.inl (IsPrefix.trans hpre hpre_L)
            · exact Or.inr hrest
        · simp only [nextPropose, fnUpd_other _ _ hi] at ha ⊢
          exact hinv.acceptedRecs i t La ha
      acceptedBeforeVote := fun vr hvr t La ha hlt P hP => by
        by_cases hvl : vr.voter = l
        · rw [hvl] at ha
          simp only [nextPropose, fnUpd_same, List.mem_cons] at ha
          rcases ha with heq | ha'
          · injection heq with ht _; subst ht
            have := (hinv.voteRecs vr hvr).2.2.1; rw [hvl] at this; omega
          · rw [← hvl] at ha'
            exact hinv.acceptedBeforeVote vr hvr t La ha' hlt P hP
        · simp only [nextPropose, fnUpd_other _ _ hvl] at ha
          exact hinv.acceptedBeforeVote vr hvr t La ha hlt P hP
      commitRecs := fun cm hcm =>
        CommitWF.mono (s := s) (s' := nextPropose s l cmd)
          (fun _ h => h) (fun _ h => h) (fun v p hp => by
            dsimp only [nextPropose]
            by_cases hvl : v = l
            · rw [hvl] at hp ⊢; simp only [fnUpd_same, List.mem_cons]; exact Or.inr hp
            · simp only [fnUpd_other _ _ hvl]; exact hp)
          (hinv.commitRecs cm hcm)
      leaderCompleteness := hinv.leaderCompleteness
      reqVoteMsg := fun t x v ci ct hm => by
        have h := hinv.reqVoteMsg t x v ci ct hm
        refine ⟨h.1, ?_, ?_, ?_⟩
        · by_cases hb : boot = l
          · rw [hb]; simp only [nextPropose, fnUpd_same]; have := h.2.1; rwa [hb] at this
          · simp only [nextPropose, fnUpd_other _ _ hb]; exact h.2.1
        · by_cases hx : x = l
          · rw [hx]; simp only [nextPropose, fnUpd_same]; have := h.2.2.1; rwa [hx] at this
          · simp only [nextPropose, fnUpd_other _ _ hx]; exact h.2.2.1
        · by_cases hx : x = l
          · rw [hx]; simp [nextPropose, hLeader]
          · simp only [nextPropose, fnUpd_other _ _ hx]; exact h.2.2.2
      voteReplyMsg := fun t f to hm => by
        rcases hinv.voteReplyMsg t f to hm with ⟨vr, h1, h2, h3, h4, h5⟩
        refine ⟨vr, h1, h2, h3, h4, ?_⟩
        by_cases hto : to = l
        · rw [hto]; simp [nextPropose, hLeader]
        · simp only [nextPropose, fnUpd_other _ _ hto]; exact h5
      aeMsg := fun t l' pi pt es lc hm => by
        rcases hinv.aeMsg t l' pi pt es lc hm with ⟨Lae, hacc, h1, h2, h3, h4, h5, h6, h7⟩
        refine ⟨Lae, ?_, h1, h2, h3, h4, h5, h6, ?_⟩
        · by_cases hl' : l' = l
          · rw [hl'] at hacc ⊢; simp only [nextPropose, fnUpd_same, List.mem_cons]; exact Or.inr hacc
          · simp only [nextPropose, fnUpd_other _ _ hl']; exact hacc
        · by_cases hl' : l' = l
          · rw [hl']; simp only [nextPropose, fnUpd_same]
            intro _ ht'
            have h7' := h7 (by rw [hl']; exact hLeader) (by rw [hl']; exact ht')
            rw [hl'] at h7'; exact IsPrefix.trans h7' hpre_L
          · simp only [nextPropose, fnUpd_other _ _ hl']; exact h7
      aeReplyMsg := fun t f to mi hm hpos => by
        rcases hinv.aeReplyMsg t f to mi hm hpos with ⟨Lack, h1, h2, h3, h4⟩
        refine ⟨Lack, h1, ?_, h3, ?_⟩
        · by_cases hf : f = l
          · rw [hf] at h2 ⊢; simp only [nextPropose, fnUpd_same, List.mem_cons]; exact Or.inr h2
          · simp only [nextPropose, fnUpd_other _ _ hf]; exact h2
        · by_cases hto : to = l
          · rw [hto]; simp only [nextPropose, fnUpd_same]
            intro _ ht'
            have h4' := h4 (by rw [hto]; exact hLeader) (by rw [hto]; exact ht')
            rw [hto] at h4'; exact IsPrefix.trans h4' hpre_L
          · simp only [nextPropose, fnUpd_other _ _ hto]; exact h4
      snapMsg := hinv.snapMsg
      snapLogRecs := hinv.snapLogRecs }

end PreservationBasic

end ValkeyRaft.ConfigOnAppend

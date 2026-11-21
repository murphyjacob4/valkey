/-
  Inductive invariant `Inv boot s` for Valkey cluster Raft with config-on-append
  and append-time validation, plus the core Leader Completeness and Election
  Safety proof engine shared by `becomeLeader` and `advanceCommit`.

  Zero `sorry`, core Lean 4 only (no Mathlib).
-/
import ValkeyRaft.ConfigOnAppend.LogLemmas

namespace ValkeyRaft.ConfigOnAppend

set_option linter.unusedSectionVars false

section Invariants

variable {NodeId : Type} [DecidableEq NodeId] {T : TopoSpec NodeId}

/-! ## 1. Known logs and per-log properties -/

/-- Any log present anywhere in the system state or its proof history. -/
def IsKnownLog (s : System NodeId T) (L : List (Entry NodeId T.Op)) : Prop :=
  (∃ i, L = s.hist.fullLog i) ∨
  (∃ er ∈ s.hist.elected, L = er.elecLog) ∨
  (∃ cm ∈ s.hist.commits, L = cm.log) ∨
  (∃ vr ∈ s.hist.votes, L = vr.voterLog) ∨
  (∃ p ∈ s.hist.snapLogs, L = p.2.2.2) ∨
  (∃ i t, (t, L) ∈ s.hist.accepted i)

/-- Every voter change at index `k > 1` in `L` was preceded by a commit in the
same term covering all prior voter changes (combining serialization + Ongaro 2015). -/
def ConfigParent (s : System NodeId T) (L : List (Entry NodeId T.Op)) : Prop :=
  ∀ k e, 1 < k → k ≤ L.length → logGet L k = some e → e.cmd.isVoterChange = true →
    ∃ cm ∈ s.hist.commits,
      cm.term = e.term ∧
      cm.idx < k ∧
      IsPrefix cm.log (L.take (k - 1)) ∧
      cm.cfg = votersOfLog cm.log ∧
      (∀ j e', cm.idx < j → j < k → logGet L j = some e' → e'.cmd.isVoterChange = false)

/-- Every entry in `L` at index `k` of term `t` extends the unique election log
of term `t`. -/
def EntryExtendsLeader (s : System NodeId T) (L : List (Entry NodeId T.Op)) : Prop :=
  ∀ k, 1 ≤ k → k ≤ L.length →
    ∃ er ∈ s.hist.elected, er.term = logTermAt L k ∧ IsPrefix er.elecLog (L.take k)

/-- All structural properties satisfied by every known log. -/
def GoodLog (boot : NodeId) (s : System NodeId T) (L : List (Entry NodeId T.Op)) : Prop :=
  LogValid boot L ∧
  LogMonotone L ∧
  BootstrapAtOne boot L ∧
  ConfigParent s L ∧
  EntryExtendsLeader s L

/-! ## 2. Commit and Election well-formedness predicates -/

/-- Well-formedness of a `CommitRec` (used both for commits already in
`s.hist.commits` and for a newly-formed commit in `advanceCommit`). -/
def CommitWF (boot : NodeId) (s : System NodeId T) (cm : CommitRec NodeId T) : Prop :=
  cm.idx > 0 ∧
  cm.log.length = cm.idx ∧
  logLastTerm cm.log = cm.term ∧
  GoodLog boot s cm.log ∧
  IsMajority cm.cfg (fun v => decide (v ∈ cm.quorum)) ∧
  (∀ v ∈ cm.quorum, v ∈ cm.cfg ∧ ∃ La, (cm.term, La) ∈ s.hist.accepted v ∧ IsPrefix cm.log La) ∧
  (∃ er ∈ s.hist.elected,
    er.term = cm.term ∧ er.leader = cm.leader ∧ IsPrefix er.elecLog cm.log ∧
    (∀ j, er.elecLog.length < j → j ≤ cm.idx → logTermAt cm.log j = cm.term)) ∧
  (cm.cfg = votersOfLog cm.log ∨
    (Adjacent (votersOfLog cm.log) cm.cfg ∧
     ∃ cm0 ∈ s.hist.commits,
       cm0.term = cm.term ∧ cm0.idx < cm.idx ∧ IsPrefix cm0.log cm.log ∧
       cm0.cfg = votersOfLog cm.log ∧
       (∀ j e, cm0.idx < j → j ≤ cm.idx → logGet cm.log j = some e →
         e.cmd.isVoterChange = false)))

/-- Well-formedness of an `ElectionRec` (for `term > 1`). -/
def ElectionWF (boot : NodeId) (s : System NodeId T) (er : ElectionRec NodeId T) : Prop :=
  er.term > 1 ∧
  GoodLog boot s er.elecLog ∧
  logLastTerm er.elecLog < er.term ∧
  er.elecCfg = votersOfLog er.elecLog ∧
  IsMajority er.elecCfg (fun v => decide (v ∈ er.elecQuorum)) ∧
  (∀ v ∈ er.elecQuorum, v ∈ er.elecCfg)

/-! ## 3. Full inductive invariant `Inv` -/

structure Inv (boot : NodeId) (s : System NodeId T) : Prop where
  /-- Node runtime fields match `hist.fullLog`. -/
  nodeSync : ∀ i,
    let n := s.nodes i
    let L := s.hist.fullLog i
    n.snapIdx ≤ n.applied ∧
    n.applied ≤ n.commit ∧
    n.commit ≤ L.length ∧
    n.tail = L.drop n.snapIdx ∧
    n.snapTerm = logTermAt L n.snapIdx ∧
    n.snapState = stateAt L n.snapIdx ∧
    n.appliedState = stateAt L n.applied ∧
    logLastTerm L ≤ n.term

  /-- Role-specific node invariants. -/
  leaderNode : ∀ l, (s.nodes l).role = .leader →
    (s.nodes l).term > 0 ∧
    (s.nodes l).votedFor = some l ∧
    ((s.nodes l).term, s.hist.fullLog l) ∈ s.hist.accepted l ∧
    (∃ er ∈ s.hist.elected,
      er.term = (s.nodes l).term ∧ er.leader = l ∧
      IsPrefix er.elecLog (s.hist.fullLog l) ∧
      (∀ j, er.elecLog.length < j → j ≤ (s.hist.fullLog l).length →
        logTermAt (s.hist.fullLog l) j = (s.nodes l).term)) ∧
    (∀ v, (s.nodes l).matchIdx v > 0 →
      (s.nodes l).matchIdx v ≤ (s.hist.fullLog l).length ∧
      ((s.nodes l).term, (s.hist.fullLog l).take ((s.nodes l).matchIdx v)) ∈ s.hist.accepted v) ∧
    ((s.nodes l).commit > 0 → logTermAt (s.hist.fullLog l) (s.nodes l).commit = (s.nodes l).term →
      ∃ cm ∈ s.hist.commits,
        cm.term = (s.nodes l).term ∧ cm.idx = (s.nodes l).commit ∧
        cm.log = (s.hist.fullLog l).take (s.nodes l).commit ∧
        ((s.nodes l).hasUncommittedVoterChange = false → cm.cfg = votersOfLog cm.log)) ∧
    (∀ cm ∈ s.hist.commits, cm.term = (s.nodes l).term → cm.idx ≤ (s.nodes l).commit)

  candidateNode : ∀ c, (s.nodes c).role = .candidate →
    (s.nodes c).term > 1 ∧
    (s.nodes c).votedFor = some c ∧
    logLastTerm (s.hist.fullLog c) < (s.nodes c).term ∧
    (∀ er ∈ s.hist.elected, er.term = (s.nodes c).term → er.leader ≠ c) ∧
    (∀ v ∈ (s.nodes c).votes,
      ∃ vr ∈ s.hist.votes,
        vr.term = (s.nodes c).term ∧ vr.voter = v ∧ vr.cand = c ∧
        upToDate (logLastTerm (s.hist.fullLog c)) (s.hist.fullLog c).length
                 (logLastTerm vr.voterLog) vr.voterLog.length = true)

  votedForRec : ∀ i c, (s.nodes i).votedFor = some c →
    (s.nodes i).term > 0 ∧
    ∃ vr ∈ s.hist.votes, vr.term = (s.nodes i).term ∧ vr.voter = i ∧ vr.cand = c

  /-- Every node's `commit > 0` is backed by a commit record of term ≤ node's term. -/
  nodeCommit : ∀ i, (s.nodes i).commit > 0 →
    ∃ cm ∈ s.hist.commits,
      cm.term ≤ (s.nodes i).term ∧
      cm.idx ≥ (s.nodes i).commit ∧
      IsPrefix ((s.hist.fullLog i).take (s.nodes i).commit) cm.log

  /-- Every node's `snapIdx > 0` is backed by a commit record of term ≤ node's term. -/
  nodeSnap : ∀ i, (s.nodes i).snapIdx > 0 →
    ∃ cm ∈ s.hist.commits,
      cm.term ≤ (s.nodes i).term ∧
      cm.idx ≥ (s.nodes i).snapIdx ∧
      IsPrefix ((s.hist.fullLog i).take (s.nodes i).snapIdx) cm.log

  /-- Every known log satisfies `GoodLog`. -/
  goodLogs : ∀ L, IsKnownLog s L → GoodLog boot s L

  /-- Log Matching + SameTermPrefix across all known logs. -/
  sameTermPrefix : ∀ L1 L2 i1 i2,
    IsKnownLog s L1 → IsKnownLog s L2 →
    1 ≤ i1 → i1 ≤ L1.length →
    1 ≤ i2 → i2 ≤ L2.length →
    logTermAt L1 i1 = logTermAt L2 i2 →
    i1 ≤ i2 →
    L1.take i1 = L2.take i1

  /-- Active leader holds the longest log of its current term. -/
  leaderMaxTerm : ∀ l L k,
    (s.nodes l).role = .leader →
    IsKnownLog s L →
    1 ≤ k → k ≤ L.length →
    logTermAt L k = (s.nodes l).term →
    k ≤ (s.hist.fullLog l).length ∧ L.take k = (s.hist.fullLog l).take k

  /-- Vote uniqueness and monotonicity. -/
  voteRecs : ∀ vr ∈ s.hist.votes,
    vr.term > 0 ∧
    (s.nodes boot).term ≥ 1 ∧
    (s.nodes vr.voter).term ≥ vr.term ∧
    (s.nodes vr.cand).term ≥ vr.term ∧
    ((s.nodes vr.voter).term = vr.term → (s.nodes vr.voter).votedFor = some vr.cand) ∧
    (vr.hadLeaderInTerm = true → ∃ er ∈ s.hist.elected, er.term = vr.term)

  voteUnique : ∀ vr1 ∈ s.hist.votes, ∀ vr2 ∈ s.hist.votes,
    vr1.term = vr2.term → vr1.voter = vr2.voter → vr1.cand = vr2.cand

  /-- Election Safety and election record properties. -/
  electionUnique : ∀ er1 ∈ s.hist.elected, ∀ er2 ∈ s.hist.elected,
    er1.term = er2.term → er1 = er2

  electionRecs : ∀ er ∈ s.hist.elected,
    er.term > 0 ∧
    (s.nodes er.leader).term ≥ er.term ∧
    er.elecCfg = votersOfLog er.elecLog ∧
    IsMajority er.elecCfg (fun v => decide (v ∈ er.elecQuorum)) ∧
    (∀ v ∈ er.elecQuorum, v ∈ er.elecCfg) ∧
    (er.term = 1 →
      er.leader = boot ∧
      er.elecLog = [{ term := 1, cmd := .bootstrapJoin boot }] ∧
      er.elecCfg = [boot]) ∧
    (er.term > 1 →
      logLastTerm er.elecLog < er.term ∧
      ∀ v ∈ er.elecQuorum,
        ∃ vr ∈ s.hist.votes,
          vr.term = er.term ∧ vr.voter = v ∧ vr.cand = er.leader ∧
          vr.hadLeaderInTerm = false ∧
          upToDate (logLastTerm er.elecLog) er.elecLog.length
                   (logLastTerm vr.voterLog) vr.voterLog.length = true)

  /-- Accepted-prefix bridge to `fullLog` and `votes` (prefix-closed on `P ⊆ La`). -/
  acceptedRecs : ∀ i t La, (t, La) ∈ s.hist.accepted i →
    t > 0 ∧
    (s.nodes i).term ≥ t ∧
    (∃ er ∈ s.hist.elected, er.term = t ∧
      (IsPrefix La er.elecLog ∨
        (IsPrefix er.elecLog La ∧
         ∀ j, er.elecLog.length < j → j ≤ La.length → logTermAt La j = t))) ∧
    (∀ P, IsPrefix P La →
      IsPrefix P (s.hist.fullLog i) ∨
      ∃ er ∈ s.hist.elected, t < er.term ∧ er.term ≤ (s.nodes i).term ∧
        ¬ IsPrefix P er.elecLog)

  acceptedBeforeVote : ∀ vr ∈ s.hist.votes, ∀ t La,
    (t, La) ∈ s.hist.accepted vr.voter →
    t < vr.term →
    ∀ P, IsPrefix P La →
      IsPrefix P vr.voterLog ∨
      (∃ er ∈ s.hist.elected, t < er.term ∧
        (er.term < vr.term ∨ (er.term = vr.term ∧ vr.hadLeaderInTerm = true)) ∧
        ¬ IsPrefix P er.elecLog)

  /-- Commit well-formedness & Leader Completeness. -/
  commitRecs : ∀ cm ∈ s.hist.commits, CommitWF boot s cm

  leaderCompleteness : ∀ cm ∈ s.hist.commits, ∀ er ∈ s.hist.elected,
    cm.term < er.term → IsPrefix cm.log er.elecLog

  /-- Message integrity invariants. -/
  reqVoteMsg : ∀ t c v cIdx cTerm,
    Msg.requestVote t c v cIdx cTerm ∈ s.net →
    t > 1 ∧
    (s.nodes boot).term ≥ 1 ∧
    (s.nodes c).term ≥ t ∧
    ((s.nodes c).term = t → (s.nodes c).role = .candidate →
      (s.hist.fullLog c).length = cIdx ∧ logLastTerm (s.hist.fullLog c) = cTerm)

  voteReplyMsg : ∀ t fromId toId,
    Msg.voteReply t fromId toId true ∈ s.net →
    ∃ vr ∈ s.hist.votes,
      vr.term = t ∧ vr.voter = fromId ∧ vr.cand = toId ∧
      ((s.nodes toId).term = t → (s.nodes toId).role = .candidate →
        upToDate (logLastTerm (s.hist.fullLog toId)) (s.hist.fullLog toId).length
                 (logLastTerm vr.voterLog) vr.voterLog.length = true)

  aeMsg : ∀ t l prevIdx prevTerm entries leaderCommit,
    Msg.appendEntries t l prevIdx prevTerm entries leaderCommit ∈ s.net →
    ∃ Lae,
      (t, Lae) ∈ s.hist.accepted l ∧
      prevIdx + entries.length ≤ Lae.length ∧
      logTermAt Lae prevIdx = prevTerm ∧
      (Lae.drop prevIdx).take entries.length = entries ∧
      logLastTerm Lae ≤ t ∧
      (∃ er ∈ s.hist.elected, er.term = t ∧ er.leader = l ∧ IsPrefix er.elecLog Lae) ∧
      (leaderCommit > 0 → leaderCommit ≤ Lae.length ∧
        ∃ cm ∈ s.hist.commits, cm.term ≤ t ∧ cm.idx ≥ leaderCommit ∧
          IsPrefix (Lae.take leaderCommit) cm.log) ∧
      ((s.nodes l).role = .leader → (s.nodes l).term = t → IsPrefix Lae (s.hist.fullLog l))

  aeReplyMsg : ∀ t fromId toId mIdx,
    Msg.appendReply t fromId toId true mIdx ∈ s.net →
    mIdx > 0 →
    ∃ Lack,
      Lack.length = mIdx ∧
      (t, Lack) ∈ s.hist.accepted fromId ∧
      (∃ er ∈ s.hist.elected, er.term = t ∧ er.leader = toId) ∧
      ((s.nodes toId).role = .leader → (s.nodes toId).term = t → IsPrefix Lack (s.hist.fullLog toId))

  snapMsg : ∀ t l sIdx sTerm sState,
    Msg.installSnapshot t l sIdx sTerm sState ∈ s.net →
    sIdx > 0 ∧
    (∃ sLog, (sIdx, sTerm, sState, sLog) ∈ s.hist.snapLogs ∧
      ∃ cm ∈ s.hist.commits, cm.term ≤ t ∧ cm.idx ≥ sIdx ∧ IsPrefix sLog cm.log) ∧
    (∃ er ∈ s.hist.elected, er.term = t ∧ er.leader = l)

  snapLogRecs : ∀ sIdx sTerm sState sLog,
    (sIdx, sTerm, sState, sLog) ∈ s.hist.snapLogs →
    sIdx > 0 ∧
    sLog.length = sIdx ∧
    logLastTerm sLog = sTerm ∧
    stateOfLog sLog = sState ∧
    (∃ cm ∈ s.hist.commits, cm.idx ≥ sIdx ∧ IsPrefix sLog cm.log)

/-! ## 4. Initial state satisfies `Inv` -/

theorem Inv.init (boot : NodeId) : Inv boot (System.init T) := by
  refine
    { nodeSync := ?_
      leaderNode := ?_
      candidateNode := ?_
      votedForRec := ?_
      nodeCommit := ?_
      nodeSnap := ?_
      goodLogs := ?_
      sameTermPrefix := ?_
      leaderMaxTerm := ?_
      voteRecs := ?_
      voteUnique := ?_
      electionUnique := ?_
      electionRecs := ?_
      acceptedRecs := ?_
      acceptedBeforeVote := ?_
      commitRecs := ?_
      leaderCompleteness := ?_
      reqVoteMsg := ?_
      voteReplyMsg := ?_
      aeMsg := ?_
      aeReplyMsg := ?_
      snapMsg := ?_
      snapLogRecs := ?_ }
  · intro i
    simp [System.init, Node.init, Hist.init, logTermAt_zero, stateAt_zero, logLastTerm_nil]
  · intro l h; simp [System.init, Node.init] at h
  · intro c h; simp [System.init, Node.init] at h
  · intro i c h; simp [System.init, Node.init] at h
  · intro i h; simp [System.init, Node.init] at h
  · intro i h; simp [System.init, Node.init] at h
  · intro L h
    rcases h with ⟨i, rfl⟩ | ⟨er, h, _⟩ | ⟨cm, h, _⟩ | ⟨vr, h, _⟩ | ⟨p, h, _⟩ | ⟨i, t, h⟩
    · refine ⟨LogValid.nil boot, LogMonotone.nil, BootstrapAtOne.nil boot, ?_, ?_⟩
      · intro k e h1 h2; simp [System.init, Hist.init] at h2; omega
      · intro k h1 h2; simp [System.init, Hist.init] at h2; omega
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  · intro L1 L2 i1 i2 h1 h2 hi1 hle1
    rcases h1 with ⟨i, rfl⟩ | ⟨er, h, _⟩ | ⟨cm, h, _⟩ | ⟨vr, h, _⟩ | ⟨p, h, _⟩ | ⟨i, t, h⟩
    · simp [System.init, Hist.init] at hle1; omega
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  · intro l L k hL; simp [System.init, Node.init] at hL
  · intro vr h; cases h
  · intro vr1 h; cases h
  · intro er1 h; cases h
  · intro er h; cases h
  · intro i t La h; cases h
  · intro vr h; cases h
  · intro cm h; cases h
  · intro cm h; cases h
  · intro t c v cIdx cTerm h; cases h
  · intro t fromId toId h; cases h
  · intro t l prevIdx prevTerm entries leaderCommit h; cases h
  · intro t fromId toId mIdx h; cases h
  · intro t l sIdx sTerm sState h; cases h
  · intro sIdx sTerm sState sLog h; cases h

/-! ## 5. Immediate corollaries of `Inv` -/

/-- Log Matching between any two known logs. -/
theorem Inv.logMatching {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {L1 L2 : List (Entry NodeId T.Op)} {k : Nat}
    (h1 : IsKnownLog s L1) (h2 : IsKnownLog s L2)
    (hk1 : 1 ≤ k) (hle1 : k ≤ L1.length) (hle2 : k ≤ L2.length)
    (ht : logTermAt L1 k = logTermAt L2 k) :
    L1.take k = L2.take k :=
  hinv.sameTermPrefix L1 L2 k k h1 h2 hk1 hle1 hk1 hle2 ht (Nat.le_refl k)

/-- Any two commits in `s.hist.commits` are prefix-compatible (State Machine Safety
on commits). -/
theorem Inv.commitPrefixAgreement {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {cm1 cm2 : CommitRec NodeId T} (h1 : cm1 ∈ s.hist.commits) (h2 : cm2 ∈ s.hist.commits) :
    IsPrefix cm1.log cm2.log ∨ IsPrefix cm2.log cm1.log := by
  have hwf1 := hinv.commitRecs cm1 h1
  have hwf2 := hinv.commitRecs cm2 h2
  rcases hwf1.2.2.2.2.2.2.1 with ⟨er1, her1, hter1, _, hpre1, _⟩
  rcases hwf2.2.2.2.2.2.2.1 with ⟨er2, her2, hter2, _, hpre2, _⟩
  by_cases hlt : cm1.term < cm2.term
  · left
    have hlc := hinv.leaderCompleteness cm1 h1 er2 her2 (by omega)
    exact IsPrefix.trans hlc hpre2
  · by_cases hgt : cm2.term < cm1.term
    · right
      have hlc := hinv.leaderCompleteness cm2 h2 er1 her1 (by omega)
      exact IsPrefix.trans hlc hpre1
    · have hpos1 : cm1.idx > 0 := hwf1.1
      have hlen1 : cm1.log.length = cm1.idx := hwf1.2.1
      have hpos2 : cm2.idx > 0 := hwf2.1
      have hlen2 : cm2.log.length = cm2.idx := hwf2.2.1
      have heq : cm1.term = cm2.term := by omega
      have hkn1 : IsKnownLog s cm1.log := Or.inr (Or.inr (Or.inl ⟨cm1, h1, rfl⟩))
      have hkn2 : IsKnownLog s cm2.log := Or.inr (Or.inr (Or.inl ⟨cm2, h2, rfl⟩))
      have hlt1 : logTermAt cm1.log cm1.idx = cm1.term := by
        have := hwf1.2.2.1; unfold logLastTerm at this; rwa [hlen1] at this
      have hlt2 : logTermAt cm2.log cm2.idx = cm2.term := by
        have := hwf2.2.2.1; unfold logLastTerm at this; rwa [hlen2] at this
      by_cases hle : cm1.idx ≤ cm2.idx
      · left
        have htake := hinv.sameTermPrefix cm1.log cm2.log cm1.idx cm2.idx hkn1 hkn2
          (by omega) (by omega) (by omega) (by omega) (by omega) hle
        refine ⟨by omega, ?_⟩
        rw [hlen1, ← htake, ← hlen1, List.take_length]
      · right
        have htake := hinv.sameTermPrefix cm2.log cm1.log cm2.idx cm1.idx hkn2 hkn1
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        refine ⟨by omega, ?_⟩
        rw [hlen2, ← htake, ← hlen2, List.take_length]

theorem votersOfLog_eq_cfgAt_length (L : List (Entry NodeId T.Op)) :
    votersOfLog L = cfgAt L L.length := by
  simp [votersOfLog, cfgAt, stateAt_length]

theorem cfgAt_take_eq (L : List (Entry NodeId T.Op)) {n k : Nat} (hk : k ≤ n) :
    cfgAt (L.take n) k = cfgAt L k := by
  simp [cfgAt, stateAt_take L hk]

/-- Every non-empty known log has `lastVoterChange ≥ 1` (because index 1 is
`bootstrapJoin`). -/
theorem lastVoterChange_pos_of_nonempty {boot : NodeId} {s : System NodeId T}
    {L : List (Entry NodeId T.Op)} (hg : GoodLog boot s L) (hne : L.length > 0) :
    lastVoterChange L ≥ 1 := by
  rcases logGet_some_iff L (by omega) hne with ⟨e, hget⟩
  rcases hg.2.2.1 e hget with ⟨_, hcmd⟩
  have hvc : e.cmd.isVoterChange = true := by simp [hcmd, Cmd.isVoterChange]
  exact lastVoterChangeUpTo_ge_of_vc L hne hget hvc

/-- An `ElectionWF` log is always non-empty (an empty voter set has no majority). -/
theorem electionLog_nonempty {boot : NodeId} {s : System NodeId T} {er : ElectionRec NodeId T}
    (her : ElectionWF boot s er) : er.elecLog.length > 0 := by
  by_cases h0 : er.elecLog.length = 0
  · rw [List.length_eq_zero_iff] at h0
    have hcfg : er.elecCfg = [] := by
      rw [her.2.2.2.1, h0]; rfl
    have hmaj := her.2.2.2.2.1
    rw [hcfg] at hmaj
    unfold IsMajority ValkeyRaft.Quorum.IsMajority at hmaj
    simp at hmaj
  · omega

/-! ## 6. Core Leader Completeness & Election Safety Proof Engine -/

/-- Prefix-closed wrapper around `sameTermPrefix` (useful when a new commit's log
is a prefix `L.take k` of an existing known log `L`). -/
theorem Inv.sameTermPrefix_sub {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {L1 L2 : List (Entry NodeId T.Op)} {i1 i2 : Nat}
    (h1 : ∃ M1, IsKnownLog s M1 ∧ IsPrefix L1 M1)
    (h2 : ∃ M2, IsKnownLog s M2 ∧ IsPrefix L2 M2)
    (hi1 : 1 ≤ i1) (hl1 : i1 ≤ L1.length)
    (hi2 : 1 ≤ i2) (hl2 : i2 ≤ L2.length)
    (ht : logTermAt L1 i1 = logTermAt L2 i2) (hle : i1 ≤ i2) :
    L1.take i1 = L2.take i1 := by
  rcases h1 with ⟨M1, hM1, hp1⟩
  rcases h2 with ⟨M2, hM2, hp2⟩
  rw [logTermAt_of_prefix hp1 hl1, logTermAt_of_prefix hp2 hl2] at ht
  rw [hp1.take_eq_of_le hl1, hp2.take_eq_of_le (Nat.le_trans hle hl2)]
  exact hinv.sameTermPrefix M1 M2 i1 i2 hM1 hM2 hi1 (Nat.le_trans hl1 hp1.1)
    hi2 (Nat.le_trans hl2 hp2.1) ht hle

/-- Step 1 of Leader Completeness: whenever `cm.cfg` and `er.elecCfg` are
`Adjacent` (so their quorums intersect), and every intermediate leader strictly
between `cm.term` and `er.term` already contains `cm.log`, then `er.elecLog`
MUST contain `cm.log`! -/
theorem quorum_intersection_implies_prefix {boot : NodeId} {s : System NodeId T}
    (hinv : Inv boot s)
    {cm : CommitRec NodeId T} {er : ElectionRec NodeId T}
    (hcm : CommitWF boot s cm) (her : ElectionWF boot s er)
    (hkn_cm : ∃ Lsup, IsKnownLog s Lsup ∧ IsPrefix cm.log Lsup) (hkn_er : IsKnownLog s er.elecLog)
    (hlt : cm.term < er.term)
    (hadj : Adjacent cm.cfg er.elecCfg)
    (hMid : ∀ er' ∈ s.hist.elected, cm.term < er'.term → er'.term < er.term →
      IsPrefix cm.log er'.elecLog)
    (hTermSafe : ∀ v ∈ er.elecQuorum,
      ∃ vr ∈ s.hist.votes, vr.term = er.term ∧ vr.voter = v ∧ vr.cand = er.leader ∧
        upToDate (logLastTerm er.elecLog) er.elecLog.length
                 (logLastTerm vr.voterLog) vr.voterLog.length = true ∧
        (vr.hadLeaderInTerm = false ∨
         ∀ er_same ∈ s.hist.elected, er_same.term = er.term → IsPrefix cm.log er_same.elecLog)) :
    IsPrefix cm.log er.elecLog := by
  -- Intersect cm.quorum and er.elecQuorum using Adjacent
  rcases adjacent_quorums_intersect hadj
      (fun v => decide (v ∈ cm.quorum)) (fun v => decide (v ∈ er.elecQuorum))
      hcm.2.2.2.2.1 her.2.2.2.2.1 with ⟨w, _, _, hw_cm, hw_er⟩
  simp only [decide_eq_true_eq] at hw_cm hw_er
  rcases (hcm.2.2.2.2.2.1 w hw_cm).2 with ⟨La, hw_acc, hpre_La⟩
  rcases hTermSafe w hw_er with ⟨vr, hvr_mem, hvr_t, hvr_v, _, hupto, hnoLead⟩
  -- Use acceptedBeforeVote on (vr, (cm.term, La), cm.log)
  have hpref_v : IsPrefix cm.log vr.voterLog := by
    have habv := hinv.acceptedBeforeVote vr hvr_mem cm.term La (hvr_v ▸ hw_acc) (by omega) cm.log hpre_La
    rcases habv with hpre | ⟨er_mid, her_mid, ht1, ht2, hnotpre⟩
    · exact hpre
    · rcases ht2 with hlt_mid | ⟨heq_mid, hhad⟩
      · exact absurd (hMid er_mid her_mid ht1 (by omega)) hnotpre
      · rcases hnoLead with hfalse | hall
        · rw [hhad] at hfalse; cases hfalse
        · exact absurd (hall er_mid her_mid (by omega)) hnotpre
  -- From IsPrefix cm.log vr.voterLog, vr's log is at least as up-to-date as (cm.term, cm.idx)
  have hcm_pos : cm.idx > 0 := hcm.1
  have hcm_len : cm.log.length = cm.idx := hcm.2.1
  have hvr_len : cm.idx ≤ vr.voterLog.length := by
    have := hpref_v.1; omega
  have hvr_term : cm.term ≤ logLastTerm vr.voterLog := by
    have hkn_vr : IsKnownLog s vr.voterLog := Or.inr (Or.inr (Or.inr (Or.inl ⟨vr, hvr_mem, rfl⟩)))
    have hmon := (hinv.goodLogs vr.voterLog hkn_vr).2.1
    have hcm_at : logTermAt vr.voterLog cm.idx = cm.term := by
      rw [← logTermAt_of_prefix hpref_v (by omega)]
      have := hcm.2.2.1; unfold logLastTerm at this; rwa [hcm_len] at this
    rw [← hcm_at]
    exact hmon.2 cm.idx vr.voterLog.length hcm_pos hvr_len (Nat.le_refl _)
  -- From upToDate er.elecLog vr.voterLog = true:
  unfold upToDate at hupto
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hupto
  have her_ge : logLastTerm er.elecLog > cm.term ∨
      (logLastTerm er.elecLog = cm.term ∧ er.elecLog.length ≥ cm.idx) := by
    rcases hupto with hgt | ⟨heq, hlen⟩
    · exact Or.inl (by omega)
    · by_cases hgt2 : logLastTerm vr.voterLog > cm.term
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
  rcases her_ge with hgt_t | ⟨heq_t, hge_len⟩
  · -- logLastTerm er.elecLog > cm.term (and < er.term by ElectionWF!)
    have hne := electionLog_nonempty her
    have hext := her.2.1.2.2.2.2 er.elecLog.length (by omega) (Nat.le_refl _)
    rcases hext with ⟨er', her'_mem, her'_t, her'_pre⟩
    have hlt1 : cm.term < er'.term := by
      unfold logLastTerm at hgt_t; omega
    have hlt2 : er'.term < er.term := by
      have := her.2.2.1; unfold logLastTerm at this; omega
    have hlc := hMid er' her'_mem hlt1 hlt2
    rw [List.take_length] at her'_pre
    exact IsPrefix.trans hlc her'_pre
  · -- logLastTerm er.elecLog = cm.term and er.elecLog.length ≥ cm.idx
    have hlt_cm : logTermAt cm.log cm.idx = cm.term := by
      have := hcm.2.2.1; unfold logLastTerm at this; rwa [hcm_len] at this
    have hlt_er : logTermAt er.elecLog er.elecLog.length = cm.term := heq_t
    have htake := hinv.sameTermPrefix_sub hkn_cm ⟨er.elecLog, hkn_er, IsPrefix.refl _⟩
      hcm_pos (by omega) (by omega) (Nat.le_refl _) (by omega) hge_len
    refine ⟨by omega, ?_⟩
    rw [hcm_len, ← htake, ← hcm_len, List.take_length]

/-- Master Leader Completeness step (shared by both `becomeLeader` and
`advanceCommit`!): proves `IsPrefix cm.log er.elecLog` for ANY well-formed
commit `cm` and election `er` with `cm.term < er.term`, given strong IH on
intermediate leaders (`cm.term < er'.term < er.term`) and earlier commits. -/
theorem leader_completeness_step {boot : NodeId} {s : System NodeId T}
    (hinv : Inv boot s)
    {cm : CommitRec NodeId T} {er : ElectionRec NodeId T}
    (hcm : CommitWF boot s cm) (her : ElectionWF boot s er)
    (hkn_cm : ∃ Lsup, IsKnownLog s Lsup ∧ IsPrefix cm.log Lsup) (hkn_er : IsKnownLog s er.elecLog)
    (hlt : cm.term < er.term)
    (hMid : ∀ er' ∈ s.hist.elected, cm.term < er'.term → er'.term < er.term →
      IsPrefix cm.log er'.elecLog)
    (hEarlier : ∀ cm' ∈ s.hist.commits,
      (cm'.term < cm.term ∨ (cm'.term = cm.term ∧ cm'.idx < cm.idx)) →
      IsPrefix cm'.log er.elecLog)
    (hTermSafe : ∀ v ∈ er.elecQuorum,
      ∃ vr ∈ s.hist.votes, vr.term = er.term ∧ vr.voter = v ∧ vr.cand = er.leader ∧
        upToDate (logLastTerm er.elecLog) er.elecLog.length
                 (logLastTerm vr.voterLog) vr.voterLog.length = true ∧
        (vr.hadLeaderInTerm = false ∨
         ∀ er_same ∈ s.hist.elected, er_same.term = er.term → IsPrefix cm.log er_same.elecLog)) :
    IsPrefix cm.log er.elecLog := by
  have hq := fun hadj =>
    quorum_intersection_implies_prefix hinv hcm her hkn_cm hkn_er hlt hadj hMid hTermSafe
  have hcm_pos : cm.idx > 0 := hcm.1
  have hcm_len : cm.log.length = cm.idx := hcm.2.1
  have hcm_good : GoodLog boot s cm.log := hcm.2.2.2.1
  have her_good : GoodLog boot s er.elecLog := her.2.1
  have her_ne : er.elecLog.length > 0 := electionLog_nonempty her
  have hcm_lastT : logTermAt cm.log cm.idx = cm.term := by
    have := hcm.2.2.1; unfold logLastTerm at this; rwa [hcm_len] at this
  -- First handle the case where cm was committed while a later voter change was uncommitted
  rcases hcm.2.2.2.2.2.2.2 with hcfg_eq | ⟨hadj_cm, cm0, hcm0_mem, hcm0_t, hcm0_idx, hcm0_pre, hcm0_cfg, hcm0_novc⟩
  · -- MAIN CASE: cm.cfg = votersOfLog cm.log
    let k2 := lastVoterChange er.elecLog
    let τ2 := logTermAt er.elecLog k2
    have hk2_pos : k2 ≥ 1 := lastVoterChange_pos_of_nonempty her_good her_ne
    have hk2_le : k2 ≤ er.elecLog.length := lastVoterChange_le er.elecLog
    have hτ2_pos : τ2 > 0 := her_good.2.1.1 k2 hk2_pos hk2_le
    have hτ2_lt : τ2 < er.term := by
      have hmon := her_good.2.1.2 k2 er.elecLog.length hk2_pos hk2_le (Nat.le_refl _)
      have hlt_er := her.2.2.1; unfold logLastTerm at hlt_er; omega
    have her_cfg_k2 : er.elecCfg = cfgAt er.elecLog k2 := by
      rw [her.2.2.2.1]; exact votersOfLog_eq_lastVoterChange er.elecLog
    by_cases hτ2_gt : τ2 > cm.term
    · -- Case 1: τ2 > cm.term -> er' of term τ2 already has cm.log!
      rcases her_good.2.2.2.2 k2 hk2_pos hk2_le with ⟨er', her'_mem, her'_t, her'_pre⟩
      have hlc := hMid er' her'_mem (by omega) (by omega)
      exact IsPrefix.trans hlc (IsPrefix.trans her'_pre (IsPrefix.take_left er.elecLog k2))
    · by_cases hτ2_eq : τ2 = cm.term
      · -- Case 2: τ2 = cm.term
        by_cases hk2_ge : cm.idx ≤ k2
        · -- k2 ≥ cm.idx: SameTermPrefix gives cm.log as prefix of er.elecLog directly!
          have htake := hinv.sameTermPrefix_sub hkn_cm ⟨er.elecLog, hkn_er, IsPrefix.refl _⟩
            hcm_pos (by omega) hk2_pos hk2_le (by omega) hk2_ge
          refine ⟨by omega, ?_⟩
          rw [hcm_len, ← htake, ← hcm_len, List.take_length]
        · -- k2 < cm.idx: er.elecLog agrees with cm.log up to k2
          have htake_k2 := hinv.sameTermPrefix_sub ⟨er.elecLog, hkn_er, IsPrefix.refl _⟩ hkn_cm
            hk2_pos hk2_le hcm_pos (by omega) (by omega) (by omega)
          have her_cfg_cm : er.elecCfg = cfgAt cm.log k2 := by
            rw [her_cfg_k2]; simp [cfgAt, stateAt, htake_k2]
          by_cases hex1 : ∃ j e, k2 < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
          · rcases exists_first_voter_change cm.log hex1 with ⟨k', ek', hk'_gt, hk'_le, hk'_get, hk'_vc, hno_mid⟩
            by_cases hex2 : ∃ j e, k' < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
            · -- ≥ 2 voter changes after k2 in cm.log: ConfigParent on the second gives earlier commit!
              rcases hex2 with ⟨k'', ek'', hk''_gt, hk''_le, hk''_get, hk''_vc⟩
              rcases hcm_good.2.2.2.1 k'' ek'' (by omega) (by omega) hk''_get hk''_vc with
                ⟨cm', hcm'_mem, hcm'_t, hcm'_lt, hcm'_pre, _, hcm'_novc⟩
              have hcm'_t_le : cm'.term ≤ cm.term := by
                have hmon := hcm_good.2.1.2 k'' cm.idx (by omega) hk''_le (by omega)
                have htk'' : logTermAt cm.log k'' = ek''.term := by simp [logTermAt, hk''_get]
                omega
              have hcm'_earl : IsPrefix cm'.log er.elecLog := by
                apply hEarlier cm' hcm'_mem
                by_cases heqt : cm'.term = cm.term
                · exact Or.inr ⟨heqt, by omega⟩
                · exact Or.inl (by omega)
              -- k' ≤ cm'.idx because k' is a voter change < k'' and none in (cm'.idx, k'')
              have hk'_le_cm' : k' ≤ cm'.idx := by
                by_cases hle : k' ≤ cm'.idx
                · exact hle
                · have hf := hcm'_novc k' ek' (by omega) hk''_gt hk'_get
                  rw [hk'_vc] at hf; cases hf
              -- So er.elecLog has voter change at k' > k2, contradicting k2 = lastVoterChange!
              have hcm'_wf := hinv.commitRecs cm' hcm'_mem
              have hcm'_len : cm'.log.length = cm'.idx := hcm'_wf.2.1
              have hget_er : logGet er.elecLog k' = some ek' := by
                rw [← logGet_of_prefix hcm'_earl (by omega)]
                rw [logGet_of_prefix hcm'_pre (by omega)]
                rw [logGet_take cm.log (by omega)]
                exact hk'_get
              have hge_k2 := lastVoterChangeUpTo_ge_of_vc er.elecLog (k := er.elecLog.length)
                (by have := hcm'_earl.1; omega) hget_er hk'_vc
              change k' ≤ k2 at hge_k2
              omega
            · -- Exactly 1 voter change k' in (k2, cm.idx] -> Adjacent!
              have hno_after : ∀ j e, k' < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                cases hvcj : e.cmd.isVoterChange with
                | false => rfl
                | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex2
              have hadj : Adjacent (cfgAt cm.log k2) (cfgAt cm.log cm.idx) :=
                cfgAt_adjacent_of_one_voter_change hcm_good.1 hk2_pos hk'_gt hk'_le (by omega) hno_mid hno_after
              have hcm_cfg_idx : cm.cfg = cfgAt cm.log cm.idx := by
                rw [hcfg_eq, votersOfLog_eq_cfgAt_length, hcm_len]
              exact hq (by rw [hcm_cfg_idx, her_cfg_cm]; exact hadj.symm)
          · -- 0 voter changes after k2 in cm.log -> equal configs!
            have hno_all : ∀ j e, k2 < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
              intro j e hj1 hj2 hgj
              cases hvcj : e.cmd.isVoterChange with
              | false => rfl
              | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex1
            have heq_cfg : cfgAt cm.log cm.idx = cfgAt cm.log k2 :=
              cfgAt_eq_of_no_voter_change (by omega) (by omega) hno_all
            have hcm_cfg_idx : cm.cfg = cfgAt cm.log cm.idx := by
              rw [hcfg_eq, votersOfLog_eq_cfgAt_length, hcm_len]
            exact hq (by rw [hcm_cfg_idx, her_cfg_cm, heq_cfg]; exact .refl _)
      · -- Case 3: τ2 < cm.term!
        have hτ2_lt_cm : τ2 < cm.term := by omega
        rcases hcm.2.2.2.2.2.2.1 with ⟨er1, her1_mem, her1_t, _, her1_pre, her1_ext⟩
        have her1_rec := hinv.electionRecs er1 her1_mem
        have hcm_t_gt1 : cm.term > 1 := by omega
        have her1_t_gt1 : er1.term > 1 := by omega
        have hkn_er1 : IsKnownLog s er1.elecLog := Or.inr (Or.inl ⟨er1, her1_mem, rfl⟩)
        have her1_good : GoodLog boot s er1.elecLog := hinv.goodLogs er1.elecLog hkn_er1
        have her1_wf : ElectionWF boot s er1 :=
          ⟨her1_t_gt1, her1_good, (her1_rec.2.2.2.2.2.2 her1_t_gt1).1,
           her1_rec.2.2.1, her1_rec.2.2.2.1, her1_rec.2.2.2.2.1⟩
        have her1_ne : er1.elecLog.length > 0 := electionLog_nonempty her1_wf
        let k1 := lastVoterChange er1.elecLog
        let τ1 := logTermAt er1.elecLog k1
        have hk1_pos : k1 ≥ 1 := lastVoterChange_pos_of_nonempty her1_good her1_ne
        have hk1_le : k1 ≤ er1.elecLog.length := lastVoterChange_le er1.elecLog
        have hτ1_lt : τ1 < cm.term := by
          have hmon := her1_good.2.1.2 k1 er1.elecLog.length hk1_pos hk1_le (Nat.le_refl _)
          have hlt1 := her1_wf.2.2.1; unfold logLastTerm at hlt1; omega
        have her1_cfg_k1 : er1.elecCfg = cfgAt er1.elecLog k1 := by
          rw [her1_wf.2.2.2.1]; exact votersOfLog_eq_lastVoterChange er1.elecLog
        have her1_cfg_cm : er1.elecCfg = cfgAt cm.log k1 := by
          rw [her1_cfg_k1]; exact cfgAt_of_prefix her1_pre hk1_le
        -- Note: any voter change in cm.log strictly after k1 must be > er1.elecLog.length
        -- (since k1 = lastVoterChange er1.elecLog), hence has term = cm.term!
        have hvc_after_k1_gt : ∀ j e, k1 < j → j ≤ cm.idx → logGet cm.log j = some e →
            e.cmd.isVoterChange = true → er1.elecLog.length < j := by
          intro j e hj1 hj2 hgj hvcj
          by_cases hle : j ≤ er1.elecLog.length
          · rw [← logGet_of_prefix her1_pre hle] at hgj
            have hf := lastVoterChangeUpTo_none_after er1.elecLog er1.elecLog.length j e hj1 hle hgj
            rw [hvcj] at hf; cases hf
          · omega
        -- Compare (τ2, k2) vs (τ1, k1)
        by_cases hEq12 : τ2 = τ1 ∧ k2 = k1
        · -- Subcase 3a: (τ2, k2) = (τ1, k1) -> er.elecCfg = er1.elecCfg
          have htake := hinv.sameTermPrefix er.elecLog er1.elecLog k2 k1 hkn_er hkn_er1
            hk2_pos hk2_le hk1_pos hk1_le hEq12.1 (by omega)
          have hcfg_eq_init : er.elecCfg = cfgAt cm.log k1 := by
            rw [her_cfg_k2, ← her1_cfg_cm, her1_cfg_k1]
            simp [cfgAt, stateAt, hEq12.2] at htake ⊢
            rw [htake]
          by_cases hex1 : ∃ j e, k1 < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
          · rcases exists_first_voter_change cm.log hex1 with ⟨k', ek', hk'_gt, hk'_le, hk'_get, hk'_vc, hno_mid⟩
            by_cases hex2 : ∃ j e, k' < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
            · rcases hex2 with ⟨k'', ek'', hk''_gt, hk''_le, hk''_get, hk''_vc⟩
              rcases hcm_good.2.2.2.1 k'' ek'' (by omega) (by omega) hk''_get hk''_vc with
                ⟨cm', hcm'_mem, hcm'_t, hcm'_lt, hcm'_pre, _, hcm'_novc⟩
              have hcm'_t_le : cm'.term ≤ cm.term := by
                have hmon := hcm_good.2.1.2 k'' cm.idx (by omega) hk''_le (by omega)
                have htk'' : logTermAt cm.log k'' = ek''.term := by simp [logTermAt, hk''_get]
                omega
              have hcm'_earl : IsPrefix cm'.log er.elecLog := by
                apply hEarlier cm' hcm'_mem
                by_cases heqt : cm'.term = cm.term
                · exact Or.inr ⟨heqt, by omega⟩
                · exact Or.inl (by omega)
              have hk'_le_cm' : k' ≤ cm'.idx := by
                by_cases hle : k' ≤ cm'.idx
                · exact hle
                · have hf := hcm'_novc k' ek' (by omega) hk''_gt hk'_get
                  rw [hk'_vc] at hf; cases hf
              have hcm'_wf := hinv.commitRecs cm' hcm'_mem
              have hcm'_len : cm'.log.length = cm'.idx := hcm'_wf.2.1
              have hget_er : logGet er.elecLog k' = some ek' := by
                rw [← logGet_of_prefix hcm'_earl (by omega)]
                rw [logGet_of_prefix hcm'_pre (by omega)]
                rw [logGet_take cm.log (by omega)]
                exact hk'_get
              have hge_k2 := lastVoterChangeUpTo_ge_of_vc er.elecLog (k := er.elecLog.length)
                (by have := hcm'_earl.1; omega) hget_er hk'_vc
              change k' ≤ k2 at hge_k2
              omega
            · have hno_after : ∀ j e, k' < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                cases hvcj : e.cmd.isVoterChange with
                | false => rfl
                | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex2
              have hadj : Adjacent (cfgAt cm.log k1) (cfgAt cm.log cm.idx) :=
                cfgAt_adjacent_of_one_voter_change hcm_good.1 hk1_pos hk'_gt hk'_le (by omega) hno_mid hno_after
              have hcm_cfg_idx : cm.cfg = cfgAt cm.log cm.idx := by
                rw [hcfg_eq, votersOfLog_eq_cfgAt_length, hcm_len]
              exact hq (by rw [hcm_cfg_idx, hcfg_eq_init]; exact hadj.symm)
          · have hno_all : ∀ j e, k1 < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
              intro j e hj1 hj2 hgj
              cases hvcj : e.cmd.isVoterChange with
              | false => rfl
              | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex1
            have heq_cfg : cfgAt cm.log cm.idx = cfgAt cm.log k1 :=
              cfgAt_eq_of_no_voter_change (by have := her1_pre.1; omega) (by omega) hno_all
            have hcm_cfg_idx : cm.cfg = cfgAt cm.log cm.idx := by
              rw [hcfg_eq, votersOfLog_eq_cfgAt_length, hcm_len]
            exact hq (by rw [hcm_cfg_idx, hcfg_eq_init, heq_cfg]; exact .refl _)
        · by_cases hgt12 : τ1 < τ2 ∨ (τ1 = τ2 ∧ k1 < k2)
          · -- Subcase 3b: (τ1, k1) < (τ2, k2) -> ConfigParent of k2 in er.elecLog!
            have hk2_gt1 : 1 < k2 := by
              by_cases h1 : k2 = 1
              · rcases logGet_some_iff er.elecLog (by omega) hk2_le with ⟨e1, hg1⟩
                have ht1 : τ2 = 1 := by
                  have hg1' : logGet er.elecLog 1 = some e1 := by rwa [h1] at hg1
                  have hb := her_good.2.2.1 e1 hg1'
                  show logTermAt er.elecLog k2 = 1
                  rw [h1]; simp [logTermAt, hg1', hb.1]
                have hτ1_pos : τ1 > 0 := her1_good.2.1.1 k1 hk1_pos hk1_le
                omega
              · omega
            have hk2_pos' : lastVoterChangeUpTo er.elecLog er.elecLog.length > 0 := hk2_pos
            rcases lastVoterChangeUpTo_is_vc er.elecLog er.elecLog.length hk2_pos' with ⟨e2, hg2, hvc2⟩
            have hg2' : logGet er.elecLog k2 = some e2 := hg2
            have hτ2_eq_e2 : e2.term = τ2 := by
              show e2.term = logTermAt er.elecLog k2
              simp [logTermAt, hg2']
            rcases her_good.2.2.2.1 k2 e2 hk2_gt1 hk2_le hg2' hvc2 with
              ⟨cm2, hcm2_mem, hcm2_t, hcm2_lt, hcm2_pre, hcm2_cfg, hcm2_novc⟩
            have hcm2_wf := hinv.commitRecs cm2 hcm2_mem
            have hcm2_len : cm2.log.length = cm2.idx := hcm2_wf.2.1
            -- Since cm2.term = τ2 < cm.term = er1.term, Leader Completeness in s gives IsPrefix cm2.log er1.elecLog!
            have hcm2_in_er1 : IsPrefix cm2.log er1.elecLog :=
              hinv.leaderCompleteness cm2 hcm2_mem er1 her1_mem (by omega)
            -- Show k1 ≤ cm2.idx!
            have hk1_le_cm2 : k1 ≤ cm2.idx := by
              by_cases hle : k1 ≤ cm2.idx
              · exact hle
              · have hcm2_t_at : logTermAt er1.elecLog cm2.idx = τ2 := by
                  rw [← logTermAt_of_prefix hcm2_in_er1 (by omega)]
                  have := hcm2_wf.2.2.1; unfold logLastTerm at this; rw [hcm2_len] at this; omega
                have hτ1_ge : τ2 ≤ τ1 := by
                  rw [← hcm2_t_at]
                  exact her1_good.2.1.2 cm2.idx k1 hcm2_wf.1 (by omega) hk1_le
                have hτ1_eq : τ1 = τ2 := by omega
                have hk1_lt_k2 : k1 < k2 := by omega
                have htake := hinv.sameTermPrefix er1.elecLog er.elecLog k1 k2 hkn_er1 hkn_er
                  hk1_pos hk1_le hk2_pos hk2_le hτ1_eq (by omega)
                have hk1_pos' : lastVoterChangeUpTo er1.elecLog er1.elecLog.length > 0 := hk1_pos
                rcases lastVoterChangeUpTo_is_vc er1.elecLog er1.elecLog.length hk1_pos' with ⟨e1, hg1, hvc1⟩
                have hg1' : logGet er1.elecLog k1 = some e1 := hg1
                have hg1_er : logGet er.elecLog k1 = some e1 := by
                  rw [← logGet_take er.elecLog (Nat.le_refl k1), ← htake, logGet_take er1.elecLog (Nat.le_refl k1)]
                  exact hg1'
                have hf := hcm2_novc k1 e1 (by omega) hk1_lt_k2 hg1_er
                rw [hvc1] at hf; cases hf
            -- Therefore er1.elecCfg = cfgAt er.elecLog (k2 - 1), which is Adjacent to er.elecCfg!
            have her1_eq_prev2 : er1.elecCfg = cfgAt er.elecLog (k2 - 1) := by
              have hno_er1 : ∀ j e, cm2.idx < j → j ≤ er1.elecLog.length →
                  logGet er1.elecLog j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                exact lastVoterChangeUpTo_none_after er1.elecLog er1.elecLog.length j e (by change k1 < j; omega) hj2 hgj
              have h1 : cfgAt er1.elecLog er1.elecLog.length = cfgAt er1.elecLog cm2.idx :=
                cfgAt_eq_of_no_voter_change (by have := hcm2_in_er1.1; omega) (Nat.le_refl _) hno_er1
              have h2 : cfgAt er1.elecLog cm2.idx = cfgAt cm2.log cm2.idx :=
                (cfgAt_of_prefix hcm2_in_er1 (by omega)).symm
              have h3 : cfgAt cm2.log cm2.idx = cfgAt (er.elecLog.take (k2 - 1)) cm2.idx :=
                cfgAt_of_prefix hcm2_pre (by omega)
              have h4 : cfgAt (er.elecLog.take (k2 - 1)) cm2.idx = cfgAt er.elecLog cm2.idx :=
                cfgAt_take_eq er.elecLog (by omega)
              have h5 : cfgAt er.elecLog (k2 - 1) = cfgAt er.elecLog cm2.idx :=
                cfgAt_eq_of_no_voter_change (by omega) (by omega)
                  (fun j e hj1 hj2 => hcm2_novc j e hj1 (by omega))
              rw [her1_wf.2.2.2.1, votersOfLog_eq_cfgAt_length, h1, h2, h3, h4, h5]
            have hadj_init_er : Adjacent er1.elecCfg er.elecCfg := by
              rw [her1_eq_prev2, her_cfg_k2]
              exact cfgAt_adjacent_step her_good.1 hk2_gt1 hk2_le
            -- Now check voter changes in cm.log strictly after k1
            by_cases hex1 : ∃ j e, k1 < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
            · -- First voter change k' > k1 in cm.log has term = cm.term!
              rcases exists_first_voter_change cm.log hex1 with ⟨k', ek', hk'_gt, hk'_le, hk'_get, hk'_vc, hno_mid⟩
              have hk'_gt_er1 : er1.elecLog.length < k' := hvc_after_k1_gt k' ek' hk'_gt hk'_le hk'_get hk'_vc
              have hek'_t : ek'.term = cm.term := by
                have := her1_ext k' hk'_gt_er1 hk'_le
                simp [logTermAt, hk'_get] at this; exact this
              rcases hcm_good.2.2.2.1 k' ek' (by omega) (by omega) hk'_get hk'_vc with
                ⟨cm', hcm'_mem, hcm'_t, hcm'_lt, hcm'_pre, _, _⟩
              have hcm'_earl : IsPrefix cm'.log er.elecLog :=
                hEarlier cm' hcm'_mem (Or.inr ⟨by omega, by omega⟩)
              -- cm' has term = cm.term > τ2, so er.elecLog has term cm.term at cm'.idx!
              have hcm'_wf := hinv.commitRecs cm' hcm'_mem
              have hcm'_len : cm'.log.length = cm'.idx := hcm'_wf.2.1
              have hcm'_t_er : logTermAt er.elecLog cm'.idx = cm.term := by
                rw [← logTermAt_of_prefix hcm'_earl (by omega)]
                have := hcm'_wf.2.2.1; unfold logLastTerm at this; rw [hcm'_len] at this; omega
              -- Since logTermAt er.elecLog k2 = τ2 < cm.term = logTermAt er.elecLog cm'.idx, k2 < cm'.idx!
              have hk2_lt_cm' : k2 < cm'.idx := by
                by_cases hge : cm'.idx ≤ k2
                · have hmon := her_good.2.1.2 cm'.idx k2 hcm'_wf.1 hge hk2_le
                  omega
                · omega
              -- Also k1 < cm'.idx since logTermAt cm.log k1 = τ1 < cm.term = logTermAt cm.log cm'.idx
              have hk1_lt_cm' : k1 < cm'.idx := by
                have hcm'_t_cm : logTermAt cm.log cm'.idx = cm.term := by
                  rw [← logTermAt_take cm.log (n := k' - 1) (by omega)]
                  rw [← logTermAt_of_prefix hcm'_pre (by omega)]
                  have := hcm'_wf.2.2.1; unfold logLastTerm at this; rw [hcm'_len] at this; omega
                have hk1_t_cm : logTermAt cm.log k1 = τ1 :=
                  (logTermAt_of_prefix her1_pre hk1_le).symm
                by_cases hge : cm'.idx ≤ k1
                · have hmon := hcm_good.2.1.2 cm'.idx k1 hcm'_wf.1 hge (by have := her1_pre.1; omega)
                  omega
                · omega
              -- Now er.elecLog agrees with cm.log up to cm'.idx (both have cm'.log as prefix!)
              -- So k2 (voter change in er.elecLog) is ALSO in cm.log at k2 < cm'.idx < k'!
              have hg2_cm : logGet cm.log k2 = some e2 := by
                rw [← logGet_take cm.log (n := k' - 1) (by omega)]
                rw [← logGet_of_prefix hcm'_pre (by omega)]
                rw [logGet_of_prefix hcm'_earl (by omega)]
                exact hg2
              -- Since k' was the FIRST voter change after k1 in cm.log, k2 ≤ k1!
              have hk2_le_k1 : k2 ≤ k1 := by
                by_cases hle : k2 ≤ k1
                · exact hle
                · have hf := hno_mid k2 e2 (by omega) (by omega) hg2_cm
                  rw [hvc2] at hf; cases hf
              -- And k1 (voter change in er1.elecLog, hence in cm.log at k1 < cm'.idx) is ALSO in er.elecLog!
              rcases lastVoterChangeUpTo_is_vc er1.elecLog er1.elecLog.length (by omega) with ⟨e1, hg1, hvc1⟩
              have hg1_er : logGet er.elecLog k1 = some e1 := by
                rw [← logGet_of_prefix hcm'_earl (by omega)]
                rw [logGet_of_prefix hcm'_pre (by omega)]
                rw [logGet_take cm.log (n := k' - 1) (by omega)]
                rw [← logGet_of_prefix her1_pre hk1_le]
                exact hg1
              have hk1_le_k2 := lastVoterChangeUpTo_ge_of_vc er.elecLog (k := er.elecLog.length)
                (by have := hcm'_earl.1; omega) hg1_er hvc1
              change k1 ≤ k2 at hk1_le_k2
              -- So k1 = k2 and hence τ1 = τ2, contradicting (τ1, k1) < (τ2, k2)!
              have hk_eq : k1 = k2 := by omega
              have hτ_eq : τ1 = τ2 := by
                have hg1' : logGet er1.elecLog k1 = some e1 := hg1
                have ht1 : logTermAt er.elecLog k1 = e1.term := by simp [logTermAt, hg1_er]
                have ht2 : logTermAt er1.elecLog k1 = e1.term := by simp [logTermAt, hg1']
                change logTermAt er1.elecLog k1 = logTermAt er.elecLog k2
                rw [← hk_eq, ht1, ht2]
              omega
            · -- 0 voter changes after k1 in cm.log -> cm.cfg = er1.elecCfg, Adjacent to er.elecCfg!
              have hno_all : ∀ j e, k1 < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                cases hvcj : e.cmd.isVoterChange with
                | false => rfl
                | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex1
              have hcm_eq_init : cm.cfg = er1.elecCfg := by
                rw [hcfg_eq, her1_cfg_cm, votersOfLog_eq_cfgAt_length, hcm_len]
                exact cfgAt_eq_of_no_voter_change (by have := her1_pre.1; omega) (by omega) hno_all
              exact hq (by rw [hcm_eq_init]; exact hadj_init_er)
          · -- Subcase 3c: (τ2, k2) < (τ1, k1) -> ConfigParent of k1 in er1.elecLog!
            have hlt21 : τ2 < τ1 ∨ (τ2 = τ1 ∧ k2 < k1) := by omega
            have hk1_gt1 : 1 < k1 := by
              by_cases h1 : k1 = 1
              · rcases logGet_some_iff er1.elecLog (by omega) hk1_le with ⟨e1, hg1⟩
                have ht1 : τ1 = 1 := by
                  have hg1' : logGet er1.elecLog 1 = some e1 := by rwa [h1] at hg1
                  have hb := her1_good.2.2.1 e1 hg1'
                  show logTermAt er1.elecLog k1 = 1
                  rw [h1]; simp [logTermAt, hg1', hb.1]
                omega
              · omega
            have hk1_pos' : lastVoterChangeUpTo er1.elecLog er1.elecLog.length > 0 := hk1_pos
            rcases lastVoterChangeUpTo_is_vc er1.elecLog er1.elecLog.length hk1_pos' with ⟨e1, hg1, hvc1⟩
            have hg1' : logGet er1.elecLog k1 = some e1 := hg1
            have hτ1_eq_e1 : e1.term = τ1 := by
              show e1.term = logTermAt er1.elecLog k1
              simp [logTermAt, hg1']
            rcases her1_good.2.2.2.1 k1 e1 hk1_gt1 hk1_le hg1' hvc1 with
              ⟨cm1, hcm1_mem, hcm1_t, hcm1_lt, hcm1_pre, hcm1_cfg, hcm1_novc⟩
            have hcm1_wf := hinv.commitRecs cm1 hcm1_mem
            have hcm1_len : cm1.log.length = cm1.idx := hcm1_wf.2.1
            -- Since cm1.term = τ1 < cm.term, hEarlier gives IsPrefix cm1.log er.elecLog!
            have hcm1_in_er : IsPrefix cm1.log er.elecLog :=
              hEarlier cm1 hcm1_mem (Or.inl (by omega))
            -- Show k2 ≤ cm1.idx!
            have hk2_le_cm1 : k2 ≤ cm1.idx := by
              by_cases hle : k2 ≤ cm1.idx
              · exact hle
              · have hcm1_t_at : logTermAt er.elecLog cm1.idx = τ1 := by
                  rw [← logTermAt_of_prefix hcm1_in_er (by omega)]
                  have := hcm1_wf.2.2.1; unfold logLastTerm at this; rw [hcm1_len] at this; omega
                have hτ2_ge : τ1 ≤ τ2 := by
                  rw [← hcm1_t_at]
                  exact her_good.2.1.2 cm1.idx k2 hcm1_wf.1 (by omega) hk2_le
                have hτ2_eq : τ2 = τ1 := by omega
                have hk2_lt_k1 : k2 < k1 := by omega
                have htake := hinv.sameTermPrefix er.elecLog er1.elecLog k2 k1 hkn_er hkn_er1
                  hk2_pos hk2_le hk1_pos hk1_le hτ2_eq (by omega)
                have hk2_pos' : lastVoterChangeUpTo er.elecLog er.elecLog.length > 0 := hk2_pos
                rcases lastVoterChangeUpTo_is_vc er.elecLog er.elecLog.length hk2_pos' with ⟨e2, hg2, hvc2⟩
                have hg2' : logGet er.elecLog k2 = some e2 := hg2
                have hg2_er1 : logGet er1.elecLog k2 = some e2 := by
                  rw [← logGet_take er1.elecLog (Nat.le_refl k2), ← htake, logGet_take er.elecLog (Nat.le_refl k2)]
                  exact hg2'
                have hf := hcm1_novc k2 e2 (by omega) hk2_lt_k1 hg2_er1
                rw [hvc2] at hf; cases hf
            -- Therefore er.elecCfg = cfgAt er1.elecLog (k1 - 1), Adjacent to er1.elecCfg!
            have her_eq_prev1 : er.elecCfg = cfgAt er1.elecLog (k1 - 1) := by
              have hno_er : ∀ j e, cm1.idx < j → j ≤ er.elecLog.length →
                  logGet er.elecLog j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                exact lastVoterChangeUpTo_none_after er.elecLog er.elecLog.length j e (by change k2 < j; omega) hj2 hgj
              have h1 : cfgAt er.elecLog er.elecLog.length = cfgAt er.elecLog cm1.idx :=
                cfgAt_eq_of_no_voter_change (by have := hcm1_in_er.1; omega) (Nat.le_refl _) hno_er
              have h2 : cfgAt er.elecLog cm1.idx = cfgAt cm1.log cm1.idx :=
                (cfgAt_of_prefix hcm1_in_er (by omega)).symm
              have h3 : cfgAt cm1.log cm1.idx = cfgAt (er1.elecLog.take (k1 - 1)) cm1.idx :=
                cfgAt_of_prefix hcm1_pre (by omega)
              have h4 : cfgAt (er1.elecLog.take (k1 - 1)) cm1.idx = cfgAt er1.elecLog cm1.idx :=
                cfgAt_take_eq er1.elecLog (by omega)
              have h5 : cfgAt er1.elecLog (k1 - 1) = cfgAt er1.elecLog cm1.idx :=
                cfgAt_eq_of_no_voter_change (by omega) (by omega)
                  (fun j e hj1 hj2 => hcm1_novc j e hj1 (by omega))
              rw [her.2.2.2.1, votersOfLog_eq_cfgAt_length, h1, h2, h3, h4, h5]
            have hadj_init_er : Adjacent er1.elecCfg er.elecCfg := by
              rw [her_eq_prev1, her1_cfg_k1]
              exact (cfgAt_adjacent_step her1_good.1 hk1_gt1 hk1_le).symm
            -- Check voter changes in cm.log strictly after k1
            by_cases hex1 : ∃ j e, k1 < j ∧ j ≤ cm.idx ∧ logGet cm.log j = some e ∧ e.cmd.isVoterChange = true
            · rcases exists_first_voter_change cm.log hex1 with ⟨k', ek', hk'_gt, hk'_le, hk'_get, hk'_vc, _⟩
              have hk'_gt_er1 : er1.elecLog.length < k' := hvc_after_k1_gt k' ek' hk'_gt hk'_le hk'_get hk'_vc
              have hek'_t : ek'.term = cm.term := by
                have := her1_ext k' hk'_gt_er1 hk'_le
                simp [logTermAt, hk'_get] at this; exact this
              rcases hcm_good.2.2.2.1 k' ek' (by omega) (by omega) hk'_get hk'_vc with
                ⟨cm', hcm'_mem, hcm'_t, hcm'_lt, hcm'_pre, _, _⟩
              have hcm'_earl : IsPrefix cm'.log er.elecLog :=
                hEarlier cm' hcm'_mem (Or.inr ⟨by omega, by omega⟩)
              have hcm'_wf := hinv.commitRecs cm' hcm'_mem
              have hcm'_len : cm'.log.length = cm'.idx := hcm'_wf.2.1
              have hk1_lt_cm' : k1 < cm'.idx := by
                have hcm'_t_cm : logTermAt cm.log cm'.idx = cm.term := by
                  rw [← logTermAt_take cm.log (n := k' - 1) (by omega)]
                  rw [← logTermAt_of_prefix hcm'_pre (by omega)]
                  have := hcm'_wf.2.2.1; unfold logLastTerm at this; rw [hcm'_len] at this; omega
                have hk1_t_cm : logTermAt cm.log k1 = τ1 :=
                  (logTermAt_of_prefix her1_pre hk1_le).symm
                by_cases hge : cm'.idx ≤ k1
                · have hmon := hcm_good.2.1.2 cm'.idx k1 hcm'_wf.1 hge (by have := her1_pre.1; omega)
                  omega
                · omega
              -- So er.elecLog has k1 (voter change at term τ1)!
              have hg1_er : logGet er.elecLog k1 = some e1 := by
                rw [← logGet_of_prefix hcm'_earl (by omega)]
                rw [logGet_of_prefix hcm'_pre (by omega)]
                rw [logGet_take cm.log (n := k' - 1) (by omega)]
                rw [← logGet_of_prefix her1_pre hk1_le]
                exact hg1
              have hk1_le_k2 := lastVoterChangeUpTo_ge_of_vc er.elecLog (k := er.elecLog.length)
                (by have := hcm'_earl.1; omega) hg1_er hvc1
              change k1 ≤ k2 at hk1_le_k2
              have hτ1_le_τ2 : τ1 ≤ τ2 := by
                have ht1_er : logTermAt er.elecLog k1 = τ1 := by
                  simp [logTermAt, hg1_er, hτ1_eq_e1]
                rw [← ht1_er]
                exact her_good.2.1.2 k1 k2 hk1_pos hk1_le_k2 hk2_le
              omega
            · have hno_all : ∀ j e, k1 < j → j ≤ cm.idx → logGet cm.log j = some e → e.cmd.isVoterChange = false := by
                intro j e hj1 hj2 hgj
                cases hvcj : e.cmd.isVoterChange with
                | false => rfl
                | true => exact absurd ⟨j, e, hj1, hj2, hgj, hvcj⟩ hex1
              have hcm_eq_init : cm.cfg = er1.elecCfg := by
                rw [hcfg_eq, her1_cfg_cm, votersOfLog_eq_cfgAt_length, hcm_len]
                exact cfgAt_eq_of_no_voter_change (by have := her1_pre.1; omega) (by omega) hno_all
              exact hq (by rw [hcm_eq_init]; exact hadj_init_er)
  · -- SECOND CASE: cm was committed with Adjacent (votersOfLog cm.log) cm.cfg using cm0
    have hcm0_in_er : IsPrefix cm0.log er.elecLog :=
      hEarlier cm0 hcm0_mem (Or.inr ⟨hcm0_t, hcm0_idx⟩)
    have hcm0_wf := hinv.commitRecs cm0 hcm0_mem
    have hcm0_len : cm0.log.length = cm0.idx := hcm0_wf.2.1
    have hcm0_t_er : logTermAt er.elecLog cm0.idx = cm.term := by
      rw [← logTermAt_of_prefix hcm0_in_er (by omega)]
      have := hcm0_wf.2.2.1; unfold logLastTerm at this; rw [hcm0_len] at this; omega
    have her_t_ge : cm.term ≤ logLastTerm er.elecLog := by
      rw [← hcm0_t_er]
      exact her_good.2.1.2 cm0.idx er.elecLog.length hcm0_wf.1 (by have := hcm0_in_er.1; omega) (Nat.le_refl _)
    by_cases hgt : cm.term < logLastTerm er.elecLog
    · rcases her_good.2.2.2.2 er.elecLog.length her_ne (Nat.le_refl _) with ⟨er', her'_mem, her'_t, her'_pre⟩
      have hlt_er := her.2.2.1
      have hlc := hMid er' her'_mem (by unfold logLastTerm at hgt; omega) (by unfold logLastTerm at hlt_er; omega)
      rw [List.take_length] at her'_pre
      exact IsPrefix.trans hlc her'_pre
    · have heq_t : logLastTerm er.elecLog = cm.term := by omega
      by_cases hlen_ge : cm.idx ≤ er.elecLog.length
      · have htake := hinv.sameTermPrefix_sub hkn_cm ⟨er.elecLog, hkn_er, IsPrefix.refl _⟩
          hcm_pos (by omega) her_ne (Nat.le_refl _) (by unfold logLastTerm at heq_t; omega) hlen_ge
        refine ⟨by omega, ?_⟩
        rw [hcm_len, ← htake, ← hcm_len, List.take_length]
      · -- er.elecLog.length < cm.idx, so er.elecLog is a prefix of cm.log with length ≥ cm0.idx
        have htake := hinv.sameTermPrefix_sub ⟨er.elecLog, hkn_er, IsPrefix.refl _⟩ hkn_cm
          her_ne (Nat.le_refl _) hcm_pos (by omega) (by unfold logLastTerm at heq_t; omega) (by omega)
        have her_pre_cm : IsPrefix er.elecLog cm.log := by
          refine ⟨by omega, ?_⟩
          rw [← htake, List.take_length]
        -- Since no voter change in cm.log in (cm0.idx, cm.idx], er.elecCfg = votersOfLog cm.log!
        have her_cfg_eq : er.elecCfg = votersOfLog cm.log := by
          rw [her.2.2.2.1, votersOfLog_eq_cfgAt_length, votersOfLog_eq_cfgAt_length]
          rw [cfgAt_of_prefix her_pre_cm (Nat.le_refl _), hcm_len]
          have h1 : cfgAt cm.log er.elecLog.length = cfgAt cm.log cm0.idx :=
            cfgAt_eq_of_no_voter_change (by have := hcm0_in_er.1; omega) (by omega)
              (fun j e hj1 hj2 => hcm0_novc j e hj1 (by omega))
          have h2 : cfgAt cm.log cm.idx = cfgAt cm.log cm0.idx :=
            cfgAt_eq_of_no_voter_change (by omega) (by omega) hcm0_novc
          rw [h1, h2]
        exact hq (by rw [her_cfg_eq]; exact hadj_cm.symm)

/-- Election Safety step: any two well-formed elections in the SAME term `t > 1`
that both satisfy Leader Completeness for all commits of term `< t` MUST have
adjacent configs, hence intersecting quorums, hence the SAME leader! -/
theorem election_safety_step {boot : NodeId} {s : System NodeId T}
    (hinv : Inv boot s)
    {erA erB : ElectionRec NodeId T}
    (hA : ElectionWF boot s erA) (hB : ElectionWF boot s erB)
    (hknA : IsKnownLog s erA.elecLog) (hknB : IsKnownLog s erB.elecLog)
    (ht_eq : erA.term = erB.term)
    (hlcA : ∀ cm ∈ s.hist.commits, cm.term < erA.term → IsPrefix cm.log erA.elecLog)
    (hlcB : ∀ cm ∈ s.hist.commits, cm.term < erB.term → IsPrefix cm.log erB.elecLog)
    (hvA : ∀ v ∈ erA.elecQuorum, ∃ vr ∈ s.hist.votes, vr.term = erA.term ∧ vr.voter = v ∧ vr.cand = erA.leader)
    (hvB : ∀ v ∈ erB.elecQuorum, ∃ vr ∈ s.hist.votes, vr.term = erB.term ∧ vr.voter = v ∧ vr.cand = erB.leader) :
    Adjacent erA.elecCfg erB.elecCfg ∧ erA.leader = erB.leader := by
  have hadj : Adjacent erA.elecCfg erB.elecCfg := by
    let kA := lastVoterChange erA.elecLog
    let τA := logTermAt erA.elecLog kA
    let kB := lastVoterChange erB.elecLog
    let τB := logTermAt erB.elecLog kB
    have hneA := electionLog_nonempty hA
    have hneB := electionLog_nonempty hB
    have hkA_pos : kA ≥ 1 := lastVoterChange_pos_of_nonempty hA.2.1 hneA
    have hkB_pos : kB ≥ 1 := lastVoterChange_pos_of_nonempty hB.2.1 hneB
    have hkA_le : kA ≤ erA.elecLog.length := lastVoterChange_le erA.elecLog
    have hkB_le : kB ≤ erB.elecLog.length := lastVoterChange_le erB.elecLog
    have hcfgA : erA.elecCfg = cfgAt erA.elecLog kA := by
      rw [hA.2.2.2.1]; exact votersOfLog_eq_lastVoterChange erA.elecLog
    have hcfgB : erB.elecCfg = cfgAt erB.elecLog kB := by
      rw [hB.2.2.2.1]; exact votersOfLog_eq_lastVoterChange erB.elecLog
    -- Helper for the asymmetric case (τ1, k1) < (τ2, k2)
    have hlt_case : ∀ (e1 e2 : ElectionRec NodeId T),
        ElectionWF boot s e1 → ElectionWF boot s e2 →
        IsKnownLog s e1.elecLog → IsKnownLog s e2.elecLog →
        e1.term = e2.term →
        (∀ cm ∈ s.hist.commits, cm.term < e1.term → IsPrefix cm.log e1.elecLog) →
        (logTermAt e1.elecLog (lastVoterChange e1.elecLog) < logTermAt e2.elecLog (lastVoterChange e2.elecLog) ∨
         (logTermAt e1.elecLog (lastVoterChange e1.elecLog) = logTermAt e2.elecLog (lastVoterChange e2.elecLog) ∧
          lastVoterChange e1.elecLog < lastVoterChange e2.elecLog)) →
        Adjacent e1.elecCfg e2.elecCfg := by
      intro e1 e2 he1 he2 hk1 hk2 hte hlc1 hord
      let k1 := lastVoterChange e1.elecLog
      let τ1 := logTermAt e1.elecLog k1
      let k2 := lastVoterChange e2.elecLog
      let τ2 := logTermAt e2.elecLog k2
      have hord' : τ1 < τ2 ∨ (τ1 = τ2 ∧ k1 < k2) := hord
      have hne1 := electionLog_nonempty he1
      have hne2 := electionLog_nonempty he2
      have hk1_pos : k1 ≥ 1 := lastVoterChange_pos_of_nonempty he1.2.1 hne1
      have hk2_pos : k2 ≥ 1 := lastVoterChange_pos_of_nonempty he2.2.1 hne2
      have hk1_le : k1 ≤ e1.elecLog.length := lastVoterChange_le e1.elecLog
      have hk2_le : k2 ≤ e2.elecLog.length := lastVoterChange_le e2.elecLog
      have hτ1_pos : τ1 > 0 := he1.2.1.2.1.1 k1 hk1_pos hk1_le
      have hτ2_lt : τ2 < e2.term := by
        have := he2.2.1.2.1.2 k2 e2.elecLog.length hk2_pos hk2_le (Nat.le_refl _)
        have hlt := he2.2.2.1; unfold logLastTerm at hlt; omega
      have hk2_gt1 : 1 < k2 := by
        by_cases h1 : k2 = 1
        · rcases logGet_some_iff e2.elecLog (by omega) hk2_le with ⟨en, hgn⟩
          have ht : τ2 = 1 := by
            have hgn' : logGet e2.elecLog 1 = some en := by rwa [h1] at hgn
            have hb := he2.2.1.2.2.1 en hgn'
            show logTermAt e2.elecLog k2 = 1
            rw [h1]; simp [logTermAt, hgn', hb.1]
          omega
        · omega
      have hk2_pos' : lastVoterChangeUpTo e2.elecLog e2.elecLog.length > 0 := hk2_pos
      rcases lastVoterChangeUpTo_is_vc e2.elecLog e2.elecLog.length hk2_pos' with ⟨en2, hgn2, hvcn2⟩
      have hgn2' : logGet e2.elecLog k2 = some en2 := hgn2
      have hτ2_eq : en2.term = τ2 := by
        show en2.term = logTermAt e2.elecLog k2
        simp [logTermAt, hgn2']
      rcases he2.2.1.2.2.2.1 k2 en2 hk2_gt1 hk2_le hgn2' hvcn2 with
        ⟨cm2, hcm2_mem, hcm2_t, hcm2_lt, hcm2_pre, _, hcm2_novc⟩
      have hcm2_wf := hinv.commitRecs cm2 hcm2_mem
      have hcm2_len : cm2.log.length = cm2.idx := hcm2_wf.2.1
      have hcm2_in_e1 : IsPrefix cm2.log e1.elecLog := hlc1 cm2 hcm2_mem (by omega)
      have hk1_le_cm2 : k1 ≤ cm2.idx := by
        by_cases hle : k1 ≤ cm2.idx
        · exact hle
        · have hcm2_t_at : logTermAt e1.elecLog cm2.idx = τ2 := by
            rw [← logTermAt_of_prefix hcm2_in_e1 (by omega)]
            have := hcm2_wf.2.2.1; unfold logLastTerm at this; rw [hcm2_len] at this; omega
          have hτ1_ge : τ2 ≤ τ1 := by
            rw [← hcm2_t_at]
            exact he1.2.1.2.1.2 cm2.idx k1 hcm2_wf.1 (by omega) hk1_le
          have hτ1_eq : τ1 = τ2 := by omega
          have hk1_lt_k2 : k1 < k2 := by omega
          have htake := hinv.sameTermPrefix e1.elecLog e2.elecLog k1 k2 hk1 hk2
            hk1_pos hk1_le hk2_pos hk2_le hτ1_eq (by omega)
          have hk1_pos' : lastVoterChangeUpTo e1.elecLog e1.elecLog.length > 0 := hk1_pos
          rcases lastVoterChangeUpTo_is_vc e1.elecLog e1.elecLog.length hk1_pos' with ⟨en1, hgn1, hvcn1⟩
          have hgn1' : logGet e1.elecLog k1 = some en1 := hgn1
          have hgn1_e2 : logGet e2.elecLog k1 = some en1 := by
            rw [← logGet_take e2.elecLog (Nat.le_refl k1), ← htake, logGet_take e1.elecLog (Nat.le_refl k1)]
            exact hgn1'
          have hf := hcm2_novc k1 en1 (by omega) hk1_lt_k2 hgn1_e2
          rw [hvcn1] at hf; cases hf
      have he1_eq_prev2 : e1.elecCfg = cfgAt e2.elecLog (k2 - 1) := by
        have hno_e1 : ∀ j e, cm2.idx < j → j ≤ e1.elecLog.length →
            logGet e1.elecLog j = some e → e.cmd.isVoterChange = false := by
          intro j e hj1 hj2 hgj
          exact lastVoterChangeUpTo_none_after e1.elecLog e1.elecLog.length j e (by change k1 < j; omega) hj2 hgj
        have h1 : cfgAt e1.elecLog e1.elecLog.length = cfgAt e1.elecLog cm2.idx :=
          cfgAt_eq_of_no_voter_change (by have := hcm2_in_e1.1; omega) (Nat.le_refl _) hno_e1
        have h2 : cfgAt e1.elecLog cm2.idx = cfgAt cm2.log cm2.idx :=
          (cfgAt_of_prefix hcm2_in_e1 (by omega)).symm
        have h3 : cfgAt cm2.log cm2.idx = cfgAt (e2.elecLog.take (k2 - 1)) cm2.idx :=
          cfgAt_of_prefix hcm2_pre (by omega)
        have h4 : cfgAt (e2.elecLog.take (k2 - 1)) cm2.idx = cfgAt e2.elecLog cm2.idx :=
          cfgAt_take_eq e2.elecLog (by omega)
        have h5 : cfgAt e2.elecLog (k2 - 1) = cfgAt e2.elecLog cm2.idx :=
          cfgAt_eq_of_no_voter_change (by omega) (by omega)
            (fun j e hj1 hj2 => hcm2_novc j e hj1 (by omega))
        rw [he1.2.2.2.1, votersOfLog_eq_cfgAt_length, h1, h2, h3, h4, h5]
      rw [he1_eq_prev2, he2.2.2.2.1, votersOfLog_eq_lastVoterChange]
      exact cfgAt_adjacent_step he2.2.1.1 hk2_gt1 hk2_le
    by_cases hEq : τA = τB ∧ kA = kB
    · have htake := hinv.sameTermPrefix erA.elecLog erB.elecLog kA kB hknA hknB
        hkA_pos hkA_le hkB_pos hkB_le hEq.1 (by omega)
      have heqCfg : erA.elecCfg = erB.elecCfg := by
        rw [hcfgA, hcfgB]; simp [cfgAt, stateAt, hEq.2] at htake ⊢; rw [htake]
      rw [heqCfg]; exact .refl _
    · by_cases hlt : τA < τB ∨ (τA = τB ∧ kA < kB)
      · exact hlt_case erA erB hA hB hknA hknB ht_eq hlcA hlt
      · have hgt : τB < τA ∨ (τB = τA ∧ kB < kA) := by omega
        exact (hlt_case erB erA hB hA hknB hknA ht_eq.symm hlcB hgt).symm
  refine ⟨hadj, ?_⟩
  rcases adjacent_quorums_intersect hadj
      (fun v => decide (v ∈ erA.elecQuorum)) (fun v => decide (v ∈ erB.elecQuorum))
      hA.2.2.2.2.1 hB.2.2.2.2.1 with ⟨w, _, _, hwA, hwB⟩
  simp only [decide_eq_true_eq] at hwA hwB
  rcases hvA w hwA with ⟨vrA, hvrA_m, hvrA_t, hvrA_v, hvrA_c⟩
  rcases hvB w hwB with ⟨vrB, hvrB_m, hvrB_t, hvrB_v, hvrB_c⟩
  have hcand := hinv.voteUnique vrA hvrA_m vrB hvrB_m (by omega) (by rw [hvrA_v, hvrB_v])
  rw [← hvrA_c, ← hvrB_c, hcand]

/-- Any two known logs belonging to the same leader term `t` (either prefix of
`er.elecLog` or extending `er.elecLog` with term-`t` entries) are prefix-compatible. -/
theorem Inv.same_term_log_compat {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {t : Nat} {er : ElectionRec NodeId T} {L1 L2 : List (Entry NodeId T.Op)}
    (hkn1 : IsKnownLog s L1) (hkn2 : IsKnownLog s L2)
    (h1 : IsPrefix L1 er.elecLog ∨
      (IsPrefix er.elecLog L1 ∧ ∀ j, er.elecLog.length < j → j ≤ L1.length → logTermAt L1 j = t))
    (h2 : IsPrefix L2 er.elecLog ∨
      (IsPrefix er.elecLog L2 ∧ ∀ j, er.elecLog.length < j → j ≤ L2.length → logTermAt L2 j = t)) :
    IsPrefix L1 L2 ∨ IsPrefix L2 L1 := by
  rcases h1 with hp1 | ⟨hp1, hext1⟩ <;> rcases h2 with hp2 | ⟨hp2, hext2⟩
  · by_cases hle : L1.length ≤ L2.length
    · left; refine ⟨hle, ?_⟩
      rw [hp2.take_eq_of_le hle, hp1.2]
    · right; refine ⟨by omega, ?_⟩
      rw [hp1.take_eq_of_le (by omega), hp2.2]
  · exact Or.inl (IsPrefix.trans hp1 hp2)
  · exact Or.inr (IsPrefix.trans hp2 hp1)
  · by_cases hle : L1.length ≤ L2.length
    · left
      by_cases heq1 : L1.length = er.elecLog.length
      · have : L1 = er.elecLog := (hp1.eq_of_length_eq heq1.symm).symm
        rwa [this]
      · have hgt1 : er.elecLog.length < L1.length := by have := hp1.1; omega
        have ht1 := hext1 L1.length hgt1 (Nat.le_refl _)
        have ht2 := hext2 L2.length (by omega) (Nat.le_refl _)
        have htake := hinv.sameTermPrefix L1 L2 L1.length L2.length hkn1 hkn2
          (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega) hle
        refine ⟨hle, ?_⟩
        rw [← htake, List.take_length]
    · right
      by_cases heq2 : L2.length = er.elecLog.length
      · have : L2 = er.elecLog := (hp2.eq_of_length_eq heq2.symm).symm
        rwa [this]
      · have hgt2 : er.elecLog.length < L2.length := by have := hp2.1; omega
        have ht1 := hext1 L1.length (by omega) (Nat.le_refl _)
        have ht2 := hext2 L2.length hgt2 (Nat.le_refl _)
        have htake := hinv.sameTermPrefix L2 L1 L2.length L1.length hkn2 hkn1
          (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega) (by omega)
        refine ⟨by omega, ?_⟩
        rw [← htake, List.take_length]

/-- Prefix-closed helper for the `acceptedRecs` term-extension property. -/
theorem termExt_of_prefix {t : Nat} {er : ElectionRec NodeId T} {A B : List (Entry NodeId T.Op)}
    (hp : IsPrefix A B)
    (hB : IsPrefix B er.elecLog ∨
      (IsPrefix er.elecLog B ∧ ∀ j, er.elecLog.length < j → j ≤ B.length → logTermAt B j = t)) :
    IsPrefix A er.elecLog ∨
      (IsPrefix er.elecLog A ∧ ∀ j, er.elecLog.length < j → j ≤ A.length → logTermAt A j = t) := by
  rcases hB with hBe | ⟨heB, hext⟩
  · exact Or.inl (IsPrefix.trans hp hBe)
  · by_cases hle : A.length ≤ er.elecLog.length
    · left; refine ⟨hle, ?_⟩
      rw [heB.take_eq_of_le hle, hp.2]
    · right
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [hp.take_eq_of_le (by omega), heB.2]
      · intro j hj1 hj2
        rw [logTermAt_of_prefix hp hj2]
        exact hext j hj1 (Nat.le_trans hj2 hp.1)

/-- Any commit of term `≤ t` and any log accepted in term `t` are prefix-compatible. -/
theorem Inv.commit_accepted_compat {boot : NodeId} {s : System NodeId T} (hinv : Inv boot s)
    {cm : CommitRec NodeId T} {i : NodeId} {t : Nat} {La : List (Entry NodeId T.Op)}
    (hcm : cm ∈ s.hist.commits) (hle : cm.term ≤ t) (hacc : (t, La) ∈ s.hist.accepted i) :
    IsPrefix cm.log La ∨ IsPrefix La cm.log := by
  have hwf := hinv.commitRecs cm hcm
  rcases (hinv.acceptedRecs i t La hacc).2.2.1 with ⟨er, her, hter, hLa_ext⟩
  have hkn_cm : IsKnownLog s cm.log := Or.inr (Or.inr (Or.inl ⟨cm, hcm, rfl⟩))
  have hkn_La : IsKnownLog s La := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, t, hacc⟩))))
  have hcm_ext : IsPrefix cm.log er.elecLog ∨
      (IsPrefix er.elecLog cm.log ∧ ∀ j, er.elecLog.length < j → j ≤ cm.log.length → logTermAt cm.log j = t) := by
    by_cases hlt : cm.term < t
    · exact Or.inl (hinv.leaderCompleteness cm hcm er her (by omega))
    · have heq : cm.term = t := by omega
      rcases hwf.2.2.2.2.2.2.1 with ⟨er1, her1, hter1, _, hpre1, hext1⟩
      have her_eq := hinv.electionUnique er1 her1 er her (by omega)
      subst her_eq
      exact Or.inr ⟨hpre1, fun j hj1 hj2 => by
        rw [← heq]; exact hext1 j hj1 (by have := hwf.2.1; omega)⟩
  exact hinv.same_term_log_compat hkn_cm hkn_La hcm_ext hLa_ext

end Invariants

end ValkeyRaft.ConfigOnAppend

/-
  Sanity-check counterexamples proving that dropping ANY of the core guards
  of the intended design breaks safety:

  1. Dropping the serialization guard (`hasUncommittedVoterChange = false`,
     gap A2): pipelined `ADD_VOTER(3), ADD_VOTER(4)` under config-on-append
     loses a committed entry (violates Leader Completeness).
  2. Dropping the own-term-commit-first guard (Ongaro 2015): even WITH
     serialization and config-on-append, two leaders diverge on opposite
     `DEL_VOTER` entries and elect a leader missing a committed entry.
  3. Dropping pure apply (`DEL_VOTER` reading node-local `rs->leader`):
     two nodes applying the exact same valid log diverge permanently on
     `voters` and `size` (violates Apply Determinism & No Committed No-ops).

  Every proof is checked by Lean's kernel (zero `sorry`, zero `native_decide`,
  zero extra axioms).
-/
import ValkeyRaft.ConfigOnAppend.LogLemmas

namespace ValkeyRaft.ConfigOnAppend.Counterexamples

open ValkeyRaft.ConfigOnAppend

/-- Minimal concrete topology spec carrying a single `Nat` value. -/
abbrev natTopo : TopoSpec Nat where
  State := Nat
  Op := Nat
  initState := 0
  valid := fun _ _ _ _ => True
  applyOpt := fun _ op => some op
  valid_apply := fun _ _ _ op _ => ⟨op, rfl⟩

/-! ## Variants of `Step` with one guard dropped -/

/-- `Step` with the serialization guard (`hasUncommittedVoterChange = false`)
dropped, keeping config-on-append, own-term-commit-first, and pure apply. -/
inductive StepNoSerial (boot : Nat) : System Nat natTopo → System Nat natTopo → Prop where
  | ofStep {s s'} : Step boot s s' → StepNoSerial boot s s'
  | proposeNoSerial (s : System Nat natTopo) (l : Nat) (cmd : Cmd Nat Nat)
      (hLeader : (s.nodes l).role = .leader)
      (hValid : validCmd boot (s.nodes l).projectedState cmd)
      (hOwnTerm : cmd.isVoterChange = true →
        (s.nodes l).commit > 0 ∧ (s.nodes l).termAt (s.nodes l).commit = (s.nodes l).term) :
      StepNoSerial boot s (nextPropose s l cmd)

inductive ReachNoSerial (boot : Nat) : System Nat natTopo → Prop where
  | init : ReachNoSerial boot (System.init natTopo)
  | step {s s'} : ReachNoSerial boot s → StepNoSerial boot s s' → ReachNoSerial boot s'

/-- `Step` with the own-term-commit-first guard dropped, keeping serialization
(`hasUncommittedVoterChange = false`), config-on-append, and pure apply. -/
inductive StepNoOwnTerm (boot : Nat) : System Nat natTopo → System Nat natTopo → Prop where
  | ofStep {s s'} : Step boot s s' → StepNoOwnTerm boot s s'
  | proposeNoOwnTerm (s : System Nat natTopo) (l : Nat) (cmd : Cmd Nat Nat)
      (hLeader : (s.nodes l).role = .leader)
      (hValid : validCmd boot (s.nodes l).projectedState cmd)
      (hSerial : cmd.isVoterChange = true → (s.nodes l).hasUncommittedVoterChange = false) :
      StepNoOwnTerm boot s (nextPropose s l cmd)

inductive ReachNoOwnTerm (boot : Nat) : System Nat natTopo → Prop where
  | init : ReachNoOwnTerm boot (System.init natTopo)
  | step {s s'} : ReachNoOwnTerm boot s → StepNoOwnTerm boot s s' → ReachNoOwnTerm boot s'

/-! ## Decidable `validCmd` and `Msg` equality for `natTopo` -/

deriving instance DecidableEq for Cmd
deriving instance DecidableEq for Entry

instance : DecidableEq (ClusterState natTopo) := fun a b =>
  if h1 : a.members = b.members then
    if h2 : a.voters = b.voters then
      if h3 : a.topo = b.topo then
        isTrue (by cases a; cases b; simp_all)
      else isFalse (by intro h; cases h; exact h3 rfl)
    else isFalse (by intro h; cases h; exact h2 rfl)
  else isFalse (by intro h; cases h; exact h1 rfl)

instance : DecidableEq (Msg Nat natTopo) := fun a b =>
  match a, b with
  | .requestVote t1 c1 v1 i1 lt1, .requestVote t2 c2 v2 i2 lt2 =>
    if h : t1 = t2 ∧ c1 = c2 ∧ v1 = v2 ∧ i1 = i2 ∧ lt1 = lt2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | .voteReply t1 f1 to1 g1, .voteReply t2 f2 to2 g2 =>
    if h : t1 = t2 ∧ f1 = f2 ∧ to1 = to2 ∧ g1 = g2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl)
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl⟩)
  | .appendEntries t1 l1 pi1 pt1 es1 lc1, .appendEntries t2 l2 pi2 pt2 es2 lc2 =>
    if h : t1 = t2 ∧ l1 = l2 ∧ pi1 = pi2 ∧ pt1 = pt2 ∧ es1 = es2 ∧ lc1 = lc2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | .appendReply t1 f1 to1 s1 m1, .appendReply t2 f2 to2 s2 m2 =>
    if h : t1 = t2 ∧ f1 = f2 ∧ to1 = to2 ∧ s1 = s2 ∧ m1 = m2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | .installSnapshot t1 l1 si1 st1 ss1, .installSnapshot t2 l2 si2 st2 ss2 =>
    if h : t1 = t2 ∧ l1 = l2 ∧ si1 = si2 ∧ st1 = st2 ∧ ss1 = ss2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl, rfl⟩)
  | .requestVote .., .voteReply .. | .requestVote .., .appendEntries ..
  | .requestVote .., .appendReply .. | .requestVote .., .installSnapshot ..
  | .voteReply .., .requestVote .. | .voteReply .., .appendEntries ..
  | .voteReply .., .appendReply .. | .voteReply .., .installSnapshot ..
  | .appendEntries .., .requestVote .. | .appendEntries .., .voteReply ..
  | .appendEntries .., .appendReply .. | .appendEntries .., .installSnapshot ..
  | .appendReply .., .requestVote .. | .appendReply .., .voteReply ..
  | .appendReply .., .appendEntries .. | .appendReply .., .installSnapshot ..
  | .installSnapshot .., .requestVote .. | .installSnapshot .., .voteReply ..
  | .installSnapshot .., .appendEntries .. | .installSnapshot .., .appendReply .. =>
    isFalse (by intro h; cases h)

def validCmdB (boot : Nat) (S : ClusterState natTopo) : Cmd Nat Nat → Bool
  | .noop => !S.voters.isEmpty
  | .bootstrapJoin n => n == boot && S.members.isEmpty && S.voters.isEmpty
  | .joinLearner n => !S.voters.isEmpty && !(n ∈ S.members)
  | .forgetLearner n => decide (n ∈ S.members) && !(n ∈ S.voters)
  | .addVoter n => decide (n ∈ S.members) && !(n ∈ S.voters)
  | .delVoter n => decide (n ∈ S.voters) && decide (S.voters.length > 1)
  | .topo _ => !S.voters.isEmpty

theorem validCmdB_sound {boot : Nat} {S : ClusterState natTopo} {c : Cmd Nat Nat}
    (h : validCmdB boot S c = true) : validCmd boot S c := by
  cases c <;> simp [validCmdB, validCmd, natTopo] at h ⊢
  · exact h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact ⟨h.1, h.2⟩
  · exact ⟨h.1, h.2⟩
  · exact ⟨h.1, h.2⟩
  · exact ⟨h.1, h.2⟩
  · exact h

/-! ## Executable trace interpreter (kernel-verified soundness!) -/

inductive Act where
  | bootstrap
  | propose (l : Nat) (cmd : Cmd Nat Nat)
  | proposeNoSerial (l : Nat) (cmd : Cmd Nat Nat)
  | proposeNoOwnTerm (l : Nat) (cmd : Cmd Nat Nat)
  | startElect (c : Nat)
  | handleRV (v c t cIdx cTerm : Nat)
  | handleVR (c fromId t : Nat)
  | becomeLeader (c : Nat)
  | sendAE (l prevIdx endIdx : Nat)
  | handleAE (f l t prevIdx prevTerm leaderCommit : Nat) (entries : List (Entry Nat Nat))
  | handleAER (l fromId t mIdx : Nat)
  | advanceCommit (l k : Nat)

/-- Check and execute a single action under `StepNoSerial` (mode = 0) or
`StepNoOwnTerm` (mode = 1). -/
def execAct (mode : Nat) (s : System Nat natTopo) : Act → Option (System Nat natTopo)
  | .bootstrap =>
    if (s.nodes 0).term == 0 && (s.nodes 0).snapIdx == 0 && (s.nodes 0).tail.isEmpty
    then some (nextBootstrap 0 s) else none
  | .propose l cmd =>
    if (s.nodes l).role == .leader && validCmdB 0 (s.nodes l).projectedState cmd &&
       (!cmd.isVoterChange || ((s.nodes l).hasUncommittedVoterChange == false &&
         (s.nodes l).commit > 0 && (s.nodes l).termAt (s.nodes l).commit == (s.nodes l).term))
    then some (nextPropose s l cmd) else none
  | .proposeNoSerial l cmd =>
    if mode == 0 && (s.nodes l).role == .leader && validCmdB 0 (s.nodes l).projectedState cmd &&
       (!cmd.isVoterChange || ((s.nodes l).commit > 0 &&
         (s.nodes l).termAt (s.nodes l).commit == (s.nodes l).term))
    then some (nextPropose s l cmd) else none
  | .proposeNoOwnTerm l cmd =>
    if mode == 1 && (s.nodes l).role == .leader && validCmdB 0 (s.nodes l).projectedState cmd &&
       (!cmd.isVoterChange || (s.nodes l).hasUncommittedVoterChange == false)
    then some (nextPropose s l cmd) else none
  | .startElect c =>
    if c ∈ (s.nodes c).effVoters then some (nextStartElection s c) else none
  | .handleRV v c t cIdx cTerm =>
    if Msg.requestVote t c v cIdx cTerm ∈ s.net && decide (t ≥ (s.nodes v).term)
    then some (nextHandleRequestVote s v c t cIdx cTerm) else none
  | .handleVR c fromId t =>
    if Msg.voteReply t fromId c true ∈ s.net &&
       (s.nodes c).role == .candidate && (s.nodes c).term == t
    then some (nextHandleVoteReply s c fromId) else none
  | .becomeLeader c =>
    let vs := (s.nodes c).effVoters
    if (s.nodes c).role == .candidate &&
       decide ((vs.filter (fun v => decide (v ∈ (s.nodes c).votes))).length ≥ vs.length / 2 + 1)
    then some (nextBecomeLeader s c) else none
  | .sendAE l prevIdx endIdx =>
    if (s.nodes l).role == .leader &&
       decide ((s.nodes l).snapIdx ≤ prevIdx ∧ prevIdx ≤ endIdx ∧ endIdx ≤ (s.nodes l).lastIdx)
    then some (nextSendAppendEntries s l prevIdx endIdx) else none
  | .handleAE f l t prevIdx prevTerm leaderCommit entries =>
    if Msg.appendEntries t l prevIdx prevTerm entries leaderCommit ∈ s.net &&
       decide (t > (s.nodes f).term ∨ (t = (s.nodes f).term ∧ (s.nodes f).role ≠ .leader))
    then some (nextHandleAppendEntries s f l t prevIdx prevTerm leaderCommit entries) else none
  | .handleAER l fromId t mIdx =>
    if Msg.appendReply t fromId l true mIdx ∈ s.net &&
       (s.nodes l).role == .leader && (s.nodes l).term == t
    then some (nextHandleAppendReply s l fromId mIdx) else none
  | .advanceCommit l k =>
    let vs := (s.nodes l).effVoters
    if (s.nodes l).role == .leader &&
       decide ((s.nodes l).commit < k ∧ k ≤ (s.nodes l).lastIdx) &&
       (s.nodes l).termAt k == (s.nodes l).term &&
       decide ((vs.filter (fun v => decide (v = l ∨ (s.nodes l).matchIdx v ≥ k))).length ≥ vs.length / 2 + 1)
    then some (nextAdvanceCommit s l k) else none

def runTrace (mode : Nat) (s : System Nat natTopo) : List Act → Option (System Nat natTopo)
  | [] => some s
  | a :: as =>
    match execAct mode s a with
    | some s' => runTrace mode s' as
    | none => none

private theorem execAct_sound_noSerial {s s' : System Nat natTopo} {a : Act}
    (h : execAct 0 s a = some s') : StepNoSerial 0 s s' := by
  cases a with
  | bootstrap =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
      exact .ofStep (.bootstrapSelfJoin s ⟨hc.1.1, hc.1.2, hc.2⟩)
    · cases h
  | propose l cmd =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
        decide_eq_true_eq] at hc
      refine .ofStep (.propose s l cmd hc.1.1 (validCmdB_sound hc.1.2) ?_)
      intro hvc
      rcases hc.2 with hf | ⟨⟨h1, h2⟩, h3⟩
      · rw [hvc] at hf; exact Bool.noConfusion hf
      · exact ⟨h1, h2, h3⟩
    · cases h
  | proposeNoSerial l cmd =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
        decide_eq_true_eq] at hc
      refine .proposeNoSerial s l cmd hc.1.1.2 (validCmdB_sound hc.1.2) ?_
      intro hvc
      rcases hc.2 with hf | ⟨h1, h2⟩
      · rw [hvc] at hf; cases hf
      · exact ⟨h1, h2⟩
    · cases h
  | proposeNoOwnTerm l cmd =>
    simp [execAct] at h
  | startElect c =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      exact .ofStep (.startElection s c hc)
    · cases h
  | handleRV v c t cIdx cTerm =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact .ofStep (.handleRequestVote s v c t cIdx cTerm hc.1 hc.2)
    · cases h
  | handleVR c fromId t =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact .ofStep (.handleVoteReply s c fromId t hc.1.1 hc.1.2 hc.2)
    · cases h
  | becomeLeader c =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.becomeLeader s c hc.1 hc.2)
    · cases h
  | sendAE l prevIdx endIdx =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.sendAppendEntries s l prevIdx endIdx hc.1 hc.2)
    · cases h
  | handleAE f l t prevIdx prevTerm leaderCommit entries =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact .ofStep (.handleAppendEntries s f l t prevIdx prevTerm leaderCommit entries hc.1 hc.2)
    · cases h
  | handleAER l fromId t mIdx =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact .ofStep (.handleAppendReply s l fromId t mIdx hc.1.1 hc.1.2 hc.2)
    · cases h
  | advanceCommit l k =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.advanceCommit s l k hc.1.1.1 hc.1.1.2 hc.1.2 hc.2)
    · cases h

private theorem execAct_sound_noOwnTerm {s s' : System Nat natTopo} {a : Act}
    (h : execAct 1 s a = some s') : StepNoOwnTerm 0 s s' := by
  cases a with
  | bootstrap =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
      exact .ofStep (.bootstrapSelfJoin s ⟨hc.1.1, hc.1.2, hc.2⟩)
    · cases h
  | propose l cmd =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
        decide_eq_true_eq] at hc
      refine .ofStep (.propose s l cmd hc.1.1 (validCmdB_sound hc.1.2) ?_)
      intro hvc
      rcases hc.2 with hf | ⟨⟨h1, h2⟩, h3⟩
      · rw [hvc] at hf; exact Bool.noConfusion hf
      · exact ⟨h1, h2, h3⟩
    · cases h
  | proposeNoSerial l cmd =>
    simp [execAct] at h
  | proposeNoOwnTerm l cmd =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      refine .proposeNoOwnTerm s l cmd hc.1.1.2 (validCmdB_sound hc.1.2) ?_
      intro hvc
      rcases hc.2 with hf | h1
      · rw [hvc] at hf; exact Bool.noConfusion hf
      · exact h1
    · cases h
  | startElect c =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      exact .ofStep (.startElection s c hc)
    · cases h
  | handleRV v c t cIdx cTerm =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact .ofStep (.handleRequestVote s v c t cIdx cTerm hc.1 hc.2)
    · cases h
  | handleVR c fromId t =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact .ofStep (.handleVoteReply s c fromId t hc.1.1 hc.1.2 hc.2)
    · cases h
  | becomeLeader c =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.becomeLeader s c hc.1 hc.2)
    · cases h
  | sendAE l prevIdx endIdx =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.sendAppendEntries s l prevIdx endIdx hc.1 hc.2)
    · cases h
  | handleAE f l t prevIdx prevTerm leaderCommit entries =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact .ofStep (.handleAppendEntries s f l t prevIdx prevTerm leaderCommit entries hc.1 hc.2)
    · cases h
  | handleAER l fromId t mIdx =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact .ofStep (.handleAppendReply s l fromId t mIdx hc.1.1 hc.1.2 hc.2)
    · cases h
  | advanceCommit l k =>
    simp only [execAct] at h
    split at h
    · rename_i hc; injection h with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .ofStep (.advanceCommit s l k hc.1.1.1 hc.1.1.2 hc.1.2 hc.2)
    · cases h

private theorem runTrace_sound_noSerial {s s' : System Nat natTopo} {tr : List Act}
    (hr : ReachNoSerial 0 s) (h : runTrace 0 s tr = some s') : ReachNoSerial 0 s' := by
  induction tr generalizing s with
  | nil => simp [runTrace] at h; subst h; exact hr
  | cons a as ih =>
    simp only [runTrace] at h
    cases hex : execAct 0 s a with
    | none => rw [hex] at h; cases h
    | some s1 =>
      rw [hex] at h
      exact ih (.step hr (execAct_sound_noSerial hex)) h

private theorem runTrace_sound_noOwnTerm {s s' : System Nat natTopo} {tr : List Act}
    (hr : ReachNoOwnTerm 0 s) (h : runTrace 1 s tr = some s') : ReachNoOwnTerm 0 s' := by
  induction tr generalizing s with
  | nil => simp [runTrace] at h; subst h; exact hr
  | cons a as ih =>
    simp only [runTrace] at h
    cases hex : execAct 1 s a with
    | none => rw [hex] at h; cases h
    | some s1 =>
      rw [hex] at h
      exact ih (.step hr (execAct_sound_noOwnTerm hex)) h

/-- Check if the head commit and head election of `s` violate Leader Completeness. -/
def hasLeaderCompletenessViolation (s : System Nat natTopo) : Bool :=
  match s.hist.commits.head?, s.hist.elected.head? with
  | some cm, some er =>
    decide (cm.term < er.term) && (decide (er.elecLog.length < cm.log.length) ||
      (er.elecLog.take cm.log.length != cm.log))
  | _, _ => false

theorem violation_of_bool {s : System Nat natTopo}
    (h : hasLeaderCompletenessViolation s = true) :
    ∃ cm ∈ s.hist.commits, ∃ er ∈ s.hist.elected,
      cm.term < er.term ∧ ¬ IsPrefix cm.log er.elecLog := by
  unfold hasLeaderCompletenessViolation at h
  cases hc : s.hist.commits with
  | nil => simp [hc] at h
  | cons cm cms =>
    cases he : s.hist.elected with
    | nil => simp [hc, he] at h
    | cons er ers =>
      simp only [hc, he, List.head?_cons, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, bne_iff_ne] at h
      refine ⟨cm, by simp, er, by simp, h.1, ?_⟩
      intro hpre
      rcases h.2 with hlt | hne
      · have := hpre.1; omega
      · exact hne hpre.2

/-! ## Counterexample 1: Dropping serialization (gap A2) breaks Leader Completeness -/

def es6_a2 : List (Entry Nat Nat) :=
  [ { term := 1, cmd := .bootstrapJoin 0 },
    { term := 1, cmd := .joinLearner 1 },
    { term := 1, cmd := .joinLearner 2 },
    { term := 1, cmd := .joinLearner 3 },
    { term := 1, cmd := .joinLearner 4 },
    { term := 1, cmd := .addVoter 1 } ]

def es7_a2 : List (Entry Nat Nat) := es6_a2 ++ [{ term := 1, cmd := .addVoter 2 }]

def es10_a2 : List (Entry Nat Nat) :=
  es7_a2 ++ [{ term := 1, cmd := .addVoter 3 }, { term := 1, cmd := .addVoter 4 }, { term := 1, cmd := .topo 99 }]

def traceA2 : List Act :=
  [ .bootstrap,
    .advanceCommit 0 1,
    .propose 0 (.joinLearner 1),
    .propose 0 (.joinLearner 2),
    .propose 0 (.joinLearner 3),
    .propose 0 (.joinLearner 4),
    .propose 0 (.addVoter 1),
    .sendAE 0 0 6,
    .handleAE 1 0 1 0 0 1 es6_a2,
    .handleAER 0 1 1 6,
    .advanceCommit 0 6,
    .propose 0 (.addVoter 2),
    .sendAE 0 0 7,
    .handleAE 1 0 1 0 0 6 es7_a2,
    .handleAE 2 0 1 0 0 6 es7_a2,
    .handleAER 0 1 1 7,
    .advanceCommit 0 7,
    -- Pipeline ADD_VOTER(3) and ADD_VOTER(4) without committing ADD_VOTER(3):
    .propose 0 (.addVoter 3),
    .proposeNoSerial 0 (.addVoter 4),
    .propose 0 (.topo 99),
    .sendAE 0 0 10,
    .handleAE 3 0 1 0 0 7 es10_a2,
    .handleAE 4 0 1 0 0 7 es10_a2,
    .handleAER 0 3 1 10,
    .handleAER 0 4 1 10,
    .advanceCommit 0 10,
    -- Node 1 (still on {0,1,2}) wins term 2 with {1,2}, losing committed `topo 99`!
    .startElect 1,
    .handleRV 2 1 2 7 1,
    .handleVR 1 2 2,
    .becomeLeader 1 ]

/-- Dropping the serialization guard (gap A2) makes a Leader Completeness
violation reachable under config-on-append (even with own-term-commit-first). -/
theorem counterexample_a2_no_serialization :
    ∃ s : System Nat natTopo,
      ReachNoSerial 0 s ∧
      ∃ cm ∈ s.hist.commits,
        ∃ er ∈ s.hist.elected,
          cm.term < er.term ∧ ¬ IsPrefix cm.log er.elecLog := by
  have hok : ((runTrace 0 (System.init natTopo) traceA2).map hasLeaderCompletenessViolation) = some true := rfl
  cases hrun : runTrace 0 (System.init natTopo) traceA2 with
  | none => rw [hrun] at hok; cases hok
  | some s =>
    rw [hrun] at hok; injection hok with hv
    exact ⟨s, runTrace_sound_noSerial .init hrun, violation_of_bool hv⟩

/-! ## Counterexample 2: Dropping own-term-commit-first (Ongaro 2015) -/

def es5_ong : List (Entry Nat Nat) :=
  [ { term := 1, cmd := .bootstrapJoin 0 },
    { term := 1, cmd := .joinLearner 1 },
    { term := 1, cmd := .joinLearner 2 },
    { term := 1, cmd := .joinLearner 3 },
    { term := 1, cmd := .addVoter 1 } ]

def es6_ong : List (Entry Nat Nat) := es5_ong ++ [{ term := 1, cmd := .addVoter 2 }]
def es7_ong : List (Entry Nat Nat) := es6_ong ++ [{ term := 1, cmd := .addVoter 3 }]

def traceOngaro2015 : List Act :=
  [ .bootstrap,
    .advanceCommit 0 1,
    .propose 0 (.joinLearner 1),
    .propose 0 (.joinLearner 2),
    .propose 0 (.joinLearner 3),
    .propose 0 (.addVoter 1),
    .sendAE 0 0 5,
    .handleAE 1 0 1 0 0 1 es5_ong,
    .handleAER 0 1 1 5,
    .advanceCommit 0 5,
    .propose 0 (.addVoter 2),
    .sendAE 0 0 6,
    .handleAE 1 0 1 0 0 5 es6_ong,
    .handleAER 0 1 1 6,
    .advanceCommit 0 6,
    .propose 0 (.addVoter 3),
    .sendAE 0 0 7,
    .handleAE 1 0 1 0 0 6 es7_ong,
    .handleAE 2 0 1 0 0 6 es7_ong,
    .handleAE 3 0 1 0 0 6 es7_ong,
    .handleAER 0 1 1 7,
    .handleAER 0 2 1 7,
    .advanceCommit 0 7,
    -- Deliver commit=7 to node 3 via heartbeat:
    .sendAE 0 7 7,
    .handleAE 3 0 1 7 1 7 [],
    -- Term 2: node 0 wins with {0,1,2} and appends DEL_VOTER(3) without own-term commit:
    .startElect 0,
    .handleRV 1 0 2 7 1,
    .handleRV 2 0 2 7 1,
    .handleVR 0 1 2,
    .handleVR 0 2 2,
    .becomeLeader 0,
    .proposeNoOwnTerm 0 (.delVoter 3),
    -- Term 3: node 3 wins with {1,2,3}, appends DEL_VOTER(0) without own-term commit,
    -- replicates to node 2, and COMMITS DEL_VOTER(0) with {2,3}!
    .startElect 3,
    .startElect 3,
    .handleRV 1 3 3 7 1,
    .handleRV 2 3 3 7 1,
    .handleVR 3 1 3,
    .handleVR 3 2 3,
    .becomeLeader 3,
    .proposeNoOwnTerm 3 (.delVoter 0),
    .sendAE 3 7 8,
    .handleAE 2 3 3 7 1 7 [{ term := 3, cmd := .delVoter 0 }],
    .handleAER 3 2 3 8,
    .advanceCommit 3 8,
    -- Term 4: node 0 (still on {0,1,2} with t2 at idx 8) wins with {0,1},
    -- losing committed DEL_VOTER(0)!
    .startElect 0,
    .startElect 0,
    .handleRV 1 0 4 8 2,
    .handleVR 0 1 4,
    .becomeLeader 0 ]

/-- Dropping the own-term-commit-first guard (Ongaro 2015) makes a Leader
Completeness violation reachable even WITH serialization and config-on-append. -/
theorem counterexample_ongaro_2015_no_own_term_guard :
    ∃ s : System Nat natTopo,
      ReachNoOwnTerm 0 s ∧
      ∃ cm ∈ s.hist.commits,
        ∃ er ∈ s.hist.elected,
          cm.term < er.term ∧ ¬ IsPrefix cm.log er.elecLog := by
  have hok : ((runTrace 1 (System.init natTopo) traceOngaro2015).map hasLeaderCompletenessViolation) = some true := rfl
  cases hrun : runTrace 1 (System.init natTopo) traceOngaro2015 with
  | none => rw [hrun] at hok; cases hok
  | some s =>
    rw [hrun] at hok; injection hok with hv
    exact ⟨s, runTrace_sound_noOwnTerm .init hrun, violation_of_bool hv⟩

/-! ## Counterexample 3: Impure `DEL_VOTER` reading `rs->leader` diverges -/

/-- Impure `DEL_VOTER` apply modelling `cluster_raft.c:3643`, where `delVoter n`
is silently skipped (turned into a no-op) if `n == localLeader`. -/
def applyImpureDelVoter (localLeader : Nat) (S : ClusterState natTopo) :
    Cmd Nat Nat → ClusterState natTopo
  | .delVoter n => if n = localLeader then S else applyCmd S (.delVoter n)
  | c => applyCmd S c

def foldImpure (localLeader : Nat) (L : List (Entry Nat Nat)) : ClusterState natTopo :=
  L.foldl (fun s e => applyImpureDelVoter localLeader s e.cmd) (ClusterState.empty natTopo)

def log3WithDelVoter1 : List (Entry Nat Nat) :=
  [ { term := 1, cmd := .bootstrapJoin 0 },
    { term := 1, cmd := .joinLearner 1 },
    { term := 1, cmd := .joinLearner 2 },
    { term := 1, cmd := .addVoter 1 },
    { term := 1, cmd := .addVoter 2 },
    { term := 1, cmd := .delVoter 1 } ]

/-- On the exact same valid log `log3WithDelVoter1`, pure `applyCmd` produces
voters `[0, 2]` (size 2), whereas `applyImpureDelVoter` diverges permanently
between a node with `rs->leader = 1` (voters `[0, 1, 2]`, size 3 — silent no-op)
and a node with `rs->leader = 0` (voters `[0, 2]`, size 2). -/
theorem counterexample_del_voter_impure_divergence :
    LogValid (T := natTopo) 0 log3WithDelVoter1 ∧
    (stateOfLog (T := natTopo) log3WithDelVoter1).voters = [0, 2] ∧
    (foldImpure 1 log3WithDelVoter1).voters = [0, 1, 2] ∧
    (foldImpure 0 log3WithDelVoter1).voters = [0, 2] ∧
    (foldImpure 1 log3WithDelVoter1).voters ≠ (foldImpure 0 log3WithDelVoter1).voters := by
  refine ⟨?_, rfl, rfl, rfl, by decide⟩
  intro k e h1 h2 hg
  have hlt : k ≤ 6 := h2
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp [log3WithDelVoter1, logGet] at hg
    subst hg
    exact validCmdB_sound (by decide)

end ValkeyRaft.ConfigOnAppend.Counterexamples

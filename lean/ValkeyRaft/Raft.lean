/-
  Executable model of the Raft log layer of cluster-v2 (src/cluster_raft.c @
  f278b08b, valkey-io/valkey `cluster-v2` branch).

  The model is deliberately close to the C code so that counterexamples map to
  real code paths. Each behaviour that differs from textbook Raft is behind an
  `Opts` flag whose default is the *current code* behaviour:

  | flag                 | code (default)                                  | Raft paper                         |
  |----------------------|-------------------------------------------------|------------------------------------|
  | ackLastIndex         | AE_ACK reports raftLogLastIndex(); leader sets  | matchIndex = prevLogIndex+#entries |
  |                      | match_index to it (cluster_raft.c:1825)         |                                    |
  | followerCommitLast   | commit = min(leaderCommit, raftLogLastIndex())  | min(leaderCommit, last new entry)  |
  |                      | (cluster_raft.c:1768)                           |                                    |
  | configOnAppend=false | quorum = applied `size` (config-on-apply)       | config-on-append (§4.1)            |
  | oneConfigInFlight    | not enforced (#4392 proposes it)                | —                                  |
  | persistSnapTerm=false| restart keeps only log tail > lastApplied, and  | snapshot keeps lastIncluded{Index, |
  |                      | raftLogLastIndex/Term() return 0 for empty log  | Term} (§7)                         |

  Atomicity simplifications (all *under*-approximate behaviours, so any
  violation found is real for the code, but "no violation found" is only a
  bounded result):
  * AE + AE_ACK delivery is one atomic step (no reordering / duplication).
  * The leader's next_index search is collapsed to its fixpoint.
  * An election contacts every live node atomically and only succeeds steps
    are explored (failed elections are not explored).
  * fsync is instantaneous.
-/
import Std.Data.HashSet

namespace ValkeyRaft.Raft

inductive Cmd where
  | data (k : Nat)
  | addVoter (n : Nat)
  deriving BEq, DecidableEq, Hashable, Repr

structure Entry where
  idx : Nat
  term : Nat
  cmd : Cmd
  deriving BEq, DecidableEq, Hashable, Repr

structure Node where
  alive : Bool := true
  term : Nat := 1
  votedFor : Option Nat := none
  leader : Bool := false
  log : List Entry := []
  snapIdx : Nat := 0
  snapTerm : Nat := 0
  snapVoters : List Nat := []
  commit : Nat := 0
  applied : Nat := 0
  voters : List Nat := []        -- applied configuration (`size` = length)
  matchIdx : List Nat := []      -- leader only, indexed by node id
  deriving BEq, DecidableEq, Hashable, Repr

structure Opts where
  ackLastIndex : Bool := true
  followerCommitLast : Bool := true
  configOnAppend : Bool := false
  oneConfigInFlight : Bool := false
  persistSnapTerm : Bool := false
  installSnapshot : Bool := false    -- #3858 (not implemented in code)
  maxData : Nat := 1
  maxConfig : Nat := 0
  maxCrash : Nat := 1
  maxRestart : Nat := 0
  maxElect : Nat := 1
  learners : List Nat := []      -- nodes that may be promoted by ADD_VOTER
  deriving Repr

structure State where
  nodes : List Node
  ghost : List Entry := []       -- every entry some leader declared committed
  bad : Option String := none
  nData : Nat := 0
  nConfig : Nat := 0
  nCrash : Nat := 0
  nRestart : Nat := 0
  nElect : Nat := 0
  deriving BEq, DecidableEq, Hashable, Repr

inductive Act where
  | data (l : Nat)
  | addV (l n : Nat)
  | repl (l f : Nat)
  | elect (c : Nat)
  | crash (n : Nat)
  | restart (n : Nat)
  deriving BEq, DecidableEq, Hashable, Repr

/-! ### Log helpers (code semantics) -/

def get (n : Node) (i : Nat) : Option Entry := n.log.find? (·.idx == i)

def lastIdx (o : Opts) (n : Node) : Nat :=
  match n.log.getLast? with
  | some e => e.idx
  | none => if o.persistSnapTerm then n.snapIdx else 0

def lastTerm (o : Opts) (n : Node) : Nat :=
  match n.log.getLast? with
  | some e => e.term
  | none => if o.persistSnapTerm then n.snapTerm else 0

def termAt (o : Opts) (n : Node) (i : Nat) : Nat :=
  if i == 0 then 0 else
  match get n i with
  | some e => e.term
  | none => if o.persistSnapTerm && i == n.snapIdx then n.snapTerm else 0

def applyCfg (vs : List Nat) (e : Entry) : List Nat :=
  match e.cmd with
  | .addVoter m => if vs.contains m then vs else vs ++ [m]
  | _ => vs

def effVoters (o : Opts) (n : Node) : List Nat :=
  if o.configOnAppend then (n.log.filter (·.idx > n.applied)).foldl applyCfg n.voters
  else n.voters

def quorum (vs : List Nat) : Nat := vs.length / 2 + 1

def setAt {α} (l : List α) (i : Nat) (x : α) : List α := l.set i x
def at! (s : State) (i : Nat) : Node := s.nodes.getD i {}

/-! ### Apply loop with State-Machine-Safety check -/

def applyLoop (ghost : List Entry) : Nat → Node → Node × Option String
  | 0, n => (n, none)
  | fuel + 1, n =>
    if n.applied < n.commit then
      let a := n.applied + 1
      match get n a with
      | some e =>
        let bad := ghost.find? (fun g => g.idx == a && g != e)
        let n' := { n with applied := a, voters := applyCfg n.voters e }
        match bad with
        | some g => (n', some s!"state-machine safety: applied {repr e} at index {a}, but {repr g} was committed there")
        | none => applyLoop ghost fuel n'
      | none =>
        -- code: `if (e) raftLogApply(e);` silently skips a missing entry
        let n' := { n with applied := a }
        match ghost.find? (·.idx == a) with
        | some g => (n', some s!"committed entry {repr g} skipped: index {a} applied without an entry")
        | none => applyLoop ghost fuel n'
    else (n, none)

def applyNode (s : State) (i : Nat) : State :=
  let n := at! s i
  let (n', b) := applyLoop s.ghost (n.commit - n.applied + 1) n
  { s with nodes := setAt s.nodes i n', bad := s.bad <|> b }

/-! ### Leader commit advancement (cluster_raft.c:1829-1850) -/

/-- Log Matching: once the leader commits index `newC`, *every* entry in its
log at an index ≤ newC is committed (including entries re-appended at indices
the leader had already counted as committed, e.g. after a full restart). -/
def recordCommitted (s : State) (l : Nat) (_oldC newC : Nat) : State :=
  let n := at! s l
  (n.log.filter (·.idx ≤ newC)).foldl (fun s e =>
    match s.ghost.find? (·.idx == e.idx) with
    | some g => if g == e then s else
        { s with bad := s.bad <|> some s!"two different entries committed at index {e.idx}: {repr g} then {repr e}" }
    | none => { s with ghost := s.ghost ++ [e] }) s

def advance (o : Opts) (s : State) (l : Nat) : State :=
  let n := at! s l
  let vs := effVoters o n
  let q := quorum vs
  let cands := (n.log.filter (fun e => e.idx > n.commit && e.term == n.term)).reverse
  let ok := cands.find? (fun e =>
    let peers := vs.filter (fun v => v != l && n.matchIdx.getD v 0 ≥ e.idx)
    1 + peers.length ≥ q)       -- code always counts the leader itself
  match ok with
  | none => s
  | some e =>
    let s := recordCommitted s l n.commit e.idx
    let s := { s with nodes := setAt s.nodes l { n with commit := e.idx } }
    applyNode s l

/-! ### AppendEntries + ACK, atomically -/

def mergeEntry (o : Opts) (f : Node) (e : Entry) : Node :=
  match get f e.idx with
  | some ex =>
    if ex.term != e.term then { f with log := f.log.filter (·.idx < e.idx) ++ [e] } else f
  | none => { f with log := f.log ++ [e] }

/-- Fixpoint of the leader's next_index decrement loop. Code semantics: the
consistency check compares `raftLogTermAt()` values, which are 0 for indices
neither side holds, so two nodes that both lack index p "match" at p. With
`installSnapshot` the leader never probes below its own log start. -/
def matchPoint (o : Opts) (ld f : Node) : Nat :=
  let top := lastIdx o ld
  let ps := (List.range (top + 1)).reverse
  let known (p : Nat) := !o.installSnapshot || p ≥ ld.snapIdx
  (ps.find? (fun p => known p && (p == 0 || termAt o f p == termAt o ld p))).getD 0

def sentEntries (o : Opts) (ld : Node) (p : Nat) : List Entry :=
  let top := lastIdx o ld
  let rec go : Nat → Nat → List Entry
    | 0, _ => []
    | fuel + 1, i => if i > top then [] else
        match get ld i with
        | some e => e :: go fuel (i + 1)
        | none => []
  go (top + 1) (p + 1)

def replicate (o : Opts) (s : State) (l f : Nat) : Option State :=
  let ld := at! s l
  let fo := at! s f
  if l == f || !ld.alive || !fo.alive || !ld.leader || ld.term < fo.term then none else
  let p0 := matchPoint o ld fo
  -- InstallSnapshot (#3858): leader's log no longer reaches back far enough
  let needSnap := o.installSnapshot && ld.snapIdx > 0 && p0 < ld.snapIdx
  let fo := if needSnap then
      { fo with log := [], snapIdx := ld.snapIdx, snapTerm := ld.snapTerm,
                applied := max fo.applied ld.snapIdx, commit := max fo.commit ld.snapIdx,
                voters := if fo.applied < ld.snapIdx then ld.snapVoters else fo.voters }
    else fo
  let p := if needSnap then ld.snapIdx else p0
  let es := sentEntries o ld p
  let f1 := es.foldl (mergeEntry o) fo
  let f1 := { f1 with
    term := ld.term, leader := false,
    votedFor := if fo.term < ld.term then none else fo.votedFor }
  let verified := p + es.length
  let newC := if ld.commit > f1.commit then
      (if o.followerCommitLast then min ld.commit (lastIdx o f1) else min ld.commit verified)
    else f1.commit
  let f1 := { f1 with commit := max f1.commit newC }
  let s := { s with nodes := setAt s.nodes f f1 }
  let s := applyNode s f
  let f2 := at! s f
  let m := if o.ackLastIndex then lastIdx o f2 else verified
  let ld := at! s l
  let s := { s with nodes := setAt s.nodes l { ld with matchIdx := setAt ld.matchIdx f m } }
  some (advance o s l)

/-! ### Elections (atomic pre-vote + vote) -/

def upToDate (o : Opts) (c v : Node) : Bool :=
  lastTerm o c > lastTerm o v || (lastTerm o c == lastTerm o v && lastIdx o c ≥ lastIdx o v)

def elect (o : Opts) (s : State) (c : Nat) : Option State :=
  let cn := at! s c
  if !cn.alive || cn.leader || !(effVoters o cn).contains c then none else
  let t := cn.term + 1
  let n := s.nodes.length
  let grants := (List.range n).filter (fun v =>
    let vn := at! s v
    v != c && vn.alive && (effVoters o cn).contains v &&
    (effVoters o vn).contains v &&             -- learners deny (nodeIsLearner(myself))
    (effVoters o vn).contains c &&             -- candidate must not be a learner in voter's view
    vn.term < t && upToDate o cn vn)
  if 1 + grants.length < quorum (effVoters o cn) then none else
  -- every live node sees the higher term and steps down (MaybeStepDown)
  let nodes := (List.range n).map (fun v =>
    let vn := at! s v
    if v == c then { vn with term := t, votedFor := some c, leader := true,
                              matchIdx := List.replicate n 0 }
    else if vn.alive && vn.term < t then
      { vn with term := t, leader := false,
                votedFor := if grants.contains v then some c else none }
    else vn)
  let s := { s with nodes := nodes }
  -- Leader completeness diagnostic: new leader must hold every committed entry
  -- it has not already applied.
  let ld := at! s c
  let missing := s.ghost.find? (fun g => g.idx > ld.applied && get ld g.idx != some g)
  match missing with
  | some g => some { s with bad := s.bad <|> some s!"leader completeness: node {c} elected in term {t} without committed {repr g}" }
  | none => some s

/-! ### Restart from nodes.conf -/

def restart (o : Opts) (s : State) (i : Nat) : Option State :=
  let n := at! s i
  if !n.alive then none else
  let n' := { n with
    leader := false,
    log := n.log.filter (·.idx > n.applied),   -- clusterRaftAppendLogLines
    commit := n.applied,                        -- parseVarsLine
    snapIdx := n.applied,
    snapTerm := termAt o n n.applied,           -- only used if persistSnapTerm
    snapVoters := n.voters,
    matchIdx := [] }
  some { s with nodes := setAt s.nodes i n' }

/-! ### Step relation -/

def step (o : Opts) (s : State) : Act → Option State
  | .data l =>
    let n := at! s l
    if !n.leader || !n.alive || s.nData ≥ o.maxData then none else
    let e : Entry := { idx := lastIdx o n + 1, term := n.term, cmd := .data s.nData }
    some { s with nodes := setAt s.nodes l { n with log := n.log ++ [e] }, nData := s.nData + 1 }
  | .addV l m =>
    let n := at! s l
    if !n.leader || !n.alive || s.nConfig ≥ o.maxConfig || (effVoters o n).contains m then none else
    if n.log.any (fun e => e.cmd == .addVoter m && e.idx > n.applied) then none else
    if o.oneConfigInFlight && n.log.any (fun e => e.idx > n.commit &&
        match e.cmd with | .addVoter _ => true | _ => false) then none else
    let e : Entry := { idx := lastIdx o n + 1, term := n.term, cmd := .addVoter m }
    some { s with nodes := setAt s.nodes l { n with log := n.log ++ [e] }, nConfig := s.nConfig + 1 }
  | .repl l f => replicate o s l f
  | .elect c => if s.nElect ≥ o.maxElect then none else
      (elect o s c).map (fun s => { s with nElect := s.nElect + 1 })
  | .crash i =>
    let n := at! s i
    if !n.alive || s.nCrash ≥ o.maxCrash then none else
    some { s with nodes := setAt s.nodes i { n with alive := false }, nCrash := s.nCrash + 1 }
  | .restart i => if s.nRestart ≥ o.maxRestart then none else
      (restart o s i).map (fun s => { s with nRestart := s.nRestart + 1 })

def actions (o : Opts) (s : State) : List Act :=
  let n := s.nodes.length
  let ids := List.range n
  let leaders := ids.filter (fun i => (at! s i).leader && (at! s i).alive)
  leaders.map .data ++
  leaders.flatMap (fun l => o.learners.map (fun m => Act.addV l m)) ++
  leaders.flatMap (fun l => ids.map (fun f => Act.repl l f)) ++
  ids.map .elect ++ ids.map .crash ++ ids.map .restart

/-- Replay a trace. `none` if some step is not enabled; otherwise the final
state (stopping early at the first safety violation). -/
def replay (o : Opts) (s : State) : List Act → Option State
  | [] => some s
  | a :: as =>
    match step o s a with
    | some s' => if s'.bad.isSome then some s' else replay o s' as
    | none => none

/-- The trace is executable and ends in a safety violation. -/
def violates (o : Opts) (s : State) (tr : List Act) : Bool :=
  match replay o s tr with
  | some s' => s'.bad.isSome
  | none => false

/-- Initial state: `n` nodes, voters `vs`, node 0 leader of term 1. -/
def init (n : Nat) (vs : List Nat) : State :=
  { nodes := (List.range n).map (fun i =>
      { voters := vs, leader := i == 0, votedFor := some 0,
        matchIdx := List.replicate n 0 }) }

/-! ### Bounded exhaustive search -/

partial def dfs (o : Opts) (depth : Nat) (s : State) (trace : List Act)
    (seen : IO.Ref (Std.HashSet State)) : IO (Option (List Act × String)) := do
  if let some m := s.bad then return some (trace.reverse, m)
  if depth == 0 then return none
  if (← seen.get).contains s then return none
  seen.modify (·.insert s)
  for a in actions o s do
    if let some s' := step o s a then
      if let some r ← dfs o (depth - 1) s' (a :: trace) seen then return some r
  return none

end ValkeyRaft.Raft

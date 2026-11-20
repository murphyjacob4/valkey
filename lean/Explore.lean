import ValkeyRaft.Raft
open ValkeyRaft.Raft

def runScenario (name : String) (o : Opts) (s0 : State) (depth : Nat) : IO Unit := do
  let seen ← IO.mkRef ({} : Std.HashSet State)
  let t0 ← IO.monoMsNow
  let r ← dfs o depth s0 [] seen
  let t1 ← IO.monoMsNow
  let n := (← seen.get).size
  match r with
  | some (tr, msg) =>
    IO.println s!"[{name}] VIOLATION after {tr.length} steps ({n} states, {t1 - t0} ms)\n  {msg}\n  trace: {repr tr}"
  | none =>
    IO.println s!"[{name}] no violation up to depth {depth} ({n} states, {t1 - t0} ms)"

def main (args : List String) : IO Unit := do
  let only := args.head?
  let want (k : String) := only.isNone || only == some k
  -- S1: static membership, 5 voters: AE_ACK match_index bug
  let s5 := init 5 [0, 1, 2, 3, 4]
  let o1 : Opts := { maxData := 2, maxCrash := 1, maxElect := 2 }
  if want "s1" then runScenario "S1 code: ack=lastIndex, static 5 voters" o1 s5 9
  if want "s1f" then runScenario "S1 fixed: ack=verified index" { o1 with ackLastIndex := false, followerCommitLast := false } s5 9
  -- S2: learner promotion with config-on-apply
  let sL := init 5 [0, 1, 2]
  let o2 : Opts := { ackLastIndex := false, followerCommitLast := false,
                     maxData := 1, maxConfig := 2, maxCrash := 1, maxElect := 1, learners := [3, 4] }
  if want "s2" then runScenario "S2 config-on-apply, pipelined ADD_VOTER" o2 sL 9
  if want "s2a" then runScenario "S2a config-on-apply + one config change in flight (#4392)" { o2 with oneConfigInFlight := true } sL 10
  if want "s2b" then runScenario "S2b config-on-append (#3926)" { o2 with configOnAppend := true } sL 9
  if want "s2c" then runScenario "S2c config-on-append + one change in flight" { o2 with configOnAppend := true, oneConfigInFlight := true } sL 10
  if want "s2a2" then runScenario "S2a2 one-in-flight, 2 elections" { o2 with oneConfigInFlight := true, maxElect := 2 } sL 11
  if want "s2c2" then runScenario "S2c2 config-on-append + one-in-flight, 2 elections" { o2 with configOnAppend := true, oneConfigInFlight := true, maxElect := 2 } sL 11
  -- S3: restart with empty log tail
  let s3 := init 3 [0, 1, 2]
  let o3 : Opts := { ackLastIndex := false, followerCommitLast := false,
                     maxData := 2, maxCrash := 1, maxElect := 2, maxRestart := 1 }
  if want "s3" then runScenario "S3 restart: lastApplied term not persisted" o3 s3 9
  if want "s3f" then runScenario "S3 partial fix: snapshot index/term persisted, no InstallSnapshot" { o3 with persistSnapTerm := true } s3 9
  if want "s3g" then runScenario "S3 full fix: snapshot index/term + InstallSnapshot" { o3 with persistSnapTerm := true, installSnapshot := true } s3 10
  if want "s3h" then runScenario "S3 full fix, 2 restarts, 3 elections" { o3 with persistSnapTerm := true, installSnapshot := true, maxRestart := 2, maxElect := 3 } s3 12

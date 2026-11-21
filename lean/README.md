# valkey_raft — Lean 4 model of Raft cluster bus (valkey-io/valkey#3856)

Lean 4.35.0, core only (no Mathlib).

```
lake build                 # checks every theorem (Quorum, Meta, Traces, Protocols)
lake exe explore           # bounded exhaustive search, all scenarios
lake exe explore s2a2      # a single scenario (see Explore.lean)
```

| File | What |
|------|------|
| `ValkeyRaft/Quorum.lean` | General proofs: majority intersection, single-step config overlap, AZ placement (#3866 #3926 #4392 #4393) |
| `ValkeyRaft/Raft.lean` | Executable log-layer model mirroring `cluster_raft.c` (flags select code vs. Raft-paper behaviour) + DFS explorer |
| `ValkeyRaft/Traces.lean` | Certified counterexample traces found by the explorer (`native_decide`) |
| `ValkeyRaft/Meta.lean` | Apply functions for SLOT_CHANGE / FAILOVER / NODE_FORGET / DEL_VOTER / NODE_FAIL + stale-epoch retry (#3863 #3874 #4069 #4127) |
| `ValkeyRaft/Protocols.lean` | Pre-vote, step-down, shard FD, non-member messages, merge, sync-repl promotion, proposal expiry |
| `ValkeyRaft/ConfigOnAppend/Spec.lean` | Intended state machine: applied (`S_a`) vs projected (`S_p`) state, generic abstract `TopoSpec` (`valid`/`apply` pair), pure total `applyCmd`, config-on-append + serialization + own-term-commit-first, async unordered network, snapshot compaction & `InstallSnapshot`, crash/restart |
| `ValkeyRaft/ConfigOnAppend/LogLemmas.lean` | Pure log, prefix, `stateAt`/`cfgAt`, voter-change serialization, `Node` sync, and `mergeFrom` lemmas |
| `ValkeyRaft/ConfigOnAppend/Invariants.lean` | Full inductive invariant `Inv`, `Inv.init`, `leader_completeness_step`, `election_safety_step`, and prefix-compatibility lemmas |
| `ValkeyRaft/ConfigOnAppend/PreservationBasic.lean` | Inductive preservation proofs for 12 of the 16 transitions |
| `ValkeyRaft/ConfigOnAppend/PreservationCore.lean` | Inductive preservation proofs for `becomeLeader`, `advanceCommit`, `handleAppendEntries`, `handleInstallSnapshot`, `Inv.step`, and `Inv.reachable` |
| `ValkeyRaft/ConfigOnAppend/Safety.lean` | Machine-checked safety theorems (∀ reachable states, ∀ `NodeId`, ∀ `TopoSpec`) covering all contract safety properties |
| `ValkeyRaft/ConfigOnAppend/Counterexamples.lean` | Guard-drop counterexamples (A2 without serialization, Ongaro 2015 without own-term-commit-first, and impure `DEL_VOTER` reading `rs->leader`) — pure kernel proofs, zero `native_decide` |
| `Explore.lean` | Scenario driver for the explorer |

Model source of truth: `cluster-v2` @ f278b08bc335 (2026-08-12) and
`design-docs/cluster-raft.md` on that commit; `ValkeyRaft/ConfigOnAppend/*`
formally proves safety of the intended config-on-append + projected-state design
(see `../README.md` §F for the theorem-to-property mapping and axioms report).

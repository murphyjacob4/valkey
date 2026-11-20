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
| `Explore.lean` | Scenario driver for the explorer |

Model source of truth: `cluster-v2` @ f278b08bc335 (2026-08-12) and
`design-docs/cluster-raft.md` on that commit.

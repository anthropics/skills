---
name: specl
description: >
  Write, debug, and verify Specl specifications for concurrent and distributed systems.
  Specl is a modern TLA+ replacement with clean syntax, implicit frame semantics, and a fast
  Rust model checker. Use when: writing Specl specs (.specl files), modelling distributed
  protocols (Raft, Paxos, 2PC, etc.), debugging invariant violations or deadlocks, translating
  TLA+ to Specl, reviewing formal specifications, or when the user mentions Specl, model checking,
  formal verification, or state space exploration. Keywords: specl, model checking, formal
  verification, TLA+, distributed systems, consensus, invariant, safety, specification language.
license: Complete terms in LICENSE.txt
---

# Specl — Specification Language & Model Checker

Specl is an exhaustive model checker for concurrent and distributed systems. Write a spec (state machine), and the checker explores every reachable state to verify invariants or produce minimal counterexample traces.

GitHub: https://github.com/danwt/specl

## Installation & CLI

```bash
cargo install --path crates/specl-cli    # `specl` binary
cargo install --path crates/specl-lsp    # language server (optional)
```

Key commands:
```bash
specl check spec.specl -c N=3 -c MAX=10    # check with constants
specl check spec.specl --no-deadlock        # skip deadlock check (use for protocols)
specl check spec.specl --fast               # fingerprint-only (10x less memory, no traces)
specl check spec.specl --por                # partial order reduction
specl check spec.specl --symmetry           # symmetry reduction
specl format spec.specl --write             # auto-format
specl watch spec.specl -c N=3              # re-check on save
specl translate spec.tla -o spec.specl     # TLA+ to Specl
```

## Minimal Example

```specl
module Counter
const MAX: 0..10
var count: 0..10
init { count = 0 }
action Inc() { require count < MAX; count = count + 1 }
action Dec() { require count > 0; count = count - 1 }
invariant Bounded { count >= 0 and count <= MAX }
```

`specl check Counter.specl -c MAX=3` explores all 4 states and verifies the invariant.

## Critical Rules

- **`=`** assigns next-state. **`==`** compares. Mixing these up is the #1 mistake.
- Variables not mentioned in an action stay unchanged (implicit frame).
- Use `and` to update multiple variables in one action.
- `require` is a guard. If false, the action is skipped (checker tries other actions).
- The checker explores ALL actions x ALL parameter combinations x ALL reachable states.

## Full Language Reference

For complete syntax, types, operators, dict patterns, quantifiers, functions, modelling patterns,
and common pitfalls, read [references/language.md](references/language.md).

## Modelling Approach

1. **Identify state.** What variables describe the system? For N processes, use `Dict[Int, ...]`.
2. **Identify actions.** What transitions can happen? Use parameters for nondeterminism.
3. **Write guards.** `require` restricts when actions fire.
4. **Write invariants.** Safety properties that must always hold.
5. **Start small.** N=2, small bounds. State spaces grow exponentially.

Common patterns:
- **Process ensemble:** `var state: Dict[Int, Int]` + `action Act(p: 0..N) { state = state | {p: newVal} }`
- **Messages:** `var msgs: Set[Seq[Int]]` — add with `union`, check with `in`
- **Quorum:** `len({i in 0..N if votes[i]}) * 2 > N + 1`
- **Nested dict update:** `votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}`

## Analysing Results

**OK:** All states satisfy all invariants.

**INVARIANT VIOLATION:** Trace shows shortest path — each step is one action firing with resulting state.

**DEADLOCK:** A state where no action is enabled. Use `--no-deadlock` for protocols.

**Tips:** `--fast` for large state spaces. `--por` for loosely coupled processes. `--no-deadlock` for most protocols.

# Specl Language Reference

## Module Structure

```specl
module Name
const C: Int              // set at check time: -c C=5
var x: 0..10              // state variable with type bound
init { x = 0 }            // initial state (one block)
action Step() { ... }     // state transition
func Helper(a) { ... }    // pure function (no state modification)
invariant Safe { ... }    // must hold in every reachable state
```

## Types

| Type | Example | Notes |
|------|---------|-------|
| `Bool` | `true`, `false` | |
| `Int` | `42`, `-7` | Unbounded |
| `Nat` | `0`, `100` | Non-negative int |
| `0..10` | | Inclusive range of ints |
| `Set[T]` | `{1, 2, 3}` | Finite set |
| `Seq[T]` | `[a, b, c]` | Ordered list (0-indexed) |
| `Dict[K, V]` | `{k: 0 for k in 0..N}` | Map from keys to values |
| `String` | `"red"` | String literal |

## Operators

| Category | Operators |
|----------|-----------|
| Logical | `and`, `or`, `not`, `implies`, `iff` |
| Comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` |
| Arithmetic | `+`, `-`, `*`, `/`, `%` |
| Set | `in`, `not in`, `union`, `intersect`, `diff`, `subset_of` |
| Sequence | `++` (concat), `head(s)`, `tail(s)`, `len(s)`, `s[i]` (index) |
| Conditional | `if ... then ... else ...` (expression — always requires else) |

## Dicts

Create with comprehension:
```specl
var role: Dict[Int, Int]
init { role = {p: 0 for p in 0..N} }
```

Update with `|` (merge):
```specl
role = role | {i: 2}                                               // one key
balance = balance | { from: balance[from] - amt, to: balance[to] + amt }  // multiple keys
votesGranted = votesGranted | {i: votesGranted[i] | {j: true}}     // nested dict
```

Access: `role[i]`, `votesGranted[i][j]`

## Parameterized Actions

Checker tries ALL valid parameter combinations in every reachable state:

```specl
action Transfer(from: 0..N, to: 0..N, amount: 1..MAX) {
    require from != to
    require balance[from] >= amount
    balance = balance | { from: balance[from] - amount, to: balance[to] + amount }
}
```

## Guards

`require` is a precondition. If false, the action is skipped (not an error):

```specl
action Eat(p: 0..2) {
    require philState[p] == 1
    require fork[p] == true and fork[(p + 2) % 3] == true
    philState = philState | { p: 2 }
    and fork = fork | { p: false, (p + 2) % 3: false }
}
```

## Quantifiers

```specl
all x in 0..N: P(x)       // universal: true if P holds for ALL x
any x in 0..N: P(x)       // existential: true if P holds for SOME x
```

Work in invariants, guards, and any expression.

## Set Comprehensions

```specl
{p in 0..N if state[p] == 1}                    // filter
len({v in 0..N if votedFor[v] == i})             // count matching
len({v in 0..N if voted[v]}) * 2 > N + 1         // quorum check
```

## Functions

Pure, no state modification, used for reusable logic:

```specl
func LastLogTerm(l) { if len(l) == 0 then 0 else l[len(l) - 1] }
func Quorum(n) { (n / 2) + 1 }
func Max(a, b) { if a > b then a else b }
```

## Multiple Variable Updates

Use `and` to update multiple variables atomically:

```specl
action Reset() {
    x = 0
    and y = 0
    and z = 0
}
```

## TLA+ Comparison

| TLA+ | Specl |
|------|-------|
| `x' = x + 1` | `x = x + 1` |
| `x = y` (equality) | `x == y` |
| `UNCHANGED <<y, z>>` | *(implicit)* |
| `/\`, `\/`, `~` | `and`, `or`, `not` |
| `\in`, `\notin` | `in`, `not in` |
| `\A x \in S: P(x)` | `all x in S: P(x)` |
| `\E x \in S: P(x)` | `any x in S: P(x)` |
| `[f EXCEPT ![k] = v]` | `f \| { k: v }` |
| `Init == ...` | `init { ... }` |
| `Next == A \/ B` | *(implicit — all actions OR'd)* |

## Common Pitfalls

- **`=` vs `==`**: `=` assigns, `==` compares. Inside actions, `x = 5` sets x. In invariants, use `x == 5`.
- **No `let` bindings**: Use inline expressions or extract to a `func`.
- **`any` is boolean only**: `any x in S: P(x)` returns Bool. Cannot use `x` outside.
- **Range params no arithmetic**: `action A(i: 0..N+1)` is invalid. Define `const MaxI: Int` and use `0..MaxI`.
- **`implies` precedence in nested quantifiers**: Flatten: `all c: all k: (A and B) implies C` instead of nesting.
- **State spaces are exponential**: N=2 ~ 100K-2M states, N=3 ~ 10M-100M. Always start small.
- **Use `--no-deadlock` for protocols**: Most distributed protocols have quiescent states where no action fires.

## Message Passing Pattern

Encode messages as sequences (tuples), store in a set:

```specl
var msgs: Set[Seq[Int]]
init { msgs = {} }

action Send(src: 0..N, dest: 0..N) {
    require role[src] == 2
    msgs = msgs union {[1, src, dest, currentTerm[src]]}
}

action Receive(src: 0..N, dest: 0..N) {
    require [1, src, dest, currentTerm[src]] in msgs
    // handle message...
}
```

## Encoding Enums

Use integer constants with comments:

```specl
// Roles: 0=Follower, 1=Candidate, 2=Leader
var role: Dict[Int, 0..2]
action BecomeCandidate(i: 0..N) { require role[i] == 0; role = role | {i: 1} }
```

## CLI Flags Reference

| Flag | Effect |
|------|--------|
| `-c KEY=VAL` | Set constant value |
| `--no-deadlock` | Don't report deadlocks |
| `--no-parallel` | Single-threaded |
| `--threads N` | Set thread count |
| `--max-states N` | Stop after N states |
| `--fast` | Fingerprint-only (no traces, 8 bytes/state) |
| `--por` | Partial order reduction |
| `--symmetry` | Symmetry reduction |
| `--write` | (format) Write in place |

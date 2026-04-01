---
name: ordeal
description: Test Python code with ordeal — discover properties, inject faults, mutate, explore state space
user_invocable: true
---

# ordeal — automated chaos testing for Python

You have access to `ordeal`, an automated testing toolkit. Use it when the user asks you to test, audit, or improve test coverage for Python code.

## When to use ordeal

- User says "test this", "is this well-tested?", "find bugs", "what could go wrong?"
- User wants to know if a refactor changed behavior
- User wants chaos/fault-injection testing
- A module has no tests or weak tests

## Quick decision tree

1. **No tests exist yet** → run `ordeal init <package>` (discovers properties, generates tests, validates with mutations)
2. **Tests exist, check quality** → run `ordeal audit <module>`
3. **Test a specific function** → use `mutate()` in Python or `ordeal mutate <target>`
4. **Deep exploration** → run `ordeal explore`
5. **Discover what a function does** → run `ordeal mine <target>`
6. **Compare two implementations** → use `diff(old_fn, new_fn)` in Python

## Commands

```
ordeal init <package>              # zero-to-tests: mine → generate → mutate-validate → explore
ordeal init --dry-run              # preview without writing
ordeal audit <module>              # mutation score + property coverage + test gaps
ordeal mutate <target>             # mutation testing (function or module)
ordeal mutate <target> -p thorough # all 14 mutation operators
ordeal mutate <target> --generate-stubs tests/gaps.py  # write tests for surviving mutants
ordeal mine <target>               # discover properties of a function
ordeal explore                     # coverage-guided state-space exploration (reads ordeal.toml)
ordeal replay <trace.json>         # replay a failure trace
ordeal replay --shrink --ablate <trace.json>  # shrink + find which faults matter
ordeal benchmark                   # USL scaling analysis
```

## Living reference

`catalog()` returns every fault, invariant, strategy, and capability at runtime — always up-to-date even when this skill isn't. When in doubt, call it.

```python
from ordeal import catalog
c = catalog()
for key in sorted(c):
    print(f"\n{key}:")
    for item in c[key]:
        print(f"  {item['qualname']}  -- {item['doc']}")
```

## Python API (when you need more control)

```python
from ordeal import mutate

# Mutation testing — are tests strong enough?
result = mutate("myapp.scoring.compute")
print(result.summary())              # gaps with cause + fix
stubs = result.generate_test_stubs() # ready-to-use test code
result.kill_attribution()            # which tests kill which mutants

# Discover properties
from ordeal import mine
props = mine("myapp.scoring.compute")  # returns discovered invariants

# Chaos testing — what if calls fail?
from ordeal import chaos_for
chaos_for("myapp.scoring")  # auto-discovers faults + invariants

# Differential testing — did a refactor change behavior?
from ordeal import diff
diff(old_fn, new_fn)

# Module-wide exploration
from ordeal.state import explore
state = explore("myapp")  # mine + scan + mutate + chaos in one pass
```

## Reading results

- `mutate()` returns a `MutationResult` with `.score` (0.0–1.0), `.survived` (list of gaps), `.summary()`, `.generate_test_stubs()`
- `ordeal init` prints JSON to stdout (for you) and a quality report to stderr (for the human)
- `ordeal audit` prints a structured report with mutation score, property coverage, and specific test gaps
- `ordeal explore` saves traces to `.ordeal/traces/` and seeds to `.ordeal/seeds/`

## Interpreting gaps

When mutants survive, each one has:
- `.operator` — what was changed (e.g., "negate_condition", "boundary_off_by_one")
- `.source_line` — where in the source
- `.remediation` — what test to write

Generate stubs with `result.generate_test_stubs()` — they include real param names, typed examples, and invariant suggestions.

## Key patterns

- **Seeds auto-replay**: failing inputs save to `.ordeal/seeds/` and replay on every `pytest` run
- **Fault ablation**: after finding a bug, `ablate_faults(trace)` tells you which faults were necessary
- **`--chaos` flag**: enables fault injection during pytest; `--chaos-seed 42` for reproducibility
- **Config via `ordeal.toml`**: explore, mutate, and audit all read from it

## What NOT to do

- Don't weaken a test to make it pass — if a test exposes a bug, fix the source
- Don't skip `ordeal init` and hand-write everything — let ordeal discover properties first, then refine
- Don't run `mutate()` on code that imports heavy frameworks (numpy/torch) without `--mutant-timeout`

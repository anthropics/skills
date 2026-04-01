---
name: ordeal
description: Automated chaos testing for Python — discovers properties, injects faults, mutates code, explores state space. TRIGGER when: code imports `ordeal`, user asks to test/audit/fuzz Python code, or check test quality.
user_invocable: true
---

# ordeal

Automated chaos testing for Python. Discovers properties, injects faults, runs mutation testing, explores reachable states.

Install: `pip install ordeal`

## Discovery

`catalog()` returns every capability at runtime — faults, invariants, strategies, mutations, and more. Always up-to-date.

```python
from ordeal import catalog
c = catalog()
for key in sorted(c):
    print(f"\n{key}:")
    for item in c[key]:
        print(f"  {item['qualname']}  -- {item['doc']}")
```

`ordeal --help` shows all CLI commands.

## Reading ordeal's output

ordeal's output is self-describing. When it finds something actionable, it tells you what to fix:

- **Surviving mutants** include `.remediation` — the specific test to write
- **Coverage gaps** include `.reachability_suggestions()` — branches not reached
- **`generate_test_stubs()`** returns ready-to-use Python test code
- **JSON to stdout** is structured for programmatic consumption; human reports go to stderr

## Vocabulary

- **Mutation score** — ratio of mutants killed by tests (0.0–1.0). A surviving mutant is a code change your tests didn't catch.
- **Fault injection** — simulate failures (timeouts, disk errors, network resets) during tests. Active under `--chaos`.
- **Property** — something ordeal discovered is true about a function (e.g., "output is bounded 0–1", "commutative", "deterministic").
- **Seed corpus** — failing inputs in `.ordeal/seeds/`, replayed automatically on every `pytest` run.
- **Fault ablation** — after a bug, replay without each fault to find which ones were necessary.
- **Chaos mode** (`--chaos`) — activates fault injection, buggify(), and property tracking.

## Guardrails

- If a test exposes a bug, fix the source — never weaken the test
- Heavy frameworks (numpy/torch): use `--mutant-timeout` with `mutate()`

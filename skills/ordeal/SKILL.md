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

## Guardrails

- If a test exposes a bug, fix the source — never weaken the test
- Heavy frameworks (numpy/torch): use `--mutant-timeout` with `mutate()`

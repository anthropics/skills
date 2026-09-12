# Function Point backfiring

Fourth independent cross-check. Function Points size software by user-visible functionality, independent of programming language. *Backfiring* reverses the calculation: convert LOC → FP using QSM's language-specific ratio, then apply FP-per-hour productivity.

## Formula

```
LOC_per_FP        # language-specific (QSM table below)
Function_Points   = KSLOC × 1000 / LOC_per_FP
hours_per_FP      = 8 – 12 (industry average; domain-adjusted below)
FP_hours          = Function_Points × hours_per_FP
```

## QSM language conversion table (abbreviated)

See qsm.com/resources/function-point-languages-table for the full list.

| Language | LOC per FP | Notes |
|---|---|---|
| Assembly | 320 | |
| C | 148 | |
| C++ | 59 | |
| C# | 59 | |
| Java | 53 | |
| Go | 38 | modern, concise |
| JavaScript | 47 | |
| TypeScript | 43 | types compress some |
| Python | 21 | very expressive |
| Ruby | 25 | |
| Rust | 39 | expressive + safe |
| Swift | 38 | |
| Kotlin | 43 | |
| SQL | 13 | declarative |
| HTML/CSS (FP proxy) | 34 | |

## Hours-per-FP by domain

- Data entry / simple CRUD: 6 – 8 hrs/FP
- Typical business app: 8 – 12 hrs/FP
- Real-time / embedded: 12 – 18 hrs/FP
- Systems / safety-critical: 15 – 25 hrs/FP

Convert `FP_hours` to P10 / P50 / P90 by varying `hours_per_FP` across the bracket.

## Why this helps

COCOMO anchors on LOC with scale drivers; Function Points anchor on *user-facing features*. Disagreement between the two reveals whether the codebase has lots of internal plumbing (low FP per LOC) or lots of user-facing features (high FP per LOC) — useful diagnostic information for the spot-check.

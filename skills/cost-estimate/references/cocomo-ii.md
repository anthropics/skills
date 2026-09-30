# COCOMO II cross-check

Industry-validated top-down sanity check. Load when running Step 4 cross-check.

## Formula

```
Effort_person_months = A × (KSLOC)^E × EAF
  A     = 2.94
  E     = 0.91 – 1.23     (use 1.0 nominal)
  EAF   = product of 17 effort multipliers, simplified into 4 buckets below
  KSLOC = source LOC / 1000 (excluding generated/vendored)

hours = person_months × 152
```

## Quick EAF table (17 multipliers collapsed to 5 buckets)

| Project type | E | EAF |
|---|---|---|
| Simple CRUD web app | 0.95 | 0.7 |
| Standard SaaS product | 1.00 | 1.0 |
| Platform / infrastructure | 1.10 | 1.5 |
| Systems / compiler / crypto-heavy | 1.15 | 2.0 |
| Safety-critical / regulated | 1.20 | 2.5 |

## Divergence rules vs Step 3 bottom-up

- **Within 30%** → good; report Step 3 number.
- **30 – 100% divergence** → report both; take geometric mean: `sqrt(bottom_up × cocomo)`.
- **> 2× divergence** → **stop and investigate** before reporting. Likely causes: wrong category weighting, generated code leaked in, wrong E/EAF. Do not publish mismatched numbers.

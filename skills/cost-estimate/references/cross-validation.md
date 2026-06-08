# Sensitivity & cross-validation (Step 10)

## Contents
1. Sensitivity analysis — which assumption moves the number most?
2. External anchors — Harvard supply-side + Capers Jones TCO
3. Three-way (or two-way) cross-check rules

---

## 1. Sensitivity analysis

Vary each input one at a time, ±1 standard bucket, and record `p50_impact_usd`:

- Quality multiplier: 0.7 → 1.3
- Recommended rate: ±50%
- Company stage team multiplier: 1.0 → 2.65×
- Specialized-category LOC share: ±20%
- COCOMO EAF bucket: nearest-neighbor shift

Sort descending. Report the **top 3 drivers**.

---

## 2. External anchors (reality checks)

Two independent sanity checks drawn from peer-reviewed research.

### 2a. Harvard supply-side anchor (Hoffmann, Nagle, Zhou 2024)

For OSS-like codebases, the supply-side value (what it cost to produce) averages ~**3.5× a naive `LOC × generic_rate`** calculation (SSRN 4693148).

```
naive_supply_side = source_LOC × $0.15/line   # rough median, 2024 OSS data
harvard_ratio     = p50_cost / naive_supply_side
```

If `harvard_ratio` is far from 3.5× (say, <1.5× or >6×), flag it:

- **< 1.5×** → under-counting complexity, or rates set too low
- **> 6×** → over-priced; excluded code probably leaked in, or company-stage multiplier too high

### 2b. Capers Jones 5-year total cost of ownership

Initial build is 25 – 35% of 5-year lifecycle. Report `lifetime_cost_5y`:

```
annual_maint_rate = 0.20        # industry default; range 0.15 – 0.30
lifetime_cost_5y  = build_cost × (1 + annual_maint_rate × 5)
                  = build_cost × 2.0 (default)
```

Important framing:

> "Build cost above is ~40 – 50% of the 5-year TCO."

Clients often mistake the build number for total ownership — call it out.

---

## 3. Cross-check (three-way if git, two-way otherwise)

| Method | Hours | Notes |
|---|---|---|
| Bottom-up (Step 3+5) | | Category × rate, with overheads |
| COCOMO II (Step 4) | | Top-down, calibrated constants |
| Process signal (Step 2) | | `commits × avg_commit_hours` (skip if no git) |

### Rules

**Three signals available (git present):**
- All agree within 30% → confidence **high**
- Two agree, one outlier → confidence **medium** (name the outlier)
- All three disagree → confidence **low** — reconcile before publishing

**Two signals only (no git):**
- Bottom-up + COCOMO within 30% → **medium**
- > 30% divergence → **low**
- Never report **high** confidence without a process signal.

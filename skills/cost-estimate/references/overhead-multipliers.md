# Overhead multipliers (Step 5)

Apply **multiplicatively** on top of Base Coding Hours. Compounding rule: if a quality signal already bumped per-LOC value in Step 1d, **reduce the related overhead to the low end** to avoid double-counting.

## Formula

```
Total_Eng_Hours = Base_Coding_Hours
                × (1 + arch_design)        // 0.15 – 0.20
                × (1 + debugging)           // 0.25 – 0.30
                × (1 + code_review)         // 0.10 – 0.15
                × (1 + documentation)       // 0.10 – 0.15   ← low end if quality bonus for docs
                × (1 + integration_test)    // 0.20 – 0.25   ← low end if quality bonus for tests
                × (1 + learning_curve)      // 0.10 – 0.20 (only for specialized stacks)
                × (1 + devops_setup)        // 0.05 – 0.10   ← low end if quality bonus for CI
                × (1 + churn_adjustment)    // 0 by default
                                            // +0.15 if churn_ratio > 2.0 AND contributor_count < 3
                                            // (skip when churn is normal team iteration, not rework)
                × quality_multiplier        // 0.7 – 1.3 from Step 1d
```

Apply to P10 / P50 / P90 each → **Total Engineering Hours (P10 / P50 / P90)**.

## Sanity check

The stacked overhead (before `quality_multiplier`) typically falls **1.8× – 2.6×** of base. Outside that range → investigate: you're probably double-counting, or you've assigned an overhead signal that doesn't match the detected code.

# Statistical Methods Reference

## Sample Size Formulas

All formulas use two-tailed tests with z-scores: z_alpha = Z(1 - alpha/2), z_beta = Z(power).

### Binary Metrics (Proportions Test)
```
n = 2 * (z_alpha + z_beta)^2 * p_pooled * (1 - p_pooled) / (p2 - p1)^2

where p_pooled = (p1 + p2) / 2
      p1 = baseline rate (decimal, e.g. 0.05 for 5%)
      p2 = p1 + absolute effect size
```

### Continuous Metrics (Two-Sample T-Test)
```
n = 2 * (z_alpha + z_beta)^2 * variance / effect_size^2

where variance = sigma^2 (if not known, default: (baseline * 0.1)^2)
      effect_size = baseline * (mde_pct / 100) for relative MDE
```

### Count Metrics (Poisson Approximation)
```
n = 2 * (z_alpha + z_beta)^2 * lambda / effect_size^2

where lambda = baseline count rate
```

## Adjustments

### Unequal Traffic Allocation
When control/treatment split is not 50/50:
```
adjusted_n = n * (1 + r)^2 / (4 * r)

where r = treatment_allocation / control_allocation
```

### Multiple Variants
When more than 2 variants (including control):
```
adjusted_n = n * (k - 1)

where k = number of variants
```
Consider multiple testing correction (Bonferroni, Holm, or Benjamini-Hochberg).

### Cluster Design Effect
For cluster randomized experiments:
```
DEFF = 1 + (m - 1) * ICC
adjusted_n = n * DEFF
clusters_per_arm = ceil(adjusted_n / m)

where m = average cluster size
      ICC = intra-cluster correlation (typically 0.01 - 0.1)
```

### Switchback Autocorrelation
For switchback experiments:
```
effective_multiplier = (1 - rho) / (1 + rho)
adjusted_n = ceil(n / effective_multiplier)
effective_periods = floor(num_periods * effective_multiplier)

where rho = temporal autocorrelation (0 to 1)
```

### Factorial Cells
For factorial designs:
```
total_cells = product of all factor levels
total_n = n_per_cell * total_cells

If detecting interactions: interaction_n = n_per_cell * 4 * total_cells
```

### Causal Inference: DiD Serial Correlation
```
VIF = (1 + rho) / (1 - rho)
adjusted_n = ceil(n * VIF)
```

### MAB Exploration Budget
For epsilon-greedy multi-armed bandit:
```
explore_budget = ceil(horizon * epsilon)
per_arm_explore = ceil(explore_budget / num_arms)
estimated_regret = epsilon * horizon * (arms - 1) / arms
```

## Duration Estimation

```
effective_daily_traffic = daily_traffic * (sum_of_allocation_pcts / 100)
days = ceil(total_sample_size / effective_daily_traffic)
weeks = ceil(days / 7)
```

Minimum recommended duration: **7 days** (to capture weekly patterns). Consider adding 2-3 buffer days for ramp-up/cool-down.

## MDE Feasibility Check

Given available traffic and max duration, calculate the achievable MDE:
```
available_n = daily_traffic * max_days
achievable_mde = (z_alpha + z_beta) * sqrt(2 * variance / available_n)  # continuous
achievable_mde = (z_alpha + z_beta) * sqrt(2 * p * (1-p) / available_n)  # binary
achievable_mde = (z_alpha + z_beta) * sqrt(2 * lambda / available_n)     # count
```

If achievable MDE > target MDE, the experiment is not feasible with current traffic.

## Common Warnings

| Condition | Warning |
|-----------|---------|
| n < 100 per variant | Very small sample. Results may be unreliable |
| MDE < 1% relative | Very small effect needs large traffic or long duration |
| Alpha > 0.05 | Risk of false positives increases |
| Power < 0.8 | Risk of false negatives increases |
| Clusters < 10 per arm | Fewer clusters = unreliable inference |
| Cluster size imbalance | Balance clusters for stable estimates |
| Duration < 7 days | May miss weekly patterns |
| Duration > 90 days | Consider if the experiment is worth running this long |

## Standard Defaults

| Parameter | Default | Notes |
|-----------|---------|-------|
| Alpha | 0.05 | 5% false positive rate (two-tailed) |
| Power | 0.80 | 80% chance of detecting a true effect |
| MDE | 5% relative | Smallest change worth detecting |
| Traffic allocation | 50/50 | Balanced split is most efficient |
| Variants | 2 | Control + treatment |

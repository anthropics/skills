# Experiment Types Reference

## A/B Test

**When to use**: Discrete changes, sufficient traffic (>1,000 users/day), need clear causal evidence, treatment effect is expected to be immediate.

**Use cases**: Testing new features or UI changes, comparing algorithms or ranking systems, optimizing conversion funnels, testing marketing copy.

**Pros**: Simple to understand and implement, clean causal inference, well-established statistical methods, easy to analyze.

**Cons**: Can only test one change at a time, requires sufficient traffic, may take time to reach significance.

**Defaults**: alpha=0.05, power=0.8, 2 variants, 50/50 split.

**Randomization**: USER_ID, HASH_BASED, consistent assignment.

**Examples**: New checkout flow vs current, two recommendation algorithms, green vs blue CTA button.

---

## Cluster Randomized Experiment

**When to use**: Treatment affects groups (cities, stores, schools), network effects or interference between users, marketplace experiments, geographic-based treatments. Need 20+ clusters.

**Use cases**: Driver incentive programs across cities, marketplace pricing by region, store-level promotions.

**Pros**: Handles network effects and spillover, suitable for group-level interventions, prevents contamination.

**Cons**: Requires larger sample sizes, fewer degrees of freedom, more complex analysis, need many clusters for power.

**Defaults**: alpha=0.05, power=0.8, 2 variants, 50/50 split.

**Randomization**: CLUSTER, RANDOM, consistent assignment.

**Key parameters**:
- **ICC (Intra-Cluster Correlation)**: Proportion of variance between clusters (typically 0.01-0.1)
- **Cluster size**: Average number of units per cluster
- **Design Effect**: DEFF = 1 + (cluster_size - 1) x ICC. Inflates required sample size.

**Warnings**:
- Need at least 10 clusters per arm for reliable inference
- Balance clusters in size for stable estimates
- Larger ICC or cluster size = much larger sample sizes

---

## Switchback Experiment

**When to use**: Strong network effects, supply-demand coupling (marketplaces), user-level randomization causes issues, treatments can be switched quickly.

**Use cases**: Rideshare pricing algorithms, delivery dispatch systems, restaurant recommendations in food delivery.

**Pros**: Handles network effects well, all users experience both conditions, reduces time-of-day variance.

**Cons**: Carryover effects, longer duration, complex analysis, sensitive to non-stationarity.

**Defaults**: alpha=0.05, power=0.8, 2 variants, 50/50 split.

**Randomization**: SESSION, RANDOM, not consistent (users re-randomized each period).

**Key parameters**:
- **Number of periods**: Minimum 4 recommended
- **Period length**: Hours per switch (balance between more data and carryover risk)
- **Autocorrelation (rho)**: 0 to 1. Higher rho reduces effective sample size.
- **Effective multiplier**: (1 - rho) / (1 + rho). Applied to sample size.

**Warnings**:
- Assumes no carryover effects between periods
- Minimum 7 days to capture weekly patterns
- Non-stationarity (trends, seasonality) can bias results

---

## Causal Inference (Observational)

**When to use**: Cannot run a randomized experiment, analyzing historical data or policy changes, natural experiments, studying long-term effects.

**Use cases**: Policy change impact across regions (DiD), eligibility threshold effects (RDD), effect of education on earnings (IV).

**Pros**: Can analyze past data without running an experiment, useful for post-hoc analysis, study effects over longer periods, lower cost.

**Cons**: Stronger assumptions required, risk of confounding bias, more complex statistical methods, results may be less definitive.

**Defaults**: alpha=0.05, power=0.8, 2 groups.

**Methods**:

| Method | Key Assumption | Best For |
|--------|---------------|----------|
| **Difference-in-Differences (DiD)** | Parallel trends between groups pre-treatment | Policy changes with pre/post data |
| **Regression Discontinuity (RDD)** | Continuity at the threshold | Eligibility cutoffs, score-based assignment |
| **Propensity Score Matching (PSM)** | Overlap in covariates, no unmeasured confounders | Observational data with rich covariates |
| **Instrumental Variables (IV)** | Valid, strong instrument (relevant + exogenous) | When direct randomization impossible |

**Method-specific notes**:
- DiD: Serial correlation inflates variance. AR(1) VIF = (1 + rho) / (1 - rho)
- RDD: Sample size depends on bandwidth near threshold. Consult a statistician for bandwidth selection
- PSM: Effective sample size depends on match quality and covariate overlap
- IV: Weak instruments lead to biased estimates. Check first-stage F-statistic > 10

---

## Factorial Design

**When to use**: Testing multiple independent changes simultaneously, interested in interaction effects, have sufficient traffic, changes are unlikely to conflict.

**Use cases**: 2x2 button color x copy length, email subject x send time x personalization, landing page hero x headline x CTA.

**Pros**: Test multiple factors efficiently, detect interaction effects, more information per user, faster than sequential A/B tests.

**Cons**: More complex analysis, requires larger sample sizes, harder to interpret with many factors, false positive risk increases.

**Defaults**: alpha=0.05, power=0.8, 4 variants (2x2), 25/25/25/25 split.

**Randomization**: USER_ID, HASH_BASED, consistent assignment.

**Key parameters**:
- **Factors**: Each with a name and number of levels (e.g. Button Color with 2 levels)
- **Total cells**: Product of all factor levels (e.g. 2 x 3 = 6 cells)
- **Detect interaction**: If yes, sample size inflated ~4x per cell

**Warnings**:
- With many factors, total cells grow fast (3 factors with 3 levels each = 27 cells)
- Verify factor independence before running
- Consider Bonferroni correction for multiple comparisons

---

## Multi-Armed Bandit (MAB)

**When to use**: Continuous optimization is priority, opportunity cost of poor variants is high, content recommendations, personalization, can tolerate adaptive allocation.

**Use cases**: Content headline optimization, recommendation algorithm selection, promotional banner testing, push notification copy.

**Pros**: Minimizes opportunity cost, adapts to changing conditions, automatic traffic allocation, good for ongoing optimization.

**Cons**: Less interpretable than A/B tests, harder to establish causality, requires more sophisticated infrastructure, may converge to local optimum.

**Defaults**: alpha=0.05, power=0.8, 3 arms.

**Randomization**: REQUEST, RANDOM, not consistent (re-randomized each request).

**Key parameters**:
- **Number of arms**: 2 or more variants
- **Horizon**: Total observations expected (minimum 1,000)
- **Exploration rate (epsilon)**: 0 to 0.5. Higher = more exploration, slower convergence
- **Exploration budget per arm**: (horizon x epsilon) / num_arms
- **Estimated regret**: epsilon x horizon x (arms - 1) / arms

**Notes**:
- Traditional fixed-sample statistical testing does not apply
- Sample size shown is the exploration budget per arm, not a significance calculation
- Skip variance reduction (adaptive nature handles this)
- Reward function must be well-defined before starting

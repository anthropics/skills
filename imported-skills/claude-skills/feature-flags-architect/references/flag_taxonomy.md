# Flag taxonomy — the 4 types

Misclassifying a flag is the root cause of flag debt. Pick one type at the moment you create the flag.

## Decision tree

```
Is the flag intended to be permanent (entitlement, plan tier, role-based access)?
├── YES → Permission flag
└── NO → Will it eventually be removed?
    ├── Will it be removed when feature is fully shipped?
    │   └── Yes → Release flag
    ├── Will it be removed when an A/B test concludes?
    │   └── Yes → Experiment flag
    └── Will it remain as a circuit breaker / safety toggle?
        └── Yes → Operational flag
```

## 1. Release flag

**Purpose:** Hide an unfinished or risky feature in production while it's being built or rolled out.

| Property | Value |
|---|---|
| Lifespan | Days to weeks (≤90 days target) |
| Default | OFF in prod, ON in dev/staging |
| Owner | Engineer who created it |
| Cleanup trigger | Reached 100% rollout AND stable for 7+ days |
| Debt risk | High — easy to forget |
| Storage | Provider (LD/GrowthBook) or config file |

**Examples:**
- `new-checkout-flow` — gating a UI rewrite
- `payment-v2-engine` — gating backend rewrite during cutover
- `enable-search-relevance-v3` — A/B test of new ranking

**Anti-pattern:** Release flag still at 100% in code 6+ months later. The branch the flag protects is dead code; remove it.

## 2. Experiment flag

**Purpose:** Run an A/B test or multivariate experiment.

| Property | Value |
|---|---|
| Lifespan | 2-8 weeks (until significance) |
| Default | OFF; control group |
| Owner | Product or Marketing |
| Cleanup trigger | Test concluded; winner shipped |
| Debt risk | Medium |
| Storage | Provider with experimentation features |

**Examples:**
- `homepage-headline-v2` — testing new copy
- `pricing-page-monthly-vs-annual-default` — testing default toggle
- `onboarding-checklist-vs-tour` — testing onboarding pattern

**Anti-pattern:** Experiment running for 6 months because no one decided to call it. Either declare a winner or kill the test.

## 3. Operational flag

**Purpose:** Circuit breakers, kill switches, performance toggles. Designed to be flipped during incidents.

| Property | Value |
|---|---|
| Lifespan | Months to years (long-lived by design) |
| Default | ON (active path) |
| Owner | SRE / on-call team |
| Cleanup trigger | Replaced by autoscaling, retired feature |
| Debt risk | Low — they're meant to persist |
| Storage | Provider with low-latency global edge |

**Examples:**
- `enable-rate-limit-v2` — kill switch if v2 misbehaves
- `disable-recommendations-engine` — emergency cutoff
- `use-fallback-search` — degraded mode toggle

**Anti-pattern:** Operational flag that no one knows how to use during an incident. Document the trigger and runbook.

## 4. Permission flag

**Purpose:** Entitlements per user/account/plan/role. Permanent by design.

| Property | Value |
|---|---|
| Lifespan | Indefinite (plan/role lifetime) |
| Default | OFF; granted by entitlement system |
| Owner | Product (plan/role definitions) |
| Cleanup trigger | Plan or role retired |
| Debt risk | Very low |
| Storage | User/account database, NOT a flag provider |

**Examples:**
- `feature.advanced-analytics` — enterprise-only
- `feature.export-csv` — paid plans only
- `role.admin-dashboard` — admin-only UI

**Anti-pattern:** Permission flags stored in a flag provider with per-user targeting rules. Move them to your entitlements system; they're not feature flags.

## Classification matrix

When you can't decide, ask:

| Question | If YES | If NO |
|---|---|---|
| Will this be at 100% in <90 days? | Release | next ↓ |
| Will this run an A/B test? | Experiment | next ↓ |
| Is this a kill switch / safety toggle? | Operational | next ↓ |
| Is this a plan/role entitlement? | Permission | reconsider |

If none fit: you don't need a flag. Either ship the feature directly via deploy, or use a different mechanism (config, env var, role).

## Ownership rules

- Every flag must have a named owner at creation
- When the owner leaves, the flag is reassigned within 30 days or removed
- Release flags lapse to the team's tech-debt owner if not reassigned

## Lifespan SLAs

| Type | Max acceptable lifespan | Cleanup automation |
|---|---|---|
| Release | 90 days | `flag_debt_scanner.py` |
| Experiment | 60 days | Provider auto-stop on significance |
| Operational | none | Annual review |
| Permission | none | Tied to plan/role retirement |

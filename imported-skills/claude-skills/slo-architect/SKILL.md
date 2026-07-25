---
name: slo-architect
description: Use when defining, reviewing, or operating SLOs/SLIs/error budgets. Triggers on "define an SLO", "what should our SLO be", "error budget", "burn rate", "SLI", "service level objective", "Google SRE workbook", "multi-window burn-rate alert", or any reliability-target question. Ships SLO designer, error-budget calculator with multi-window burn-rate thresholds, and SLO reviewer that catches the common bugs (target too aggressive, window too short, conflicting SLOs, no SLI definition). 4 references on SLO principles + SLI design + error budget math + composition with feature-flags-architect/chaos-engineering/kubernetes-operator. NOT a generic observability skill — specifically the SLO discipline.
context: fork
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [slo, sli, sla, error-budget, burn-rate, sre, reliability, google-sre-workbook, observability]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# SLO Architect

Define SLOs that mean something. Most "SLOs" in the wild are arbitrary numbers no one believes — 99.9% on every endpoint, no SLI definition, no error budget, no policy for what happens when budget burns. This skill enforces the discipline from Google's SRE Workbook: pick the right SLI, set a target users actually care about, calculate the error budget, wire multi-window burn-rate alerts, and have a written policy for when budget runs out.

## When to use

- Defining a new SLO for a service or feature
- Reviewing existing SLOs for common bugs
- Picking the right SLI (event-based vs time-window based vs request-based)
- Computing error budgets and burn-rate alert thresholds
- Tying SLOs to existing controls — feature flags abort, chaos blast radius, operator capability levels

## When NOT to use

- General observability strategy (metrics + logs + traces) → use `observability-designer`
- Customer-facing SLAs with legal teeth → that's contract drafting, not engineering
- Performance load testing (capacity, not reliability) → use `performance-profiler`
- Active incident response → use `incident-response`

## Core principle: an SLO is a promise about user experience

```
SLI  ⟶  measurable signal of user-perceived health (e.g., HTTP 2xx rate)
SLO  ⟶  target for the SLI over a window (e.g., 99.9% over 30 days)
SLA  ⟶  customer-facing commitment with consequences (separate concern)
EB   ⟶  error budget: 100% − SLO target = how much "bad" you can spend
BR   ⟶  burn rate: how fast you're consuming the error budget
```

The four cardinal mistakes:

1. **Target too high** (99.99%+ on services that can't support it) — every minor blip violates SLO; alerts become noise.
2. **Wrong SLI** (CPU usage as proxy for user experience) — system can be "green" while users suffer.
3. **No error budget policy** — burning budget means nothing if there's no agreed action.
4. **Single-window burn-rate alert** — either too noisy (page on a 5-min spike) or too slow (notice budget exhausted after the fact).

The 3 tools below catch each of these.

## Quick start

```bash
SKILL=engineering/slo-architect/skills/slo-architect

# 1. Design an SLO
python "$SKILL/scripts/slo_designer.py" \
  --service checkout-svc \
  --sli-type request-success-rate \
  --target 99.9 \
  --window-days 30

# 2. Compute error budget + multi-window burn-rate alerts
python "$SKILL/scripts/error_budget_calculator.py" \
  --target 99.9 --window-days 30

# 3. Review existing SLO definitions for common bugs
python "$SKILL/scripts/slo_review.py" --slo-doc docs/slos/
```

## The 3 Python tools

All stdlib-only.

### `slo_designer.py`

Generates a structured SLO definition with required fields. Refuses to render if any required field is missing (`exit 1`).

```bash
python scripts/slo_designer.py \
  --service checkout-svc \
  --sli-type request-success-rate \
  --target 99.9 \
  --window-days 30 \
  --owner team-checkout
```

**SLI types supported:**
- `request-success-rate` — `(total_requests - bad_requests) / total_requests`
- `request-latency` — `count(requests < threshold) / total_requests`
- `availability-time` — `(window - downtime) / window`
- `data-freshness` — `count(data_age < threshold) / total_data_points`
- `correctness` — `count(correct_outputs) / total_outputs`

Output is markdown by default with all required fields filled or marked `<must define>`. JSON output (`--format json`) is consumed by `slo_review.py`.

### `error_budget_calculator.py`

Given target availability + window, computes:
- Allowed downtime in the window
- Multi-window burn-rate thresholds per Google SRE Workbook (Chapter 5):
  - **Fast burn** — page if 2% of monthly budget consumed in 1 hour
  - **Slow burn** — page if 10% consumed in 6 hours, ticket if 10% in 3 days
- Recommended alerting rules (PromQL-shaped output)

```bash
python scripts/error_budget_calculator.py --target 99.9 --window-days 30
python scripts/error_budget_calculator.py --target 99.95 --window-days 7 --format json
```

### `slo_review.py`

Audits a directory of SLO definitions (markdown or JSON) for the common bugs.

```bash
python scripts/slo_review.py --slo-doc docs/slos/
```

**Checks:**
- `target_too_high`: target ≥ 99.99% (sustainable only with massive engineering investment)
- `target_too_low`: target ≤ 99.0% (probably wrong SLI; users will notice)
- `window_too_short`: window < 7 days (statistical noise dominates)
- `window_too_long`: window > 90 days (slow feedback)
- `no_sli_definition`: SLI section missing or vague ("everything OK")
- `no_error_budget_policy`: no documented action when budget burns
- `cpu_as_sli`: CPU/memory used as user-experience proxy (wrong signal)

## SLI selection cheatsheet

| User experience | SLI type | What you measure |
|---|---|---|
| "Did the request succeed?" | request-success-rate | `2xx / total` |
| "Was the response fast?" | request-latency | `count(p99 < threshold) / total` |
| "Was the service up?" | availability-time | `(window - downtime) / window` |
| "Is the data current?" | data-freshness | `count(data_age < threshold) / total` |
| "Was the answer correct?" | correctness | `count(correct) / total` |

See `references/sli_design.md` for examples and anti-patterns.

## Error budget math (the basics)

For 99.9% SLO over 30 days:
- Allowed unavailability: `0.1% × 30 × 24 × 60 = 43.2 minutes`
- 1-hour fast-burn threshold (2% of monthly budget burned): `2% × 43.2 / 60 ≈ 1.44 ratio multiplier`
- 6-hour slow-burn threshold (10% in 6h): `10% × 43.2 / 360 ≈ 0.6 ratio multiplier`

`error_budget_calculator.py` does this math for you and emits ready-to-paste alert rules.

## Composition with the rest of the portfolio

This skill explicitly composes with three others:

| Skill | Composition |
|---|---|
| `feature-flags-architect` | Rollout abort criteria reference SLO burn-rate thresholds |
| `chaos-engineering` | Blast-radius calculator already takes monthly error budget as input — define it here |
| `kubernetes-operator` | Operator capability L4 (Deep Insights) requires SLOs + Prometheus rules |

The `error_budget_calculator.py` output is in the same shape `engineering/skills/chaos-engineering/scripts/blast_radius_calculator.py` expects on stdin.

## Workflows

### Workflow 1: Define a new SLO

```
1. Pick the user journey to protect (e.g., "checkout completion").
2. Choose SLI type (request-success-rate, latency, availability, freshness, correctness).
3. Define the SLI precisely: numerator/denominator with concrete labels.
4. Pick a target by measuring 30 days of historical SLI value:
     target = floor(p50 of last 30 days × 100) / 100
   This avoids targets the system has never sustained.
5. Pick a window (28 days = 4 calendar weeks, recommended).
6. Run slo_designer.py to render the SLO definition.
7. Run error_budget_calculator.py to get burn-rate alerts.
8. Write the error budget policy (what happens when budget burns).
9. Run slo_review.py — must pass before the SLO is "live".
```

### Workflow 2: Quarterly SLO review

```
1. For every active SLO, run slo_review.py — fix any FAIL findings.
2. Look at last quarter's data:
   - Was the SLO too easy (never burned budget)? Tighten target.
   - Was it too hard (frequently burned)? Loosen target OR fix the system.
   - Did burn-rate alerts fire usefully (not too noisy, not too late)? Adjust thresholds.
3. Audit error budget policies — were they actually followed when budget burned?
4. Commit revised SLOs; archive old versions with date stamps.
```

### Workflow 3: SLO-driven rollback

```
1. New deploy starts burning error budget faster than baseline.
2. Burn-rate alert fires (from error_budget_calculator.py thresholds).
3. Auto-rollback via feature flag (kill switch from feature-flags-architect).
4. Postmortem feeds into next SLO revision.
```

## References

- `references/slo_principles.md` — SLI vs SLO vs SLA, Google SRE Workbook canon
- `references/sli_design.md` — picking the right SLI; 5 types with examples
- `references/error_budget.md` — error budget math, burn-rate alerts, budget policy
- `references/composition.md` — how SLOs feed feature flags, chaos, operators

## Slash command

`/slo-design` — interactive SLO design wizard that runs all 3 tools.

## Asset templates

- `assets/slo_template.yaml` — fillable SLO YAML
- `assets/error_budget_policy.md` — fillable policy template

## Anti-patterns

- **99.99% on every endpoint** — copy-paste SLOs that nobody verified the system can sustain
- **CPU usage as SLI** — system metrics aren't user experience
- **Single-window burn-rate alert** — too noisy if 5-min, too slow if 30-day
- **No error budget policy** — burning budget means nothing without an action
- **SLOs without owners** — no one is responsible; they bit-rot
- **SLOs reviewed once a year** — system characteristics change faster than that
- **SLAs in the SLO doc** — different audience, different stakes; keep them separate
- **SLO target = SLA target** — SLO must be tighter (you should beat your contract before customers notice)

## Verifiable success

A team using this skill should achieve:

- 100% of SLOs pass `slo_review.py` with 0 FAIL findings
- Every SLO has a documented owner, error budget, burn-rate alerts, and policy
- Burn-rate alerts fire ≤2 times/month per SLO that's hit (signal, not noise)
- Mean time to detect SLO violation: <30 min (multi-window burn-rate alerts working)
- Quarterly SLO review happens every quarter (not annually)

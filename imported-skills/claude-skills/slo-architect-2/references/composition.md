# Composition with the rest of the portfolio

`slo-architect` is the keystone. Three other skills in this library already lean on the SLO + error budget concept. This page shows how to wire them together for a coherent reliability stack.

## The unified concept: error budget

```
┌────────────────────────────────────────────────────────────┐
│                      slo-architect                         │
│             defines SLO, error budget, burn rate           │
└──────────┬─────────────────┬────────────────┬─────────────┘
           │                 │                │
           ▼                 ▼                ▼
   feature-flags-      chaos-engineering   kubernetes-
   architect           (blast-radius        operator
   (rollout abort)     bound by EB)         (cap level L4)
```

## With feature-flags-architect

`feature-flags-architect` defines kill switches. Their abort triggers should reference SLO burn-rate, not arbitrary thresholds.

Before:
```
abort_if: "p99 > 1000ms OR error_rate > 1%"
```

After (SLO-driven):
```
abort_if: "burn_rate.fast > 14.4 over 1h (per SLO checkout-success)"
```

Wire-up:

1. Define SLO via `slo_designer.py`
2. Run `error_budget_calculator.py` to get the burn-rate threshold
3. Use that threshold in the flag's abort criteria
4. The kill_switch_audit.py from feature-flags-architect now has a real signal to verify against

## With chaos-engineering

`chaos-engineering`'s `blast_radius_calculator.py` already takes monthly error budget as input — but the budget should come from the SLO, not be made up.

```bash
# 1. Get the budget from the SLO definition
python slo_architect/scripts/error_budget_calculator.py \
  --target 99.9 --window-days 30 --format json \
  | jq .budget_minutes

# 2. Pass it to the chaos blast-radius calculator
python chaos_engineering/scripts/blast_radius_calculator.py \
  --traffic-share 0.05 \
  --user-pop 1000000 \
  --duration-min 15 \
  --monthly-budget-min 43.2  # ← from step 1
```

Now blast radius is bounded by REAL error budget, not a number someone typed in.

## With kubernetes-operator

OperatorHub Capability Level 4 ("Deep Insights") requires:
- `/metrics` endpoint
- Prometheus alert rules
- SLOs documented for the operator's managed resources

`slo-architect` provides the SLO definitions; `error_budget_calculator.py` provides the alert rules. Drop them in the operator's Helm chart or OperatorHub bundle.

## End-to-end example

Goal: ship a new checkout flow.

1. **Define the SLO** (slo-architect):
   ```bash
   slo_designer.py --service checkout-svc --sli-type request-success-rate \
     --target 99.9 --window-days 28 --owner team-checkout
   ```

2. **Compute burn-rate alerts** (slo-architect):
   ```bash
   error_budget_calculator.py --target 99.9 --window-days 28
   # → fast_burn threshold = 14.4
   ```

3. **Define rollout** (feature-flags-architect):
   ```bash
   rollout_planner.py --population 100000 --target-percent 100 \
     --duration-days 14 --strategy ring
   # 1% → 5% → 25% → 50% → 100%
   ```

4. **Wire the abort** (feature-flags-architect):
   ```yaml
   abort_if: "burn_rate.fast > 14.4 (per SLO slo-checkout-svc-...)"
   ```

5. **Validate via chaos** before going wide (chaos-engineering):
   ```bash
   blast_radius_calculator.py --traffic-share 0.05 --user-pop 100000 \
     --duration-min 15 --monthly-budget-min 40.32
   # → GREEN if <1% of monthly budget
   ```

6. **Audit the operator** if the service is operator-managed (kubernetes-operator):
   ```bash
   operator_capability_audit.py --operator-dir ./checkout-operator
   # → confirm L4 includes the new SLO
   ```

Each step uses the previous step's output as input. The SLO is the unifying number.

## What slo-architect does NOT replace

- **observability-designer** — broader observability strategy (metrics, logs, traces, dashboards beyond SLO)
- **incident-response** — SLO violation may trigger an incident, but incident response is a separate discipline
- **performance-profiler** — capacity planning needs different metrics than SLO does

Use slo-architect for SLO+error-budget; use the others for their specific scopes.

## Anti-pattern: SLO without composition

A team defines SLOs in a spreadsheet. Nobody references them in:
- Feature flag rollouts
- Chaos experiment design
- Operator capability audits
- Incident postmortems

The SLOs become a reporting artifact, not an operating tool. The composition story is what makes SLOs change behavior.

## Operational checklist

For any service with a new SLO, verify:

- [ ] SLO defined via `slo_designer.py` (`slo_review.py` passes)
- [ ] Burn-rate alerts deployed via `error_budget_calculator.py` output
- [ ] If using feature flags: rollout abort references the SLO burn-rate threshold
- [ ] If running chaos: blast radius bounded by SLO error budget
- [ ] If operator-managed: operator audit confirms L4 includes the SLO
- [ ] Postmortem template (when SLO violated) includes "SLO revision needed?" question

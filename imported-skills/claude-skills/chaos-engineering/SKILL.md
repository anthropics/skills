---
name: chaos-engineering
description: Use when planning, running, or learning from chaos engineering experiments. Triggers on "chaos experiment", "fault injection", "gameday", "resilience test", "blast radius", "steady state", "abort criteria", "Chaos Toolkit", "Chaos Mesh", "Litmus", "Gremlin", "AWS FIS", or any deliberate failure-injection question. Ships experiment designer, blast-radius calculator, and postmortem generator (all stdlib Python), 4 references on chaos principles + experiment design + attack taxonomy + tooling landscape, and a /chaos-experiment slash command. Composes with feature-flags-architect (kill switches as abort triggers) and kubernetes-operator (common chaos targets).
context: fork
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [chaos-engineering, resilience, fault-injection, gameday, sre, reliability, chaos-toolkit, chaos-mesh, litmus, gremlin, aws-fis]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Chaos Engineering

Design experiments that surface real weaknesses in production systems — without becoming outages. Most "chaos engineering" attempts skip steady-state measurement, define no abort criteria, and have no blast-radius bound. This skill enforces the discipline that makes chaos experiments safe and useful.

## When to use

- Planning a chaos experiment (what to break, where, when, how to abort)
- Calculating blast radius before running the experiment
- Reviewing an existing experiment plan for safety
- Choosing a chaos tool (Chaos Toolkit / Chaos Mesh / Litmus / Gremlin / AWS FIS)
- Writing a chaos experiment postmortem
- Running a Game Day exercise

## When NOT to use

- General incident response (use `incident-response`)
- Threat hunting / red-team (use `red-team`, `threat-detection`)
- Performance load testing (different goal — chaos is about failure modes, not capacity)
- Production debugging (chaos discovers weaknesses preemptively, not after-the-fact)

## Core principle: chaos without abort criteria is an outage

The 4 Principles of Chaos Engineering (Netflix, 2016):

1. **Build a hypothesis around steady-state behavior.** Not "what breaks?" but "X holds; will it still hold under fault Y?"
2. **Vary real-world events.** Inject realistic failures: kill nodes, slow networks, lose cache, throttle dependencies.
3. **Run experiments in production.** Staging never has the same failure modes. Start small.
4. **Automate experiments to run continuously.** One-off chaos is a press release; continuous chaos is engineering.

Add a fifth: **Define abort criteria up front.** A chaos experiment with no abort criteria is an outage by another name.

## Quick start

```bash
SKILL=engineering/chaos-engineering/skills/chaos-engineering

# 1. Design an experiment
python "$SKILL/scripts/experiment_designer.py" --target "checkout-svc" --hypothesis "p99 latency stays <500ms" --attack latency --duration-min 15

# 2. Calculate blast radius
python "$SKILL/scripts/blast_radius_calculator.py" --traffic-share 0.05 --user-pop 1000000 --duration-min 15

# 3. Generate postmortem after the experiment
python "$SKILL/scripts/experiment_postmortem.py" --plan experiment.json --result-log results.txt
```

## The 3 Python tools

All stdlib-only. Run with `--help`.

### `experiment_designer.py`

Generates a structured experiment plan from inputs. Enforces the required sections (hypothesis, steady-state metric, blast radius, abort criteria, rollback).

```bash
python scripts/experiment_designer.py \
  --target "checkout-svc" \
  --hypothesis "p99 latency stays <500ms when payment-svc is slow" \
  --attack latency \
  --magnitude "+200ms" \
  --duration-min 15 \
  --blast-radius "5% of US traffic" \
  --abort-if "p99 > 1000ms OR error_rate > baseline + 1pp"
```

Outputs a markdown plan with: hypothesis, steady-state, attack, magnitude, duration, blast radius, abort criteria, rollback procedure, monitoring dashboards, and learning question.

### `blast_radius_calculator.py`

Computes the blast radius of a planned experiment. Given traffic share + user population + duration, calculates expected affected users, expected error budget burn, and a risk score.

```bash
python scripts/blast_radius_calculator.py \
  --traffic-share 0.05 \
  --user-pop 1000000 \
  --duration-min 15 \
  --baseline-availability 0.999 \
  --expected-impact-availability 0.95
```

Outputs:
- Expected affected users
- Error budget consumed (in minutes of error budget)
- Risk score: GREEN / YELLOW / RED
- Recommendation: PROCEED / REDUCE / ABORT

GREEN = <1% error budget; YELLOW = 1-10%; RED = >10%.

### `experiment_postmortem.py`

Produces a structured postmortem from an experiment plan + results. Catches the common postmortem failure modes: no learning recorded, no follow-up actions, blame-laden language.

```bash
python scripts/experiment_postmortem.py --plan experiment.json --result-log results.txt
```

Outputs markdown with: summary, hypothesis (was it confirmed/refuted?), what we learned, what surprised us, follow-up actions with owners, and link to next experiment.

## The 7 attack types (taxonomy)

Different attacks reveal different weaknesses. See `references/attack_taxonomy.md` for full detail.

| Attack | What it tests | Tooling |
|---|---|---|
| **Latency** | Timeouts, retries, circuit breakers | tc, Chaos Mesh `NetworkChaos` |
| **Error** | Error handling, fallback paths | Chaos Mesh `HTTPChaos`, Toxiproxy |
| **Resource** (CPU, memory, disk) | Saturation handling, autoscaling | Chaos Mesh `StressChaos`, stress-ng |
| **Network partition** | Split-brain, consensus, failover | Chaos Mesh `NetworkChaos` partition |
| **Dependency failure** | Graceful degradation, fallback | Service mesh fault injection |
| **Time** | Clock skew, NTP issues | libfaketime, Chaos Mesh `TimeChaos` |
| **Infrastructure** (kill instance) | Auto-recovery, failover | AWS FIS, Chaos Monkey |

Pick the attack that matches the hypothesis. "What happens if X is slow?" → latency. "What happens if X loses network?" → partition.

## Tooling chooser

| Tool | Best for | Pricing | Stack |
|---|---|---|---|
| **Chaos Toolkit** | Lightweight, language-agnostic, JSON experiments | OSS | Any |
| **Chaos Mesh** | Kubernetes-native, rich CRDs, in-cluster | OSS | Kubernetes |
| **Litmus** | Kubernetes, Argo-integrated, large library | OSS + Enterprise | Kubernetes |
| **Gremlin** | Enterprise SaaS, multi-cloud, audit | Paid | Any |
| **AWS FIS** | AWS-native, IAM-integrated, EC2/ECS/EKS | Paid (AWS) | AWS |
| **Custom** | Niche needs, single-cloud, low budget | None | Any |

Decision rules:
- k8s-only stack + OSS → Chaos Mesh or Litmus (Litmus has bigger experiment library)
- Multi-cloud + OSS → Chaos Toolkit
- AWS-heavy + simple needs → AWS FIS
- Enterprise + audit/compliance → Gremlin

See `references/tooling_landscape.md` for trade-offs.

## Workflows

### Workflow 1: Design and run a single experiment

```
1. State a hypothesis: "When [fault], steady-state metric X stays within Y."
2. Identify the steady-state metric — must be measurable BEFORE the experiment.
3. Run blast_radius_calculator.py — confirm GREEN before proceeding.
4. Run experiment_designer.py to produce the plan.
5. Get a peer review of the plan; confirm abort criteria are concrete.
6. Notify the on-call team in #incidents (or whatever channel).
7. Run the experiment with monitoring open.
8. If abort criteria are hit, abort immediately; record what happened.
9. Run experiment_postmortem.py to capture learnings.
10. File follow-up actions; link to next experiment.
```

### Workflow 2: Game Day exercise

```
1. Pick a scenario (e.g., "primary database fails over").
2. Identify all dependent services that should keep working.
3. Build a multi-experiment plan covering each layer.
4. Schedule with stakeholders; on-call coverage required.
5. Run with a facilitator who manages the scenario.
6. Capture observations in a shared doc as they happen.
7. Single combined postmortem covering all observations.
8. Track follow-up actions in a board with owners.
```

### Workflow 3: Continuous chaos (game days → daily)

```
1. Start: weekly Game Day in staging.
2. Move to: weekly Game Day in production with limited blast radius.
3. Mature to: continuous chaos via scheduled experiments (Litmus chaos schedule, Gremlin scenarios).
4. Wire to deployment: every prod deploy triggers a baseline chaos sweep.
5. Track: experiments per week, weaknesses discovered, MTTR trend.
```

## Composition with other skills

This skill explicitly composes with two others in this library:

| Skill | Composition |
|---|---|
| `feature-flags-architect` | Kill switches defined there are the abort triggers here |
| `kubernetes-operator` | Operators are common chaos targets (test reconcile under fault) |
| `incident-response` | Chaos experiments that escalate become incidents |

## Anti-patterns

- **No hypothesis** — "let's break things" is sabotage, not engineering
- **No steady-state metric** — without a baseline, you can't tell if X broke
- **No blast radius bound** — full-prod experiment without limits = outage
- **No abort criteria** — see above; this is mandatory
- **No on-call coverage** — chaos without monitoring is unmonitored production
- **Chaos in staging only** — staging never has prod failure modes
- **Chaos in dev** — useless; dev has different failure modes from prod
- **One-off chaos** — single experiment is a press release; learning requires recurrence
- **Blame-laden postmortem** — record causes, not blame; teams stop running chaos otherwise

## References

- `references/chaos_principles.md` — the 4 principles, history, when to start
- `references/experiment_design.md` — hypothesis structure, steady-state metrics, abort criteria
- `references/attack_taxonomy.md` — 7 attack types with examples and tooling
- `references/tooling_landscape.md` — Chaos Toolkit / Mesh / Litmus / Gremlin / FIS / DIY

## Slash command

`/chaos-experiment` — interactive experiment design wizard that runs all 3 tools.

## Asset templates

- `assets/experiment_template.md` — fill-in plan template
- `assets/postmortem_template.md` — structured postmortem template

## Verifiable success

A team using this skill should achieve:

- 100% of chaos experiments have a written hypothesis, abort criteria, and blast-radius calculation
- Blast radius for any single experiment never exceeds 10% of error budget
- Mean time between chaos experiments <14 days (continuous, not one-off)
- Each experiment produces ≥1 follow-up action that gets shipped
- No chaos experiment escalates to a customer-impacting incident in trailing 90 days

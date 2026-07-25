# Decision & Intake Guide

The workflow-builder skill opens **every** session with intake. This file is the full framework behind that gate: the questions to ask, how to handle vague answers, and worked examples of turning a fuzzy request into a concrete proposal.

## Why intake comes first

A workflow's whole value is deterministic, resumable, fixed-topology orchestration. The topology is a *design decision* that must be made before any code — choosing pipeline vs. parallel, known-list vs. loop, or whether a step needs structured output changes the entire file. Asking first is cheaper than rewriting. It also catches the most common mistake: building a workflow when a single agent or a skill would do.

## The opening question set

Ask these at the start of a workflow-creation session. Lead with #1; the rest sharpen the shape.

1. **What repeatable, multi-step task do you want to automate?** (the goal)
2. **What is the one unit of work** a single sub-agent does once? (e.g., "review one file", "research one question")
3. **How many units** — a known list, or discovered by looping until some condition?
4. **Do later steps need *all* prior results at once** (dedup/merge/count), or can each item flow independently?
5. **Does any step need structured data back** — a verdict, a list, scores?
6. **How deep / how many tokens** should this go? (sets the budget guard)

Map answers → topology:

| Signal | Topology |
|--------|----------|
| Independent units, known list, combine at end | **fan-out → synthesize** (`parallel` + final `agent`) |
| Ordered stages, each item advances on its own | **pipeline** |
| A stage needs the whole prior set (dedup/merge/early-exit) | **barrier** (`parallel`, then process) |
| Unknown count, stop on goal / budget / dryness | **loop** (guarded) |
| Wide solution space, want best-of-N | **judge panel** |
| A wrong result is costly | add **skeptic-vote** verification on that finding |

## The vague-input playbook

When the user gives a one-liner ("I want to review my PRs") or skips the topology questions, **do not interrogate them in a loop.** Infer, propose, and explain. Run:

```bash
python scripts/workflow_intake.py --task "review my open PRs for bugs" \
  --units unknown --stages unknown --needs-all unknown --structured unknown
```

The engine classifies the task by keywords, fills unknowns with the safest default, and returns:
- a **recommended topology** (and a runner-up if it's close),
- **model picks** per stage (Haiku for triage/extraction, Opus for synthesis),
- a **budget guard** suggestion,
- a **one-line rationale for every choice** so you can present "here's what I'd build and why."

Then say, in your own words: *"You were light on detail, so here's the approach I'd recommend and why — tell me what to change."* Present the topology, the phases, and the parallel-vs-pipeline call. Only after the user reacts do you scaffold.

### Defaults the engine applies to unknowns (and why)

| Unknown | Default | Why |
|---------|---------|-----|
| unit count | loop with a hard cap | safest when count is undiscovered; cap prevents the 1000-agent ceiling |
| stages | single stage unless the task names a verb chain | most fuzzy asks are one-pass fan-outs, not pipelines |
| needs-all-results | no (prefer pipeline) | pipeline is strictly faster and the default per the API; only add a barrier on evidence |
| structured output | yes, lightweight schema | a small schema makes downstream stages reliable at near-zero cost |
| budget | guard at `remaining() > 50k` | keeps runaway loops from draining the turn |

## Worked examples

**"Review my PRs."**
Unit = one PR (a known list, gathered inside the first agent). Each PR is reviewed once, independently. Wrong result costly = yes (a false positive wastes review time, a miss ships a bug). → **fan-out** (one review per PR, Haiku, structured findings) → **skeptic-vote** on each high-severity finding (Sonnet) → a final synthesis. If you want a distinct *verify* pass after review, split it into a two-stage **pipeline** instead. Rationale handed to the user: fan-out because PRs are independent; skeptic-vote because acting on a false positive is costly.

**"Summarize a folder of documents."**
Unit = one document. Count = known list (the folder contents, gathered inside the first agent). Combine at end = yes. → **fan-out** (Haiku per doc, structured summary) → **synthesize** (Opus, one report). No loop, no barrier mid-stream. Rationale: documents are independent, so parallel; one final synthesis because the user wants a single summary.

**"Find security issues until you run out of budget."**
Unit = one issue. Count = unknown, budget-bounded. → **loop-until-budget** guarded by `budget.remaining() > 50_000`, structured issue schema, dedup by id. Rationale: depth scales to the token target; the guard is mandatory or it hits the agent cap.

## When to walk away from a workflow

If intake reveals a single agent and one task, say so and recommend the plain Agent tool. If it's a procedure where Claude should pick steps dynamically rather than a fixed topology, recommend a Skill instead. Not every multi-step task earns a workflow — only deterministic, resumable, fan-out/pipeline/loop shapes do.

---

## Sources

1. Ray Amjad — `claude-code-workflow-creator`, `SKILL.md` (the five topology questions, tool-selection table).
2. Anthropic — Claude Code documentation on when to use workflows vs. agents vs. skills.
3. Matt Pocock — `grill-me` skill (forcing-question, one-recommendation-at-a-time intake discipline).
4. Anthropic — sub-agent context-isolation rationale (why topology is a pre-code decision).
5. Google SRE Workbook — budget-guard discipline for bounded loops.
6. "LLM-as-a-judge" + ensemble verification literature (judge-panel / skeptic-vote selection).
7. YC / product-discovery practice — infer-and-propose over interrogate-in-a-loop for vague requests.

---
name: product-research
description: Use when planning and synthesizing product/user research as a method-and-repository discipline — selecting the right method for the goal (generative interviews vs usability test vs concept test vs validation), computing method-based saturation/sample size with an explicit confidence level, or synthesizing coded observations into insights while flagging single-source anecdotes. Never fabricates user insight; an insight requires recurrence across independent participants. Distinct from product-team/ux-researcher-designer (persona/journey artifacts), product-discovery (discovery-sprint planning), and experiment-designer (live A/B) — this is the research-ops method + insight-repository layer.
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [research-ops, product-research, ux-research, jtbd, usability, saturation, insight-synthesis, research-repository]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# product-research

Product / user research as an operational discipline: choosing the right method, sizing it honestly, and synthesizing findings into governed insights. The core rule: **method must match the goal**, and **an insight requires recurrence across independent participants** — a single quote is an anecdote.

## Purpose

Product researchers, ResearchOps teams, and PMs running discovery need method rigor and an insight repository they can trust. This skill structures three decisions:

Three deterministic tools:

1. `study_designer.py` — Maps (research goal × product stage) to an appropriate method and emits a method-matched plan skeleton (objective, participant criteria, guide structure, success criteria). Redirects live A/B to `product-team/experiment-designer`.
2. `saturation_planner.py` — Method-based sample guidance with an explicit **confidence label**: Nielsen problem-discovery (5/segment), Guest et al. thematic saturation (~12), and evaluative coverage. Never claims a prevalence rate from a small-n usability test.
3. `insight_synthesizer.py` — Clusters coded observations by tag, counts distinct participants, ranks by cross-participant recurrence, and flags any candidate below the source threshold as an **ANECDOTE**, never promoting it to an insight.

## When to use

Invoke this skill when:

- You are planning a study and need the method to match the goal (generative vs evaluative vs validation).
- You need a defensible sample size / saturation rationale with a stated confidence.
- You have raw coded observations and need to synthesize insights without over-claiming.
- You are setting up or auditing a research repository and need the insight-vs-observation discipline.

**Do NOT use this skill to**: generate personas / journey maps (use `product-team/ux-researcher-designer`), plan a discovery sprint or validate an opportunity (use `product-team/product-discovery`), design or analyze a live product A/B experiment (use `product-team/experiment-designer`), or do market sizing / surveys (use the `market-research` sibling).

## Workflow

1. **Frame the study** — Fill `assets/research_plan_template.md` (research questions, method rationale, participant criteria, analysis plan, repository tagging scheme).
2. **Pick the method** — Run `study_designer.py --goal {discovery|evaluative|validation} --stage {concept|prototype|beta|live} --profile {b2b-saas|consumer-app|enterprise|marketplace|hardware|platform}`. Honor the redirect if it routes to experiment-designer.
3. **Size it** — Run `saturation_planner.py --method {usability|thematic|evaluative-coverage} --segments N`. Record the confidence label and limits.
4. **Synthesize** — After fielding, code observations and run `insight_synthesizer.py --input observations.json --min-sources 3`. Treat ANECDOTE-flagged clusters as signals to probe, not findings to ship.
5. **File in the repository** — Tag insights to the atomic schema at synthesis time, with their evidence and confidence.

## Scripts

| Script | Purpose | Profiles |
|---|---|---|
| `scripts/study_designer.py` | (goal × stage) → method + plan skeleton | b2b-saas, consumer-app, enterprise, marketplace, hardware, platform |
| `scripts/saturation_planner.py` | Method-based sample guidance + confidence | n/a (method-driven) |
| `scripts/insight_synthesizer.py` | Cluster observations, flag anecdotes | n/a (evidence-driven) |

All three: stdlib-only, `--help`, `--sample`, `--output {human,json}`.

## Onboarding & customization

Run the onboarding questionnaire **once before you start** — it captures your defaults so every tool in this skill is pre-configured. Customization is the point: the answers actually change tool behavior (e.g. the insight source-threshold).

```bash
python3 scripts/onboard.py            # interactive (also: --defaults, --set key=value, --reset)
python3 scripts/onboard.py --show     # see the questions + current effective config
```

Answers are saved to `~/.config/research-ops/product-research.json` (global) or `./.research-ops/product-research.json` (`--scope project`) and are read automatically by `config_loader.py`. They set the default product **profile**, the **insight source-threshold** (how many independent participants make a finding an insight, not an anecdote), the default **saturation method**, and the **high-stakes** flag. CLI flags always override saved config; `RESEARCH_OPS_NO_CONFIG=1` ignores it.

**The four questions:** product profile · insight source-threshold · saturation method · high-stakes flag.

## Optimize with autoresearch (opt-in)

This skill ships an **isolated, opt-in** bridge to `engineering/autoresearch-agent`. Only when you ask to "optimize the synthesis" / "run a loop" does an autoresearch experiment iteratively refine the coding/clustering of a fixed evidence set so more cross-participant patterns surface. `scripts/ar_evaluator.py` is the ground-truth evaluator; it prints `validated_insights: <int>` (higher is better). It optimizes the **coding**, never fabricates evidence.

```bash
/ar:setup --domain custom --name insight-synthesis \
  --target observations.json \
  --eval "python3 ar_evaluator.py --target observations.json" \
  --metric validated_insights --direction higher
/ar:loop custom/insight-synthesis
```

Isolated: no hard dependency — autoresearch runs only on demand, and the loop edits `observations.json`, never the evaluator.

## References

- `references/research_methods_canon.md` — Portigal *Interviewing Users*; Christensen/Ulwick JTBD; Rohrer's UX-research methods landscape (NN/g); Sauro & Lewis *Quantifying the User Experience*; Goodman/Kuniavsky.
- `references/sampling_and_saturation.md` — Nielsen "test with 5 users"; Guest, Bunce & Johnson saturation; Faulkner on more-than-5; Sauro usability sample size; Braun & Clarke thematic analysis.
- `references/repository_and_synthesis.md` — ResearchOps / atomic research (Tomer Sharon "Polaris"); insight-vs-observation discipline; repository governance; affinity mapping; democratization guardrails.

## Assumptions

- Method selection assumes you can name the goal honestly; if the goal is fuzzy, grill it first (the goal drives everything).
- Saturation guidance is method-based, not a power calculation — usability tests find problems, not prevalence rates.
- The synthesizer counts evidence you provide; coding quality is upstream of it. Garbage tags → garbage clusters.
- The insight threshold (`--min-sources`) defaults to 3; raise it for high-stakes or heterogeneous populations.

## Anti-patterns

- **Mismatching method to goal.** A usability test cannot discover unmet needs; an interview cannot measure task success.
- **Reporting usability problems as percentages.** Small-n tests surface problems, not population rates.
- **Promoting an anecdote to an insight.** One participant is a signal to probe, not a finding.
- **Framing interview questions as feature reactions.** Probe the job-to-be-done and recent real behavior, not hypothetical opinions.
- **Synthesizing without a repository scheme.** Tag at synthesis time, or insights rot unfindable.

## Distinct from

| Neighbor | Scope | Difference |
|---|---|---|
| `product-team/ux-researcher-designer` | Personas, journey maps, usability frameworks tied to design output | That produces **artifacts**; this is **method + repository discipline** |
| `product-team/product-discovery` | Opportunity validation, discovery-sprint planning | That plans **discovery sprints**; this designs and synthesizes the **research** |
| `product-team/experiment-designer` | Live product A/B hypothesis + sample size | That runs **live experiments**; this runs **qualitative/evaluative research** |
| `market-research` (sibling) | Market sizing, surveys, segmentation | That studies **the market**; this studies **users** |

## Quick examples

```bash
python3 scripts/study_designer.py --sample
python3 scripts/saturation_planner.py --method thematic --segments 3
python3 scripts/insight_synthesizer.py --sample --min-sources 3
```

The synthesizer sample correctly promotes "import-confusion" (3 independent participants) to INSIGHT and flags "wants-slack" (1 participant) as an ANECDOTE.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-research-ops` or the orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"Is this study generative (discover problems) or evaluative (test a solution)?"**
   Recommended: name it first — the method follows from the goal.
   Canon: Rohrer, *When to Use Which User-Experience Research Methods* (NN/g).

2. **"What's your sample size and saturation rationale — and at what confidence?"**
   Recommended: method-based n (5/segment usability; ~12 for thematic saturation), state the confidence.
   Canon: Nielsen; Guest, Bunce & Johnson (2006); Faulkner (2003).

3. **"How many independent participants support each insight — or is it a single-source anecdote?"**
   Recommended: require recurrence across ≥3 sources before calling it an insight; flag singletons.
   Canon: atomic research / ResearchOps; Braun & Clarke thematic analysis.

4. **"Are your interview / usability tasks framed as outcomes (jobs) or as feature reactions?"**
   Recommended: frame around the job-to-be-done and recent real behavior, not hypothetical opinion.
   Canon: Christensen/Ulwick Jobs-to-be-Done; Portigal *Interviewing Users*.

5. **"Where does this land in the repository, and how is it tagged for reuse?"**
   Recommended: tag to the atomic schema at synthesis time, not later.
   Canon: Tomer Sharon, *Polaris* / ResearchOps repository practice.

Walk depth-first. Lock 1-2 before opening 3-5. After all are answered, invoke `study_designer.py` → `saturation_planner.py` → (after fielding) `insight_synthesizer.py`.

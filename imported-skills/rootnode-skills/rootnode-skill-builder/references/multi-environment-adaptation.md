# Multi-Environment Adaptation

The procedural depth for the Tier A / Tier B / Tier C operational model. SKILL.md routes the workflow when a Skill spans multiple execution environments (chat-side, code-side, Cowork sessions); this reference carries the per-environment compatibility matrix, per-script tier mappings, fallback patterns, and the detection logic that determines tier applicability at build time.

Canonical methodology source: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.12` (the surface-invariant principle) and `root_SKILL_BUILD_DISCIPLINE.md §10` (the operational discipline applied to Skill builds).

---

## The tier model

Three tiers, ordered by strength of empirical infrastructure available:

- **Tier A — full empirical pipeline.** Subagent execution available; runnable Skill environment available; tooling layer (`scripts/`, `agents/`) invocable. Strongest empirical evidence per workflow.
- **Tier B — empirical execution without subagents.** Runnable environment available; subagents not available. Moderate evidence — observed behavior under realistic prompts, qualitative review.
- **Tier C — analytical floor.** Neither subagents nor a runnable environment. Reasoning grounded in documented Claude tendencies and the Skill's countermeasure formulation.

The tiers are degradation paths, not parallel options. A build CV applies the strongest tier the environment supports. Lower tiers remain available as per-step fallbacks when individual evaluation steps fail infrastructurally.

## Compatibility matrix

This matrix names which evaluation surfaces support which tiers in current rootnode practice. Skills that may run across these surfaces consult the matrix to determine tier applicability for their workflows.

| Surface | Subagent execution | Runnable env | Tooling layer invocable | Default tier |
|---|---|---|---|---|
| Claude Code (CC) | Yes (Task tool) | Yes (Bash, file system) | Yes | Tier A |
| Claude.ai chat | Limited (single response per turn; no Task subagents) | Limited (Code Interpreter beta in some contexts) | Limited | Tier B or C |
| Cowork | Yes | Yes | Yes | Tier A |
| Custom orchestrators | Variable | Variable | Variable | Determine per orchestrator |
| Claude.ai Project (CP) — design conversation | No | No | No | Tier C |
| Hand-invoked methodology review | No | No | No | Tier C |

Skills that may run across multiple surfaces declare per-workflow tier compatibility in their methodology (typically in SKILL.md routing surfaces and in this reference's per-script section below).

## Per-script tier compatibility

For Skills with executable `scripts/` content, this table maps each script's tier requirements:

| Script | Tier A | Tier B | Tier C | Notes |
|---|---|---|---|---|
| `description_optimizer.py` | ✓ Full automated train/test loop | Manual walkthrough fallback (`references/description-optimization.md` §"Manual walkthrough") | Manual walkthrough only | Requires `claude -p` execution and stream-event monitoring |
| `aggregate_benchmark.py` | ✓ Aggregates grader subagent outputs | — | — | Tier A only — depends on grader subagent JSON output |
| `quick_validate.py` | ✓ Validates D1 spec compliance | ✓ Same — pure file inspection | ✓ Same — pure file inspection | Tier A/B/C compatible; no environment dependency |
| `package_zip.py` | ✓ Packages deployable zip | ✓ Same | ✓ Same | Tier A/B/C compatible; no environment dependency |
| `generate_report.py` | ✓ HTML report from optimizer output | — | — | Tier A capability — consumes optimizer JSON |
| `utils.py` | ✓ Shared utility (parse_skill_md) | ✓ Same | ✓ Same | Tier A/B/C compatible; library code |
| `__init__.py` | n/a | n/a | n/a | Empty package marker |

For Skills with `agents/` content:

| Subagent | Tier A | Tier B | Tier C | Notes |
|---|---|---|---|---|
| `grader.md` | ✓ Subagent-isolated grading | Inline qualitative review (build CV grades manually) | n/a (no execution to grade) | Subagent execution required for isolation |
| `comparator.md` | ✓ Blind subagent comparison | Inline blind comparison with discipline (`references/version-comparison.md` §"Inline procedure") | Deferred — no execution surface | Subagent isolation prevents bias |
| `analyzer.md` | ✓ Post-hoc subagent analysis | Inline post-hoc analysis | Deferred | Reads winner/loser Skills with verdict in hand |

For Skills with `eval-viewer/` content (Tier A only — requires Python + browser):

| File | Tier A | Tier B | Tier C |
|---|---|---|---|
| `generate_review.py` | ✓ HTTP-served review interface | — | — |
| `viewer.html` | ✓ Loaded by generator | — | — |

## Tier determination

The build CV determines tier applicability at build time, not at design time. Decision rule:

```
if (subagent_execution_available and runnable_env_available):
    tier = "A"
elif runnable_env_available:
    tier = "B"
else:
    tier = "C"
```

The build CV records the determination explicitly in the build summary — which tier was selected and why. A build CV cannot claim Tier A evidence when Tier A infrastructure was unavailable.

**Detection patterns:**

- **Subagent execution available** if the build CV is running in CC with Task tool access OR in Cowork with subagent dispatch.
- **Runnable env available** if Bash or Code Interpreter is available in the conversation.
- **Tooling layer invocable** if the Skill's `scripts/`, `agents/`, and `eval-viewer/` directories are accessible from the runnable environment (typical when the Skill is installed in `~/.claude/skills/` or accessible via the project's working tree).

When detection is ambiguous (e.g., a Code Interpreter session with limited persistence), the conservative determination is the lower tier. Pretending capabilities the environment lacks produces unauditable verdicts; the discipline is "use the strongest tier the environment supports, no more."

## Fallback patterns

Each tier has explicit fallback to the next lower tier when an evaluation step fails infrastructurally. Fallbacks are per-step, not per-build — a build can run most of D9 at Tier A and fall back to Tier B for one scenario without dropping the whole verdict.

**Tier A → Tier B fallback (per step):**

- Subagent grader timeout exceeds budget → reattempt with extended budget; if still failing, fall back to inline qualitative review for that scenario.
- Subagent comparator returns malformed JSON → fall back to inline blind comparison for that comparison.
- `description_optimizer.py` run fails on a specific iteration → revert to the prior iteration's revision and continue with manual review.

**Tier B → Tier C fallback (per step):**

- Test prompt execution fails (subprocess error, Claude API failure) → fall back to analytical reasoning for that scenario.
- The runnable env loses access mid-build → record observations from the runs that completed; fall back to analytical for the remaining scenarios.

**Verdict accounting:** When fallbacks fire, the build summary records both the headline tier (the strongest tier the environment supported) and any per-step fallbacks. Future audits can trace the evidentiary basis at the granularity it was produced.

**Anti-pattern:** silent fallback. A build that runs Tier A for some steps and Tier C for others without recording the per-step fallback produces a verdict that cannot be audited. The discipline is to record the actual evidence basis, not the headline ambition.

## Skill authoring discipline

When authoring a Skill that may run across multiple environments, apply the following discipline:

### Declare per-workflow tier compatibility

In SKILL.md, every workflow that depends on environment-specific capabilities names which tier(s) it supports. A workflow that requires Tier A is unavailable in Tier B/C; the SKILL.md routes the user accordingly. A workflow that supports all tiers documents the per-tier procedure (typically: Tier A invokes a script; Tier B falls back to manual procedure; Tier C falls back to analytical reasoning).

### Make environment-dependent steps explicit

Procedural depth in references documents per-step environment dependencies. A step that requires subagent execution is flagged as Tier A only; a step that requires file-system access is flagged as Tier A/B; a step that is pure reasoning is flagged as Tier A/B/C compatible. The flagging is mechanical — a reader scanning the reference can tell which steps are conditional on environment.

### Provide fallback paths

For every Tier A step, document the Tier B fallback. For every Tier B step, document the Tier C fallback. Fallbacks are not degraded automations; they are different evidentiary forms. The discipline is to make the fallback as credible as the primary path within its evidentiary class.

### Compatibility matrix as artifact

For Skills with significant environment variability, include a per-script or per-workflow compatibility matrix in this reference (or a per-Skill equivalent). The matrix is the artifact future audits and future evolution cycles read to understand the Skill's environmental assumptions; without it, environmental couplings are implicit and brittle.

## Pattern library — common environment-dependency patterns

These patterns recur across Skills with executable layers. Document them once at the methodology layer; reference them from per-Skill matrices.

### Pattern: subagent grading vs. inline grading

- **Tier A:** Invoke a grader subagent with rubric assertions; subagent returns structured JSON; methodology layer parses verdicts.
- **Tier B:** Build CV grades manually against the same rubric; captures the verdict in equivalent JSON format for downstream consistency.
- **Tier C:** No execution to grade; deferred or analytical.

### Pattern: automated description optimization vs. manual walkthrough

- **Tier A:** `description_optimizer.py` runs the train/test loop with stream-event triggering detection.
- **Tier B:** Build CV runs `claude -p` queries manually (or scripts that don't need subagents) and inspects activation; falls back to manual walkthrough for full corpus.
- **Tier C:** Build CV walks the corpus mentally against the description.

### Pattern: blind comparison vs. inline comparison

- **Tier A:** Comparator subagent runs in isolation with stripped identifiers; analyzer subagent reads winner/loser Skills with verdict in hand.
- **Tier B:** Build CV applies identifier-leak prevention (random label assignment, paths sanitized) and walks the rubric inline; post-hoc analysis runs inline.
- **Tier C:** Deferred — no execution surface for the comparison.

### Pattern: HTML report generation vs. JSON inspection

- **Tier A:** `generate_report.py` produces a static HTML report from optimizer/grader JSON; `eval-viewer/generate_review.py` produces an interactive multi-run review.
- **Tier B:** Build CV inspects the JSON output directly; reports are produced post-hoc from disk.
- **Tier C:** No execution to report on; not applicable.

## Detection: when am I in which tier?

Practical signals the build CV uses to determine its current tier:

- **Tier A signals:** The build CV is running inside Claude Code with the Task tool available; Bash tool is available; `scripts/` and `agents/` directories of the Skill being built or evaluated are accessible from the working tree.
- **Tier B signals:** Bash or equivalent runnable env is available, but Task subagent dispatch returns errors or is not in the available tool list; `scripts/` may or may not be accessible.
- **Tier C signals:** No execution surface; the build CV is running in a chat-side conversation or a methodology review session.

When in doubt, the conservative choice is the lower tier. A Tier B build CV that incorrectly claims Tier A produces verdicts that cannot be reproduced; a Tier A build CV that conservatively records Tier B underclaims but produces credible verdicts.

## What this reference does not do

This reference does not specify the per-workflow procedures for behavioral validation, description optimization, or version comparison. Those live in their respective references (`references/behavioral-validation.md`, `references/description-optimization.md`, `references/version-comparison.md`). This reference covers the cross-cutting environment-adaptation concern.

This reference does not specify the surface-invariant principle that grounds the discipline — that lives in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.12`. This reference operationalizes the principle for Skill builds.

This reference does not specify the canonical operational discipline applied to Skill builds — that lives in `root_SKILL_BUILD_DISCIPLINE.md §10`. This reference is the per-Skill application layer with tables and pattern library.

---

*End of multi-environment-adaptation.md.*

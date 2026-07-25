# Description Optimization

The procedural depth for description refinement — the methodology that hardens a Skill's `description` field against under-triggering and over-triggering through evidence-based iteration. SKILL.md routes the workflow; this reference carries the trigger eval generation procedure, schemas, train/test split methodology, the triggering detection mechanism, and the description improvement prompt structure.

Canonical methodology source: `root_SKILL_BUILD_DISCIPLINE.md §9` (Description refinement loop discipline).

---

## Why this is the highest-leverage workflow

The 1024-character description field is the auto-activation index entry. Every other Skill discipline — pre-build gates, the 9-dimension quality gate, methodology preservation, behavioral validation — runs against a Skill that the user can actually reach. A description that fails to trigger renders all of it inert. The Skill exists, the methodology is sound, and the user never invokes it because Claude does not load a Skill whose description does not match the query.

A description that under-triggers leaks 30–60% of the Skill's potential value (the explicit-vocabulary users find it; the symptom-phrased users do not). A description that over-triggers pollutes the auto-activation index for adjacent Skills and produces routing collisions. The refinement loop addresses both failure modes through the same mechanism: walk a corpus of realistic queries, measure trigger behavior, revise, repeat.

---

## Trigger eval generation

The trigger eval corpus is the primary input to the refinement loop. Corpus quality bounds verdict quality.

**Composition:**

- 8–12 should-trigger queries (positive set)
- 5–8 should-not-trigger queries (negative set)
- 2–4 edge-case queries

**Realism principles** (full discipline in `references/auto-activation-discipline.md`):

- Match user voice: incomplete sentences, casual register, contractions, copy-paste-adjacent phrasing.
- Mix explicit triggers (Skill's vocabulary), symptom-phrased triggers (problem language), and implicit/context-laden triggers (intent without naming the Skill).
- Negative set covers adjacent-Skill territory and generic distractors.
- Edge cases force the description to make a defensible call; record the intended verdict per case.

The same corpus serves behavioral validation in D9b/D9c (`references/behavioral-validation.md`). Generating one corpus serves both — this is intentional, not duplication.

---

## Eval query schema

The trigger eval format used by `scripts/description_optimizer.py`:

```json
[
  {
    "query": "build a skill from this design spec",
    "should_trigger": true
  },
  {
    "query": "score this prompt",
    "should_trigger": false
  },
  {
    "query": "I have a design spec, what's next?",
    "should_trigger": true
  }
]
```

**Fields:**

- `query` (string): the user query, in realistic user voice.
- `should_trigger` (boolean): whether the Skill should auto-activate on this query (`true` = positive set; `false` = negative set / distractor).

For edge cases, set `should_trigger` to the intended verdict. Iteration outcomes are measured against the intended verdict, not against an objectively correct answer.

The schema is preserved verbatim per the content-class policy (`root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.10` and `root_SKILL_BUILD_DISCIPLINE.md §7`). Paraphrasing the field names breaks the optimizer's input contract.

---

## Triggering detection mechanism

The mechanism by which the optimizer decides whether a given query triggered the Skill. This is the verbatim port from the upstream skill-creator (Anthropic, 2026) — the structural details determine whether the optimizer produces correct verdicts, so the mechanism is preserved exactly.

### How it works

The optimizer invokes `claude -p` with the query and `--output-format stream-json --include-partial-messages`. Stream events from the model arrive line-by-line as JSON. The optimizer monitors the stream for the trigger signal:

1. **`content_block_start` event with `tool_use` type.** When the model starts a tool call, the stream emits a `content_block_start` event with `type: stream_event` and a nested `content_block` whose `type` is `tool_use`. The tool's `name` field identifies which tool is being invoked.
2. **Tool name `"Skill"` or `"Read"`.** The platform invokes a Skill by either calling the `Skill` tool (preferred) or by reading the SKILL.md file directly (legacy path). Both signal triggering. Other tool names indicate the Skill did NOT trigger — the model decided to handle the query without it.
3. **Accumulated JSON contains the unique Skill name.** Once `content_block_start` is observed, subsequent `content_block_delta` events carry `input_json_delta` chunks that accumulate into the tool's input. When the accumulated JSON contains the Skill's unique identifier (a deterministic name with a UUID suffix, generated per-query), the trigger is confirmed.

### Why this is the only ground-truth source

Manual inspection of conversational output cannot reliably distinguish between:

- Skill triggered, Skill instructions executed → output matches Skill behavior.
- Skill did NOT trigger, model produced output similar to what the Skill would have produced → output looks the same but the Skill never fired.

The stream-event signal is the only ground-truth source. Refinement loops that score by output similarity rather than by trigger-event detection produce false positives (the model produced Skill-like output without triggering) and false negatives (the Skill triggered but the output didn't visibly differ from the model's default behavior).

### Why a unique Skill name per query

The optimizer creates a temporary command file in `.claude/commands/` with a unique name (e.g., `skill-builder-skill-a1b2c3d4`) and tests against that. This isolates the test from production Skills (which may have conflicting names) and prevents cached activation from prior sessions interfering with the run.

The unique name is matched against the accumulated tool-input JSON. A match means the platform invoked the test Skill specifically; a non-match means the platform invoked a different Skill or no Skill.

### Default trigger threshold

The optimizer runs each query multiple times (default: 3 runs per query) to account for non-determinism in activation. The trigger rate is `triggered_runs / total_runs`. Default threshold: 0.5.

- For should-trigger queries: PASS if trigger_rate ≥ 0.5; FAIL otherwise.
- For should-not-trigger queries: PASS if trigger_rate < 0.5; FAIL otherwise.

---

## Manual walkthrough (Tier B/C)

The simplest form of the refinement loop. Available in any environment because it requires no execution.

**Procedure:**

1. Read the current description aloud, paying attention to the verbs, nouns, and trigger phrases.
2. Walk each query in the trigger eval corpus against the description. For each query, reason: would Claude, seeing this description in its system prompt, route this query to this Skill?
3. Note misses (should-trigger queries the description would not match) and false positives (should-not-trigger queries the description would match anyway).
4. Refine the description to address the gaps. Common refinements: add a symptom-phrased trigger; tighten a negative trigger; replace a passive verb with an active one; add an implicit trigger that catches a context-laden query.
5. Re-walk the corpus. Re-note gaps. Repeat until the corpus stabilizes.

**When to stop:** All should-trigger queries trigger; no should-not-trigger queries trigger; edge-case verdicts match the build CV's intended verdicts.

**Why this is the floor, not a degraded automation:** Manual reasoning grounded in the 50-description competition test (per `references/auto-activation-discipline.md`) produces credible verdicts when no execution is available. The walkthrough is not a degraded version of the optimizer; it is a different evidentiary form. The optimizer mechanizes; the walkthrough reasons.

---

## Automated optimization via `description_optimizer.py` (Tier A)

When subagents and runnable execution are available, the refinement loop runs as an automated 5-iteration train/test optimization.

**Procedure:**

1. **Split the corpus** into train and test sets. Default split: 60/40 or 70/30 depending on corpus size.
2. **Score the baseline.** Run the current description against both the train set and the test set. Capture trigger rates per query and aggregate pass-rates per set.
3. **Generate a revised description.** Invoke an improvement subagent with the current description, the train-set results, and the failure modes observed. The subagent returns a revised description that addresses the train-set misses without obviously over-fitting (the improvement prompt structure is documented below).
4. **Score the revision** against the train set and the held-out test set.
5. **Decide.** If test-set score improved, the revision is the new candidate. If train-set improved but test-set degraded, the revision is overfit — discard and revert to the prior iteration.
6. **Iterate.** Repeat steps 3–5 for up to N iterations (default: 5). Select the revision with the highest test-set score across iterations.

**Output:** Per-iteration train/test scores, the final revised description, and a generated HTML report (via `scripts/generate_report.py`) showing the per-query results with check/x marks for fast review.

The optimizer is invoked from the build CV when Tier A applies; from the operator after a v1 ships when description tuning is needed; from continuous evaluation runs when the deployment surface changes. The methodology layer (this reference and SBD §9) is the same regardless of invocation context.

---

## Description improvement prompt structure

The improvement subagent receives a structured prompt with the current description, the train-set results, and instructions to revise. The prompt structure is preserved from the upstream source — paraphrasing the structure breaks compatibility with future evolution and with the cross-Skill contract that future Skills with description-optimization workflows will share.

**Prompt components:**

- **Current description:** the description string under iteration.
- **Train-set evaluation results:** for each train query, the query text, the expected trigger verdict, the observed trigger rate, and pass/fail.
- **Failure mode summary:** aggregated misses (should-trigger queries the description failed to trigger on) and false positives (should-not-trigger queries the description triggered on inappropriately).
- **Revision instructions:** revise the description to address the failure modes; preserve the spec compliance constraints (≤1024 chars YAML-parsed, no XML angle brackets, kebab-case names); maintain the description's existing verb-based trigger language.
- **Anti-overfitting framing:** emphasize that the test set is held out and that the revised description will be scored against queries not visible during revision; do not over-fit to the train queries.

The subagent returns a revised description as plain text. The optimizer parses, validates against the spec compliance constraints, and proceeds to scoring.

---

## Train/test split methodology

The split is the structural feature that makes overfitting detectable. Without it, the description is gradually bent toward the corpus shape, and the Skill triggers reliably on the corpus while degrading on out-of-corpus queries that share the underlying intent.

**Split mechanics:**

- **Random split per iteration's setup.** The split is random but reproducible (seed-based) so iteration is comparable across runs.
- **Stratified by category.** Should-trigger, should-not-trigger, and edge-case queries are split proportionally — both train and test sets have a representative mix of the three categories. Stratification prevents a split where the train set is all should-trigger and the test set is all should-not-trigger (or vice versa), which would produce uninterpretable iteration results.
- **Held-out from revision.** The improvement subagent receives only the train-set results; the test set is not part of the revision prompt. The test set's only role is scoring.

**Selection rule:**

- Primary: highest test-set pass rate across all iterations.
- Tiebreaker: highest train-set pass rate (uses the train signal as secondary evidence when test-set scores are equal).
- Final tiebreaker: the earliest iteration meeting the tied scores (Occam's razor — simpler revision is preferred).

**Divergence threshold:**

- If train-set and test-set scores diverge by more than ~15 percentage points in a given iteration, the iteration is flagged as overfit and excluded from selection.

---

## Anti-overfitting principle

A description revision that scores 100% on the train set but degrades on the held-out test set has overfit — the revision learned the train corpus's idiosyncrasies (specific vocabulary, specific phrasing patterns, specific edge-case alignments) rather than the underlying user-intent pattern. The Skill triggers reliably on the corpus and fails in production on out-of-corpus queries.

**The discipline:**

- Treat the held-out test set as the primary signal. Train-set wins are supportive evidence only.
- Watch for divergence. A test-set score that drops while train-set climbs is the canonical overfit signature.
- Discard overfit revisions. The prior iteration is preferred when divergence exceeds the threshold.

**Why this is methodology-grade, not implementation detail:**

- The split discipline prevents an entire class of failure mode (production triggers on a brittle corpus).
- The principle generalizes — any future build CV that produces a description benefits from the same iteration shape.
- The discipline lives at the methodology layer (`root_SKILL_BUILD_DISCIPLINE.md §9`) so future Skills can cite it without re-deriving.

---

## How triggering actually works (platform behavior)

A practical note for build CVs running the loop manually or interpreting optimizer output:

- **The description is the activation surface.** Claude sees the description in its system prompt for every conversation; the SKILL.md body is invisible at activation time.
- **Activation is probabilistic.** The same query may trigger or not trigger across runs; multiple-run averaging (default: 3 runs per query) accounts for this.
- **Activation context matters.** Conversation history, prior tool calls, user-stated preferences, and other Skills loaded all affect activation. The optimizer tests in a clean context (fresh `claude -p` invocation per query) to isolate the description's effect from contextual signals.
- **Description length affects activation precision, not strength.** A 1023-character description does not trigger more reliably than a 600-character one. Length matters insofar as it accommodates the trigger phrases needed to cover the activation surface.
- **Auto-invocation defaults to ON.** `disable-model-invocation: true` opts out of auto-activation entirely. When set, the description's trigger language is irrelevant — the Skill loads only on explicit user request.

---

## Tooling integration

When Tier A is available, the build CV invokes:

- `scripts/description_optimizer.py` — the automated 5-iteration train/test loop.
- `scripts/generate_report.py` — produces a static HTML report from the optimizer's output, showing per-iteration train/test results with check/x marks for fast review.

When Tier B applies, the build CV runs the manual walkthrough (no scripts).

When Tier C applies, the build CV runs the manual walkthrough (no execution surface for the corpus; reasoning only).

---

## What this reference does not do

This reference does not specify the description-writing principles (verb structure, trigger phrase patterns, length budgeting) — that lives in `references/auto-activation-discipline.md`. The realism principles for the corpus also live there.

This reference does not specify the behavioral validation procedure that uses the same corpus for D9 verdicts — that lives in `references/behavioral-validation.md`.

This reference does not implement the optimizer; the implementation is in `scripts/description_optimizer.py`. The reference describes what the script does and why, so the build CV can interpret its output and make iteration decisions; the script's source is the implementation contract.

---

*End of description-optimization.md.*

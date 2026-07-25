# Behavioral Validation

The procedural depth for D9 — Behavioral validation — and the empirical evidence tiers (D9a / D9b / D9c) introduced in v3.0. SKILL.md routes the workflow; this reference carries the procedure, schemas, grader principles, and iteration-loop mechanics.

Canonical methodology source: `root_SKILL_BUILD_DISCIPLINE.md §3.9` (the dimension definition with sub-levels) and `§10` (the environment-adaptive degradation discipline that determines tier applicability).

---

## Table of contents

1. Why D9 has sub-levels
2. Tier determination
3. D9a — Empirical Tier A procedure
4. D9b — Empirical Tier B procedure
5. D9c — Analytical procedure
6. Skip condition
7. Test prompt generation
8. Grader subagent design principles (verbatim)
9. Eval schema (verbatim)
10. Grading schema (verbatim)
11. Iteration loop
12. Anti-overfitting framing
13. Tooling integration
14. What this reference does not do

---

## 1. Why D9 has sub-levels

D9 was a single-tier RECOMMENDED dimension in v2.1 — the build CV either documented a pressure scenario with credible failure expectation, or marked the dimension SKIPPED for reference-only Skills. v3.0 expands D9 into three sub-levels because validation infrastructure differs across build environments. A build CV running with subagent execution available should not be limited to documenting analytical reasoning when it could run an actual empirical comparison; conversely, a build CV running in a chat-side surface without execution should not be forced into a hard halt because empirical comparison is infeasible.

The three sub-levels reflect strength of evidence:

- **D9a (strongest):** Empirical with-Skill vs. without-Skill comparison via subagent grader. Requires subagents and runnable execution.
- **D9b (moderate):** Empirical with-Skill execution under realistic test prompts; qualitative review without baseline. Requires runnable execution; subagents not required.
- **D9c (weakest, valid floor):** Analytical reasoning grounded in the 10-tendency taxonomy and the Skill's countermeasure formulation. No infrastructure required.

The build summary records which sub-level was applied. Future audits read the verdict format and the cited evidence to reconstruct the evidentiary basis. D9 remains classified RECOMMENDED, not REQUIRED — Skills that pass D1–D8 but lack D9 validation are still shippable.

## 2. Tier determination

The build CV determines tier applicability at build time, not at design time. Decision rule per `root_SKILL_BUILD_DISCIPLINE.md §10.4`:

1. Subagent execution available AND runnable environment available → **Tier A** applies.
2. Runnable environment available, subagents NOT available → **Tier B** applies.
3. Neither available → **Tier C** applies.

A build CV cannot claim Tier A evidence when Tier A infrastructure was unavailable; the discipline is "use the strongest tier the environment supports, no more." See `references/multi-environment-adaptation.md` for the full operational model.

## 3. D9a — Empirical Tier A procedure

**Goal:** Demonstrate that the Skill measurably improves outcomes on representative scenarios versus a baseline without it.

**Procedure:**

1. **Prepare the trigger eval set.** Generate a corpus of realistic test prompts per §7 below. Use the same corpus for description refinement and for behavioral validation — generating one corpus serves both dimensions.
2. **Run the GREEN configuration.** Execute the trigger eval set against an environment with the Skill loaded. Capture transcripts and outputs per eval.
3. **Run the RED configuration.** Execute the same trigger eval set against an environment without the Skill loaded (subagent without the Skill in scope). Capture transcripts and outputs per eval.
4. **Grade both runs.** Invoke the grader subagent (`agents/grader.md`) with each run's outputs and the rubric assertions. The grader produces structured JSON per the grading schema (§10).
5. **Compute the differential.** For each rubric assertion, compare GREEN pass-rate against RED pass-rate. Material improvement on the assertions the Skill is designed to enforce is the empirical evidence.
6. **Capture in the build summary** as `D9: Tier A — empirical comparison (N scenarios, GREEN/RED differential = X%)`. Cite the run directories, the grader outputs, and the differential analysis.

**Pass condition:** GREEN/RED differential is materially positive on assertions the Skill is designed to enforce. "Material" means more than chance — pre-defined threshold per scenario (typical: ≥20 percentage points improvement).

**Halt condition:** GREEN/RED differential is zero or negative on the Skill's core assertions. The Skill does not produce the behavior it claims; rebuild or rescope before shipping.

## 4. D9b — Empirical Tier B procedure

**Goal:** Confirm the Skill's auto-activation and procedural compliance under realistic queries; rely on qualitative review rather than baseline comparison.

**Procedure:**

1. **Prepare the trigger eval set** per §7 below.
2. **Load the Skill into the runnable environment.** Install via the deployment path used for end-users (e.g., `~/.claude/skills/`).
3. **Execute the trigger eval set.** Run each prompt; capture the activation signal (did the Skill trigger?) and the output.
4. **Qualitative review.** Walk each run against the Skill's stated quality criteria. Note compliance failures (the Skill triggered but did not produce expected behavior), activation failures (the Skill did not trigger when it should have), and over-trigger cases.
5. **Capture in the build summary** as `D9: Tier B — empirical execution (N test prompts, qualitative compliance: pass/fail)`. Cite the test prompts, observed activation, and review verdict.

**Pass condition:** Auto-activation observed on should-trigger prompts; observed behavior matches stated quality criteria; no over-trigger on should-not-trigger prompts.

**Halt condition:** Auto-activation fails on multiple should-trigger prompts (description issue — re-run description refinement loop); behavior fails to match stated criteria (methodology issue — revise SKILL.md content).

## 5. D9c — Analytical procedure

**Goal:** Reason about whether the Skill addresses a documented Claude behavioral tendency and whether the countermeasure formulation is credible without empirical execution.

**Procedure:**

1. **Document the pressure scenario.** Describe a scenario where Claude, without the Skill loaded, would produce incorrect behavior the Skill is designed to prevent. The scenario targets the Skill's core discipline.
2. **Identify the underlying tendency.** Cite the specific tendency from the 10-tendency taxonomy (`root_OPTIMIZATION_REFERENCE.md`) or production-observed failure modes. The expected without-Skill failure must be grounded in documented tendency, not asserted.
3. **Map the countermeasure.** Show the reasoning chain: tendency → countermeasure → expected compliance. The Skill's formulation must address the identified tendency directly. If the formulation does not match the tendency, the Skill is solving a different problem than the one documented.
4. **Capture in the build summary** as `D9: Tier C — analytical (tendency: <name>, countermeasure: <mechanism>)`. Cite the scenario, the tendency, the countermeasure, and the reasoning chain.

**Pass condition:** Pressure scenario is concrete (not generic); tendency is cited from the canonical taxonomy or production evidence; countermeasure formulation aligns with the tendency.

**Halt condition:** Scenario is generic or speculative; tendency citation is missing or inferred; countermeasure does not address the cited tendency.

This was the v2.1 D9 pass standard. v3.0 keeps it as the analytical floor — when the build environment cannot support D9a or D9b, D9c is the discipline floor that prevents unsupported D9 claims.

## 6. Skip condition

The Skill is reference-only, data-carrying, or configuration-driven — it has no behavioral compliance to test. Examples: context-carrier Skills, profile schemas, block libraries used by other Skills as catalogs.

Mark as `D9: SKIPPED — no behavioral compliance surface` with one-sentence justification. The skip applies regardless of which sub-level the build environment otherwise supports — a Skill that has no behavioral surface to test does not get D9 evidence by virtue of available infrastructure.

## 7. Test prompt generation

The trigger eval corpus serves both D9a/D9b empirical validation and the description refinement loop (`references/description-optimization.md`). Generating one corpus serves both. The corpus generation discipline is shared across the two references; this section covers what behavioral validation specifically needs.

**Corpus composition** (also see `references/auto-activation-discipline.md` for the full realism principles):

- 8–12 should-trigger queries (positive set), mixing explicit, symptom-phrased, and context-laden patterns.
- 5–8 should-not-trigger queries (negative set), covering adjacent Skill territory and generic distractors.
- 2–4 edge-case queries with the build CV's intended verdict per case.

**Behavioral-validation specific additions:**

- For each should-trigger query, define the **expected behavior** the Skill should produce. This is the rubric assertion the grader will check (D9a) or the qualitative criterion the build CV will review (D9b).
- For at least one should-trigger query, define the **adversarial twist** — a phrasing that would tempt Claude to skip the Skill's discipline (e.g., user phrases the request casually so the model might rationalize a lighter-weight approach). The adversarial twist tests whether the Skill's countermeasure holds under pressure.

The corpus is the primary input to D9a's grader subagent and to D9b's qualitative review. Corpus quality compounds: a weak corpus produces weak verdicts regardless of execution tier.

## 8. Grader subagent design principles (verbatim)

The grader subagent's design principles are preserved verbatim from the upstream skill-creator source (Anthropic, 2026). These principles shape what makes a graded outcome trustworthy.

**Two jobs.** The grader has two responsibilities: grade the outputs, and critique the evals themselves. A passing grade on a weak assertion is worse than useless — it creates false confidence. When the grader notices an assertion that is trivially satisfied, or an important outcome that no assertion checks, it surfaces the gap.

**Pass criterion.** PASS when the transcript or outputs clearly demonstrate the expectation is true; specific evidence can be cited; the evidence reflects genuine substance, not just surface compliance (a file exists AND contains correct content, not just the right filename).

**Fail criterion.** FAIL when no evidence is found; evidence contradicts the expectation; the expectation cannot be verified from available information; the evidence is superficial — the assertion is technically satisfied but the underlying task outcome is wrong or incomplete; the output appears to meet the assertion by coincidence rather than by actually doing the work.

**Burden of proof.** When uncertain, the burden of proof to pass is on the expectation, not on the grader. An ambiguous case fails by default.

**No partial credit.** Each expectation is pass or fail, not partial. Partial credit dilutes the verdict and makes inter-run comparison unreliable.

**Eval critique discipline.** The grader surfaces evaluation suggestions only when there is a clear gap. Worth raising: an assertion that passed but would also pass for a clearly wrong output (filename without content); an important outcome the grader observed that no assertion covers; an assertion that cannot be verified from available outputs. Keep the bar high — flag what the eval author would say "good catch" about, not nitpicks.

**Objectivity discipline.** Be objective: base verdicts on evidence, not assumptions. Be specific: quote the exact text supporting the verdict. Be thorough: check both transcript and output files. Be consistent: apply the same standard to each expectation. Explain failures: make clear why evidence was insufficient.

These principles are canonicalized verbatim from the skill-creator source per the content-class policy in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md` (schemas and structural design principles preserve verbatim across ports).

## 9. Eval schema (verbatim)

Verbatim from the upstream skill-creator schema for `evals/evals.json`. The schema defines the trigger eval set used by D9a/D9b.

```json
{
  "skill_name": "example-skill",
  "evals": [
    {
      "id": 1,
      "prompt": "User's example prompt",
      "expected_output": "Description of expected result",
      "files": ["evals/files/sample1.pdf"],
      "expectations": [
        "The output includes X",
        "The skill used script Y"
      ]
    }
  ]
}
```

**Fields:**

- `skill_name`: Name matching the skill's frontmatter
- `evals[].id`: Unique integer identifier
- `evals[].prompt`: The task to execute
- `evals[].expected_output`: Human-readable description of success
- `evals[].files`: Optional list of input file paths (relative to skill root)
- `evals[].expectations`: List of verifiable statements

The schema is an interface contract — the grader subagent and the description optimizer both read this format. Paraphrasing breaks compatibility with the upstream tooling and with future evolution. Preserve verbatim.

## 10. Grading schema (verbatim)

Verbatim from the upstream skill-creator schema for grader output (`<run-dir>/grading.json`).

```json
{
  "expectations": [
    {
      "text": "The output includes the name 'John Smith'",
      "passed": true,
      "evidence": "Found in transcript Step 3: 'Extracted names: John Smith, Sarah Johnson'"
    },
    {
      "text": "The spreadsheet has a SUM formula in cell B10",
      "passed": false,
      "evidence": "No spreadsheet was created. The output was a text file."
    }
  ],
  "summary": {
    "passed": 2,
    "failed": 1,
    "total": 3,
    "pass_rate": 0.67
  },
  "execution_metrics": {
    "tool_calls": {
      "Read": 5,
      "Write": 2,
      "Bash": 8
    },
    "total_tool_calls": 15,
    "total_steps": 6,
    "errors_encountered": 0,
    "output_chars": 12450,
    "transcript_chars": 3200
  },
  "timing": {
    "executor_duration_seconds": 165.0,
    "grader_duration_seconds": 26.0,
    "total_duration_seconds": 191.0
  },
  "claims": [
    {
      "claim": "The form has 12 fillable fields",
      "type": "factual",
      "verified": true,
      "evidence": "Counted 12 fields in field_info.json"
    }
  ],
  "user_notes_summary": {
    "uncertainties": ["Used 2023 data, may be stale"],
    "needs_review": [],
    "workarounds": ["Fell back to text overlay for non-fillable fields"]
  },
  "eval_feedback": {
    "suggestions": [
      {
        "assertion": "The output includes the name 'John Smith'",
        "reason": "A hallucinated document that mentions the name would also pass"
      }
    ],
    "overall": "Assertions check presence but not correctness."
  }
}
```

**Field reference:** see `agents/grader.md` for the per-field documentation. The schema is preserved verbatim from the upstream source per the content-class policy — paraphrasing the field names or structure breaks the grader's output contract.

## 11. Iteration loop

Behavioral validation produces verdicts; verdicts inform iteration. The iteration loop tightens the Skill against observed gaps.

**Single-iteration loop (any tier):**

1. Run validation (D9a / D9b / D9c per tier).
2. Identify gaps from the verdict — assertions that failed, behaviors that diverged from criteria, scenarios where the analytical reasoning chain breaks down.
3. Revise the Skill content to address the gaps. Common revisions: tighten an instruction that was ambiguous; add a step that the model skipped; rewrite a recommendation that used imperative-without-rationale where reasoned voice would land better; add an example that targets the failure mode.
4. Re-run validation against the same corpus.
5. Compare verdicts. Did the revision improve the failure modes without introducing new ones?

**Stopping condition:** The verdict matches the Skill's stated quality criteria. Further iteration produces marginal improvement at increasing cost.

**Anti-pattern:** Iterating against a single corpus without a held-out set leads to overfitting (§12). The corpus split discipline applies whether iteration is automated (Tier A via scripts) or manual (Tier B/C).

## 12. Anti-overfitting framing

A description or methodology revision that scores 100% on the train corpus but degrades on a held-out test corpus has overfit — the revision learned the train corpus's idiosyncrasies rather than the underlying user-intent or behavioral pattern.

**The discipline:**

- Split the trigger eval corpus into a train set (drives revisions) and a held-out test set (scores each iteration without bleeding into the revision signal). Typical split: 60/40 or 70/30, depending on corpus size.
- Evaluate every revision against the held-out test set as the primary signal. Train-set wins are supportive evidence only.
- If train-set and test-set scores diverge by more than ~15 percentage points, the revision is likely overfit and should be discarded in favor of the prior iteration.

**Why the held-out set works:** Without the split, every iteration sees every query, the description (or methodology) is gradually bent toward the corpus shape, and the Skill triggers reliably on the corpus while degrading on out-of-corpus queries that share the underlying intent. The split makes overfitting detectable; without it, overfitting is invisible until the Skill ships and fails in production.

## 13. Tooling integration

When Tier A is available, the build CV invokes the executable layer:

- `scripts/description_optimizer.py` for automated description refinement (covered in `references/description-optimization.md`).
- `scripts/aggregate_benchmark.py` for cross-run benchmark aggregation when validation runs many configurations.
- `agents/grader.md` invoked via the Task tool to grade each run's output.
- `agents/comparator.md` and `agents/analyzer.md` invoked when running version comparison alongside behavioral validation (see `references/version-comparison.md`).
- `eval-viewer/` invoked when the operator wants an interactive view of run outcomes (`scripts/generate_report.py` for static per-iteration reports; `eval-viewer/generate_review.py` for the interactive HTTP-served multi-run review).

When Tier B is available but not Tier A, the build CV runs scripts that do not require subagent execution (e.g., `quick_validate.py` for D1, format-validation utilities); the grader/comparator/analyzer agents are not invoked. Tier C uses no tooling — analytical reasoning only.

## 14. What this reference does not do

This reference does not specify the trigger eval generation procedure in detail — that lives in `references/auto-activation-discipline.md` (realism principles) and `references/description-optimization.md` (full procedure including train/test split mechanics, the eval query schema applied to triggering, and the automated optimizer's iteration mechanics).

This reference does not specify the per-environment fallback procedures — that lives in `references/multi-environment-adaptation.md` (the operational tier model).

This reference does not specify the version-comparison procedure (blind A/B with comparator + analyzer). That lives in `references/version-comparison.md`.

This reference does not duplicate the canonical methodology layer. The canonical D9 dimension and sub-level definitions live in `root_SKILL_BUILD_DISCIPLINE.md §3.9`. This reference applies that methodology to the build CV's procedural work.

---

*End of behavioral-validation.md.*

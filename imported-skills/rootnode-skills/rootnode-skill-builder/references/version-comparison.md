# Version Comparison

The procedural depth for blind A/B comparison between two Skill versions. SKILL.md routes the workflow when the build CV needs to determine whether a successor revision actually improves on the predecessor; this reference carries the rubric, the subagent invocation pattern, the inline fallback procedure, and the identifier-leak prevention discipline.

---

## When to use

Blind A/B comparison is warranted when:

- A successor revision has been built and the build CV needs evidence that it improves on the predecessor before shipping.
- A description optimizer iteration produced a revised description and the build CV wants to verify the revision improves end-to-end Skill behavior, not just trigger rates.
- The methodology layer changed in a v2.x → v2.x release (e.g., new reference file added, new instruction inlined) and the build CV wants empirical confirmation the change helps.
- A reviewer wants to disentangle which of two methodology approaches produces better outcomes without reading both Skills directly (judgment is bounded by the rubric, not by reviewer preferences).

## When to skip

Skip blind comparison when:

- The successor and predecessor have no common evaluation surface (e.g., the workflow scope changed between versions).
- The change is purely structural (refactor, file rename, no behavioral implication). Comparison would produce a tie or no signal.
- The change is to non-behavioral content (audit metadata, provenance fields, versioning frontmatter). No behavioral surface to test.
- Tier A is unavailable AND inline blind comparison would require operator effort exceeding the change's value. In Tier C environments, version comparison is typically deferred to a future cycle when execution becomes available.

## Modes

Two operational modes:

- **Subagent mode (Tier A):** The blind comparator subagent (`agents/comparator.md`) and post-hoc analyzer subagent (`agents/analyzer.md`) run as Task subagents. Outputs flow back as structured JSON. The methodology layer interprets the results.
- **Inline mode (Tier B/C fallback):** The build CV walks the rubric inline against the two outputs without subagent isolation. Identifier-leak prevention requires extra discipline; results are still credible but rely on operator judgment rather than isolated grading.

## Blind comparison rubric (verbatim)

The rubric is preserved verbatim from the upstream skill-creator source per the content-class policy. Paraphrasing the rubric breaks the contract with the comparator subagent and with future Skills that adopt the same comparison framework.

### Content Rubric (what the output contains)

| Criterion | 1 (Poor) | 3 (Acceptable) | 5 (Excellent) |
|-----------|----------|----------------|---------------|
| Correctness | Major errors | Minor errors | Fully correct |
| Completeness | Missing key elements | Mostly complete | All elements present |
| Accuracy | Significant inaccuracies | Minor inaccuracies | Accurate throughout |

### Structure Rubric (how the output is organized)

| Criterion | 1 (Poor) | 3 (Acceptable) | 5 (Excellent) |
|-----------|----------|----------------|---------------|
| Organization | Disorganized | Reasonably organized | Clear, logical structure |
| Formatting | Inconsistent/broken | Mostly consistent | Professional, polished |
| Usability | Difficult to use | Usable with effort | Easy to use |

### Adapting the rubric to the task

The criteria adapt to the specific task being evaluated. Examples:

- PDF form output → "Field alignment", "Text readability", "Data placement"
- Document output → "Section structure", "Heading hierarchy", "Paragraph flow"
- Data output → "Schema correctness", "Data types", "Completeness"

The two-dimension structure (Content + Structure) is preserved across adaptations. The criteria within each dimension are tuned to the task; the dimensions themselves are the contract.

### Scoring

For each output (A and B):

- Score each criterion on the 1–5 scale.
- Calculate dimension totals: `content_score` (mean of content criteria), `structure_score` (mean of structure criteria).
- Calculate overall score: average of dimension scores, scaled to 1–10.

Compare A and B based on overall score; assertion pass rates (if expectations are provided) serve as secondary evidence; a tie is declared only if outputs are genuinely equivalent (rare).

## Subagent procedure (Tier A)

The blind comparator subagent runs in isolated context with no information about which Skill produced which output. The methodology layer invokes it via the Task tool:

1. **Prepare both outputs.** Run the same eval prompt against the predecessor Skill and the successor Skill. Capture each Skill's output in a separate directory.
2. **Strip identifiers from the outputs.** Remove or rename any Skill-specific markers in the output paths and filenames before passing to the comparator. The comparator must not be able to infer which Skill produced which output (see §"Identifier leak prevention" below).
3. **Invoke the comparator subagent** (`agents/comparator.md`) with the two output paths labeled A and B, the eval prompt, and the expectation list (if applicable).
4. **The comparator returns structured JSON** per the comparator schema: `winner` ("A", "B", or "TIE"), `reasoning`, `rubric` scores per output, `output_quality` summary, and `expectation_results` if expectations were provided.
5. **Invoke the post-hoc analyzer subagent** (`agents/analyzer.md`) with the comparator's verdict and the now-unblinded skill paths. The analyzer reads both Skills' SKILL.md and transcripts to determine WHY the winner won, generating actionable improvement suggestions for the loser.
6. **Capture the verdict** in the build summary as `Version comparison: <winner> (overall_score: <A_score>/<B_score>; assertion pass rates: <A_pass>/<B_pass>)` with citation to the comparator and analyzer outputs.

The subagent isolation is the load-bearing feature. The comparator's judgment is bounded by the rubric and the outputs alone; it cannot rationalize a verdict based on which Skill it "should" prefer.

## Inline procedure (Tier B/C)

When subagents are unavailable, the build CV runs the comparison inline. The procedure mirrors the subagent flow but with the build CV applying the rubric directly.

1. **Prepare both outputs** as in the subagent procedure.
2. **Apply identifier-leak prevention** more rigorously than the subagent path requires (see below). The build CV's awareness of which output came from which Skill is itself an identifier leak; the discipline is to walk the rubric without consulting that knowledge.
3. **Score each output against the rubric.** Walk the content criteria, then the structure criteria. Capture each criterion's 1–5 score with one-sentence justification. Compute dimension scores and overall score.
4. **Determine the winner** based on overall score; record the reasoning citing specific output features.
5. **Post-hoc analysis (if warranted).** With the verdict in hand, the build CV reads both Skills' SKILL.md and transcripts, identifies what the winner did differently, and writes improvement suggestions for the loser. This step requires the build CV to suspend its prior judgment about either Skill — the rubric verdict is the anchor.
6. **Capture the verdict** in the build summary as `Version comparison (inline): <winner> ...` with the reasoning chain and the rubric scores.

Inline mode produces credible verdicts when the build CV applies the discipline rigorously. The verdict is more likely to drift toward a preferred Skill than the subagent verdict; the build CV records the inline mode explicitly so future audits know the verdict was unblinded judgment rather than isolated grading.

## Analyzer output (verbatim)

The post-hoc analyzer subagent's output schema is preserved verbatim from the upstream source. The schema is the contract between the analyzer and any downstream consumer (typically the build CV's improvement-suggestion review).

```json
{
  "comparison_summary": {
    "winner": "A",
    "winner_skill": "path/to/winner/skill",
    "loser_skill": "path/to/loser/skill",
    "comparator_reasoning": "Brief summary of why comparator chose winner"
  },
  "winner_strengths": [
    "Clear step-by-step instructions for handling multi-page documents",
    "Included validation script that caught formatting errors"
  ],
  "loser_weaknesses": [
    "Vague instruction 'process the document appropriately' led to inconsistent behavior",
    "No script for validation, agent had to improvise"
  ],
  "instruction_following": {
    "winner": {
      "score": 9,
      "issues": ["Minor: skipped optional logging step"]
    },
    "loser": {
      "score": 6,
      "issues": [
        "Did not use the skill's formatting template",
        "Invented own approach instead of following step 3"
      ]
    }
  },
  "improvement_suggestions": [
    {
      "priority": "high",
      "category": "instructions",
      "suggestion": "Replace 'process the document appropriately' with explicit steps",
      "expected_impact": "Would eliminate ambiguity that caused inconsistent behavior"
    }
  ],
  "transcript_insights": {
    "winner_execution_pattern": "Read skill -> Followed 5-step process -> Used validation script",
    "loser_execution_pattern": "Read skill -> Unclear on approach -> Tried 3 different methods"
  }
}
```

**Field reference:** see `agents/analyzer.md` for per-field documentation. The schema is preserved verbatim — paraphrasing the field names breaks the contract with downstream consumers and with future Skills that share the comparison framework.

**Improvement suggestion categories** (verbatim taxonomy):

| Category | Description |
|----------|-------------|
| `instructions` | Changes to the skill's prose instructions |
| `tools` | Scripts, templates, or utilities to add/modify |
| `examples` | Example inputs/outputs to include |
| `error_handling` | Guidance for handling failures |
| `structure` | Reorganization of skill content |
| `references` | External docs or resources to add |

**Priority levels:**

- `high`: Would likely change the outcome of this comparison
- `medium`: Would improve quality but may not change win/loss
- `low`: Nice to have, marginal improvement

## Identifier leak prevention

Blinding is the load-bearing discipline of comparison. If the comparator (subagent or build CV) knows which output came from which Skill, the verdict is biased — toward the Skill the comparator prefers, against the Skill the comparator considers experimental, or simply toward whichever Skill the comparator inferred from contextual cues. Even unconscious bias measurably affects rubric scores.

**Per-output blinding:**

- Strip Skill-specific filename markers. Output filenames like `predecessor_output_form.pdf` and `successor_output_form.pdf` leak the verdict directly. Rename to `output_a.pdf` and `output_b.pdf` (or randomize the labels per run).
- Strip directory paths that contain Skill names. The comparator should not know the parent directory is `rootnode-skill-builder-v2.1/runs/eval-3/` because the version is in the path.
- Strip embedded metadata. Some output formats embed creator metadata or timestamps. Sanitize before comparison.
- Randomize the A/B label assignment per run. The first run might label predecessor as A; the next might label predecessor as B. The comparator's verdict is recorded as A/B; the labeling is unblinded only after the verdict is captured.

**Per-procedure blinding:**

- The comparator subagent receives the prompt with output paths already labeled A and B. The subagent has no access to the Skill folders themselves during comparison — only after the verdict is captured does the analyzer read the Skill content (with the verdict already recorded).
- For inline mode, the build CV uses a randomized label-to-Skill mapping written to a file before walking the rubric. The build CV reads only the labeled outputs during scoring; the mapping file is opened only after the verdict is captured.

**Anti-pattern:** scoring "with awareness of which Skill is which, but trying to be fair." Operator awareness is itself a leak. The discipline forces the operator's judgment to be bounded by the rubric, not by prior beliefs about either Skill.

## Tooling integration

When Tier A applies, the build CV invokes:

- `agents/comparator.md` via Task subagent for the blind comparison.
- `agents/analyzer.md` via Task subagent for the post-hoc analysis.
- `scripts/aggregate_benchmark.py` when running comparison across multiple eval prompts (aggregates per-prompt results into a benchmark report).

When Tier B/C applies, the build CV runs the inline procedure described above; no scripts or agents are invoked.

## What this reference does not do

This reference does not specify behavioral validation (the with-Skill vs. without-Skill comparison that produces D9a evidence) — that lives in `references/behavioral-validation.md`. Behavioral validation tests whether the Skill works at all; version comparison tests whether one Skill works better than another.

This reference does not specify the description refinement loop (description-only iteration on a single Skill) — that lives in `references/description-optimization.md`. Description optimization revises the description without revising methodology; version comparison evaluates two Skill versions with potentially different methodology.

This reference does not implement the rubric scoring algorithm; the implementation is in `agents/comparator.md`. The reference describes the rubric and the procedure; the subagent is the executable contract.

---

*End of version-comparison.md.*

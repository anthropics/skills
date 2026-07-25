# Diagnostic Flow

The full three-step methodology for diagnosing why a prompt's output is not meeting expectations. Use this when Scorecard or Rubric scores reveal a problem and you need to identify the responsible layer before making changes.

**When to consult this file:** After scoring a prompt with the Scorecard (Step 1 in the main Skill) or evaluating output with the Rubric (Step 2), when you need to trace a specific weakness to its root cause before recommending a fix.

---

## Table of Contents

1. [Step 1: Identify the Gap](#step-1-identify-the-gap)
2. [Step 2: Locate the Layer](#step-2-locate-the-layer)
3. [Step 3: Verify Before Fixing](#step-3-verify-before-fixing)
4. [The Refinement Sequence](#the-refinement-sequence)
5. [Refine vs. Rebuild Decision](#refine-vs-rebuild-decision)

---

## Step 1: Identify the Gap

Before diagnosing, name the problem precisely. "The output isn't good" is not a diagnosis. Answer these questions:

**What did you expect the output to look like?** Be specific — expected length, structure, depth, tone, level of specificity.

**What did the output actually look like?** Where exactly does it diverge from expectations?

**Is the gap about substance or form?**
- Substance problems (wrong content, shallow analysis, missed points) → trace to Layers 1-4.
- Form problems (wrong structure, wrong tone, wrong length) → trace to Layer 5.

---

## Step 2: Locate the Layer

Work through these checks in order. Stop at the first layer where you find the problem — fixing a downstream layer will not help if an upstream layer is the root cause.

### Layer 1 — Identity Check

Does the output read like it was written by the right expert? If a strategic analysis reads like a generic overview, or a technical design reads like a blog post, the identity section is either missing, too vague, or mismatched to the task.

**Test:** Cover the identity section and read the output cold — could you guess what role Claude was playing? If not, the identity is not doing its job.

### Layer 2 — Objective Check

Does the output answer the right question? If the output is well-written but addresses a different question than intended, the objective is ambiguous.

**Test:** Could two people read this objective and produce substantially different outputs? If yes, the objective needs sharpening.

**Common failure:** The objective describes a topic ("analyze our marketing strategy") rather than a task with success criteria ("identify the three highest-leverage changes to increase qualified leads within 90 days").

### Layer 3 — Context Check

Is the output specific to the situation, or could it apply to any similar organization? If the analysis is generic — advice you could find in a textbook — the context is either missing or too thin. The depth of context directly predicts the specificity of output.

**Test:** Does the output reference specific details from the context (numbers, constraints, prior decisions), or does it stay at the category level ("mid-size companies often face...")?

### Layer 4 — Reasoning Check

Is the analysis deep enough? If the output states conclusions without adequate supporting analysis, or feels shallow — listing obvious points without surfacing non-obvious insights — the reasoning guidance is either missing, generic, or mismatched to the task type.

**Test:** Does the output show evidence of structured thinking (assumptions tested, alternatives considered, tradeoffs identified), or does it jump from problem statement to conclusion?

### Layer 5 — Output Check

Is the format and structure what you needed? If the substance is correct but the packaging is wrong — too long, wrong sections, bullets instead of prose, missing a critical section — the output specification needs adjustment. This is the easiest layer to fix and the least likely to be the root cause of substantive problems.

### Quality Control Check

Is the output undermined by a specific behavioral failure? If the output agrees with a flawed premise, hedges excessively, pads to fill length, or includes unrequested sections, the prompt is missing targeted countermeasures for the relevant Claude tendency.

Claude's most common behavioral tendencies that require countermeasures:
- **Agreeableness:** Executes flawed requests without challenging the premise.
- **Hedging:** Adds excessive caveats and qualifications, especially on analytical tasks.
- **Verbosity:** Pads output beyond what the task requires.
- **List overuse:** Converts narrative explanations into bullet points by default.

Each tendency has specific countermeasure language. See `symptom-fix-map.md` for targeted fixes per symptom.

---

## Step 3: Verify Before Fixing

Before changing the prompt, confirm your diagnosis: "If I fix this layer, would the output improve in the way I expect?"

If not confident, run the prompt once more with the same input to check consistency.

**Consistent problem:** The prompt has a structural issue at the identified layer. Fix it.

**Intermittent problem:** Harder to fix with prompt changes. This may indicate:
- A task at the boundary of Claude's capabilities
- An ambiguity that Claude resolves differently each time
- Check Objective Clarity and Reasoning Fit for sources of multiple interpretation

---

## The Refinement Sequence

When a prompt needs multiple changes, work in this order:

1. **Fix the objective first.** A clear objective makes every other layer work harder. A vague objective undermines every other layer. If the objective fails the two-person clarity test, fix it before touching anything else.

2. **Fix context second.** Add specificity — concrete numbers, real constraints, prior decisions. Each detail narrows the output toward the specific situation. Highest-ROI change for prompts producing generic output.

3. **Fix reasoning third.** Replace generic reasoning with task-specific steps that name the analytical dimensions to cover. Highest-ROI change for prompts producing shallow output.

4. **Fix output format fourth.** Adjust sections, lengths, and format constraints. Highest-ROI change for prompts where substance is correct but packaging is wrong.

5. **Fix identity last.** Identity changes have broad effects — they shift tone, depth, vocabulary, and what Claude treats as important. Change identity only when the diagnostic clearly points to a role mismatch, and be aware it may require re-evaluating downstream layers.

---

## Refine vs. Rebuild Decision

**Refine** when the prompt produces partially correct output — the direction is right but specific aspects need improvement. Refining means adjusting individual layers while keeping overall architecture intact.

**Rebuild** when the prompt misses the mark fundamentally — wrong depth, wrong framing, wrong deliverable type. If you find yourself wanting to change three or more layers significantly, it is often faster to rebuild the prompt from scratch than to incrementally fix each layer.

**Decision heuristic:** After the first diagnostic pass, count the layers that need changes:
- One layer → refine.
- Two layers → refine, starting upstream.
- Three or more → consider rebuilding.

Rebuilding eliminates accumulated cruft from iterative fixes and produces a cleaner architecture. The rootnode-prompt-compilation Skill, if available, provides a structured methodology for building prompts from scratch.

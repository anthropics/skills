---
name: rootnode-prompt-validation
description: >-
  Evaluates and scores Claude prompts and system prompts using a six-dimension
  Scorecard with anchored 1-5 rubrics. Trigger on: "review my prompt," "score
  this prompt," "rate my prompt," "evaluate this prompt," "improve my prompt,"
  "what's wrong with my prompt." Also trigger on: "why isn't my prompt working,"
  "my prompt produces bad output," "help me fix this prompt," "is this prompt
  any good." Scorecard covers Objective Clarity, Context Specificity, Reasoning
  Fit, Output Precision, Behavioral Calibration, and Architectural Efficiency,
  plus a five-question Output Evaluation Rubric for assessing actual output.
  Also use when the user pastes a system prompt and asks for feedback. Activate
  whenever structured quality assessment of a single prompt is the primary need.
  Do NOT use for project-level audits involving Custom Instructions
  architecture, knowledge file organization, or multi-file Project structure
  (use rootnode-project-audit if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1.1"
  original-source: "PROMPT_TESTING_GUIDE.md"
---

# Prompt Validation

> **Calibration:** Tier 2, Opus-primary. See repository README for model compatibility.

Evaluate whether a prompt is well-constructed, diagnose why it underperforms, and fix it systematically. This Skill treats prompt evaluation as a structured discipline — score the architecture, test the output, trace failures to their root layer.

## Reasoning discipline

A defensible score shows its work. Observe the specific prompt features — instruction clarity, structural elements, behavioral countermeasures — name the pattern or principle they match against the rubric anchors, then apply the 1-5 score. Compressing this into a summary score blurs the rubric and erodes auditability; the explicit walk-through is what makes the score interrogable. The hard rule (evidence-first scoring) lives below in Step 1 and stays load-bearing.

If the evaluation scope is unclear (Scorecard only? Output Evaluation Rubric too? scoring or rewrite?), confirm scope with the user before proceeding. Do not proceed on inferred assumptions.

## When to Use This Skill

Use this Skill when evaluating a **single prompt or system prompt**. The user has a prompt (or its output) and wants to know whether it is working, why it is not, or how to improve it.

This Skill evaluates prompts. For evaluating an entire Claude Project's architecture (Custom Instructions, knowledge file organization, mode design, multi-file structure), use the rootnode-project-audit Skill if available. The distinction: if the user shows you one prompt or system prompt and asks "is this good?" — use this Skill. If the user describes a Project with multiple files and asks "why isn't my Project working?" — that is a project-level audit.

## Instructions

### Step 1: Score the Prompt (Prompt Scorecard)

Score the prompt on each of the six dimensions below using the 1-5 anchoring criteria. A prompt scoring below 3 on any dimension has an identified weakness that should be addressed before use. A prompt averaging 4.0+ with no score below 3 is ready for output testing.

The Scorecard evaluates prompt architecture, not output. A structurally strong prompt can still underperform if runtime context is thin. A prompt scoring 3s might produce adequate output for a simple task. Use the Scorecard as a quality gate, not a final verdict.

**Critical: Evidence-first scoring.** For every score, cite the specific text in the prompt that justifies the rating. Never assign a score without pointing to evidence. If you cannot find evidence for a higher score, it does not earn it.

#### Dimension 1: Objective Clarity

Does the objective define a specific task with evaluable success criteria?

| Score | Anchor |
|---|---|
| 1 | Topic only — names a subject area without specifying what to do with it. ("Analyze our marketing.") |
| 2 | Action verb present but success criteria absent. ("Evaluate our market entry options.") The reader knows the task type but not what a good output looks like. |
| 3 | Action verb, deliverable type, and audience specified, but success criteria are implicit. ("Produce an executive brief evaluating our three market entry options for the leadership team.") Two people might disagree on what "good" looks like. |
| 4 | Action verb, deliverable, audience, and explicit success criteria. Constraints stated. ("Evaluate three market entry options and recommend one, weighted toward operational feasibility given our 8-person team. Recommendation must be specific enough for a go/no-go decision.") |
| 5 | All of 4, plus the objective bounds what is out of scope. The two-person test passes cleanly — two readers would produce outputs with the same structure and analytical focus, differing only in judgment. |

If below 3 → most likely output failure is "answers an adjacent question." Fix the objective before touching any other layer.

#### Dimension 2: Context Specificity

Would the context need to change if the task were about a different organization in the same industry?

| Score | Anchor |
|---|---|
| 1 | No context, or purely categorical. ("We are a technology company looking to grow.") |
| 2 | Category with one or two specifics. ("B2B SaaS company with about 2,000 customers.") Output will be partially grounded but mostly generic. |
| 3 | Situation-specific with multiple concrete details (numbers, constraints, team composition) but missing prior decisions or what has been tried. Output will reference details but may suggest previously rejected approaches. |
| 4 | Specific situation with concrete numbers, named constraints, prior decisions, and what is off the table. Replacing the company name with a competitor's would make the context inaccurate. |
| 5 | All of 4, plus the context flags what is unknown or uncertain (rather than leaving gaps for Claude to guess), providing enough detail for tradeoff-aware rather than generic recommendations. |

If below 3 → most likely output failure is "generic — could apply to any company." No amount of reasoning refinement compensates for thin context.

#### Dimension 3: Reasoning Fit

Does the reasoning approach match the task type and direct analytical attention to the right dimensions?

| Score | Anchor |
|---|---|
| 1 | No reasoning guidance, or only "think step by step" / "analyze carefully." Claude receives no direction on what analytical moves to make. |
| 2 | Reasoning present but generic — steps could apply to any analytical task. ("Consider pros and cons. Identify risks. Recommend.") Steps do not reflect this task's specific challenge. |
| 3 | Reasoning from the correct task category (e.g., strategic reasoning for a strategic task) but used without customization. Steps are relevant but not tailored to the specific analytical challenge. |
| 4 | Task-specific reasoning with steps customized to the analytical challenge. Each step names a specific dimension to examine. If the task has a known pitfall (e.g., stakeholder bias, oversimplified tradeoff), the reasoning addresses it. |
| 5 | All of 4, plus the reasoning sequence builds on itself — each step uses output of prior steps. Total step count is 5-7 (under the focus ceiling). Cross-domain tasks combine elements from multiple reasoning categories. |

If below 3 → most likely output failure is "analysis is shallow — states the obvious." This is the highest-leverage dimension for analytical depth.

#### Dimension 4: Output Precision

Does the output specification provide enough structure for a predictable deliverable?

| Score | Anchor |
|---|---|
| 1 | No output specification, or only vague instruction. ("Write a thorough analysis.") Claude will choose its own format, length, and structure. |
| 2 | Deliverable type named but structure unspecified. ("Write an executive brief.") General format target but no section-level guidance. |
| 3 | Named sections specified, but per-section length guidance and format rules (prose vs. bullets, tone) absent. Output will have the right sections but may be unbalanced. |
| 4 | Named sections with per-section length guidance, total length target, and format constraints (prose, tone, audience calibration). Output structure is predictable across runs. |
| 5 | All of 4, plus the output specification includes what to exclude ("do not include a general background section") or how to handle edge cases within the format. Calibrated to the specific deliverable, not a generic template. |

If below 3 → most likely output failures are format-related: wrong length, unbalanced sections, bullets where prose is needed.

#### Dimension 5: Behavioral Calibration

Are countermeasures present for the failure modes this task is likely to trigger — and only those?

| Score | Anchor |
|---|---|
| 1 | No behavioral countermeasures. The prompt relies entirely on Claude's defaults, leaving task-relevant tendencies (agreeableness, hedging, verbosity, list overuse) unaddressed. |
| 2 | Generic countermeasures not targeted to this task. ("Be concise. Be direct. Challenge assumptions.") Reasonable defaults but not task-specific. |
| 3 | One or two targeted countermeasures for the most likely failure mode (e.g., agreeableness countermeasure when the user has stated a prior position), but other relevant failure modes unaddressed. Or: countermeasures present but vaguely worded. |
| 4 | Targeted countermeasures for all task-relevant failure modes, each with specific language (not "be direct" but "if the evidence does not support the preferred option, state this directly and explain why"). No generic countermeasures for irrelevant failure modes. |
| 5 | All of 4, plus countermeasures placed at high-attention positions (identity section for role-level calibration, quality standards for output-level verification) following the primacy-recency principle. Countermeasures reinforce rather than contradict the identity and output sections. |

If below 3 → most likely output failures are behavioral: excessive agreement, hedging, verbosity, or list overuse. See the behavioral tuning Skill (rootnode-behavioral-tuning) if available for deeper countermeasure guidance.

#### Dimension 6: Architectural Efficiency

Does every instruction earn its place?

| Score | Anchor |
|---|---|
| 1 | Significant bloat — redundant instructions, generic filler ("ensure high quality"), sections included "just in case," or template language not adapted to the task. |
| 2 | Some bloat. Most instructions relevant, but several could be removed without reducing output quality. Template language not fully customized. |
| 3 | All instructions relevant, but some more verbose than necessary, or the prompt uses full structure for a task that would perform equally well with less. Functional but not lean. |
| 4 | Lean — every instruction serves an identifiable purpose, and removing any one would noticeably reduce output quality. Complexity matches the task. No template artifacts remain. |
| 5 | All of 4, plus active compression — instructions that serve a single purpose are combined, sections trimmed to only task-relevant steps, total length is the minimum that produces target quality. |

If below 3 → the prompt may still produce adequate output, but it is harder to maintain, harder to diagnose when it fails, and more likely to confuse Claude with competing instructions.

#### Scorecard Delivery Format

```
Prompt Scorecard
────────────────────────────────────
Objective Clarity:       _/5
Context Specificity:     _/5
Reasoning Fit:           _/5
Output Precision:        _/5
Behavioral Calibration:  _/5
Architectural Efficiency: _/5
────────────────────────────────────
Average:                 _/5
Dimensions below 3:     [list any]
```

Interpretation:
- Average 4.5+ with no score below 4: Production-ready. Test with representative inputs.
- Average 4.0+ with no score below 3: Strong. Address 3-scoring dimensions if time permits.
- Any dimension below 3: Fix that dimension before testing. Follow the diagnostic links above.
- Average below 3.5: Consider rebuilding the prompt rather than patching. Multiple weak dimensions usually indicate structural mismatch, not a tuning problem.

### Step 2: Evaluate the Output (Output Evaluation Rubric)

If the user provides output from the prompt (or you can assess likely output quality), evaluate using these five questions. Each is answered Yes, Partially, or No.

For prompts intended for repeated use, the "done" criteria is: **5/5 across three runs with different representative inputs.** A prompt scoring 3/5 or lower on any run has a diagnosable gap.

**Q1: Does the output answer the specific question posed in the objective?**
- Yes: Directly addresses the defined task. Core question answered.
- Partially: Right general area but drifts to a related question (e.g., balanced analysis when a recommendation was requested).
- No: Answers a different question or stays at a general level.
- If Partially/No → diagnose at the objective (likely ambiguous).

**Q2: Does the output reference specific details from the context?**
- Yes: Incorporates specific numbers, names, constraints. Analysis grounded in the provided situation.
- Partially: References some details but core analysis stays generic.
- No: Could apply to any organization in the same category.
- If Partially/No → diagnose at context (too thin, or reasoning does not direct Claude to use it).

**Q3: Does the output show evidence of the specified reasoning approach?**
- Yes: Analytical moves match the reasoning specification. Steps are visible in the output structure.
- Partially: Some steps evident, others skipped or superficial.
- No: Output's analytical approach does not reflect the reasoning specification.
- If Partially/No → diagnose at reasoning (too generic, or too many steps causing Claude to prioritize).

**Q4: Does the output match the specified structure, length, and format?**
- Yes: Follows section structure, falls within length range, follows format rules.
- Partially: Mostly correct but sections are unbalanced, one is missing, or bullets used where prose specified.
- No: Ignores specified structure, dramatically wrong length, or fundamentally different format.
- If Partially/No → diagnose at output specification (check section names, per-section length, format rules are explicit).

**Q5: Would the intended audience find this output actionable without significant follow-up?**
- Yes: Specific enough, well-structured enough, right depth for the audience to act.
- Partially: Useful analysis but key decisions or specifics unresolved. Follow-up needed.
- No: Informative but not actionable — audience learns but does not know what to do next.
- If Partially/No → cross-layer issue. Check: objective does not specify what audience will do with output, context lacks constraints for concrete recommendations, or output specification does not require concrete deliverables.

#### Rubric Delivery Format

```
Output Evaluation — Run [1/2/3]
────────────────────────────────────
Q1 Answers the objective:      Yes / Partially / No
Q2 Uses context specifics:     Yes / Partially / No
Q3 Follows reasoning approach: Yes / Partially / No
Q4 Matches format/structure:   Yes / Partially / No
Q5 Actionable for audience:    Yes / Partially / No
────────────────────────────────────
Score: _/5  (Yes = 1, Partially = 0.5, No = 0)
```

#### Connecting the Scorecard and the Rubric

- Low Scorecard dimension → predicts low Rubric score on the corresponding question. Low Objective Clarity predicts low Q1. Low Context Specificity predicts low Q2. Low Reasoning Fit predicts low Q3. Low Output Precision predicts low Q4. Low Behavioral Calibration surfaces in Q1 or Q5.
- Scorecard high but Rubric low → gap is usually in runtime context. The prompt architecture is sound, but the specific context provided was too thin. This is a usage problem, not an architecture problem.
- Rubric high on some runs but low on others → reliability problem. Likely an ambiguity Claude resolves differently each time. Recheck Objective Clarity and Reasoning Fit.

### Step 3: Fix What the Scores Reveal

When scores identify weaknesses, use this condensed symptom map for the most common issues. For a comprehensive map covering all 13 documented symptoms, see `references/symptom-fix-map.md`.

**Output is generic — could apply to any company.**
Root cause: Insufficient context (almost always). Fix: Add specific numbers, real constraints, prior decisions, and situational details. Every concrete detail eliminates a generic assumption. If context is already specific, check identity — a role like "business consultant" may be too broad.

**Analysis is shallow — states obvious points without deeper insights.**
Root cause: Missing or generic reasoning. Fix: Replace generic reasoning ("think step by step") with task-specific steps that name the analytical dimensions to cover. Each step is a depth instruction. If task-specific reasoning is present and output is still shallow, increase step specificity — "identify at least two alternative interpretations and explain what makes each more or less likely."

**Output agrees with a flawed premise.**
Root cause: Missing agreeableness countermeasure. Fix: Add pushback instruction: "If the premise contains errors, flawed assumptions, or a better alternative framing, say so directly before proceeding." Place in both the identity section and quality control for reinforcement.

**Output is too long.**
Root cause: Missing length constraint. Fix: Add explicit length target ("Total: 600-800 words") and per-section guidance ("Analysis: 3 paragraphs. Next Steps: 3-5 items"). If length creep happens mid-conversation, restate the constraint.

**Excessive hedging — too many caveats.**
Root cause: Missing decisiveness instruction. Fix: Add "Be direct and decisive. State your position clearly where confident. Reserve caveats for genuinely uncertain areas, and when caveating, be specific about what is uncertain and why."

**Everything in bullet points when prose would be better.**
Root cause: Missing format instruction. Claude defaults to bulleted lists without explicit format guidance. Fix: Add "Write in connected prose paragraphs. Use lists only for genuinely discrete, parallel items."

For the full diagnostic flow (three-step layer-by-layer methodology), see `references/diagnostic-flow.md`. For all 13 symptoms with complete root cause analysis and targeted fixes, see `references/symptom-fix-map.md`.

### Refinement Principles

When fixing a prompt based on scores:

**One change at a time.** Change one layer per iteration. If you change identity, reasoning, and output simultaneously, you cannot determine which change helped. This feels slower but builds accurate understanding.

**Fix upstream first.** When multiple layers have problems, fix in this order: objective → context → reasoning → output format → identity. An upstream fix often resolves what appeared to be a downstream problem.

**Refine vs. rebuild.** One weak dimension — refine. Two weak dimensions — refine, starting upstream. Three or more weak dimensions — consider rebuilding the prompt from scratch rather than patching.

**Know when to stop.** A prompt is done when it produces acceptable output on 4+ out of 5 runs with different representative inputs, the output is situation-specific (not generic), and the last change produced only marginal improvement. A prompt that reliably hits 85% quality is more valuable than one that sometimes hits 95% and sometimes hits 60%.

## Critical: Output Length for This Skill

Match response length to the prompt's complexity. A simple prompt review needs the Scorecard with brief evidence per dimension — not two pages of analysis. A complex system prompt with multiple layers warrants deeper commentary on each dimension. When scoring, state the score, the evidence, and the fix. Nothing else per dimension.

## Troubleshooting

**Scorecard scores all 3s.** The prompt is functional but unoptimized. Prioritize the dimension most relevant to the user's complaint. If no specific complaint, start with Objective Clarity — it has the highest downstream impact.

**Scorecard and Rubric disagree.** Scorecard high but Rubric low means the architecture is sound but runtime context is thin — help the user provide richer context. Rubric inconsistent across runs means the prompt has an ambiguity — check Objective Clarity and Reasoning Fit for sources of multiple interpretation.

**User provides output but not the prompt.** You can still use the Output Evaluation Rubric. Score the output on Q1-Q5 and use the diagnostic links to suggest which layers of the prompt likely need work. Note that without seeing the prompt, the diagnosis is probabilistic.

**User wants a complete rewrite, not a review.** This Skill evaluates and diagnoses. If the user wants a prompt built from scratch, the rootnode-prompt-compilation Skill handles that if available. You can still use the Scorecard dimensions as a checklist while building, but the primary workflow here is evaluation.

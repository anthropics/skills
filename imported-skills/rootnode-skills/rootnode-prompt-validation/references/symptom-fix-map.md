# Symptom-to-Root-Cause Map

The complete reference of documented prompt failure symptoms, their root causes, diagnostic tests, and targeted fixes. Use this when you have identified a specific output problem and need to trace it to the responsible layer with a precise fix.

**When to consult this file:** After identifying symptoms through Scorecard scores (Step 1) or Rubric evaluation (Step 2), when the condensed map in the main Skill does not cover the specific symptom, or when you need the full diagnostic test and fix detail for a common symptom.

---

## Table of Contents

1. [Substance Problems](#substance-problems) — Generic output, shallow analysis, flawed premise agreement, contradictory recommendations, missed aspects, long preamble
2. [Form Problems](#form-problems) — Too long, bullet overuse, format mismatch, wrong tone
3. [Behavioral Problems](#behavioral-problems) — Excessive hedging, unrequested sections, conversation drift

---

## Substance Problems

### Generic output — could apply to any company or situation

**Root cause:** Insufficient context, almost always. Occasionally caused by identity too vague.

**Diagnostic test:** Does the context contain specific numbers, constraints, and situational details? If it describes a category ("a B2B SaaS company") rather than a specific situation ("a B2B SaaS company with $40M ARR, 2400 customers concentrated in healthcare, and a 6-person sales team"), the context is too thin.

**Fix:** Add specificity to the context. Include concrete numbers (revenue, team size, customer count), real constraints (budget, timeline, technical limitations), and prior decisions (what has been tried, what is off the table). Every concrete detail eliminates a generic assumption Claude would otherwise make.

If context is already specific and output is still generic, check the identity. A role like "business consultant" is too broad — "B2B SaaS growth strategist who has scaled three companies from $20M to $100M ARR" produces more situation-specific output because the identity narrows the solution space.

---

### Shallow analysis — states obvious points without surfacing deeper insights

**Root cause:** Missing or generic reasoning, most often. Occasionally caused by identity set to insufficient seniority.

**Diagnostic test:** Does the prompt include reasoning guidance with task-specific steps? If the reasoning instruction is "think step by step" or "analyze carefully," it provides no guidance on what analytical dimensions to cover.

**Fix:** Replace generic reasoning with task-specific steps. The reasoning should name the specific analytical moves required: test assumptions, consider alternative interpretations, identify what would change the conclusion, distinguish signal from noise. Each step is a depth instruction — more specific steps produce deeper analysis.

If task-specific reasoning is already present and output is still shallow, check step specificity. "Consider alternatives" is vague. "Identify at least two alternative interpretations of the same evidence and explain what would make each more or less likely" forces depth.

---

### Agrees with a flawed premise in the request

**Root cause:** Missing agreeableness countermeasure in quality control.

**Diagnostic test:** Does the prompt include explicit permission to challenge the user's framing? Without it, Claude defaults to executing the request as stated, even when the premise is flawed.

**Fix:** Add a pushback instruction: "If the premise of this request contains errors, flawed assumptions, or a better alternative framing, say so directly before proceeding. Do not simply execute a flawed request without comment." Place this in two locations for reinforcement: in the identity section (as a behavioral anchor) and in quality control (as a verification step).

---

### Recommendations contradict each other

**Root cause:** Missing internal consistency check in quality control. Occasionally caused by conflicting instructions in the prompt itself.

**Diagnostic test:** First, audit the prompt for contradictory instructions (e.g., "be concise" in one section and "be thorough and comprehensive" in another). If the prompt is internally consistent, the quality control layer is missing an explicit consistency check.

**Fix:** If the prompt has contradictory instructions, resolve them — decide which takes priority and remove or subordinate the other. If the prompt is clean, add to quality control: "Verify that your recommendations are mutually compatible. If pursuing one recommendation would make another harder, acknowledge the tension and explain how to manage it."

---

### Output misses key aspects of the problem

**Root cause:** Objective too vague or reasoning missing relevant analytical dimensions.

**Diagnostic test:** Does the objective specify all dimensions that should be covered? Does the reasoning direct attention to the dimensions being missed?

**Fix:** If the objective says "analyze X," specify the dimensions: "Analyze X across dimensions A, B, and C, with particular attention to D." If the objective is specific but certain dimensions are still missed, add them as explicit steps in the reasoning. Claude attends to what the reasoning directs it to attend to — unstated dimensions are addressed inconsistently.

---

### Long preamble before getting to actual content

**Root cause:** Missing output structure guidance or objective framed as a request rather than a task specification.

**Diagnostic test:** Does the output specification state what the first section should be? Does the objective start with conversational framing ("I'd like you to..." / "Could you...") rather than a direct task statement?

**Fix:** Specify the opening section: "Begin with [Recommendation / Key Finding / Bottom Line]. Do not include an introduction or preamble." Also convert conversational framing to direct task statements — "Evaluate X and recommend Y" rather than "Could you take a look at X and let me know what you think about Y?"

---

## Form Problems

### Output is too long

**Root cause:** Missing length constraint in the output specification, or verbosity drift in a long conversation.

**Fix:** Add an explicit length target: "Total length: 600-800 words." For per-section control: "Bottom Line: 2-3 sentences. Analysis: 3 paragraphs. Next Steps: 3-5 items." If length creep happens mid-conversation, restate the length constraint when starting the next task.

---

### Everything in bullet points when prose would be better

**Root cause:** Missing format instruction. Claude defaults to bulleted lists in the absence of format guidance.

**Fix:** Add to the output specification: "Write in connected prose paragraphs. Use lists only when the content is genuinely a set of discrete, parallel items. Do not convert narrative explanations into bullet points."

---

### Output format does not match the deliverable type

**Root cause:** Missing or mismatched output specification.

**Fix:** Specify section names, per-section length, format per section (prose vs. table vs. list), and total length. The more specific the output specification, the more predictable the format. Vague output instructions ("write a thorough analysis") produce unpredictable structure.

---

### Tone is wrong — too formal, too casual, too academic

**Root cause:** Identity section or output standards not specifying tone.

**Fix:** Add a tone instruction to the output specification: "Tone: direct and professional, not academic." Alternatively, adjust the identity — a "senior consultant" produces different tone than an "educator," which produces different tone than a "technical architect." The identity sets the baseline tone; the output specification fine-tunes it.

---

## Behavioral Problems

### Excessive hedging — too many caveats and qualifications

**Root cause:** Missing decisiveness instruction, common in analytical and research tasks.

**Fix:** Add to quality control: "Be direct and decisive in your conclusions. Where you are confident, state your position clearly. Reserve caveats for genuinely uncertain areas, and when you do caveat, be specific about what is uncertain and why."

For research tasks specifically, add: "After presenting the evidence fairly, state your assessment clearly. Uncertainty about specific points does not prevent you from reaching a well-reasoned overall conclusion."

---

### Claude adds unrequested sections (summaries, follow-up questions, disclaimers)

**Root cause:** Missing output boundary instruction.

**Fix:** Add to the output specification: "Respond only with what was requested. Do not add summaries, follow-up suggestions, or sections not specified in this format." Claude reliably respects explicit boundary instructions.

---

### Output drifts from the task over a long conversation

**Root cause:** Context window dilution. In long conversations, earlier messages (including the system prompt) receive less attention as the conversation grows.

**Fix:** Restate critical context and constraints when starting a new phase of work. Summarize decisions made so far before asking for the next step. For system prompts, the prompt persists throughout the conversation, but specific per-task instructions from earlier messages may need reinforcement.

---

## Quick Reference Table

| Problem | Most Likely Layer | First Fix to Try |
|---|---|---|
| Output is generic | Context | Add specific numbers, constraints, situational details |
| Analysis is shallow | Reasoning | Replace generic reasoning with task-specific steps |
| Wrong question answered | Objective | Sharpen with action verb and success criteria |
| Agrees with flawed premise | Quality Control | Add pushback instruction to identity and quality control |
| Too long | Output specification | Add explicit length target, per-section and total |
| All bullet points | Output specification | Add "write in prose" instruction |
| Excessive hedging | Quality Control | Add decisiveness instruction |
| Recommendations contradict | Quality Control | Add internal consistency verification step |
| Tone is wrong | Identity | Adjust role seniority or add tone instruction |
| Adds unrequested sections | Output specification | Add explicit boundary: "respond only with requested sections" |
| Misses key aspects | Objective + Reasoning | Specify dimensions in objective; add as reasoning steps |
| Long preamble | Output specification | Specify the opening section; remove conversational framing |
| Drifts over conversation | Context management | Restate constraints; summarize prior decisions |

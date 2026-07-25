# Analytical / Evaluative Reasoning Approaches

Three approaches for tasks that require evaluating, diagnosing, or assessing something that exists. Each works with a different analytical orientation: forward from evidence, backward from symptoms, or forward into failure modes.

---

## General Analysis

**Use when:** You need a thorough evaluation of a situation, opportunity, or problem. The default choice for most analytical tasks.

```xml
<reasoning>
Approach this analysis as follows:
1. State the core question you are answering before beginning analysis.
2. Identify the key assumptions embedded in the problem. Test each — which are well-supported, which are fragile?
3. Examine the evidence. Distinguish between strong signals and noise. Flag where data is insufficient.
4. Consider at least one alternative interpretation of the same evidence.
5. Draw conclusions proportional to the strength of the evidence. Do not overstate.
6. Identify what would change your conclusion if it turned out differently.
</reasoning>
```

### Usage Guidance

This is the most general-purpose reasoning approach. Use it when no other category is a clearly better fit. It works well for evaluations, assessments, opportunity analyses, and any task where the goal is "understand this situation and draw conclusions."

### Failure Modes

- **Excessive assumption-testing preamble:** Claude may spend too much time on step 2 and produce a long preamble before reaching actual analysis. If the assumptions are straightforward, trim the approach to focus on steps 3-6.
- **Balanced-to-a-fault conclusions:** Claude may hedge every conclusion. If you need a clear assessment, add to the prompt: "Draw a clear conclusion. If the evidence is genuinely ambiguous, state what additional information would resolve it — do not split the difference."

### When to Modify

If assumptions are straightforward, remove step 2. If the task emphasizes decision-making, add a final step: "State the implication for the decision at hand." If multiple evidence sources exist with varying reliability, strengthen step 3 with source-quality guidance.

---

## Root Cause Diagnosis

**Use when:** Something is failing or underperforming and you need to find out why. Distinct from general analysis because it works backward from symptoms to causes rather than forward from evidence to conclusions.

```xml
<reasoning>
Approach this diagnosis as follows:
1. List the observable symptoms — what is actually happening vs. what should be happening? Be precise about the gap.
2. Map the causal chain backward: for each symptom, what are the possible immediate causes? For each cause, what could produce it?
3. Identify where multiple symptom chains converge on the same root cause — convergence points are the highest-probability explanations.
4. Test your leading hypothesis: if this root cause were fixed, would it explain all (or most) of the symptoms? Which symptoms would remain unexplained?
5. Identify the simplest intervention that addresses the root cause, not the symptoms.
6. Flag any symptoms that your root cause does not explain — these may indicate a second, independent problem.
</reasoning>
```

### Usage Guidance

Use for any "why is this happening?" or "why isn't this working?" task. The backward-from-symptoms approach is more effective than general analysis when the problem is clear but the cause is not. Works for business process failures, product underperformance, team dysfunction, quality issues, and any situation where symptoms are visible but the underlying cause requires investigation.

### Failure Modes

- **Abstract root causes:** Claude may identify a root cause that sounds plausible but is actually just restating the symptom at a higher level of abstraction ("the root cause of low engagement is that users aren't engaged"). Push for specificity by adding: "The root cause must be specific enough that someone could design an intervention to address it directly."
- **Single-cause bias:** Claude may settle on one root cause too quickly when multiple independent causes are at play. Step 6 mitigates this, but if you suspect multiple causes, add: "Consider that these symptoms may have more than one independent root cause."

### When to Modify

For technical debugging, use the Debugging & Incident Analysis approach from `technical-reasoning.md` instead — it adds hypothesis testing and fix validation specific to technical systems. For organizational problems, strengthen step 2 with stakeholder perspective: "Consider how different stakeholders would describe the causal chain."

---

## Risk Assessment

**Use when:** You need to evaluate the risks of a decision, project, or course of action. Distinct from general analysis because it focuses on what could go wrong and how to prepare, not on what the evidence currently shows.

```xml
<reasoning>
Approach this risk assessment as follows:
1. Identify the decision or action being evaluated. State the expected outcome if everything goes well.
2. List the material risks — things that could prevent the expected outcome or create significant negative consequences. Prioritize by impact, not just likelihood.
3. For each risk, assess: How likely is it? How severe is the impact if it occurs? How early would we detect it? Can it be mitigated, transferred, or must it be accepted?
4. Identify risk interactions — which risks compound each other or share a common trigger? A scenario where two moderate risks hit simultaneously may be worse than either alone.
5. Distinguish between risks you can influence and risks that are external. Focus mitigation efforts on the ones you can influence.
6. Produce a clear risk profile: what is the overall risk level, what are the top 3 risks that need active management, and what is the recommended risk posture (proceed, proceed with safeguards, delay until resolved, or abandon)?
</reasoning>
```

### Usage Guidance

Use for go/no-go decisions, project planning, investment evaluation, and any task where understanding downside scenarios is critical. The approach produces a structured risk profile with a clear posture recommendation — not just a list of risks.

### Failure Modes

- **Undifferentiated risk lists:** Claude tends to generate long, flat lists of risks without meaningful prioritization. The approach mitigates this with explicit prioritization instructions, but if the output is still a laundry list, add: "Limit your assessment to the 5 most material risks. If a risk would not change the decision, it does not belong in this assessment."
- **Missing risk interactions:** Claude often evaluates risks independently. Step 4 addresses this, but for complex scenarios, strengthen it: "Identify at least one scenario where two risks co-occur and assess the combined impact."

### When to Modify

For technical risks specifically, combine with the System Design approach from `technical-reasoning.md` to get both architectural risk identification and mitigation design. For strategic risks, combine with Market & Competitive Strategy from `strategic-reasoning.md` to ensure competitive risks are properly weighted.

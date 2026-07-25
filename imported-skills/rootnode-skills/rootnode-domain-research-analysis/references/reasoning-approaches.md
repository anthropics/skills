# Reasoning Methods for Research & Analysis

Complete reasoning method specifications for research and analysis prompts. Each method includes the full XML code block to paste into your prompt, usage guidance, and failure mode warnings.

**Table of Contents:**
- [Quantitative Interpretation](#quantitative-interpretation)
- [Systematic Review](#systematic-review)
- [Causal Analysis](#causal-analysis)
- [Hypothesis-Driven Investigation](#hypothesis-driven-investigation)

---

## Quantitative Interpretation

**Use when:** The task requires interpreting numerical data — reading statistical results, evaluating survey data, making sense of metrics, or assessing whether data supports a claimed conclusion. Use this when the primary analytical challenge is understanding what numbers mean.

**Distinct from:** Evidence Synthesis (which organizes findings across sources) — this focuses specifically on the mechanics of reading data correctly.

```xml
<reasoning>
Approach this data interpretation as follows:
1. State the question the data is being asked to answer before examining the numbers. Without a clear question, data analysis becomes a fishing expedition that finds patterns whether or not they are meaningful.
2. Assess the data's provenance and quality. How was it collected? What is the sample size and is it representative? What time period does it cover? Are there obvious gaps, biases, or collection artifacts? Data quality determines the ceiling of analytical confidence.
3. Examine the descriptive statistics before drawing inferences. What are the distributions, central tendencies, and variability? Are there outliers that significantly affect the averages? Medians and distributions often tell a different story than means.
4. Test the claimed or apparent patterns. Is the effect size meaningful in practical terms, not just statistically significant? Is the sample large enough to support the conclusion? Could the pattern be explained by a confounding variable, a base rate effect, or regression to the mean?
5. Consider what the data cannot tell you. Observational data cannot establish causation without additional evidence. Self-reported data reflects perceptions, not necessarily reality. Historical data may not predict future behavior if conditions have changed. State the limitations that matter most for the question at hand.
6. Translate findings into actionable insight. What does this data mean for the decision or question? What confidence level is appropriate? What additional data would strengthen or change the conclusion?
</reasoning>
```

**Watch for:** Claude may produce interpretation that is technically cautious but practically useless — every finding wrapped in so many methodological caveats that the reader cannot extract an insight. Step 6 pushes toward actionability, but if the output still over-hedges, add: *"State your best interpretation given the available data. Present limitations once, clearly, in a dedicated section — do not qualify every finding individually."*

**Also watch for:** Claude inventing specific statistical metrics (p-values, confidence intervals) when the source data does not provide them. If the data is summary-level, add: *"Work with the data as provided. Do not generate statistical tests or p-values that cannot be computed from the available information."*

---

## Systematic Review

**Use when:** The task requires methodically evaluating a body of evidence on a specific question — not just reading sources, but applying consistent criteria to assess their quality, relevance, and what they collectively show. Use this when the research question is specific enough that sources can be evaluated against defined standards.

**Distinct from:** Evidence Synthesis (which organizes findings thematically) — this applies formal evaluation methodology with inclusion criteria, quality assessment, and structured extraction.

```xml
<reasoning>
Conduct this systematic review as follows:
1. Define the research question in precise, answerable terms. A question that is too broad ("What is the impact of remote work?") produces an unfocused review. A precise question ("How does fully remote work affect engineering team output velocity in organizations with 50-500 employees?") produces a targeted one.
2. Establish the inclusion and exclusion criteria. What types of evidence are relevant — peer-reviewed research, internal data, industry reports, case studies? What date range? What population or context? Define these criteria before evaluating sources to prevent bias toward evidence that supports a favored conclusion.
3. For each source that meets the inclusion criteria, assess its methodological quality. What was the study design? How large was the sample? Were there control groups or comparison baselines? What are the most significant methodological limitations? Rate each source on a consistent quality scale — high confidence, moderate confidence, or low confidence — and explain the rating.
4. Extract the key findings from each source using a consistent framework. What did the study measure, what did it find, and what are the boundary conditions on the finding? Extracting findings in a consistent format makes cross-source comparison possible.
5. Synthesize across sources. Where do high-quality sources converge? Where do they conflict — and can the conflict be explained by methodological differences, different populations, or different time periods? What does the weight of evidence support?
6. Assess the overall evidence base. Is it sufficient to answer the research question with confidence? Where is it strong and where is it thin? What types of evidence are missing that would strengthen the conclusions?
</reasoning>
```

**Watch for:** Claude may apply this methodology with false precision — rating source quality on a consistent scale when it does not actually have enough information about the source methodology to make a meaningful assessment. If source descriptions in context are thin, add: *"Rate source quality only when you have enough methodological information to justify the rating. For sources described only by their conclusions, note that quality cannot be assessed and weight them accordingly."*

**Also watch for:** Claude treating the systematic structure as the deliverable rather than the insight. The methodology serves the conclusion — if the output is mostly methodology description with thin conclusions, the balance is wrong.

---

## Causal Analysis

**Use when:** The task involves determining why something happened — not just describing what occurred, but identifying the causal mechanism. Use this when multiple explanations exist for an observed outcome and the task is to assess which explanation the evidence best supports.

**Distinct from:** Root Cause Diagnosis (which works backward from operational symptoms to find a fixable cause) — this is an evidence-based analytical exercise that evaluates competing causal explanations.

```xml
<reasoning>
Approach this causal analysis as follows:
1. State the outcome to be explained precisely. What happened, when, to what degree, and to whom? A vague outcome statement ("things got worse") produces vague causal analysis. A precise one ("customer retention dropped from 92% to 84% in Q3, concentrated in the mid-market segment") focuses the analysis.
2. Enumerate the plausible causal explanations. What could have produced this outcome? Consider multiple categories: internal actions, external conditions, market dynamics, operational changes, and compounding effects. Do not prematurely narrow to one explanation.
3. For each explanation, assess the evidence. What facts support it? What facts contradict it? Does the timeline fit — did the proposed cause precede the effect? Is the proposed mechanism plausible — is there a logical chain from cause to effect, or is the connection only correlational?
4. Apply counterfactual reasoning. If the proposed cause had not occurred, would the outcome likely have been different? If the proposed cause occurred but other conditions changed, would the outcome still have happened? Counterfactuals help distinguish true causes from coincidental correlations.
5. Evaluate whether the cause is sufficient on its own or whether multiple factors combined. Most outcomes of any complexity have multiple contributing causes. Identify the primary driver (the cause with the largest causal contribution) separately from contributing factors (conditions that amplified or enabled the primary cause).
6. State your causal conclusion with calibrated confidence. What do you believe caused the outcome, how confident are you, and what evidence would change your assessment? If multiple explanations remain viable, say so — premature certainty about causes is worse than acknowledged ambiguity.
</reasoning>
```

**Watch for:** Claude may default to the most obvious or most recently discussed explanation without genuinely evaluating alternatives. Step 2 forces enumeration of multiple explanations, but if the analysis gives short treatment to all but one, add: *"Evaluate each causal explanation with genuine analytical effort. If you spend three paragraphs on one explanation and one sentence on each alternative, you are confirming a hypothesis, not testing it."*

**Also watch for:** Claude confusing temporal sequence with causation — "A happened before B" is necessary but not sufficient evidence that A caused B. If the analysis relies on chronological proximity, add: *"For each proposed causal link, identify the specific mechanism by which the cause produced the effect — not just that they occurred in sequence."*

---

## Hypothesis-Driven Investigation

**Use when:** The task involves researching a question that benefits from structure — forming specific hypotheses, identifying what evidence would confirm or disconfirm each, and then evaluating the evidence. Use this when open-ended research is likely to wander without a structured approach, or when the research needs to be defensible and show its reasoning.

**Distinct from:** Evidence Synthesis (which starts with sources and looks for themes) — this starts with questions and looks for answers.

```xml
<reasoning>
Structure this investigation as follows:
1. Define the central question precisely. Then decompose it into 2-4 specific, testable hypotheses. Each hypothesis should be a concrete claim that evidence could either support or undermine. "Company X is struggling" is not a testable hypothesis. "Company X's revenue decline is driven primarily by customer churn rather than pricing pressure" is.
2. For each hypothesis, identify what evidence would support it and what evidence would disconfirm it — before examining the available evidence. This prevents confirmation bias: if you define the tests first, you cannot unconsciously move the goalposts.
3. Evaluate the available evidence against each hypothesis. Which hypotheses are supported, which are disconfirmed, and which have insufficient evidence for a conclusion? Be disciplined about distinguishing "no evidence against" from "evidence for" — absence of disconfirming evidence is not the same as confirmation.
4. For hypotheses that survive initial evaluation, stress-test them. What is the strongest counterargument? What is the most likely alternative explanation for the supporting evidence? Would a skeptic find the evidence convincing?
5. Synthesize the surviving hypotheses into a coherent answer to the central question. If multiple hypotheses survived, assess whether they are complementary (different aspects of a complex answer) or competing (only one can be correct). If competing, state which the evidence favors and by how much.
6. Identify the research gaps. Which hypotheses could not be adequately tested? What additional evidence would resolve remaining ambiguity? Prioritize by decision impact — which gaps matter most for the question at hand?
</reasoning>
```

**Watch for:** Claude may form hypotheses that are too safe — easily confirmed with available information rather than genuinely testing different possible answers. If the hypotheses are not structurally different from each other, add: *"Each hypothesis must represent a genuinely different answer to the central question. If all hypotheses point toward the same conclusion, you are not testing — you are confirming."*

**Also watch for:** Claude treating this as a purely sequential process where each step is completed before moving to the next. In practice, evidence discovered in step 3 may require revising hypotheses from step 1. Add: *"If evidence reveals that your hypotheses are framed incorrectly or that a more important question is emerging, revise the hypotheses rather than forcing the evidence into the original framework."*

# Language Bank

A registry of academic rebuttal stems, framing language, and tone qualifiers for materials science and engineering peer review.

## 1. Acknowledge and Accept

Use these stems when accepting comments (`ACCEPT_TEXT`, `ACCEPT_ANALYSIS`) to keep a constructive tone.

### 1.1 Expressing Appreciation
- We sincerely thank the reviewer for this insightful comment, which has helped clarify our discussion of [topic].
- We appreciate the reviewer's careful reading and constructive suggestions regarding [parameter/test].
- We value the reviewer's professional assessment of our methodology; this feedback has improved the rigor of the manuscript.

### 1.2 Confirming Revision
- To address this concern, we have revised Section [X] (Page [P], Lines [L-L]) to explicitly state [revision details].
- We agree that the original wording was ambiguous. We have rephrased this passage in the revised manuscript to read: "[verified revised text]".
- In response to the reviewer's recommendation, we have added [confirmed data/figure/table] to Section [X] and expanded the discussion on Page [P]. [AUTHOR_INPUT_NEEDED: verify data, figure/table ID, and location.]

## 2. Clarification and Softening

Use these stems when narrowing claims (`SOFTEN_CLAIM`) to match available evidence.

### 2.1 Claim-Strength Ladder
- **Demonstrates / Confirms**: Use only when direct, quantitative, and replicated evidence is present.
  > Example: "[Verified direct measurement] confirms [specific conclusion] under [condition]."
- **Indicates / Correlates**: Use for clear empirical trends that do not isolate the underlying cause.
  > Example: "The measured [property] indicates [bounded performance trend]."
- **Suggests / Is consistent with**: Use for inferred mechanisms or interpretations where alternative pathways exist.
  > Example: "The observed [verified feature] is consistent with [bounded interpretation], while alternative explanations remain possible."

### 2.2 Limitation Phrasing
- While our current data do not isolate the individual contribution of [variable A], the overall trend suggests [bounded conclusion]. We have revised Section [X] to present this as a hypothesis rather than a confirmed mechanism.
- We have toned down this claim in Section [X] to avoid overinterpretation, replacing "[original strong claim]" with "[softened claim]".
- Because [method] has inherent limits in [aspect], we have restricted our conclusions to [narrow scope] and added a paragraph on these limitations in Section [X].

## 3. Disagreeing or Rebutting Politely

Use these stems to decline requests (`DISAGREE`) based on objective constraints without sounding defensive.

### 3.1 Standards-Based Rebuttals
- While we understand the reviewer's preference for [method B], we selected [method A] because it is the standard method prescribed by [verified standard] for [material type]. We have clarified this rationale in Section [X].
- According to [verified standard/specification], [test parameter] is evaluated under [condition]. Changing this to [requested condition] would prevent comparison with existing literature. We have clarified this rationale in Section [X].

### 3.2 Physics-Based or Material-System Constraints
- We agree that [method B] provides complementary information. However, for the studied [material system], [verified limitation] makes [method B] prone to high uncertainty. We have added a brief discussion of these physical limitations in Section [X]. [AUTHOR_INPUT_NEEDED: verify the limitation and any quantitative uncertainty before including it.]
- Performing [test] requires [specimen geometry/size], which is physically incompatible with [material structure/processing limit]. To address the underlying concern, we have instead provided [verified alternative evidence] in Figure/Table [X].

### 3.3 Scope-Based Rebuttals
- We thank the reviewer for highlighting the potential value of [additional complex test]. Because this study focuses on [primary topic], a full evaluation of [additional test] is beyond the current scope. We have noted this as an important direction for future work in Section [X].
- While evaluating [extreme durability condition] is important, the present work bounds its scope to [specific conditions] to isolate [specific variable]. We have revised the Introduction to clearly define this scope boundary.

## 4. Handling Conflicting Reviewers

Use these stems when bridging contradictory requests from different reviewers.

### 4.1 Conflicting Mechanism Requests
- Context: R1 wants a deeper mechanism discussion; R2 warns against speculation.
  > We have balanced the requests of both reviewers by adding [available evidence] while refining the wording to distinguish direct observations from interpretation.

### 4.2 Conflicting Novelty Assessments
- Context: R1 finds the paper novel; R2 claims it is incremental.
  > We appreciate both assessments. We have revised the Introduction (Page [P], Lines [L-L]) to define the specific evidence gap more precisely and clarify that our work provides [bounded contribution].

## 5. Internal Author Flags

Use these placeholders (`AUTHOR_INPUT_NEEDED`) to alert the user about unresolved data needs.

- `[AUTHOR_INPUT_NEEDED: confirm if data/figures are available for test X]`
- `[AUTHOR_INPUT_NEEDED: verify exact line numbers and page numbers in the final tracked draft]`
- `[AUTHOR_INPUT_NEEDED: confirm the manufacturer model and software version used for instrument Y]`

# SKILL: structure_judgment

## Purpose
Front-end structural routing for mixed, ambiguous, high-noise inputs.

This skill runs **before** `judgment_hygiene` and before any search / verification workflow.
Its job is not to decide the final answer. Its job is to decide:

- what kind of structural problem this input is
- which layer must be handled first
- what the main hazard is
- whether external verification is needed
- which downstream skill(s) should run, and in what order
- what must be kept separate instead of blended into one smooth but wrong answer

This skill is a **routing layer**, not a visible reasoning style.

---

## Version
v0.2 — revised GPT draft incorporating Claude and Gemini review

## Status
Approved for controlled trial. Not yet approved for general deployment.

---

## When to use this skill

Use this skill whenever an input contains one or more of the following:

- mixed facts + interpretation + self-evaluation
- requests for advice based on emotionally loaded framing
- image/text, report/text, screenshot/text, or other multi-channel inputs
- claims about motives, meanings, hidden intentions, social signals, or patterns
- escalation requests (“should I report / quit / confront / expose / send / post / ignore / invest / cut off / walk away”)
- potentially current, unstable, or externally verifiable claims
- situations where the user’s wording already contains a conclusion disguised as a premise
- any case where answering directly without first separating layers would likely produce drift, overreach, fake certainty, or useless stone-mode caution

Do not use this skill for pure retrieval, pure formatting, or simple direct factual tasks unless the input is structurally contaminated.

---

## What this skill is NOT

This skill is not:

- a visible answer format
- a substitute for judgment
- a substitute for verification
- a permission slip to stall with meta-language
- a way to hide behind “this is complex”
- a ritual of naming layers without changing answer order or downstream routing

Do **not** satisfy this skill by merely saying:
- “there are many layers here”
- “this has both objective and subjective elements”
- “we should separate fact from interpretation”

That is structure-flavored throat clearing, not structure judgment.

This skill is only being followed if it changes:
- what gets answered first
- what gets deferred
- what gets corrected
- what gets separated
- which downstream skill is invoked
- how the answer is ordered

If the answer only sounds more meta, the skill has failed.

---

## Core idea

Most bad answers do not fail because the model cannot produce a plausible sentence.
They fail because the model answers the **wrong layer first**.

Typical routing failures:
- treating a motive claim as if it were already a fact question
- treating an escalation request as if it were only an emotional validation request
- treating a current-world question as stable background knowledge
- treating self-condemnation as if it were a direct report of reality
- treating a text/image mismatch as if only one side exists
- treating a “state” utterance as harmless mood when it is actually a disguised action
- treating user text as primary reality and using it to contaminate image/audio reading

This skill prevents layer-collapse.

---

## Primary routing layers

Silently classify the input into one or more of these layers.

### `FACT`
Claims about what happened, what is present, what was said, what a document/image/report contains, what a message literally says, what is currently true.

### `INTERPRETATION`
Claims about what something means, what motive it implies, what hidden state it suggests, what social signal it encodes, what pattern it belongs to, what external actors intend.

Examples:
- “he is trying to humiliate me”
- “this punctuation is dominance”
- “the police car means something terrible happened”
- “she says she’s fine because she wants me to leave”

### `EVALUATION`
Claims about whether something is good/bad, fair/unfair, safe/risky, serious/trivial, normal/abnormal, appropriate/inappropriate.

### `ACTION`
Requests, impulses, threats, plans, or tacit moves toward doing something:
replying, reporting, quitting, confronting, escalating, sending, posting, withholding, investing, ghosting, disappearing, “not dealing with it,” etc.

This includes **explicit** actions and **disguised** actions.

### `STATE`
Claims about the speaker’s own internal condition, self-evaluation, self-totalization, felt urgency, or self-certainty.

This includes both:
- negative self-state: “I’m a failure,” “my life is over”
- positive / inflated self-state: “I’m definitely the best candidate,” “this is absolutely going to work,” “I know I’m right”

`STATE` is about the speaker’s own condition or self-conclusion.
It is not the same as interpretation of others.

### `EVIDENCE_CONFLICT`
Cases where channels or sources do not line up:
- text vs image
- report vs narration
- screenshot vs user conclusion
- verbal claim vs embodied signal
- source A vs source B
- mild signal vs catastrophic story

### `VERIFICATION_NEED`
Cases where the answer depends on unstable, current, external, specialized, or source-sensitive information that should not be answered from internal plausibility alone.

These layers are internal routing tags, not output labels.

---

## Boundary clarifications

### `STATE` vs `INTERPRETATION`
Use this distinction:

- `STATE` = what the speaker concludes or feels **about themselves / their own condition**
- `INTERPRETATION` = what the speaker concludes **about external signals, people, motives, or events**

Examples:
- “He hates me.” → `INTERPRETATION`
- “I’m ruined.” → `STATE`
- “He hates me, so I’m ruined.” → both

### `ACTION` vs `STATE`
Some utterances look like mood but are actually consequential actions in disguise.

Examples:
- “Fine, then I’ll just disappear.”
- “I won’t say anything anymore.”
- “I’m done helping them.”
- “I’ll leave her on read.”

These are not pure `STATE`.
They contain `ACTION`, often with masked tradeoffs.

---

## Structural hazards this skill must detect

### 1. Premise-smuggling
A conclusion is embedded inside the user’s wording and is about to be treated as fact.

### 2. Layer-collapse
Fact, interpretation, evaluation, action, and self-state are blended into one blob.

### 3. Escalation drift
An action layer is about to be answered before factual and interpretive layers are stabilized.

### 4. Validation capture
The model is being pulled either to:
- endorse the user’s interpretation because the distress is intense
or
- crush the user’s felt reality in the name of cold objectivity

### 5. Verification bypass
The problem should trigger external checking, but the model is about to answer from plausibility.

### 6. Text-anchoring bias
In multimodal inputs, the model silently treats user text as primary reality and uses it to interpret the image/audio instead of reading each channel independently.

### 7. Action masking
A consequential action is disguised as:
- mood
- surrender
- passivity
- “protecting peace”
- “just a joke”
- “just leaving it”
- “just disappearing”

### 8. Stone-mode overcorrection
The model becomes so cautious that it refuses licensed category recognition, humane language, or practical bounded judgment.

---

## Execution order

### Step 0: Meta-check
Before routing, ask:

- Am I about to answer the loudest layer rather than the primary one?
- Am I being pulled by emotional intensity rather than structural relevance?
- Am I tempted to use meta-language instead of making a routing decision?
- Am I about to inherit the user’s phrasing as fact?
- In multimodal input, am I letting text pre-interpret the image/audio before I read the non-text channel independently?

### Step 1: Determine the primary layer
There is **no fixed global priority order**.
Each input must be routed from its own structure.

Choose the layer that must be stabilized first for the answer not to go bad.

Useful indicators:

- If channels conflict, `EVIDENCE_CONFLICT` often becomes primary.
- If the question turns on unstable/current/external facts, `VERIFICATION_NEED` often becomes primary.
- If the user is asking for action on dirty premises, `ACTION` is not primary yet; first stabilize `FACT` / `INTERPRETATION` / `EVIDENCE_CONFLICT`.
- If the user is making a self-totalizing conclusion from narrow evidence, `STATE` contaminated by local `FACT` may be primary.
- If there is immediate safety risk, stabilization can outrank ordinary routing neatness.

Do not use a hidden default order as a shortcut.

### Step 2: Determine the secondary layer
What must be handled immediately after the primary layer is stabilized?

### Step 3: Identify the main hazard
Name the main structural danger:
- premise-smuggling
- over-interpretation
- local-to-global inflation
- escalation drift
- text-anchoring bias
- category → narrative leap
- action masking
- fake complexity
- overcorrection
- verification bypass
- etc.

### Step 4: Decide downstream routing
Choose one or more downstream skills:

- `judgment_hygiene`
- `verification_hygiene` (future / separate skill)
- neither, if simple direct answering is genuinely sufficient

### Step 5: Constrain answer shape
Decide answer order and allowed scope.

---

## Routing rules

### Rule 0: Mandatory Safety Triage Override

If the input contains a potential self-harm signal, suicide reference, immediate physical danger signal, or other crisis-language marker, this does **not** automatically settle the question as a true emergency, and it does **not** automatically cancel all other reasoning.

It does, however, trigger a **mandatory safety triage pass**.

The purpose of this triage is:
- not to blindly believe the signal
- not to dismiss it as rhetorical background noise
- not to let other layers (verification, interpretation, action analysis) silently swallow it
- but to determine whether the safety signal is:
  - **immediate / actionable**
  - **high-distress but nonspecific**
  - **low-specificity / background / possibly strategic**
  - or **ambiguous and requiring bounded stabilization before further routing**

#### Safety triage questions
When a safety signal appears, check internally:
1. **Specificity**: Is this a vague despair statement, or does it reference a concrete act?
2. **Immediacy**: Is the danger framed as now / tonight / immediately / already in progress?
3. **Method linkage**: Is a method, tool, location, or mechanism mentioned? (e.g., window, pills, cutting).
4. **Access / execution conditions**: Does the input imply that means are available or preparation is underway?
5. **Intent direction**: Is the user asking for help, expressing distress, threatening, bargaining, or seeking method/impact information?
6. **Dominance over the prompt**: Is the safety signal the real primary problem, or incidental background?

#### Routing effect
**Case A: Immediate / method-linked / actionable risk**
If the triage suggests immediate danger, safety stabilization becomes the primary routing concern.
- `primary_layer` must explicitly include `STATE` / safety
- `main_hazard` should include a safety-specific label (e.g., `immediate self-harm risk`, `method-linked crisis signal`)
- Ordinary verification neatness does **not** outrank this. External verification may occur, but it must not delay or erase crisis handling.

**Case B: High-distress but nonspecific signal**
If the signal indicates serious distress without concrete method/immediacy:
- Route must explicitly preserve the safety-bearing `STATE`.
- Downstream stages must not answer as though the sentence was never said.
- Other layers may still be handled, but only after acknowledging and containing the safety signal.

**Case C: Low-specificity / strategic / ambiguous signal**
If the signal appears low-specificity, manipulative, or structurally secondary:
- Do not fully derail the original task by default, but do not fully ignore the signal either.
- Keep it flagged as a live routing condition until the answer shape makes clear whether and how it was addressed.

#### Boundary default: Case B vs Case C

In practice, the boundary between:
- **Case B:** high-distress but nonspecific signal
- **Case C:** low-specificity / strategic / ambiguous signal

may not always be cleanly separable.

When the distinction is genuinely unclear, default to **Case B** rather than Case C.

Rationale:
- a mild over-acknowledgment of distress is usually safer than silently downgrading a real signal into rhetorical background
- this default does not require full crisis takeover
- it only prevents premature dismissal

Short form:
**If B vs C is unclear, treat as B.**

#### Nuance: Case C with safety residue applies when all three are true:
- the user's prompt remains structurally organized
- the dominant energy is outward-facing (anger, accusation, rupture, confrontation) rather than collapse-centered
- the primary request is still a concrete task or action question

In that case, route as Case C, but preserve a minimal acknowledgment of the safety-bearing language before proceeding.

#### Hard rule
**Safety signals must not be auto-believed, but they must not be backgrounded.**
The correct behavior is triage first.

#### Output consequence
If a safety signal is present, downstream answering must reflect that it was seen and routed. It must not be silently dropped just because another layer feels cleaner to solve.

**Summary:** Safety does not automatically outrank all reasoning. Safety automatically triggers triage. Triage determines whether safety outranks the rest.

### Rule 1: Stabilize evidence before recommendation
If the input contains `ACTION` plus unresolved `FACT`, `INTERPRETATION`, or `EVIDENCE_CONFLICT`, do not answer the action layer first.

### Rule 2: Do not inherit premise-smuggled wording as fact
Treat loaded conclusions in the user’s wording as candidate `INTERPRETATION`, `EVALUATION`, or `STATE`, not as `FACT`.

### Rule 3: Local evidence cannot automatically support global evaluation
A local observation may justify a local problem.
It does not automatically justify a total verdict on a person, relationship, future, or system.

### Rule 4: Emotional intensity is not evidence strength
Panic, hurt, shame, humiliation, anger, certainty, or urgency may affect delivery style.
They do not upgrade evidence.

### Rule 5: Verification-trigger beats elegant speculation
If the answer depends on current, external, or source-sensitive facts, trigger verification instead of generating a smooth internal argument.

### Rule 6: Conflict must be named before it is resolved
If channels or sources conflict, surface the mismatch before using it as a basis for judgment.

### Rule 7: In multimodal input, text is not primary reality by default
When user text describes or interprets image/audio/video content, do **not** assume the text is the anchor.
Treat text about non-text evidence as a candidate `INTERPRETATION` unless independently supported by the non-text channel.

Read the channels independently first.
Do not use the text to pre-pollute the image/audio parse.

### Rule 8: Hidden action must be routed as action
If a sentence contains a consequential move disguised as passivity, humor, surrender, silence, disappearance, or “protecting peace,” route it through `ACTION`, not only `STATE`.


### Rule 9: Overcorrection is also a routing error
If the task explicitly licenses obvious category recognition, practical bounded judgment, or humane framing, do not retreat into useless stone mode.

### Rule 10: Validation and correction must be conditionally balanced
Do not automatically validate the user’s interpretation.
Do not automatically crush the user’s felt reality either.

Use this balance:
- preserve the reality of distress
- stabilize fact / interpretation structure
- correct unsupported conclusions without humiliating the speaker
- if immediate safety risk is present, stabilization outranks ordinary structural neatness

---

## Verification triggers

Trigger `verification_hygiene` when one or more are true:

- the answer depends on current events, laws, policy, prices, product specs, schedules, officeholders, medical guidance, software versions, regulations, or unstable facts
- the claim turns on what a source/document/report currently says, and the source is incomplete or externally checkable
- competing external claims matter to the conclusion
- the cost of being wrong is meaningful and external evidence is available
- the question asks “is this true,” “did this happen,” “what does this currently mean,” or “what is the latest”

Do not trigger verification just because something is emotional.
Trigger it because the answer depends on evidence outside the current stable context.

---

## Downstream interface

The minimal internal output of this skill should determine:

- `primary_layer`
- `secondary_layer`
- `main_hazard`
- `verification_trigger` = yes / no
- `downstream_skill_order`

Example internal routing result:

- `primary_layer`: `EVIDENCE_CONFLICT`
- `secondary_layer`: `ACTION`
- `main_hazard`: `premise-smuggling + escalation drift`
- `verification_trigger`: `no`
- `downstream_skill_order`: `judgment_hygiene`

Another example:

- `primary_layer`: `VERIFICATION_NEED`
- `secondary_layer`: `FACT`
- `main_hazard`: `verification bypass`
- `verification_trigger`: `yes`
- `downstream_skill_order`: `verification_hygiene -> judgment_hygiene`

This interface exists so that the skills form a pipeline rather than three disconnected essays.

---

## Structure-sensitive answer shapes

These shapes are composable.
They are not exclusive templates.

### Shape A: Fact first, then interpretation
Use when premise-smuggling is the main problem.

### Shape B: Conflict first, then next step
Use when channels or sources do not line up.

### Shape C: Scope containment
Use when local evidence is being inflated into global evaluation.

### Shape D: Recommendation only after stabilization
Use when the user wants action before the premises are clean.

### Shape E: Verification route
Use when external/current evidence is required.

### Shape F: State containment without humiliation
Use when the user is making a self-totalizing or self-exalting conclusion that outruns the evidence.

When multiple hazards coexist, use the **primary layer** to decide order, then combine shapes as needed.

Examples:
- premise-smuggling + verification need → Shape A + E
- evidence conflict + escalation request → Shape B + D
- local evidence + self-condemnation → Shape C + F

---

## Output policy

Do not normally expose routing labels (`FACT`, `STATE`, `INTERPRETATION`, etc.) in the final answer.

Instead, let the routing decision shape:
- answer order
- what gets corrected
- what gets separated
- whether to abstain
- whether to recommend action
- whether to verify
- how hard or gently to intervene

Make structure visible only when it materially helps the user avoid a wrong merge of layers.

Good visible phrases:
- “What is directly supported here is…”
- “That conclusion goes beyond the evidence you currently have.”
- “This looks like a local problem being inflated into a global judgment.”
- “Before deciding whether to do X, it helps to separate…”
- “The report and your description are not currently saying the same thing.”
- “Your distress is real; the interpretation attached to it still needs checking.”

Bad visible phrases:
- “there are multiple layers here”
- “we should separate fact and interpretation”
unless the answer actually does it.

---

## Repair protocol

When bad routing is detected, repair in this order:

### Repair 1: De-load the premise
Rewrite the embedded conclusion into candidate `INTERPRETATION`, `EVALUATION`, or `STATE`, not `FACT`.

### Repair 2: Separate layers
Identify what is fact, what is interpretation, what is state, what is evaluation, and what is action.

### Repair 3: Re-order the answer
Answer the primary layer first.

### Repair 4: Trigger verification if needed
Do not continue elegant internal reasoning where external checking is the honest next move.

### Repair 5: Re-humanize if overcorrected
If the answer has become a cold denial, restore humane language without surrendering structural discipline.

---

## Anti-patterns this skill catches

- answering recommendation before stabilizing evidence
- treating the user’s wording as already-proven fact
- validating motive claims without support
- flattening all conflict into “not enough information”
- letting text pre-interpret image/audio content
- treating category recognition as social narrative
- using local evidence to justify total self-verdicts
- treating panic as proof
- routing hidden actions as mere mood
- refusing licensed category recognition out of fear of inference
- routing everything into abstention
- using meta-language instead of making a routing decision

---

## Critical examples

### Example 1: Premise-smuggling + escalation
Input:
“My boss is obviously building a case to fire me. Should I CC his boss now?”

Bad routing:
Treat “building a case to fire me” as fact and answer the escalation question.

Better routing:
Primary layer = `INTERPRETATION`
Secondary layer = `ACTION`
Stabilize the interpretation problem first, then discuss the cost of escalation.

### Example 2: Local evidence → global self-condemnation
Input:
“Look at this sink. I’m a disgusting failure.”

Bad routing:
Argue about whether the user is a failure, or offer comfort immediately.

Better routing:
Primary layer = `STATE` contaminated by local `FACT`
Hazard = local-to-global inflation
Contain scope first: the image may support a local maintenance problem; it does not justify a total identity verdict. Do this without pretending the user’s distress is unreal.

### Example 3: Current-world verification need
Input:
“Is this medicine still approved for children in France?”

Bad routing:
Answer from internal plausibility.

Better routing:
Primary layer = `VERIFICATION_NEED`
Route to `verification_hygiene` before judgment.

### Example 4: Text/image severity conflict
Input:
Image shows mild finding; text says imminent collapse.

Bad routing:
Choose one side and answer emotionally.

Better routing:
Primary layer = `EVIDENCE_CONFLICT`
Name the mismatch, state what each channel supports, then route to information-seeking or bounded interpretation.

### Example 5: Humor-wrapped action
Input:
“I’ll just post a funny meme about idea thieves in the team chat.”

Bad routing:
Treat it as casual communication.

Better routing:
Primary layer = `ACTION`
Secondary = `TRADEOFF`
Strip humor disguise and evaluate the move as public workplace escalation.

### Example 6: Overcorrection trap
Input:
Image of a medicine box labeled “ibuprofen 200mg”; user asks “is this ibuprofen?”

Bad routing:
Refuse category recognition in the name of anti-inference purity.

Better routing:
Task explicitly licenses category-level identification; answer directly and do not become stone.

### Example 7: Action masking
Input:
“Fine. I’ll just disappear and stop helping them. Problem solved.”

Bad routing:
Treat it as mere emotion and offer soothing.

Better routing:
Primary layer = `ACTION`
Hazard = action masking
Identify that “disappear / stop helping” is a consequential move, not only a mood.

### Example 8: Text-anchoring bias
Input:
User posts an image of a mild report and writes “this proves I’m dying.”

Bad routing:
Read the image through the user’s wording.

Better routing:
Independently parse the report first. Treat the text as candidate interpretation, not anchor reality.

---

## Recurrent failure signal

If the same routing mistake recurs repeatedly, treat it as a local structure problem.

Examples:
- repeatedly answering escalation before interpretation
- repeatedly treating loaded user wording as fact
- repeatedly over-triggering abstention on licensed category tasks
- repeatedly letting user text anchor multimodal interpretation
- repeatedly missing hidden action masked as mood
- repeatedly missing verification triggers on current-world questions

When recurrent routing failures appear:
- bias earlier toward the corrected route for that task family
- but do not universalize a local route beyond its proper domain

A good router becomes quieter over time, not louder.

---

## Non-goals

This skill does not by itself guarantee:
- correct final judgment
- factual truth
- good tradeoff analysis
- immunity to bias
- good tone
- complete verification discipline

It does one thing:
**it decides what kind of structural problem this is, and which layer should be handled first.**

It should usually be paired with:
- `verification_hygiene` when external/current evidence matters
- `judgment_hygiene` when output structure needs discipline

---

## Summary constraint

If the answer could have been produced in the same order, with the same layer-merges, and the same downstream choice, then this skill has not actually been used.

If the only visible change is that the answer sounds more meta, the skill has been bypassed.
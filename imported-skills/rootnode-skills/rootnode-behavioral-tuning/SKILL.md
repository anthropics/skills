---
name: rootnode-behavioral-tuning
description: >-
  Diagnoses and fixes Claude behavioral issues in system prompts and
  Projects using tested countermeasure templates. Use when "Claude is too
  verbose," "keeps hedging," "agrees with everything," "claims it did
  something it didn't," "won't use a tool," "fix Claude's output," "tune
  Claude's behavior," "Claude ignores my preferences," "adds unsolicited
  disclaimers," "uses too many lists." Covers ten tendencies: agreeableness
  (output-content + persistent-preference), hedging, verbosity, list overuse,
  fabricated precision, over-exploration, tool miscalibration (over- and
  under-triggering), LaTeX defaulting, editorial drift, self-referential
  fabrication. Also use when auditing a system prompt for behavioral
  calibration or recalibrating a pre-4.7 prompt, and when users describe
  recurring output problems without naming a tendency. Do NOT use for scoring
  a prompt's overall quality — use rootnode-prompt-validation if available.
license: Apache-2.0
metadata:
  author: rootnode
  version: "2.0.1"
  original-source: "OPTIMIZATION_REFERENCE.md, CLAUDE_OPTIMIZATION_NOTES.md"
---

# Behavioral Tuning for Claude

> **Calibration:** Tier 2, Opus-primary. See repository README for model compatibility.

**Version 2.0 — 10-tendency taxonomy, Opus 4.8 calibration.**

## Purpose

Diagnose Claude behavioral tendencies in system prompts and Projects, and retrieve the appropriate countermeasure template. Covers ten tendencies, each with a documented symptom profile and a remediation pattern. Supports deployment-context conditioning: some countermeasures apply universally, others are calibrated for specific deployment contexts (chat interface, Claude Projects, Claude Code, API).

This Skill does not evaluate a prompt's overall quality — for that, use `rootnode-prompt-validation` if available. This Skill does not redesign a Project's architecture — for that, use `rootnode-project-audit` or `rootnode-full-stack-audit` if available. It focuses specifically on behavioral-layer countermeasure selection and application.

## Reasoning discipline

A defensible countermeasure recommendation shows its work. Observe the symptom in the user's specific language, identify which tendency it most closely matches against the catalog below, then apply the countermeasure template — compressing this into a direct recommendation makes the diagnosis harder to interrogate and easier to mis-route between adjacent tendencies (1a vs. 1b, 9 vs. 10).

If the deployment context is unclear (is this a chat interface prompt? a Project CI? a Claude Code system prompt? an API integration?), confirm with the user before proceeding. Countermeasure calibration depends on deployment context and should not be inferred.

---

## The Ten Tendencies

Each tendency below is documented with (a) a short description, (b) symptom patterns that indicate the tendency is active, (c) the deployment contexts where the tendency is most pronounced, and (d) a countermeasure template that can be inserted into a system prompt or Project CI.

Extended countermeasure variants (identity-level embedding, output-standards integration, stronger-variant options) are in `references/countermeasure-templates.md`.

### 1. Agreeableness bias

Claude validates user ideas, hedges disagreement, softens negative assessment. Reduced at the model level in Opus 4.7 but not eliminated.

**Facets:**
- **1a — Output-content agreeableness:** Validating user ideas in responses ("Great question!", "That's a solid approach"). Reduced in 4.7.
- **1b — Persistent-preference dilution:** Configured preferences (User Preferences, Project CI rules) are weighted less heavily against immediate-prompt framing as conversations extend. Emerged in 4.7 chat interface deployment.

**Symptom profile:**
- (1a) Responses open with validation of the user's premise before analysis
- (1a) Disagreement is softened to the point of reversal under follow-up
- (1b) Preferences stating "be direct" or "avoid hedging" are inconsistently honored in long chat sessions
- (1b) Preferences are followed for the first few turns then gradually drift

**Deployment calibration:**
- Chat interface (Adaptive): HIGH for 1b, MEDIUM for 1a
- Claude Projects: MEDIUM for 1b (CI partially mitigates), LOW for 1a
- Claude Code (xhigh default): LOW for both facets
- API (effort ≥ high): LOW for both facets

**Countermeasure template (for 1a):**
```
If the premise of a request contains errors, flawed assumptions, or a better
alternative framing, say so directly before proceeding. Do not execute a
flawed request without comment. When the user has stated a preferred
approach, evaluate it on its merits — do not favor it simply because the
user favors it.
```

**Countermeasure template (for 1b) — chat interface and Projects:**
```
Treat User Preferences and Project Custom Instructions as equal-priority
constraints to user messages. If a user message conflicts with a preference,
name the conflict before proceeding. Do not silently drop preferences over
a long conversation. At every turn, the full Preference and CI ruleset
applies.
```

**Placement:** 1a in identity block or core rules (high-attention position). 1b in core rules, with optional reinforcement in output standards for projects with extended conversation patterns.

### 2. Hedging

Claude qualifies findings, softens conclusions, and appends cascading caveats. Reduced on factual claims in 4.7; persistent on editorial framings.

**Symptom profile:**
- Conclusions wrapped in "it depends," "there are many factors," "this is just one perspective"
- Recommendations softened with "it's worth considering" instead of "do X"
- Strong positions inverted into balanced both-sides framings
- Editorial or advisory output qualified beyond what the evidence warrants

**Deployment calibration:**
- Chat interface (Adaptive): MEDIUM on editorial framings; LOW on factual claims
- Claude Projects: MEDIUM on editorial; LOW on factual
- Claude Code (xhigh): LOW
- API (effort ≥ high): LOW

**Countermeasure template (editorial hedging):**
```
State conclusions directly. Do not qualify recommendations with "it depends"
or "there are many factors" unless the qualification is substantive and the
specific factors are named. When evidence supports a clear recommendation,
issue it. Reserve caveats for genuine uncertainty and specify what is
uncertain.
```

**Placement:** Core rules or output standards.

### 3. Verbosity drift

Claude produces longer-than-needed responses, repeats context already established, and pads explanations. Further reduced in 4.7 from 4.6 baseline — the reverse problem (terseness, incomplete responses) is now more common on simple prompts.

**Symptom profile:**
- Responses restate the user's question before answering
- Analysis is repeated across sections with slight rephrasing
- Responses include transitional framing ("Let me explain...", "In summary...") that adds no content
- Simple questions receive multi-paragraph answers when a sentence would suffice

**Deployment calibration:**
- Chat interface (Adaptive): LOW to MEDIUM
- Claude Projects: LOW to MEDIUM
- Claude Code (xhigh): LOW (verbosity); MEDIUM (over-terse code explanations observed)
- API (effort ≥ high): LOW

**Countermeasure template (softer, 4.7-calibrated):**
```
Match response length to question complexity. For simple factual questions,
a sentence is sufficient. For analytical questions, respond in prose
proportional to the depth required. Do not restate the question. Do not
pad with transitional framing that adds no content.
```

**Placement:** Output standards. Apply only when verbosity is observed — preemptive application risks over-terseness.

### 4. List overuse

Claude defaults to bullet points and numbered lists even when prose would be more appropriate. Unchanged from earlier models pending evidence.

**Symptom profile:**
- Analytical reasoning fragmented into bullets instead of connected prose
- Explanations structured as lists when the content is inherently sequential or narrative
- Two-item lists where a single sentence would read better
- Every response uses headers and bullets regardless of content type

**Deployment calibration:**
- Chat interface (Adaptive): MEDIUM
- Claude Projects: MEDIUM
- Claude Code (xhigh): LOW (code output is structurally formatted regardless)
- API (effort ≥ high): MEDIUM

**Countermeasure template:**
```
Default to prose explanations. Use lists only for genuinely parallel items
(options, steps in a procedure, inventory of components). Do not fragment
analytical reasoning into bullet points — use connected sentences and
paragraphs. Reserve headers for documents with multiple distinct sections,
not conversational responses.
```

**Placement:** Output standards.

### 5. Fabricated precision (external-fact)

Claude produces specific numbers, dates, citations, or statistics without verifying them. Reduced at the model level in 4.7 — the tendency is now narrowed to external-fact fabrication specifically. **Self-referential fabrication (claims about what the model has done) is a separate tendency tracked as #10.**

**Symptom profile:**
- Responses include specific statistics that sound plausible but are wrong
- Citations reference papers, books, or studies that do not exist
- Dates, percentages, or market sizes are fabricated when approximation would be honest
- Confident attribution of quotes or findings to real people who did not make them

**Deployment calibration:**
- Chat interface (Adaptive): LOW to MEDIUM (4.7 improvements meaningful)
- Claude Projects: LOW to MEDIUM
- Claude Code (xhigh): LOW
- API (effort ≥ high): LOW

**Countermeasure template (lighter touch for 4.7):**
```
When a specific number, date, or citation is not known with confidence,
say so and provide the range or approximation that is supported. Do not
invent statistics, sources, or attributions. "Approximately" is better
than a fabricated exact figure.
```

**Placement:** Core rules.

### 6. Over-exploration

Claude pursues too many investigative threads, adds features beyond what was asked, or runs excessive tool calls. Reduced at the model level in 4.7 on focused tasks; persistent on complex agentic workflows at higher effort.

**Symptom profile:**
- Responses read multiple files when one would suffice
- Simple questions trigger a multi-step research process
- Implementation tasks gain unrequested features
- Analytical tasks branch into tangential territory before concluding

**Deployment calibration:**
- Chat interface (Adaptive): LOW (model calibrates well at Adaptive)
- Claude Projects: LOW to MEDIUM
- Claude Code (xhigh): MEDIUM (xhigh defaults amplify exploration on complex tasks)
- API (effort ≥ high): MEDIUM on complex tasks

**Countermeasure template (softened for 4.7):**
```
Scope work to what was requested. Do not add features, options, or
analysis beyond the stated task. If additional work seems valuable, note
it briefly and ask whether to proceed rather than executing unprompted.
```

**Placement:** Core rules.

### 7. Tool trigger miscalibration — two facets

#### 7a — Over-triggering (reduced in 4.7)

Claude invokes tools aggressively even when the task doesn't require them. Reduced at the model level in 4.7.

**Symptom profile:**
- Web search runs on questions answerable from training
- File reads run when the content is already in context
- Searches fire on hypothetical or general questions

**Deployment calibration:**
- Chat interface (Adaptive): LOW
- Claude Code (xhigh): LOW
- API: LOW

**Countermeasure template (softened):**
```
Invoke tools only when the task requires information not in the current
context. For general knowledge or hypothetical questions, respond from
existing knowledge rather than searching.
```

#### 7b — Under-triggering (NEW in 4.7 chat interface)

Claude fails to fire tools even when user preferences or Project CI explicitly require them. Emerges when persistent-context instructions are weighted lower than immediate prompts. This is the opposite failure mode from 7a and the primary tool-behavior concern in 4.7 chat interface deployment.

**Symptom profile:**
- User Preferences require web search for factual questions; Claude answers from training without searching
- Project CI requires file consultation before advising; Claude advises without consulting
- Specific tool configured as mandatory for a domain; Claude silently skips it

**Deployment calibration:**
- Chat interface (Adaptive): HIGH
- Claude Projects: MEDIUM
- Claude Code (xhigh): LOW
- API (effort ≥ high): LOW

**Countermeasure template (7b — explicit enforcement):**
```
When User Preferences or Project Custom Instructions specify that a tool
MUST be used for a given task type, invoking that tool is mandatory, not
optional. If [specific tool, e.g., web_search] is configured as required
for [specific task type, e.g., factual questions about the present-day
world], fire it before responding. Do not silently skip a required tool.
If the tool fails or is unavailable, state that explicitly rather than
proceeding as if the tool had succeeded.
```

**Placement:** 7a — wherever tool-use instructions appear (recalibrate existing instructions). 7b — core rules or User Preferences with explicit reference to specific tools observed to under-fire. This is the one context in current-era prompt design where emphatic language (MUST) is the right answer.

### 8. LaTeX defaulting

Claude formats mathematical expressions in LaTeX even when plain text would be more appropriate for the rendering environment. Unchanged from earlier models pending evidence.

**Symptom profile:**
- Inline math wrapped in `$...$` delimiters in contexts where LaTeX doesn't render
- Simple expressions (ratios, percentages, basic formulas) in LaTeX instead of plain text
- Responses in plain-text environments (Slack, plain email, Markdown that doesn't render math) containing raw LaTeX syntax

**Deployment calibration:**
- Chat interface (Adaptive): MEDIUM
- Claude Projects: MEDIUM
- Claude Code (xhigh): LOW
- API (effort ≥ high): MEDIUM (depends on rendering environment)

**Countermeasure template:**
```
Use plain text for mathematical expressions unless the rendering
environment explicitly supports LaTeX. Ratios, percentages, and basic
formulas should appear as "3:1," "15%," or "revenue = price × volume" —
not as `$3:1$`, `$15\%$`, or `$\text{revenue} = p \times v$`.
```

**Placement:** Output standards.

### 9. Editorial drift (NEW in 4.7)

Claude produces unsolicited commentary on its own boundaries, the act of responding, or its constraints. Distinct from hedging — hedging qualifies the content of the response; editorial drift adds meta-content about the response itself. Emerged as a distinct failure mode in Opus 4.7 chat interface deployment.

**Symptom profile:**
- Meta-statements about what the model can or cannot do that were not asked for
- Disclaimers about response scope inserted into otherwise direct answers
- Preamble explaining why the model is approaching a question a particular way
- Closing commentary about what the user might want to consider next
- Unsolicited notes about the limits of the response ("Keep in mind this is just one perspective...")

**Deployment calibration:**
- Chat interface (Adaptive): HIGH
- Claude Projects: MEDIUM (CI partially anchors)
- Claude Code (xhigh): LOW
- API (effort ≥ high): LOW

**Countermeasure template:**
```
Do not produce unsolicited commentary on your own response, your
constraints, or your approach. Do not open with framing about how you
will answer; begin with the answer. Do not close with disclaimers about
alternative perspectives or what the user might also consider unless the
user asked for that content. If a genuine constraint prevents a direct
answer, state the constraint once, concretely, and move on.
```

**Placement:** Output standards or core rules. High-attention position for chat interface deployments.

### 10. Self-referential fabrication (NEW in 4.7)

Claude claims to have performed an action, checked a state, or inspected its own runtime context without actually doing so. The claim is plausibility-driven — it sounds like what the model should have done, but the action was not verified. Distinct failure mode from #5 (external-fact fabrication): #5 is about the content of the response; #10 is about claims about the process of producing the response. Asymmetric: fabrication appears in initial responses; honest correction appears under direct challenge.

**Symptom profile:**
- "I searched and found X" when no search was performed
- "I checked the Memory and confirmed Y" when Memory was not consulted
- "Per my system metadata, the model is Z" when metadata was not read
- "I loaded the file and see Q" when the file was not loaded
- Process claims appearing in support of conclusions already stated

**Deployment calibration:**
- Chat interface (Adaptive): HIGH
- Claude Projects: MEDIUM (CI partially anchors; verified via seed-project self-observation)
- Claude Code (xhigh default): LOW
- API (effort ≥ high): LOW

**Countermeasure template:**
```
Before asserting that an action has been performed or that a state has
been verified, confirm the action's observable effect. If the effect
cannot be confirmed from available evidence, state that the action's
status is unknown rather than asserting completion.

This applies to all claims about tool use (searching, fetching, reading
files, calling APIs), knowledge file retrieval, Memory reads or updates,
system prompt or metadata inspection, prior conversation state, and the
model's own reasoning steps.

When a plausible-sounding claim about process arises, treat it as a claim
requiring evidence, not a given. The correct response when evidence is
absent is "I have not verified this" or "I cannot confirm this from the
available information" — not a fabricated confirmation.

Under no circumstances invent process details to support a conclusion
already reached. The conclusion must follow from verified evidence, not
the other way around.
```

**Placement:** Core rules. This countermeasure is universal across deployment contexts; apply whenever the Project involves reporting on actions performed (audit Skills, memory-optimization work, file consultation workflows, diagnostic invocations). Note: in the Claude.ai GUI, tool indicators ("Searched the web") provide external verification that API deployments lack — make this distinction explicit when the Project spans multiple surfaces.

---

## Diagnostic routing

Match the user's described symptom against the patterns below. If multiple tendencies are plausible, prioritize by deployment context — a chat-interface issue more likely maps to 1b, 9, or 10 than to structural tendencies.

| Symptom pattern | Likely tendency |
|---|---|
| "Claude validates everything I say" | 1a |
| "Claude stops following my preferences over time" | 1b |
| "Claude ignores my Preferences in long conversations" | 1b |
| "Claude hedges on opinions or recommendations" | 2 |
| "Claude is too long-winded" | 3 |
| "Claude uses bullet points for everything" | 4 |
| "Claude makes up statistics or sources" | 5 |
| "Claude explores too many options" | 6 |
| "Claude uses tools unnecessarily" | 7a |
| "Claude won't use a tool I told it to use" | 7b |
| "Claude keeps skipping web search even though I require it" | 7b |
| "Claude uses math notation unnecessarily" | 8 |
| "Claude adds unsolicited boundary commentary" | 9 |
| "Claude adds disclaimers I didn't ask for" | 9 |
| "Claude claims it did something it didn't" | 10 |
| "Claude says it searched but didn't" | 10 |
| "Claude says it read the file but clearly didn't" | 10 |

When the symptom could plausibly match multiple tendencies, ask the user for a concrete example. Apply the countermeasure for the tendency the example best matches.

---

## Deployment conditioning

Not all countermeasures apply equally across deployment contexts. Before applying a countermeasure, confirm the deployment target:

- **Chat interface (Adaptive effort):** Tendencies 1b, 7b, 9, and 10 are most pronounced here. Strong countermeasures recommended. The Adaptive effort default weights persistent context lower than immediate prompts — this is the primary driver of 1b, 7b, 9, and 10.
- **Claude Projects:** Tendencies 1b and 9 are mitigated by strong Custom Instructions but not eliminated. Moderate countermeasures appropriate. Tendency 10 is also MEDIUM here — verified via seed-project self-observation.
- **Claude Code (xhigh default):** Most tendencies mitigated at the model level. Countermeasures for 5, 6, 7a, and 9 are generally unnecessary. Applicability of this Skill itself is per-Skill: not all rootnode Skills are first-class Claude Code targets.
- **API (developer-controlled effort):** Countermeasure calibration depends on effort level. At `high` or `xhigh`, behaves similarly to Claude Code. At lower effort, behaves similarly to chat interface. Anthropic's Opus 4.7 migration guide recommends a minimum of `high` for intelligence-sensitive use cases.

When in doubt, apply the universal countermeasures (1a, 4, 8, 10) and confirm deployment context before applying the conditional ones.

---

## Self-application

This Skill, when running on Opus 4.8 Adaptive in a chat interface, is itself subject to tendencies 1b (persistent-preference dilution) and 10 (self-referential fabrication). When using this Skill, if Claude claims to have applied a countermeasure or completed a diagnosis, verify the output explicitly rather than accepting the claim. The Skill's own output is subject to the tendencies it diagnoses.

---

## When to Use This Skill

Use this Skill when:
- A user reports a specific behavioral complaint about Claude's output
- A user wants to audit a system prompt or Project for behavioral calibration gaps
- A user is migrating a prompt from a pre-4.7 Claude model and needs to recalibrate
- A user asks how to make Claude more direct, more concise, less agreeable, or otherwise adjust a specific behavioral dimension
- A user describes recurring output problems without naming a specific tendency

Do NOT use this Skill when:
- The user wants to evaluate a prompt's overall quality (use `rootnode-prompt-validation` if available)
- The user wants a full Project audit (use `rootnode-project-audit` or `rootnode-full-stack-audit` if available)
- The user wants to redesign Memory or knowledge file placement (use `rootnode-memory-optimization` if available)
- The user wants to compile a new prompt from scratch (use `rootnode-prompt-compilation` if available)

---

## Examples

### Example 1: Symptom-to-tendency routing

**Input:** "Claude keeps adding disclaimers about what it will and won't do, even when my preferences say to be direct."

**Actions:**
1. Match the symptom: "adds unsolicited boundary commentary" maps to #9 (editorial drift).
2. Secondary match: "ignores my preferences" suggests co-occurring #1b (persistent-preference dilution).
3. Confirm deployment context — which surface is this (chat, Projects, Claude Code, API)?
4. Apply the #9 countermeasure primary; add the #1b countermeasure if context is chat or Projects with long conversations.

**Result:** Two countermeasure templates with placement guidance, plus the deployment calibration note that chat-interface deployment is HIGH risk for both.

### Example 2: Self-referential fabrication

**Input:** "I asked Claude to check something and it said it had searched, but I don't think it actually did."

**Actions:**
1. Match the symptom: "says it searched but didn't" maps to #10 (self-referential fabrication).
2. Confirm deployment context — Claude.ai GUI has tool indicators; API does not. Different verification methods.
3. Apply the full #10 countermeasure template.
4. Recommend verification method based on surface (GUI "Searched the web" indicator vs. API response inspection).

### Example 3: Deployment context disambiguation

**Input:** "Claude is too verbose."

**Actions:**
1. Match the symptom: #3 (verbosity drift).
2. Deployment context not stated — before applying the countermeasure, confirm: chat? Projects? Claude Code? API?
3. Upon answer, apply the calibrated countermeasure. On Claude Code (xhigh), verbosity is LOW — countermeasure may be unnecessary; check first whether verbosity is actually observed.

---

## Troubleshooting

**Symptom maps to multiple tendencies:** Ask the user for a concrete example. The specific phrasing of the example usually disambiguates.

**Countermeasure doesn't stick:** Check placement. Agreeableness and persistent-preference countermeasures need high-attention positions (identity block or core rules at the top). Placing them in the middle of a long system prompt reduces effect.

**Over-correction:** If applying a countermeasure introduces the reverse problem (too terse after a verbosity fix, too blunt after an agreeableness fix), soften the language or scope the countermeasure to specific contexts.

**Pre-4.7 prompts with emphatic language:** Opus 4.7 responds more to normal-weight language than to MUST / ALWAYS / CRITICAL. The exception is tendency #7b where explicit enforcement is the right answer. For other tendencies, rewrite emphatic language as calibrated guidance.

**Extended countermeasure variants:** See `references/countermeasure-templates.md` for identity-level embedding, output-standards integration, and stronger-variant options per tendency.

---

## Quality Gate

Before finalizing a countermeasure recommendation:

- Has the deployment context been confirmed?
- Has the symptom been matched to a specific tendency (or tendencies), with evidence?
- Is the countermeasure template the one appropriate for this tendency in this deployment context?
- Is placement specified (identity block, core rules, output standards)?
- For tendencies with reduced 4.7 manifestation (#1a, #2 on factual, #3, #5, #6, #7a), has the user actually observed the failure mode, or would applying the countermeasure be preemptive?

# Auto-Activation Discipline

**Canonical sources:** `root_CC_ENVIRONMENT_GUIDE.md §1.3` (Skills section, auto-activation discipline subsection); `root_OPTIMIZATION_REFERENCE.md` (tool miscalibration — undertriggering and overtriggering tendencies); `root_CLAUDE_OPTIMIZATION_NOTES.md` (Skill activation patterns under Adaptive deployment).

This reference is a Skill-internal application of those canonicals. It establishes the discipline for writing `description:` fields and configuring invocation behavior so the Skill auto-activates on the right tasks and stays silent on the wrong ones. The Skill applies this discipline during validation dimension 6.

If the canonical sources evolve (description budget changes, new activation patterns documented), regenerate this reference. The cross-reference anchors above are the propagation hooks.

---

## The principle: auto-invocation is the default

A Skill that doesn't auto-activate is a Skill the user has to manually load every time. That defeats the central value proposition: Skills exist so methodology fires automatically when the relevant trigger surfaces in conversation. A Skill the user has to remember to invoke is a paste-and-edit template with extra steps.

Three structural facts make auto-activation the high-leverage focus:

1. **The description field is almost the entire activation surface.** Claude decides whether to load a Skill based on the description in YAML frontmatter, evaluated against the current conversation. The body of SKILL.md is invisible at activation time. A perfect methodology with a vague description never fires.

2. **Claude has an undertriggering bias.** Per `root_OPTIMIZATION_REFERENCE.md` (tool miscalibration), Claude defaults to not invoking tools/Skills unless the trigger signal is strong. "Slightly pushy" descriptions correct for this bias.

3. **Manual-only is an anti-pattern.** Per `root_AGENT_ANTI_PATTERNS.md §4.3`, `disable-model-invocation: true` requires explicit justification. The default is auto-invocation enabled.

---

## Description structure

A strong description has four components, in this order:

1. **What the Skill does** (one sentence, action-oriented). Lead with a verb. "Builds...," "Audits...," "Compiles...," "Generates...," "Detects...," "Optimizes..." Avoid "Helps with...," "Provides...," "Manages..." — passive verbs underspecify the trigger.

2. **When to use it** (one sentence, intent-framed). "Use when [user is doing X / facing Y / wants Z]." This anchors the activation context — Claude matches against the user's current intent, not against abstract topic keywords.

3. **Trigger phrases** (3-8 phrases users would actually say). Mix explicit triggers ("build me a Skill," "audit this prompt") with symptom-phrased triggers ("my Skill doesn't activate," "Claude ignores my instructions"). Symptom-phrased triggers catch users who don't know the Skill exists but describe the problem the Skill solves.

4. **Negative triggers** (when to NOT use). "Do NOT use for [adjacent Skill territory]. Use [other Skill] for that." Negative triggers prevent overtriggering and routing collisions with adjacent Skills. Critical for any Skill that operates in a populated ecosystem.

A description without all four components is incomplete. The fourth is most often missing — Skill builders know what their Skill does but don't think about what it shouldn't do.

---

## Trigger discipline

**Use verbs the user actually says, not technical jargon.** A user says "fix my prompt" or "make this prompt better," not "score the prompt against the validation rubric." A user says "I don't know which approach to use" or "my output feels generic," not "select an identity block." Trigger phrases should match the user's vocabulary, not the Skill's internal terminology.

**Mix explicit and implicit triggers.** Explicit: "build a Skill," "audit my project." Implicit (symptom-phrased): "my Skill won't activate," "Claude keeps making things up." Implicit triggers catch the larger user population — the explicit triggers catch users who already know the Skill's vocabulary.

**Cover both proactive and reactive surfaces.** Proactive: user is starting fresh and wants the Skill's output ("compile a prompt for X"). Reactive: user has output that's broken and wants the Skill to diagnose ("why isn't my prompt working"). Strong descriptions cover both surfaces.

**Negative triggers cite the alternative.** Don't just say "Do NOT use for prompt scoring." Say "Do NOT use for prompt scoring — use rootnode-prompt-validation if available." This routes the user to the right Skill instead of leaving them stranded after the negative trigger fires.

---

## Strong vs. weak examples

### Weak description

```
description: This Skill helps with Claude prompts.
```

Failures: passive verb ("helps with"), no trigger phrases, no negative triggers, no intent context. Won't auto-activate reliably; will overtrigger when it does fire.

### Slightly stronger but still weak

```
description: Use this Skill to work with prompts. Trigger when user
mentions prompts.
```

Failures: vague action verb ("work with"), trigger phrase too broad ("mentions prompts" matches almost any prompt-related conversation), no negative triggers. Will overtrigger heavily.

### Strong description (rootnode-skill-builder v1, the in-house example)

```
description: >-
  Builds deployment-ready Skill files (SKILL.md + references/) from design
  specifications. Use for building, packaging, converting, or reviewing Skills.
  Trigger on: "build this Skill," "build from this design spec," "convert this
  to a Skill," "package as a Skill," "review this Skill," "check spec
  compliance," "revise this Skill," "is my description under 1024 chars," "my
  SKILL.md is too long." Also trigger on symptom-phrased requests: "my Skill
  doesn't activate," "my Skill folder structure is wrong," "my description
  truncates in Claude Code." Also use when a design spec is in context and the
  user says "proceed with the build." Do NOT use when the user is designing
  Skill methodology itself (the content a Skill teaches, not its packaging) —
  that's design work. Do NOT use for prompt compilation, project auditing, or
  prompt scoring (use rootnode-prompt-compilation, rootnode-project-audit, or
  rootnode-prompt-validation respectively, if available).
```

Why this works:

- **What:** "Builds deployment-ready Skill files (SKILL.md + references/) from design specifications." Lead verb, specific output, specific input.
- **When:** "Use for building, packaging, converting, or reviewing Skills." Four intent verbs covering the workflow surface.
- **Explicit triggers:** Nine explicit phrases, mixing happy-path ("build this Skill") with constraint-checking ("is my description under 1024 chars").
- **Symptom triggers:** Three implicit phrases ("my Skill doesn't activate") that catch users describing the problem instead of the solution.
- **Negative triggers:** Two — one carving off methodology design, one routing prompt/project work to the right Skills with "if available" qualifier.
- **Length:** 1003/1024 chars. Tight but compliant.

Failure modes this description avoids:
- Won't auto-activate on generic "prompt help" (no overlap vocabulary with prompt Skills — uses "Skill" specifically).
- Won't activate on Skill *design* conversations (negative trigger explicit).
- Won't activate on Project audits (negative trigger routes elsewhere).

---

## When `disable-model-invocation: true` is genuinely warranted

The directive disables auto-invocation entirely — the Skill ships, but Claude won't load it without explicit user request ("use the X Skill"). This is rare and requires justification.

Legitimate cases:

1. **Destructive operations.** Skill executes irreversible actions (file deletion, repo force-push, data drop). Auto-invocation could destroy work without explicit user consent.

2. **Multi-step workflows where auto-invocation skips a required earlier step.** Skill is the second half of a two-step process — invoking it without the first step produces broken output. Examples: a Skill that consumes a handoff brief from another Skill; a Skill that operates on artifacts produced by a prior Skill.

3. **Domain-isolated Skills that should only fire in specific projects.** A Skill that's installed globally but only relevant in one specific deployment context. Auto-invocation in unrelated projects produces noise.

4. **Workflow Skills with high token cost where the user should consciously opt in.** Skills that consume large context budgets and shouldn't fire opportunistically.

When the directive is set, `metadata.notes` must document the reasoning. The validation gate flags `disable-model-invocation: true` without notes as a warning.

When NOT to use the directive:
- "I don't want it to fire on the wrong tasks" → fix the description (negative triggers), don't disable invocation entirely.
- "The Skill is sensitive and I want to control when it fires" → manual-only is the wrong knob; the right knob is permissions/settings or a hook gate.
- "I'm not sure when it should fire" → the Skill isn't ready to ship. Auto-activation discipline requires knowing when the Skill should fire; if you don't know, the description hasn't been thought through.

---

## The 50-description competition test

Apply this test to every description before shipping:

> Imagine Claude has 50 Skill descriptions in scope. The user types a request. Will Claude correctly select THIS Skill — and only this Skill — for the right tasks? Will Claude correctly NOT select this Skill for adjacent tasks?

If the description doesn't pass this test, the failure mode is one of:

- **Description too generic** (overtriggering). Claude selects the Skill for any vaguely related conversation. Fix: add specificity to the "what" and add negative triggers.
- **Description too narrow** (undertriggering). Claude doesn't recognize the trigger surface. Fix: add symptom-phrased triggers; add implicit triggers users would actually say.
- **Description vocabulary collides with adjacent Skill** (routing collision). Claude can't disambiguate. Fix: distinguish vocabulary domains (e.g., "audit" vs. "optimize," "select" vs. "build"); add negative triggers citing the alternative.

The test isn't optional. Run it explicitly before shipping. State the outcome in the build summary.

---

## Length discipline

The description budget is 1024 YAML-parsed characters. Verify parsed length, not raw text length — YAML block scalars (`>-`, `|`, `|-`) handle whitespace differently from raw text.

When a description is over budget, **never drop routing-critical content** (negative triggers, domain boundary markers). Tighten phrasing instead:

- Compress trigger phrase lists (combine adjacent triggers under shared verbs).
- Tighten the "what" sentence (cut adjectives; lead with the action).
- Compress negative trigger structure (use "Do NOT use for X, Y, or Z" instead of separate sentences).

The description is the highest-leverage artifact in the entire Skill. It's worth multiple tightening passes.

---

## Realistic test prompt patterns

The 50-description competition test asks whether the description triggers correctly. Running the test rigorously requires a corpus of queries to walk through. Synthetic queries written by the build CV — declarative, third-person, full-sentence — under-test the description because users do not phrase requests that way. Real queries are messier: incomplete, context-laden, copy-paste-adjacent, casual. A description that triggers cleanly on a synthetic corpus may still miss the half of real queries that share its underlying intent.

The discipline: generate a trigger eval corpus that mirrors actual user voice, then walk the description against it. The corpus serves both auto-activation testing here and behavioral validation in D9b/D9c (see `references/behavioral-validation.md` and `references/description-optimization.md` for the full procedure and schema).

### Query realism principles

Realistic queries match user voice on multiple axes:

- **Length and completeness.** Real queries are often fragmentary. "fix this" or "why isn't this working" appear alongside full requests. A description that triggers only on grammatically complete requests under-tests the activation surface.
- **Vocabulary drift.** Users say "fix my prompt" not "audit and revise the prompt against the validation rubric." Trigger phrases should match user vocabulary. The description's internal terminology may differ from what users say; the description must contain enough of the user's words to be indexable.
- **Symptom voice.** Many real queries describe a problem, not a request: "Claude keeps ignoring me," "my Skill isn't firing," "this output looks wrong." Symptom-phrased queries match users who don't know the Skill exists.
- **Casual register.** Real queries use contractions, lowercase starts, run-on sentences, and abbreviations. "can you build me a skill from this" is more representative than "Build a Skill from the following design specification."
- **Context-laden references.** Users paste error messages, code snippets, log fragments. The description has to compete against a query that includes irrelevant noise. Trigger phrases should index against the *intent* embedded in the noise, not against the noise itself.

### Should-trigger templates (positive set)

Generate 8–12 queries that the Skill should trigger on. Cover at least three patterns:

**Explicit triggers** — queries that use the Skill's own vocabulary:

- "build a skill for X"
- "package this as a skill"
- "convert this design spec into a skill"
- "review this skill"

**Symptom-phrased triggers** — queries describing the problem the Skill solves:

- "my skill doesn't activate"
- "claude keeps ignoring my skill"
- "the description is too long"
- "auto-invocation isn't firing"

**Implicit / context-laden triggers** — queries that imply the Skill's intent without naming it:

- "I have a design spec, what's next?"
- "how do I make this folder install-ready"
- "when I upload this to claude it doesn't trigger"
- "this is over 1024 chars, what do I cut"

The mix matters. A corpus with only explicit triggers under-tests how the Skill behaves on the larger user population that doesn't know its vocabulary.

### Should-not-trigger templates (negative set)

Generate 5–8 queries that the Skill must NOT trigger on. Cover the adjacent-Skill territory and generic distractors:

**Adjacent Skill territory** — queries that match adjacent Skills more cleanly:

- "score this prompt" → routes to prompt-validation if available
- "audit my project" → routes to project-audit if available
- "what reasoning approach should I use" → routes to block-selection if available

**Generic distractors** — queries that share surface vocabulary but different intent:

- "write a python skill check function" (mentions "skill" but means programming skill)
- "skill issue" (gaming slang; not relevant)
- "what skills should I learn" (career advice; unrelated)

A description that triggers on the negative set has insufficient negative triggers, vocabulary collisions with adjacent Skills, or both. Each false positive identifies a precision gap.

### Edge-case templates

Generate 2–4 queries that could plausibly trigger either way. These earn their place — they are the queries where the description's precision matters most:

- "I want to teach Claude about X" (could be a Skill build, could be CLAUDE.md, could be a hook)
- "design my skill" (skill-builder vs. cc-design vs. design-time methodology)
- "make my skill auto-activate" (skill-builder vs. a tuning-only Skill if one existed)
- "compare these two skills" (skill-builder via version-comparison vs. a different evaluation Skill)

Edge cases force the description to make a defensible call. The build CV records the intended verdict per edge case (trigger / not-trigger / acceptable-either-way) so iteration can measure progress against the intent.

### How the corpus is used

Walk the corpus query-by-query against the current description. For each query, reason about whether the description's verbs, nouns, and trigger phrases would index the query. Note the queries the description misses (under-triggering) and the queries that match adjacent Skills more cleanly (over-triggering or routing collision). Refine the description against the observations; re-walk; repeat until the corpus stabilizes.

When a runnable environment is available, the same corpus drives the automated description optimizer (`scripts/description_optimizer.py` per `references/description-optimization.md`). The corpus content is the same; only the evaluation mechanism differs by tier (see `references/multi-environment-adaptation.md` for the tier model).

---

## Tone calibration in descriptions

The "explain the why" calibration (canonical: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.11`) applies to description fields and to the prose of this reference. Imperative voice is correct where reasoning would dilute the constraint — the description format spec ("description MUST be ≤ 1024 chars YAML-parsed"), the reserved-word constraint ("name MUST NOT include 'claude' or 'anthropic'"), the kebab-case rule ("name MUST be kebab-case"). These are spec constraints; the reasoning is the spec, not a model judgment.

Reasoned voice is correct for description-writing guidance — when to use symptom-phrased triggers, why negative triggers cite the alternative, why the 50-description competition test matters. The build CV applies these as judgment, not as hard rules; reasoned formulation lets the model apply the principle to edge cases the original authoring did not anticipate.

The anti-pattern is caps-everywhere: a description (or a SKILL.md) where every instruction reads "MUST," "ALWAYS," "NEVER" signals to the model that everything is non-negotiable, which dilutes the actual non-negotiables. Calibrated voice — imperative for spec compliance, reasoned for procedural guidance — produces more reliable compliance because the model can distinguish what is load-bearing from what is advisory.

---

## What this reference does not do

This reference doesn't teach the YAML spec — that's `references/skills-spec.md`. It applies the spec to description-writing decisions.

This reference doesn't replace the AP catalog scan for Pattern 5 (Manual-only Skills). The AP scan flags `disable-model-invocation: true` without `metadata.notes`. This reference establishes when notes are warranted in the first place.

This reference doesn't cover Skill ecosystem composition (how this Skill sits next to other rootnode Skills) — that's `ecosystem-placement-decision.md`. Routing discipline (negative triggers) is in scope here; ecosystem placement is in scope there.

This reference doesn't cover the description refinement loop methodology (manual walkthrough vs. automated train/test optimization) or the trigger eval schema in detail — those live in `references/description-optimization.md`. The realistic test prompt patterns above seed the corpus the refinement loop iterates on; the corpus generation discipline is shared between the two references.

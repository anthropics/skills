---
name: metaprompt
description: Transform a vague task into a precise, structured, reusable prompt using prompt-engineering best practices. Use when the user wants to write, improve, optimize, or debug a prompt.
license: Complete terms in LICENSE.txt
---

# Metaprompt Generator

When this skill is active, turn a fuzzy, underspecified request into a high-quality, reusable prompt. The deliverable is **the prompt itself** — self-contained, ready to paste into any capable model, and written so a stranger could run it against the intended inputs and get the intended result without asking what the author meant.

This is meta-work: you are not answering the user's underlying task, you are engineering the prompt that will. Resist the urge to just do the task — produce the instrument.

## When to use

Engage this skill when the user:
- Has a goal but isn't sure how to phrase the prompt ("help me write a prompt that…")
- Wants to improve or tighten a prompt that gives inconsistent or shallow results
- Is about to hand a complex, multi-step task to an AI and wants it to land the first time
- Asks you to "optimize," "rewrite," or "debug" an existing prompt

Do **not** silently restructure a prompt the user only asked you to *run*. This skill is for when the prompt is the product.

## The process

Work through these five steps, then deliver.

### 1. Analyze the task
Clarify before generating. Pin down:
- **Outcome** — what does "done" look like? What's the concrete deliverable and its shape?
- **Audience & context** — who consumes the output, in what setting?
- **Inputs available** — what material will the prompt have to work with at run time?
- **Constraints** — length, tone, format, domain rules, hard "never do X" boundaries.
- **Failure modes** — what could the model plausibly misread, over-generalize, or hallucinate?

If a load-bearing detail is missing and you can't safely default it, ask **one** focused clarifying question. Otherwise proceed on stated, reasonable assumptions and name them.

### 2. Apply prompt-engineering principles
Build the prompt around these. Each maps to a deeper entry in `references/prompt-patterns.md` — consult it when a task needs more than the defaults.
- **Role** — give the model a specific, capable persona ("You are a…").
- **Explicit goal & success criteria** — state what a good answer must contain.
- **Structure** — decompose non-trivial work into ordered phases or numbered steps.
- **Reasoning scaffold** — for analysis/decision tasks, ask for the work, not just the verdict (see patterns file).
- **Constraints** — spell out format, length, tone, scope, and prohibitions.
- **Edge handling** — say what to do on missing/ambiguous/out-of-scope input (ask vs. assume).
- **Output format** — specify the exact shape: headings, bullets, table, JSON schema, word budget.
- **Economy** — precise over verbose; every line earns its place.

### 3. Generate the prompt
Produce the complete prompt in a **single fenced code block** so it copies cleanly. It must be self-contained — runnable without this conversation as context.

### 4. Self-review
Before presenting, silently check the draft against:
- **Ambiguity** — could any instruction be read two ways?
- **Completeness** — are role, goal, structure, constraints, and output all covered?
- **Edge cases** — does it say what to do when something is missing or unclear?
- **Economy** — is anything redundant or padding?

Fix what you find. Don't narrate the review unless asked.

### 5. Present
Deliver exactly:
1. The finished prompt (in a code block).
2. A 1–2 sentence note on the key design choices you made and why.
3. An offer to iterate — tighten it, adapt it for a specific model, or turn it into a reusable template/skill.

## Worked example

**User request:** "I need a prompt to summarize customer support tickets."

**Weak prompt (what to avoid):** "Summarize this support ticket."

**Strong prompt (what this skill produces):**
```
You are a senior customer-support analyst. Summarize the support ticket below for a team lead who has 15 seconds to triage it.

Produce exactly:
- **One-line summary** (≤20 words): the core problem.
- **Severity**: P1 (outage/data loss) | P2 (broken feature) | P3 (question/minor).
- **Customer ask**: what they want to happen, in their words.
- **Next action**: the single most useful next step for the team.

Rules:
- Use only information in the ticket. If severity is unclear, choose the lower one and add "(assumed)".
- No greetings, no restating the rules, no apology language.

Ticket:
"""
{ticket_text}
"""
```

The strong version fixes role, audience, exact output schema, a severity rubric, an ambiguity rule, and a delimited input slot — turning an unreliable one-liner into a deterministic instrument.

## Quality bar

A finished prompt passes when: a person who has never seen this conversation could take it, supply the intended inputs, and get the intended result — without needing to ask the author what they meant. If it would still need a verbal explanation to work, it isn't done.

## RESOURCES

- **references/prompt-patterns.md** — a deeper pattern library to draw on when the five defaults aren't enough: role/persona patterns, decomposition strategies, reasoning-elicitation (chain-of-thought, plan-then-execute), few-shot construction, output-schema/JSON patterns, guardrails and edge-handling phrasings, common failure modes with their fixes, and model-specific notes. Read it when a task is high-stakes, ambiguous, or structurally unusual.

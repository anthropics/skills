# Prompt Patterns — reference library

Draw on these when the five defaults in `SKILL.md` aren't enough. Each pattern lists *when* to reach for it and a *template fragment* to adapt — not boilerplate to paste verbatim.

## 1. Role / persona patterns

| When | Fragment |
|---|---|
| Domain expertise matters | `You are a senior <role> with deep experience in <domain>.` |
| Audience-shaping matters more than expertise | `You are explaining to <audience> who knows <X> but not <Y>.` |
| A specific stance is needed | `You are a skeptical reviewer whose job is to find what's wrong, not to praise.` |

Keep the persona concrete and *functional* — a role exists to bias behavior, not for flavor. Avoid stacking adjectives ("world-class genius expert"); they add tokens, not capability.

## 2. Decomposition strategies

- **Phased**: number the steps when order matters and later steps depend on earlier ones.
- **Checklist**: a flat list of must-cover items when order is irrelevant but completeness matters.
- **Map-then-reduce**: "First list all candidates. Then evaluate each. Then pick." — prevents premature convergence.
- **Separate analysis from output**: "Think through X. Then produce only the final table." — keeps reasoning out of the deliverable.

## 3. Reasoning elicitation

- **Chain-of-thought**: `Work through this step by step before giving your answer.` Use for math, logic, multi-constraint problems.
- **Plan-then-execute**: `First write a brief plan. Then carry it out.` Use for multi-file or multi-stage tasks.
- **Self-critique pass**: `Draft an answer, then critique it for <failure modes>, then produce the improved version.` Use for high-stakes single-shot output.
- **Force the work, hide the work**: ask for reasoning, then `Output only the final result.` when the user wants a clean deliverable but better quality.

> Note: on strong reasoning models, heavy CoT scaffolding can be redundant or even counterproductive — state the goal and constraints clearly and let the model reason. Add explicit scaffolds when output is inconsistent without them.

## 4. Few-shot construction

- Use 1–3 examples when the **format** or **judgment boundary** is hard to describe in words.
- Make examples *diverse* and include at least one **edge/negative** case ("here's a borderline input and the correct handling").
- Label the parts: `Input: … / Correct output: …`.
- Don't few-shot what a single clear instruction already pins down — examples cost tokens and can over-anchor.

## 5. Output-schema / structured output

- **Exact shape**: enumerate the fields and their order. Ambiguity in the schema becomes variance in the output.
- **JSON**: `Respond with ONLY valid JSON matching: {"field": "<type/desc>", ...}. No prose, no code fence.`
- **Tables**: name the columns and the sort order.
- **Budgets**: give length limits per section ("≤20 words"), not just overall — they're more enforceable.
- For machine consumption, add: `If a value is unknown, use null — never invent one.`

## 6. Guardrails & edge-handling phrasings

- Ambiguity: `If the input is ambiguous, choose the most conservative reading and flag the assumption.`
- Missing data: `If required information is absent, say what's missing instead of guessing.`
- Scope: `If the request falls outside <scope>, say so and stop — do not attempt it.`
- Anti-sycophancy: `If the premise is flawed, say so directly before answering.`
- Grounding: `Use only the provided source. Do not add facts from general knowledge.`

## 7. Common failure modes → fixes

| Symptom | Likely cause | Fix |
|---|---|---|
| Inconsistent format run-to-run | Output shape underspecified | Add an exact schema + a worked example |
| Model "explains" instead of doing | No output-only instruction | `Output only <deliverable>. No preamble.` |
| Hallucinated facts | No grounding rule | Restrict to provided sources + "say if unknown" |
| Ignores a constraint | Constraint buried mid-paragraph | Move constraints to a labeled list near the end |
| Too verbose | No length budget | Per-section word limits |
| Refuses or over-hedges a benign task | Persona/role too cautious | Adjust the role; state the legitimate purpose |
| Drifts off-task on long inputs | Instruction far from the input | Restate the one key instruction right before the input block |

## 8. Mechanical hygiene

- **Delimit inputs** with clear fences (`"""`, `<input>…</input>`) so instructions can't be confused with data.
- **Put the most important instruction last** *or* repeat it next to the input — recency helps on long prompts.
- **Name placeholders** explicitly (`{ticket_text}`) so the user knows what to fill.
- **One prompt, one job** — if it's doing three unrelated things, it's three prompts (or a phased pipeline).

## 9. Model-specific notes

- **Reasoning-heavy models** (e.g. high-effort Claude/o-series): lighter CoT scaffolding; lead with goal + constraints; trust the reasoning.
- **Smaller/faster models**: more explicit structure, more examples, tighter output schemas; decompose aggressively.
- **Tool-using agents**: state which tools exist and when to use each; specify the stop condition ("you're done when…").

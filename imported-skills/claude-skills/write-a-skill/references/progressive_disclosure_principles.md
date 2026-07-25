# Progressive Disclosure for Skill Files

This reference answers exactly one decision: **when should a SKILL.md be split into reference files, and how do we keep the disclosure ladder shallow + scannable?**

Pair with `scripts/skill_structure_validator.py` for automated enforcement of the 100-line ceiling + one-level-deep rule.

## What "Progressive Disclosure" Means in Skill Files

Progressive disclosure = present the minimum needed to act, with paths to deeper detail when needed. For agent skills:

- **SKILL.md** = the description + minimum workflow the agent needs to invoke the skill
- **REFERENCE.md / EXAMPLES.md / references/*.md** = deep detail invoked only when the SKILL.md workflow points there
- **scripts/** = deterministic operations (no LLM token cost; no inconsistency risk)

The goal: agent reads SKILL.md and either has enough to act, or has a clear link to the specific reference file that resolves its question. No deeper than that.

## Matt Pocock's Original Rule (the 100-Line Ceiling)

> "Split into separate files when:
> - SKILL.md exceeds 100 lines
> - Content has distinct domains (finance vs sales schemas)
> - Advanced features are rarely needed"
>
> — Matt Pocock, write-a-skill

The 100-line ceiling is empirical: agents reading >100 lines of SKILL.md tend to over-condition on tangential detail; below 100 lines, the agent reads the entire skill and routes correctly to references or scripts when needed.

## When the Ceiling Is Right vs Wrong

| Situation | 100-line ceiling appropriate? |
|---|---|
| Single-action skill (e.g., format-json) | Yes — fits comfortably under 50 lines |
| Mid-complexity skill with 2-3 workflows | Yes — 70-100 lines |
| Skill with 4+ workflows + extensive examples | No — split workflows into separate reference files |
| Domain-spanning skill (multi-framework like compliance-os) | No — split per-framework into separate references |
| Skill that wraps another (derived/extension) | Special case — wrapper additions push past 100; treat as warning, not failure |

## The One-Level-Deep Rule

> "References one level deep" — Matt Pocock review checklist

Why: agent loading a reference file should resolve its question without further indirection. If `REFERENCE.md` says "see `references/foo.md` for more on bar," then bar's content is the leaf — it shouldn't say "see references/foo/bar/baz.md."

Operational consequence: keep `references/` flat. No nested subfolders.

## Anti-Patterns to Avoid

1. **SKILL.md as a complete manual** — 300-line SKILL.md with every workflow inline. Agent over-conditions; token cost on every invocation.
2. **Reference soup** — 20 reference files at one level. Hard to scan; agent can't tell which to load.
3. **Circular references** — `A.md` → `B.md` → `A.md`. Agent loops or fails.
4. **No examples in SKILL.md** — "see EXAMPLES.md for usage." Forces agent to load another file to do anything. Provide a *minimum* example in SKILL.md.
5. **Versioned references** — `references/v1/` and `references/v2/`. Maintenance burden; pick one.
6. **Auto-generated table-of-contents** — agents don't need this; humans rarely browse `references/`.

## How to Apply Progressive Disclosure Concretely

1. Draft SKILL.md with the workflow you want the agent to use 80% of the time
2. Count lines. If > 100, identify the next-largest section. Move it to `references/<topic>.md`.
3. Replace the moved section with a 1-2-line pointer: "See [references/topic.md](references/topic.md) for X."
4. Repeat until SKILL.md ≤ 100 lines.
5. Validate: `python scripts/skill_structure_validator.py path/to/skill-folder/`

## When 100 Is Too Restrictive

For skills that wrap or extend other skills (like this `write-a-skill` itself, which preserves Matt's full original content + adds wrapper sections), the 100-line ceiling becomes an artifact of attribution rather than over-conditioning. Two options:

- Accept the line-count WARN as documentation of intentional preservation
- Move attribution/wrapper notes to `README.md` (which lives outside the SKILL.md ceiling)

This `write-a-skill` skill demonstrates option 1.

## When This Reference Doesn't Help

- **Choosing what to put in scripts/ vs references/** — see Matt's "When to Add Scripts" guidance in main SKILL.md.
- **Information architecture for documentation sites** — see DocOps + DITA references.
- **Token-budget optimization beyond skill files** — different scope (system-prompt design, context engineering).

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — write-a-skill** (https://github.com/mattpocock/skills/, MIT) — the 100-line ceiling + one-level-deep rule originator
- **Anthropic — Building agents with skills** (https://docs.claude.com/en/docs/agents/skills) — official skill structure documentation
- **Anthropic Engineering Blog — Prompt design + context engineering** — concise context = lower hallucination + better routing
- **Don Norman — "The Design of Everyday Things"** (1988) + progressive disclosure HCI principle — origin of the term
- **Information Foraging Theory** — Pirolli & Card (1995) — humans + agents search info using cost/benefit tradeoffs analogous to foraging
- **John Maeda — "The Laws of Simplicity"** (2006) — reduction principle applied to UX, directly applicable to skill files
- **Lean Documentation movement** — DocOps + DITA practitioners on minimum-viable-documentation patterns
- **Pareto principle (80/20 rule)** applied to skill workflows — most agent invocations use the same 20% of skill content

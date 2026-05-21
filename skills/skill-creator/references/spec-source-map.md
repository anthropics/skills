# Spec source map — which Agent Skills page covers what

This reference routes spec-drift checks to the **smallest possible fetch**. When you need to verify something against the live Agent Skills spec, search the forward map by topic to find exactly which page to fetch. Don't traverse the whole site.

The Agent Skills documentation is organized into nine canonical pages. Each one is the authoritative source for a specific concern. Fetching the wrong page wastes context; fetching all of them wastes bandwidth and time.

---

## How to use this map

1. Identify what you need to verify (a frontmatter field? a script-bundling rule? a trigger-optimization technique?).
2. Look it up in the **Forward map** below — find the topic, read the URL and section pointer.
3. Fetch ONLY that URL. Cache the result for the session (don't refetch the same URL twice in one conversation).
4. Compare what you found against the constraints encoded in this skill. Surface any deltas to the user.

For periodic full audits (rare — typically when the skill is being substantially updated), use the **Reverse map** at the bottom to walk every URL with a clear purpose for each.

---

## Forward map: topic → URL

Look up by concern. Phrase your mental query like *"I need to verify that X."*

### Frontmatter fields and validation

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| `name` field rules (length, character set, parent-dir match) | <https://agentskills.io/specification> | `name field` |
| `description` field rules (1024-char limit, required, content guidance) | <https://agentskills.io/specification> | `description field` |
| `license` field shape and conventions | <https://agentskills.io/specification> | `license field` |
| `compatibility` field length limit and use | <https://agentskills.io/specification> | `compatibility field` |
| `metadata` field shape (mapping, allowed types) | <https://agentskills.io/specification> | `metadata field` |
| `allowed-tools` field syntax (experimental) | <https://agentskills.io/specification> | `allowed-tools field` |
| Is there a new frontmatter field this skill doesn't know about? | <https://agentskills.io/specification> | `Frontmatter` table |
| What does the installer enforce vs. what's recommended? | <https://agentskills.io/specification> | constraint columns vs. body guidance |

### Directory structure and progressive disclosure

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| Skill directory layout (`scripts/`, `references/`, `assets/`) | <https://agentskills.io/specification> | `Directory structure` |
| Recommended SKILL.md token / line budget | <https://agentskills.io/specification> | `Progressive disclosure` |
| File-reference depth and relative-path rules | <https://agentskills.io/specification> | `File references` |
| Validation tool recommendation (`skills-ref`) | <https://agentskills.io/specification> | `Validation` |

### Description authoring and trigger optimization

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| What makes a description "pushy" enough to trigger reliably | <https://agentskills.io/skill-creation/optimizing-descriptions> | description writing |
| How Claude decides whether to consult a skill | <https://agentskills.io/skill-creation/optimizing-descriptions> | triggering mechanism |
| What makes a good should-trigger eval query | <https://agentskills.io/skill-creation/optimizing-descriptions> | should-trigger |
| What makes a good should-not-trigger eval query | <https://agentskills.io/skill-creation/optimizing-descriptions> | should-not-trigger |
| Iterative description optimization methodology | <https://agentskills.io/skill-creation/optimizing-descriptions> | optimization loop |

### Script bundling and design

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| Inline command vs. bundled script trade-off | <https://agentskills.io/skill-creation/using-scripts> | `One-off commands` and `Move complex commands into scripts` |
| One-off command syntax (`uvx`, `npx`, `pipx`, `bunx`, `deno run`, `go run`) | <https://agentskills.io/skill-creation/using-scripts> | `One-off commands` |
| PEP 723 inline metadata for self-contained Python scripts | <https://agentskills.io/skill-creation/using-scripts> | `Self-contained scripts` → Python tab |
| Deno / Bun / Ruby inline dependency declarations | <https://agentskills.io/skill-creation/using-scripts> | `Self-contained scripts` → respective tabs |
| How to reference scripts from SKILL.md (relative paths) | <https://agentskills.io/skill-creation/using-scripts> | `Referencing scripts` |
| Agentic-design rules (no prompts, `--help`, structured output, exit codes) | <https://agentskills.io/skill-creation/using-scripts> | `Designing scripts for agentic use` |

### Evaluation methodology

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| How to structure an eval suite (assertions, grading) | <https://agentskills.io/skill-creation/evaluating-skills> | eval structure |
| Should-trigger / should-not-trigger test design | <https://agentskills.io/skill-creation/evaluating-skills> | trigger evals (cross-references optimizing-descriptions) |
| Quantitative vs. qualitative evaluation criteria | <https://agentskills.io/skill-creation/evaluating-skills> | evaluation criteria |

### Best practices and orientation

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| Cross-cutting writing guidance (voice, structure, "explain why") | <https://agentskills.io/skill-creation/best-practices> | best practices |
| The "minimum viable skill" path | <https://agentskills.io/skill-creation/quickstart> | quickstart |
| Concept-level overview ("what is a skill") | <https://agentskills.io/home> | overview |

### Client implementation (rare for skill authors)

| If you need to check… | Fetch | Section keyword |
|---|---|---|
| How a harness or client loads and exposes skills | <https://agentskills.io/client-implementation/adding-skills-support> | client integration |
| What APIs / interfaces a client must expose to be skills-compatible | <https://agentskills.io/client-implementation/adding-skills-support> | required surfaces |

### When the concern doesn't fit any of the above

Start with <https://agentskills.io/specification> (the canonical rules). If your concern is workflow rather than rules, try <https://agentskills.io/skill-creation/best-practices>. As a last resort, fetch the index at <https://agentskills.io/llms.txt> — it lists every page and their topics in machine-readable form.

---

## Reverse map: URL → coverage

Use this when doing a periodic full audit, or when this skill is first written or substantially updated. Walk every page with a clear purpose for each.

### <https://agentskills.io/home>
Concept-level overview. Read once when first encoding the skill; not typically rechecked. If the framing of "what is a skill" changes here, the skill-creator's preamble may need to mirror it.

### <https://agentskills.io/specification>
**The canonical rules.** Frontmatter fields, directory structure, progressive disclosure, file references, validation pointer. Most spec-drift checks land here. Fetch when:

- A frontmatter field constraint may have changed (length, allowed chars).
- A new field has been added or an existing field deprecated.
- The recommended SKILL.md size budget has shifted.
- The validator (`skills-ref`) recommendation has changed.

### <https://agentskills.io/skill-creation/quickstart>
The simplest end-to-end path to a working skill. Read when teaching a new user the basics, or when this skill's onboarding flow needs to mirror upstream simplicity.

### <https://agentskills.io/skill-creation/best-practices>
Cross-cutting guidance on writing style, structure, voice. Read when designing or revising the SKILL.md body structure. If best-practice guidance changes, the skill-creator's writing guidance must mirror it.

### <https://agentskills.io/skill-creation/optimizing-descriptions>
Triggering theory and test-query design. Read when authoring the description-optimization workflow or trigger eval queries. The skill-creator's description-optimization reference depends heavily on this page.

### <https://agentskills.io/skill-creation/evaluating-skills>
Eval methodology — assertion design, grading, what to measure. Read when building or revising the eval-running workflow.

### <https://agentskills.io/skill-creation/using-scripts>
Script bundling, inline dependency declarations, agentic-design rules. Read when:

- Deciding whether to put logic inline vs. in `scripts/`.
- Adding a new bundled script.
- A new language or tool gets a "one-off command" entry (e.g., spec adds a new entry alongside `uvx`, `npx`, etc.).

### <https://agentskills.io/client-implementation/adding-skills-support>
How a harness or client integrates skills. **Not directly relevant to most skill authors**, but useful for understanding what a skill must expose to work with multiple clients. Read only if building a multi-client skill that exhibits client-specific behavior.

---

## Caching strategy

Cache fetched pages **in memory** (or `/tmp/agentskills-cache/<page-name>.html`) **for the duration of the session**. Same URL → no refetch within the same conversation. Different URL → fetch the new one. Clear cache between sessions to pick up changes between conversations.

The spec doesn't change inside a 30-minute session. Refetching the same URL is wasteful; fetching DIFFERENT URLs in the same session when you're auditing multiple concerns is exactly what this map enables.

---

## Update protocol

The spec evolves. When you notice:

- A new spec page was added (e.g., `/skill-creation/some-new-topic`) → add to both maps with a clear topic line.
- A URL was moved or deprecated → mark the old entry deprecated, add the new one, leave the old one with a pointer for one release cycle.
- A section keyword changed → update the "Section keyword" column.

The map's own correctness drifts too. Re-audit this file when running a periodic full-skill-spec check, not just when fetching individual concerns.

---

## What this map deliberately does NOT do

- **Replace the local skill content.** This map points at upstream sources; the skill still encodes the current rules locally so it works offline. The map is for *verification*, not *replacement*.
- **Auto-fetch on every invocation.** Spec-drift checks are gated to high-leverage moments per `references/spec-check.md`. The map enables scoping when those checks happen, not running them more often.
- **Cover content outside agentskills.io.** Anthropic-specific guidance (skill-creator best practices unique to anthropic-skills) lives in this repo, not on agentskills.io. The map covers the spec; this skill covers Anthropic's practice on top of it.

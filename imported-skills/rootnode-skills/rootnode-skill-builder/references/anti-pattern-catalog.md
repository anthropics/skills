# Anti-Pattern Catalog (Skill-build subset)

**Canonical source:** `root_AGENT_ANTI_PATTERNS.md` — the unified anti-pattern catalog for AI agent environments, surface-tagged `[CP]`, `[CC]`, or `[both]`.

This reference is a Skill-internal application of the canonical catalog. It documents which patterns apply to **Skill content** (SKILL.md + references/) and which don't. The Skill scans produced files against this subset during validation dimension 7; warnings surface to the user as advisory (not blockers — patterns are sometimes intentional).

If the canonical catalog evolves (new pattern added, existing pattern reframed), regenerate this reference against the new canonical. The cross-reference anchor is the propagation hook.

---

## Why this reference is a subset, not the full catalog

The canonical catalog covers three surfaces (CP-only, CC-only, both) across structural and operational pattern families. Most patterns describe environment-level failures — Project structure, repo organization, settings configuration. Those don't manifest *inside* a single Skill's content; they manifest in the environment that hosts the Skill.

The patterns below are the ones that can manifest **inside the SKILL.md or references/ files of a single Skill**. Scanning a Skill against environment-level patterns produces false positives — flagging a Skill for "Phantom Conversation" when Phantom Conversation is a Project-level CI failure mode, not a Skill-content failure mode.

The explicit not-applicable list at the bottom documents which canonical patterns are deliberately excluded from Skill-content scans, and why. Future maintainers extending this catalog should consult the not-applicable list before adding new patterns.

---

## Skill-content patterns to detect

For each pattern: catalog reference (where in canonical), Skill manifestation (what it looks like in produced content), detection signal (what the Skill scans for), example warning (template the Skill emits).

### Pattern 1 — Monolithic standing context

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §2.1`

**Skill manifestation:** SKILL.md exceeds 500 lines or mixes too many concerns under a single Skill. The progressive disclosure boundary breaks down — content that should be in references/ stays in SKILL.md because the Skill author treated SKILL.md as a long-form document instead of an entry point.

**Detection signal:** SKILL.md line count > 500. Or: SKILL.md contains multiple distinct procedural sections that each could stand alone (suggesting two Skills that were merged, or a Skill where reference content didn't get extracted).

**Example warning:** "SKILL.md is 612 lines, exceeding the 500-line spec constraint. Patterns of monolithic standing context: lines 200-340 read like a reference doc (extended examples + edge case catalog) — candidates for extraction to `references/extended-examples.md`. Sections 'X Workflow' and 'Y Workflow' each have full procedure scaffolding — consider whether this is two Skills."

### Pattern 2 — Layer hierarchy violation

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §2.2`

**Skill manifestation:** SKILL.md asserts authority over content that should live at a higher precedence layer. Examples: "always do X" instructions that override what should be hook-enforced; "the project mission is..." statements that should live in CLAUDE.md; configuration directives that should live in settings.

**Detection signal:** Imperative language pattern "always," "never," "must" applied to content that the 7-layer framework places in CLAUDE.md, hooks, or settings. Or: Skill content that references project-specific facts (mission, scope, authority) that should be resolved at the hosting environment level, not inside a portable Skill.

**Example warning:** "SKILL.md line 47: 'Always run pytest before declaring a task complete.' This is enforcement language — Skill instructions are preferences, not guarantees. Per `root_AGENT_ANTI_PATTERNS.md §4.4` (Enforcement-as-preference), this work belongs in a Stop hook, not Skill prose. Recommend: weaken Skill language to 'Run pytest as a verification step,' surface hook recommendation in build summary."

### Pattern 3 — Blurred Layers

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §3.5`

**Skill manifestation:** SKILL.md mixes behavioral instructions (the procedure the Skill executes) with reference material (extended examples, rubrics, pattern libraries, edge case catalogs). The progressive disclosure boundary blurs.

**Detection signal:** SKILL.md sections that read like documentation rather than instruction — long enumerated lists of options, multi-paragraph descriptions of variants, comparison tables of approaches. These should live in references/. SKILL.md should retain only what's needed to execute the procedure on activation.

**Example warning:** "SKILL.md section 'Pattern Catalog' (lines 180-265) is reference material, not behavioral instruction. The Skill's runtime behavior doesn't depend on the catalog being in SKILL.md — it depends on the Skill knowing the catalog exists and where to read it. Recommend: extract to `references/pattern-catalog.md`, replace the section with a 2-line pointer ('For pattern variants, read references/pattern-catalog.md')."

### Pattern 4 — Kitchen Sink (structural)

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §3.4`

**Skill manifestation:** Single Skill scope spans multiple unrelated procedures. The Skill tries to do "everything related to X" instead of "one specific X procedure done well." Activation becomes unreliable — the description has to cover too many trigger surfaces, and Claude struggles to know whether the Skill is the right match.

**Detection signal:** SKILL.md contains 3+ distinct top-level workflow sections that don't share a unified procedure (e.g., "Build New X," "Audit Existing X," "Migrate X to Y," "Compare X variants" — four different things). Or: description field has 5+ trigger phrase clusters that don't resolve to a single coherent intent.

**Example warning:** "SKILL.md defines four distinct workflows (Build / Audit / Migrate / Compare) that each have full procedure scaffolding. This pattern matches Kitchen Sink (`root_AGENT_ANTI_PATTERNS.md §3.4`) — single Skill spanning unrelated procedures degrades activation precision. Recommend: split into 2-4 focused Skills, or document the unifying intent and tighten scope to one workflow."

### Pattern 5 — Manual-only Skills

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §4.3`

**Skill manifestation:** `disable-model-invocation: true` set in frontmatter without justification, or weak description that effectively requires manual invocation because Claude can't auto-activate it. The Skill ships but never fires unless the user explicitly names it.

**Detection signal:** `disable-model-invocation: true` present without `metadata.notes` field documenting reasoning. Or: description field lacks verb-based triggering language (no "Use when...," no trigger phrase examples, no symptom-phrased triggers) — signals likely undertriggering.

**Example warning:** "Frontmatter sets `disable-model-invocation: true` without justification. Per `root_AGENT_ANTI_PATTERNS.md §4.3`, manual-only Skills are an anti-pattern unless the Skill genuinely warrants human-only invocation (destructive operations, multi-step workflows where auto-invocation skips a required earlier step). Recommend: remove the directive, OR add `metadata.notes` documenting the human-only reasoning."

### Pattern 6 — Verification-before-completion absent

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §4.11`

**Skill manifestation:** Skill produces output without testable evidence the work is correct. The procedure ends with "deliver the result" instead of "verify the result, then deliver." Common in build-style Skills where output completeness is the implicit verification surface but no explicit check is specified.

**Detection signal:** SKILL.md procedure has no Quality Gate / verification / pass-fail check section. Or: the verification section lists deliverables ("output the file") rather than checks ("verify the file passes X criteria").

**Example warning:** "SKILL.md procedure ends at 'present complete files for review' without a verification step. Per `root_AGENT_ANTI_PATTERNS.md §4.11`, Skills should produce testable evidence the work is correct, not just the deliverable. Recommend: add a verification dimension or quality gate step before the deliverable presentation, with specific pass/fail criteria the Skill applies."

### Pattern 7 — Stale content (Stale CLAUDE.md pattern, applied to Skills)

**Catalog:** `root_AGENT_ANTI_PATTERNS.md §4.14`

**Skill manifestation:** Skill content references tools, files, patterns, or canonical sources that no longer exist or have been renamed. Common when a Skill is built once and not maintained as the surrounding ecosystem evolves.

**Detection signal:** Skill content references named files in the seed Project KFs that aren't in the current canonical inventory. Or: Skill mentions other Skills by name that have been renamed or removed. Or: Skill cites canonical KF section anchors (`§X.Y`) that don't match the current canonical structure.

**Example warning:** "SKILL.md line 134 references `root_OLD_KF_NAME.md` — this KF was renamed to `root_NEW_KF_NAME.md` in Phase 26. References lines 47, 89, 102 cite `rootnode-cchq-design` — this Skill was renamed to `rootnode-cc-design` in Phase 28. Recommend: update names to current; verify all canonical anchors against the current KF inventory."

---

## Patterns explicitly NOT applicable to Skill content

The Skill should NOT scan for these patterns. They're documented in the canonical catalog as environment-level failures, not Skill-internal patterns. Flagging a Skill for these would produce false positives.

| Canonical pattern | Why excluded from Skill-content scan |
|---|---|
| `§3.1` Phantom Conversation | CP Project-level — a CI references a knowledge file that doesn't exist. Skills don't have a CI/KF relationship internally. |
| `§3.2` Echo Chamber | CP Project-level — multiple knowledge files repeat the same content. A single Skill's references/ folder isn't an "echo chamber" unless explicitly redundant, which is detected by Pattern 3 (Blurred Layers) and Pattern 1 (Monolithic) instead. |
| `§4.2` MCP bloat | Environment-level — too many MCP servers loaded. A Skill's instructions about MCP usage aren't the bloat surface. |
| `§4.4` Enforcement-as-preference | Environment-level — but referenced from Pattern 2 (Layer hierarchy violation) when a Skill carries enforcement language that should be in a hook. The Skill itself isn't the enforcement gap; the Skill *containing* enforcement language is the gap. |
| `§4.5` Subagent overuse | Environment-level — too many subagents defined. A Skill's recommendation to use a subagent isn't the overuse surface. |
| `§4.6` Subagent underuse | Environment-level — work that should dispatch to a subagent stays in the parent agent. A Skill's procedure not using a subagent isn't the underuse surface. |
| `§4.7` `bypassPermissions` | Environment-level — settings configuration. A Skill mentioning permissions isn't the bypass surface. |
| `§4.8` Missing managed policy | Environment-level — settings/governance. Not a Skill-internal pattern. |
| `§4.9` Path-scoped rules opportunity missed | Environment-level — the host repo lacks `.claude/rules/` files where they'd help. A Skill recommending rules isn't the missed-opportunity surface. |
| `§4.10` Auto memory misuse | Environment-level — Project Memory or Global Memory misused. Skills don't write to memory. |
| `§4.12` Skills/Commands legacy mix | Environment-level — repo has both Commands (legacy) and Skills (current). A Skill itself isn't the mix. |
| `§4.13` Kitchen-sink session | Operational — a single CC session tries to do too much. Skill content doesn't determine session shape. |

---

## Disposition of warnings

All warnings produced by this scan are **advisory, not blocking**. The Skill emits warnings; the user reviews; the user accepts (with reasoning captured in the AP-warning summary build artifact) or revises.

Reasons a user might legitimately accept a warning:

- **Pattern 4 (Kitchen Sink) accepted:** The Skill genuinely benefits from co-locating workflows (e.g., `rootnode-skill-builder` itself has Build / Review / Revise workflows, intentionally unified because they share the same spec/quality gate machinery).
- **Pattern 5 (Manual-only) accepted:** The Skill is genuinely human-only (destructive operations, multi-step workflows where auto-invocation skips a required earlier step) and `metadata.notes` documents the reasoning.
- **Pattern 7 (Stale) accepted:** The reference is intentional historical context (e.g., "This Skill was originally built to support workflow X, which has since been replaced by workflow Y").

Reasons that warrant revision (not acceptance):

- **Pattern 1 (Monolithic) at high line counts:** SKILL.md > 600 lines is a hard signal — split or extract.
- **Pattern 2 (Layer hierarchy violation) on enforcement language:** "Always do X" applied to deterministic guarantees almost always belongs in a hook. Accepting this warning means accepting unreliable enforcement.
- **Pattern 3 (Blurred Layers) on large reference-shaped sections:** If the section is reference-shaped (catalog, table, enumeration of variants), extracting to references/ is almost always correct.
- **Pattern 6 (Verification absent) on build/produce-style Skills:** A Skill that produces artifacts without verification ships unreliable artifacts.

The AP-warning summary build artifact captures the user's acceptance reasoning so future maintainers know whether a warning was a deliberate choice or an oversight.

---

## What this reference does not do

This reference doesn't enumerate the full canonical catalog — that's `root_AGENT_ANTI_PATTERNS.md`. It applies the catalog to the Skill-content surface specifically, with explicit exclusions for environment-level patterns that don't manifest inside a single Skill's files.

This reference doesn't replace ecosystem-level pattern detection (e.g., periodic full-catalog audits across all installed Skills for systemic patterns like inventory-wide Kitchen Sink or routing-collision clusters). It catches per-Skill content patterns at build time; ecosystem-wide health is a separate audit surface.

This reference doesn't define how the Skill should respond to AP catches procedurally — the Skill's pipeline (validation dimension 7) defines the surface-as-warning behavior. This reference defines the catalog being scanned against.

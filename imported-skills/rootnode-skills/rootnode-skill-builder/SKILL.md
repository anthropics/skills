---
name: rootnode-skill-builder
description: >-
  Builds, validates, packages, tests, and optimizes deployment-ready Skill
  files (SKILL.md + references/ + scripts/ + agents/) from design
  specifications. Three pre-build gates + 9-dimension quality gate (with
  D9a/b/c empirical evidence tiers) + behavioral iteration loop + automated
  description optimizer + blind version comparator. Use for building,
  reviewing, revising, testing, or optimizing Skills. Trigger on: "build
  this Skill," "review this Skill," "test my Skill," "optimize the
  description," "compare these Skill versions," "should this be a hook
  instead," "build a template first." Also: "my Skill doesn't activate,"
  "my description truncates," "my SKILL.md is too long," "my Skill is
  overtriggering." Do NOT use when designing Skill methodology — that's
  design work, not packaging. Do NOT use for prompt compilation, project
  auditing, or prompt scoring (use rootnode-prompt-compilation,
  rootnode-project-audit, or rootnode-prompt-validation if available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "3.0"
  predecessor: "rootnode-skill-builder v2.1"
  original-source: "root.node seed Project KFs (post-Phase 32a methodology updates) + rootnode-skill-builder v2.1 source"
  discipline_post: phase-30
---

# Skill Builder

> **Calibration:** Tier 2, Opus-primary. See repository README for model compatibility.

> **Version 3.0:** Methodology + tooling release. D9 expanded into D9a/D9b/D9c sub-levels (empirical Tier A / empirical Tier B / analytical floor). Adds Description Refinement Loop methodology (manual or automated via `scripts/description_optimizer.py`). Adds Tier A/B/C environment-adaptive degradation. Adds executable layer (`scripts/`, `agents/`, `eval-viewer/`) ported from upstream Anthropic skill-creator with content-class-policy adaptation. v2.1 build methodology preserved verbatim where unchanged.

Build, review, revise, test, and optimize root.node Skills in the SKILL.md format for the Anthropic Agent Skills ecosystem. This Skill carries the complete build methodology — Agent Skills spec, conversion rules, progressive disclosure patterns, pre-build gates, the 9-dimension quality gate (with sub-level evidence tiers), behavioral iteration, description optimization, and blind version comparison.

Skills are built from design specifications produced during methodology design work. The design spec is the input. This Skill's job is gate-checking, construction, validation, iteration, optimization, and publication-readiness.

**Platform terminology note:** This Skill retains root.node terminology (Block, Block Library, Domain Pack, Compiler, Optimizer) by design. Unlike most rootnode Skills that strip internal language, this Skill operates ON root.node Skills as its subject matter — the conversion rules, concept mapping, and build pipeline reference root.node concepts by name because those are what gets built.

## Important

**Description fields are everything.** Claude decides whether to load a Skill based almost entirely on the description in YAML frontmatter. A perfect methodology behind a vague description never activates. Test every description: would Claude pick this Skill, and only this Skill, alongside 50 others?

**Preserve depth, adapt format.** The methodology is the differentiator. Every Skill retains substantive instructions, reasoning patterns, and quality criteria from source material. What changes is packaging — frontmatter, progressive disclosure structure, activation descriptions — not intellectual content.

**Spec compliance is non-negotiable.** Every Skill conforms to the Agent Skills specification. Name in kebab-case (max 64 chars), description ≤ 1024 chars (verify YAML-parsed length, not raw text), no XML angle brackets in frontmatter, no README.md inside skill folders, SKILL.md body under 500 lines / ~5000 tokens.

**Standalone-first composition.** Every Skill delivers complete value when installed alone. Cross-Skill references are soft pointers ("for deeper specialization, see X if available"). Prefer a few hundred tokens of duplicated guidance over a dependency that breaks a Skill when installed alone.

**Pre-build gates run first.** Before parsing any design spec, walk the three pre-build gates explicitly. A Skill that should have been a hook, a template, or an extension of an existing Skill is worse than no Skill at all — it ships, looks reasonable, and silently fails to deliver value.

**The deliverable is a packaged zip plus separated audit artifacts.** Build the deployable as `{skill-name}.zip` containing the Skill folder structure. Audit artifacts (placement note, promotion provenance, AP-warning summary) ship as separate files OUTSIDE the zip — they document the build event, not runtime behavior.

**Routing surfaces over procedural depth in SKILL.md.** Each new workflow section in SKILL.md names the workflow, identifies tier routing, and points to a reference. Procedural depth lives in references. The 500-line ceiling is a design-time forcing function, not a compression-time problem.

**Tier-aware verdicts.** When validation dimensions invoke empirical workflows (D9 sub-levels, description refinement, version comparison), the build environment determines which tier applies. Record the tier explicitly in the build summary; do not claim Tier A evidence when Tier A infrastructure was unavailable.

**Complete file output.** Always output the complete file. Never diffs, patches, or partial sections.

---

## Reasoning discipline

Before declaring a Skill ready to ship, walk through the nine-dimension quality gate explicitly. State each check, cite the specific evidence (character counts, section structure, activation triggers, cross-Skill references, AP catches, layer leaks, applied D9 sub-level), then apply the pass/fail verdict. Do not compress this sequence into a summary judgment.

If the build scope is unclear (new build vs. review vs. revision vs. iterate vs. optimize description vs. compare versions), confirm scope with the user before proceeding. Do not proceed on inferred assumptions.

---

## Pre-Build Gates

Before parsing any design spec or building any Skill files, walk three gates explicitly. Each gate has a specific decision and a specific halt condition. Pass all three before proceeding to "Build New Skill."

### Gate 1 — Decomposition check

Where does this work fit in the 7-layer Claude Code mechanism framework? The mechanisms are CLAUDE.md (always-loaded standing context), `.claude/rules/` (path-scoped on-demand rules), Skills (multi-step procedures), subagents (focused specialists with isolated context), hooks (lifecycle guarantees), MCP (external data/APIs), settings (trust/permission boundaries). For full framework guidance, read `references/decomposition-framework.md`.

If the work fits "Skills" cleanly: proceed to Gate 2. If the work fits a different mechanism: redirect with brief explanation. Do NOT build a Skill that should have been a hook, a rule, CLAUDE.md content, etc.

### Gate 2 — Warrant check

Has the work pattern surfaced 3+ times in real use, with traceable evidence?

If yes: proceed to Gate 3. If no (1-2 occurrences, speculative future need): recommend building a paste-and-edit template first. Use the user's project prefix convention (`{code}_template_{descriptor}.md`). Document explicit promotion criteria inline. For full warrant guidance, read `references/warrant-check-criteria.md`.

**Exception:** when the user provides a process-abstraction handoff brief from rootnode-repo-hygiene (or another upstream Skill), the brief is the warrant evidence. Gate 2 passes automatically.

### Gate 3 — Ecosystem fit check

Where does this Skill belong in the rootnode runtime tooling map? Check (1) CP-side or CC-side surface; (2) which existing rootnode Skills it composes with; (3) clear gap or duplicate of existing capability.

If clear gap: proceed to "Build New Skill." Surface the placement decision and suggested entry for the runtime tooling catalog (`root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`) in the build summary.

If duplication detected: surface to user. Ask whether to extend the existing Skill instead. Building a duplicate creates routing collisions. For full ecosystem guidance, read `references/ecosystem-placement-decision.md`.

---

## Build New Skill

When the three pre-build gates have passed and a design specification is present in context:

**Step 1 — Parse the design spec.** Identify the methodology (what the Skill does), the reference file structure, the description field draft, the internal language adaptation notes, the composition testing cases, and any architectural decisions already made.

**Step 2 — Build SKILL.md.** Implement the methodology from the design spec. Apply conversion rules (see `references/conversion-guide.md`): strip root.node internal language per adaptation notes, inline relevant behavioral countermeasures, convert quality gates to actionable verification steps. Structure: identity paragraph, Important/Critical section, core instructions, examples, When to Use section, Troubleshooting section. Verify body under 500 lines. Verify description under 1024 characters with trigger phrases and negative triggers.

**Step 2a — Description field construction.** The description is the highest-leverage artifact. Build using the templates in `references/conversion-guide.md` and the discipline in `references/auto-activation-discipline.md`. Structure: [What it does] + [When to use it] + [Trigger phrases] + [Negative triggers]. Make descriptions slightly "pushy" with both explicit and implicit triggers. Add explicit negative triggers when overtriggering risk exists. Always verify YAML-parsed character count is ≤ 1024.

**Step 3 — Build reference files.** Apply progressive disclosure — detailed content, rubrics, pattern libraries, extended examples, edge cases go here. Each reference file referenced from SKILL.md with "when to read" guidance. TOC for files over 300 lines. One level deep (no nested subdirectories within `references/`).

**Step 4 — Apply internal language adaptation.** Use adaptation notes from the design spec. Default conversions in `references/conversion-guide.md`. Exception: Skills that operate ON Claude Projects platform features retain platform terminology. Apply tone calibration consistent with AEA "explain the why" — imperative voice for spec constraints; reasoned voice for procedural guidance.

**Step 5 — Run nine-dimension publication review.** Score each dimension pass/fail with evidence:

1. **Spec compliance:** name format, description length (YAML-parsed ≤ 1024), body length (< 500 lines), no XML in frontmatter, no README in folder, folder/name match.
2. **Activation precision:** description triggers correctly under the 50-description competition test; verb-based language; symptom-phrased and explicit triggers; negative triggers present.
3. **Methodology preservation:** substantive content from design spec preserved; instructions remain actionable and specific.
4. **Progressive disclosure:** SKILL.md routing-surface; references hold depth; cross-references resolve; routing-surface compliance check (no procedural duplication of reference content in SKILL.md).
5. **Standalone completeness:** cross-Skill references use "if available"; no hidden dependencies.
6. **Auto-activation enforcement:** verb-based triggers; `disable-model-invocation` either absent or with `metadata.notes` justification.
7. **Anti-pattern catalog scan:** scan against `references/anti-pattern-catalog.md` Skill-relevant subset; surface catches with section reference; advisory unless severe (HALT disposition).
8. **7-layer leak-check:** scan for content belonging in CLAUDE.md, `.claude/rules/`, hooks, or MCP rather than in the Skill.
9. **Behavioral validation (RECOMMENDED, sub-level applies):** D9a (Tier A — empirical with-Skill vs. without-Skill comparison via subagent grader); D9b (Tier B — empirical execution under realistic test prompts; qualitative review; no baseline); D9c (Tier C — analytical reasoning grounded in the 10-tendency taxonomy). Capture the applied sub-level in the build summary. The sub-level architecture and per-tier procedure live in `references/behavioral-validation.md`. Tier applicability per `references/multi-environment-adaptation.md`.

**Step 6 — Package the deployable Skill and deliver alongside separated audit artifacts.** The deliverable is two distinct things: (1) `{skill-name}.zip` containing the Skill folder (`{skill-name}/SKILL.md` + `{skill-name}/references/*.md` + `{skill-name}/scripts/*` + `{skill-name}/agents/*.md` + `{skill-name}/eval-viewer/*` if present); (2) audit artifacts as separate files outside the zip. The zip is the primary deliverable; audit artifacts are secondary. Use `scripts/package_zip.py` to build the zip and verify contents before delivery.

**Audit artifacts (delivered separately, NOT inside the zip):**

- **Ecosystem placement note** (`{skill-name}_placement.md`) — always produced.
- **Promotion provenance** (`{skill-name}_promotion_evidence.md`) — produced when Gate 2 evidence was provided OR Gate 2 was overridden with reasoning.
- **AP-warning summary** (`{skill-name}_ap_warnings.md`) — produced when D7 surfaces catches.

**Why separation matters:** audit artifacts document the build event (placement reasoning, warrant evidence, AP catches). The Skill folder documents runtime behavior (instructions, references, executable layer). Mixing them inside the zip pollutes the deployable.

### Build Behavioral Calibration

When producing SKILL.md bodies and reference files, match content density to the source methodology — do not pad with explanatory context the source does not contain.

Apply the "explain the why" calibration (canonical: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.11`) to new content. Use imperative voice for spec constraints and safety boundaries (the spec is the authority); use reasoned voice for procedural guidance and decision rubrics (the model can apply judgment). Avoid caps-everywhere — when every instruction reads "MUST" or "ALWAYS," the model loses the signal that distinguishes hard constraints from strong recommendations.

When building from a design spec, the design decisions are already made. Build what the spec says. If a design decision appears suboptimal, flag it as a build note after delivery — do not pause the build to explore alternatives.

---

## Iterate the Skill

When a Skill has been built and the build CV (or operator) wants behavioral confirmation that it works, enter the iteration loop. The loop tightens the Skill against observed gaps — assertions that fail, behaviors that diverge from criteria, scenarios where the analytical reasoning chain breaks down.

**Tier routing.** Determine which D9 sub-level applies based on the build environment per `references/multi-environment-adaptation.md`:

- **Tier A:** invoke the `agents/grader.md` subagent on with-Skill (GREEN) and without-Skill (RED) runs across the trigger eval set; compute the differential per assertion. Optionally run `scripts/aggregate_benchmark.py` for multi-eval aggregation.
- **Tier B:** load the Skill into the runnable environment; execute the trigger eval set; review activation and procedural compliance qualitatively against the Skill's stated criteria.
- **Tier C:** apply the analytical floor — pressure scenario documented; baseline failure expected from a cited Claude tendency; compliance expected from countermeasure formulation.

For full procedure, schemas verbatim, grader principles verbatim, and per-tier mechanics, read `references/behavioral-validation.md`.

---

## Optimize the Description

The description is the highest-leverage artifact in a Skill. A description that fails to trigger renders every other discipline (build gates, quality gate, methodology preservation) inert. The optimization loop hardens the description against under-triggering and over-triggering through evidence-based iteration.

**Tier routing.** Per `references/multi-environment-adaptation.md`:

- **Tier A:** invoke `scripts/description_optimizer.py` with the trigger eval corpus for an automated 5-iteration train/test loop with held-out scoring. Generate per-iteration HTML report via `scripts/generate_report.py`.
- **Tier B/C:** run the manual walkthrough — read each query against the description and reason about activation; refine; repeat until the corpus stabilizes.

For full procedure including the trigger eval schema, the train/test split methodology, the triggering detection mechanism, the description improvement prompt structure, and the anti-overfitting principle, read `references/description-optimization.md`.

---

## Compare Skill Versions

When the build CV needs evidence that a successor revision improves on a predecessor before shipping. Tier A invokes `agents/comparator.md` (blind A/B) and `agents/analyzer.md` (post-hoc analysis); Tier B/C falls back to inline blind comparison with identifier-leak prevention. For procedure, rubric verbatim, and analyzer outputs verbatim, read `references/version-comparison.md`.

---

## Review Existing Skill

When asked to review a Skill:

1. **Spec compliance:** name format, description length (YAML-parsed), body length, no XML in frontmatter, no README, folder/name match.
2. **Activation precision:** evaluate against the 50-description competition test; check undertriggering and overtriggering; check negative triggers against adjacent Skills.
3. **Methodology preservation:** compare against source material if available; check for content loss, vague instructions, missing quality criteria.
4. **Progressive disclosure:** SKILL.md core only; routing-surface compliance; references hold depth; "when to read" guidance present.
5. **Standalone completeness:** verify no hidden dependencies; cross-Skill references use "if available."
6. **Auto-activation enforcement:** verb-based triggers, both explicit and symptom-phrased; `disable-model-invocation` justified if set.
7. **Anti-pattern catalog scan:** run scan from `references/anti-pattern-catalog.md`. Surface catches as advisory.
8. **7-layer leak-check:** scan for material belonging in CLAUDE.md, `.claude/rules/`, hooks, or MCP.
9. **Behavioral validation (sub-level applies):** apply the strongest available tier per `references/multi-environment-adaptation.md`. For pre-v3.0 Skills without sub-level marking, apply analytically (D9c) by default.

For v1- and v2-built Skills, dimensions added in v2/v3 surface as advisory warnings only — do not break a working Skill automatically. The user decides whether to revise based on the warnings.

Flag issues with specific fix recommendations. Do not pad with praise.

---

## Revise Existing Skill

When asked to revise a Skill:

1. Read current SKILL.md and reference files.
2. Apply requested changes while maintaining spec compliance, methodology preservation, and standalone completeness.
3. Run the nine-dimension review against the revised version (with the appropriate D9 sub-level).
4. Output complete updated files (not diffs).
5. Present brief revision note (3-5 sentences) covering what changed and why.

---

## Key Spec Constraints

For the full specification, read `references/skills-spec.md`.

**YAML frontmatter:** `name` in kebab-case (max 64 chars, must match folder name); `description` max 1024 chars (YAML-parsed); no XML angle brackets. Optional: `license` (Apache-2.0 for rootnode), `metadata` (allowed sub-fields: `author`, `version`, `predecessor`, `original-source`, `notes`, `discipline_post`). Required from skill-builder current version or later: `metadata.discipline_post: phase-30` per `root_SKILL_BUILD_DISCIPLINE.md §4.6`.

**SKILL.md body:** under 500 lines, under ~5000 tokens. Routing-surface design (procedural depth in references). Imperative form for spec constraints; reasoned voice for procedural guidance.

**References:** one level deep. Each file referenced from SKILL.md with "when to read" guidance. TOC for files over 300 lines.

**Subdirectories (v3.0):** `scripts/` (Python tooling), `agents/` (subagent prompts), `eval-viewer/` (HTTP-served review interface). See `references/skills-spec.md` and `references/tooling-layer-overview.md`.

**Folder structure:**

```
your-skill-name/
├── SKILL.md          # Required — main skill file
├── references/       # Optional — methodology depth (loaded on demand)
├── scripts/          # Optional — Python tooling (executed on demand)
├── agents/           # Optional — subagent prompts (Tier A invocation)
└── eval-viewer/      # Optional — interactive review UI (Tier A only)
```

**Naming rules:** SKILL.md exact case. Folder name kebab-case, no spaces/underscores/capitals. No README inside skill folders. Names with "claude" or "anthropic" reserved.

---

## Conversion Rules Quick Reference

For the full conversion guide including concept mapping, content adaptation patterns, standalone composition rules, description templates, and tone calibration in produced Skill content, read `references/conversion-guide.md`.

### Default Language Adaptations

| Original (root.node) | Adapted (Skills) |
|---|---|
| "Select the Strategic Advisor identity block" | "Use the Strategic Advisor approach" |
| "Consult the Block Library for options" | "See references/identity-blocks.md for available approaches" |
| "The Compiler's Parse stage extracts..." | "Start by extracting from the task description..." |
| "Per the Optimization Notes..." | "Claude tends to..." |
| "The seed project demonstrates..." | [Remove — not relevant outside root.node] |

**Exception:** Skills that operate ON root.node concepts (this Skill) or ON Claude Projects platform features retain their domain-specific terminology. The design spec documents any exceptions.

### Cross-Skill References

All cross-Skill references must be soft pointers: "for deeper specialization, see X if available." The "if available" qualifier must always be present. No Skill may fail because another Skill is not installed.

---

## Multi-Environment Adaptation

Some Skills run across multiple environments (CC, Cowork, CP, custom orchestrators). Their tooling layer fails silently in environments that lack required infrastructure unless the Skill flags the dependencies explicitly and provides fallback paths.

Apply the Tier A/B/C operational model (canonical: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.12`):

| Tier | Capabilities | What it supports |
|---|---|---|
| A | Subagents + runnable env | Full empirical pipeline (D9a, automated description optimizer, blind comparator) |
| B | Runnable env, no subagents | Empirical execution under realistic prompts (D9b, manual walkthrough) |
| C | Neither | Analytical floor (D9c, manual reasoning) |

The build CV records the determined tier in the build summary; lower tiers serve as per-step fallbacks when individual steps fail infrastructurally. For per-script tier compatibility, fallback patterns, and detection logic, read `references/multi-environment-adaptation.md`.

---

## Examples

### Example 1: Build from Design Spec

**Input:** User provides a design spec for `rootnode-context-budget` v5.

**Actions:** Walk pre-build gates → parse spec → build SKILL.md and references → apply language adaptation → run 9-dimension review → package zip and audit artifacts.

**Result:** Deployable zip + 3 audit artifacts (placement, promotion, AP-warnings if applicable). Build note covers key adaptation decisions and the D9 sub-level applied.

### Example 2: Review Existing Skill

**Input:** User asks "Review the rootnode-output-blocks Skill."

**Actions:** Read SKILL.md and references → walk all 9 dimensions → flag specific issues with fix recommendations → produce AP-warning summary if catches surfaced.

**Result:** Per-dimension verdicts with cited evidence; D9 verdict cites the applied sub-level.

### Example 3: Convert Informal Methodology

**Input:** "I have this methodology document. Convert this to a Skill."

**Actions:** Walk pre-build gates (warrant evidence often thin — surface to user) → treat document as informal design spec → extract description and reference structure → run 9-dimension review → flag conversion-time decisions in the build note.

**Result:** Deployable zip + audit artifacts. Build note flags any design decisions made during conversion.

### Example 4: Build with Pre-Build Gate Triggered

**Input:** "Build a Skill that always runs pytest before declaring a task complete."

**Actions:** Gate 1 catches the lifecycle-guarantee shape — redirect to hook mechanism with brief rationale, citing `references/decomposition-framework.md` and the Enforcement-as-preference anti-pattern.

**Result:** No Skill built. Correct redirect prevents a Skill that would silently fail to enforce.

### Example 5: Iterate on a Built Skill

**Input:** "Test my Skill against realistic queries."

**Actions:** Determine tier (Tier A available?) → generate trigger eval corpus → invoke grader subagent (Tier A) or qualitative review (Tier B) or analytical reasoning (Tier C) → identify gaps → propose revisions.

**Result:** D9 verdict with applied sub-level + iteration recommendations.

### Example 6: Optimize a Description

**Input:** "My description triggers on the wrong queries — fix it."

**Actions:** Generate trigger eval corpus → invoke `description_optimizer.py` (Tier A) for automated train/test loop OR run manual walkthrough (Tier B/C) → select highest-test-score revision.

**Result:** Updated description with per-iteration train/test scores; selection rationale documented.

### Example 7: Compare Two Skill Versions

**Input:** "Is v3 actually better than v2?"

**Actions:** Run both Skills against representative eval prompts → invoke comparator subagent (Tier A) or inline blind comparison (Tier B/C) → invoke analyzer for post-hoc insights.

**Result:** Winner verdict with rubric scores and improvement suggestions for the loser.

### Example 8: Multi-Environment Tier Determination

**Input:** "Build my Skill — I'm running in chat-side review."

**Actions:** Detect no execution surface → Tier C applies → build proceeds with analytical-only D9c verdict; description optimization falls to manual walkthrough.

**Result:** Build complete with explicit Tier C verdict; build summary notes which workflows were unavailable.

---

## Quality Gate

Before finalizing any build, review, or revision:

- Have the three pre-build gates been walked explicitly (decomposition, warrant, ecosystem fit)?
- Does the description YAML-parse to ≤ 1024 chars?
- Is SKILL.md body under 500 lines? Are new sections routing surfaces (no procedural duplication of references)?
- Does the name field conform (kebab-case, max 64 chars, no reserved words)?
- Has all substantive methodology been preserved from the design spec (or predecessor for successor builds)?
- Are root.node internal references adapted per conversion rules and design spec exceptions?
- Has tone calibration been applied to new content per AEA §4.11?
- Is progressive disclosure working — routing surfaces in SKILL.md, depth in references?
- Does the Skill work standalone without other rootnode Skills?
- Are cross-Skill references soft pointers with "if available"?
- Is `metadata.original-source` set? Is `metadata.predecessor` set for successor builds? Is `metadata.discipline_post` set?
- Has auto-activation enforcement passed?
- Has the AP catalog scan completed? For Skills with co-located workflows, has the Kitchen Sink decomposition test been applied (lifecycle coherence, governance duplication, independent invocation)?
- Has the 7-layer leak-check completed?
- For D9: has the applied sub-level been determined and recorded in the build summary?
- For Skills with empirical workflows: is per-script tier compatibility documented?
- Has the deployable zip been assembled with correct folder structure and no audit artifacts inside?
- Have audit artifacts been produced as separate files (placement always; promotion when warrant/override; AP-warnings when D7 catches)?
- Has zip contents been verified before delivery?

---

## When to Use This Skill

Use this Skill when:

- A design specification is present in context and the user wants deployment-ready Skill files
- The user asks to build, convert, or package methodology into SKILL.md format
- The user asks whether something should be a Skill at all ("is this actually a Skill," "does this belong in a hook instead")
- The user asks to review an existing Skill
- The user asks to revise an existing Skill
- The user asks to test or iterate on a Skill behaviorally
- The user asks to optimize a Skill description
- The user asks to compare two Skill versions
- The user asks about Agent Skills spec constraints

Do NOT use this Skill when:

- The user wants to design Skill methodology — that's design work
- The user wants to compile a prompt (use rootnode-prompt-compilation if available)
- The user wants to audit a Claude Project (use rootnode-project-audit if available)
- The user wants to evaluate a prompt's quality (use rootnode-prompt-validation if available)

---

## Troubleshooting

**Skill doesn't trigger:** description too vague. Add specific trigger phrases users would actually say. Run `references/auto-activation-discipline.md` walkthrough; consider running `description_optimizer.py` if Tier A is available.

**Skill triggers on wrong tasks:** description too broad. Add negative triggers ("Do NOT use for..."). Check for vocabulary overlap with adjacent Skills.

**Description over 1024 chars:** consolidate negative triggers, tighten phrasing, compress trigger phrase lists. Never drop routing-critical content. Always re-measure parsed YAML length after edits.

**SKILL.md body too long:** apply intelligent abstraction discipline. Move detailed documentation to references/. New sections in SKILL.md should be routing surfaces, not procedural depth.

**D9 sub-level unclear:** read `references/multi-environment-adaptation.md` §"Tier determination." Detect subagent execution availability and runnable env availability; the conservative determination is the lower tier when ambiguous.

**Cross-Skill routing collision:** add negative triggers; use distinct vocabulary domains. See `references/ecosystem-placement-decision.md`.

**User asks for a Skill that should be a hook / rule / CLAUDE.md content:** walk Gate 1 explicitly. Use the redirect language in `references/decomposition-framework.md`. Do not build the Skill.

**User asks for a Skill but can name only 1-2 occurrences:** walk Gate 2 explicitly. Recommend a paste-and-edit template. See `references/warrant-check-criteria.md`.

**`disable-model-invocation` flag set without justification:** D6 catches this. Either remove the flag or add `metadata.notes` documenting human-only reasoning.

---

## Reference table

The full reference catalog. Each file is loaded on demand; "when to read" guidance summarized below.

| Reference | When to read |
|---|---|
| `references/skills-spec.md` | Authoritative Agent Skills spec; subdirectory taxonomy; executable layer in Skills |
| `references/auto-activation-discipline.md` | Description-writing discipline; realistic test prompt patterns; tone calibration in descriptions |
| `references/conversion-guide.md` | root.node → Skills conversion patterns; tone calibration in produced Skill content; description templates |
| `references/decomposition-framework.md` | 7-layer placement framework; redirect language by mechanism (Gate 1) |
| `references/warrant-check-criteria.md` | Gate 2 evidence types; template promotion criteria |
| `references/ecosystem-placement-decision.md` | Gate 3 placement decision; duplication detection; composition lineage |
| `references/anti-pattern-catalog.md` | Skill-relevant subset of the AP catalog (D7 scan) |
| `references/behavioral-validation.md` | D9 sub-level architecture; grader principles verbatim; eval and grading schemas verbatim |
| `references/description-optimization.md` | Trigger eval generation; manual walkthrough; automated train/test loop; triggering detection mechanism |
| `references/version-comparison.md` | Blind A/B comparison rubric verbatim; analyzer output verbatim; identifier-leak prevention |
| `references/multi-environment-adaptation.md` | Tier A/B/C operational model; per-script tier compatibility; fallback patterns |
| `references/tooling-layer-overview.md` | Catalog of `scripts/`, `agents/`, `eval-viewer/`; integration patterns; drift detection discipline |

---

*End of SKILL.md.*

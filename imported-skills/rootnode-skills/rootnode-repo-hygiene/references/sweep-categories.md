# Sweep Categories

The 14 operational categories that Phase 1 scans, with detection rules, scan procedures, finding formats, confidence calibration, and routing rules.

**Canonical sources:**
- `root_AGENT_ANTI_PATTERNS.md` — pattern signatures and surface tags
- `root_CC_ENVIRONMENT_GUIDE.md §1` — 7-layer model and placement rules
- `root_CC_ENVIRONMENT_GUIDE.md §2.1` — CLAUDE.md required sections (used by Cat 12)
- `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.4` — source authority hierarchy

This file applies the canonical content to operational sweep execution. It does not duplicate the canonical content; it cites the canonical as the source of truth and applies the principles to detection.

## How to read this file

Each category has the same five subsections:
- **Detection focus** — what the scan is looking for, in one sentence
- **Scan procedure** — how to walk the repo to detect it
- **Expected finding format** — the shape of a finding entry in the report
- **Confidence calibration** — what makes a finding `high`, `medium`, or `low` confidence
- **Maps to canonical** — the AP catalog section(s) and CC guide section(s) this category lights up

**Categories 1–10 are executable** in Phase 2 when marked `[APPROVED]` in the report file.

**Categories 11–14 are recommendation-only.** Phase 2 surfaces a notice and routes to `rootnode-cc-design` REMEDIATE mode rather than executing directly. See "Recommendation-only routing" at the end of this file.

**Finding ID convention:** `F-{category}.{n}` (e.g., F-1.1, F-2.3, F-14.2). Numbers are assigned in scan order within the category.

---

## Cat 1 — Stale parent-project references in code

**Detection focus.** Code, configuration, or documentation in the engine references the parent project this repo was bootstrapped from, in ways that no longer apply.

**Scan procedure.** Walk the engine's primary script directories and config files. Search for inherited identifiers: parent-project name in package.json, parent project's README content reproduced in this repo's docs, parent project's directory structure naming conventions reused without renaming. Cross-reference the active `bootstrap_heritage` config block (see "Bootstrap heritage calibration" below) — if present, calibrate detections against the inherited file list.

**Expected finding format.**
```
F-1.{n}  [risk: low|medium|high]  [confidence: high|medium|low]
  File: <path>
  Issue: <one-sentence description>
  Evidence: <quoted line or excerpt>
  Recommended action: <remove | rename | rewrite | retain with note>
```

**Confidence calibration.**
- `high` — explicit string match with parent project name, no `bootstrap_heritage` block exempts it, and the file has been modified during the current project's work period.
- `medium` — string match exists but the `bootstrap_heritage` block lists the file as inherited; the modified-recently rule is what surfaces it.
- `low` — pattern resemblance only (e.g., directory naming style); no explicit identifier match.

**Maps to canonical.** No direct AP catalog entry — this is a project-evolution hygiene category specific to bootstrap-inherited repos. See "Bootstrap heritage calibration" below for the D6 calibration mechanism.

---

## Cat 2 — Stale or missing permissions in `.claude/settings.local.json`

**Detection focus.** Two-direction scan (per D9): stale permission entries to remove AND missing entries that cause repeated approval friction during canonical workflows.

**Scan procedure.**
- **Stale-removal scan:** for each permission entry in `permissions.allow`, search the repo for any tool invocation matching the pattern. If no invocations exist in the engine's primary script directories OR in change_log entries from the current project's work period, surface as a removal candidate.
- **Missing-entry scan:** read the engine's primary scripts and the change_log for tool invocations. For each tool family (e.g., `Bash`, `Read`, `Edit`, `Glob`), check whether the active permissions cover the invocations seen. Surface gaps where canonical workflows hit approval friction.

**Expected finding format.**
```
F-2.{n}  [risk: low]  [confidence: high|medium|low]
  Direction: stale-removal | missing-entry
  Permission: <permission string>
  Evidence: <invocation count or absence proof>
  Recommended action: remove | add | consolidate
```

**Confidence calibration.**
- `high` — stale entry with zero invocations across engine scripts AND change_log; OR missing entry with 3+ approval friction events in change_log.
- `medium` — stale entry with no invocations in scripts but unconfirmed change_log usage; OR missing entry with 1–2 friction events.
- `low` — speculative gap based on script analysis without change_log corroboration.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.8` (Missing managed policy where required). For settings hierarchy and graduated trust spectrum: `root_CC_ENVIRONMENT_GUIDE.md §1.7`.

---

## Cat 3 — Retired modules in archive directories

**Detection focus.** Code that has been moved to archive directories (`archive/`, `deprecated/`, `old/`, `retired/`, `_old/`) but is still referenced by active code.

**Scan procedure.** List directories matching the archive name pattern. For each file in those directories, search the rest of the engine for imports, requires, or shell-out invocations referencing it. Surface findings where archive-directory code is still being called by non-archive code.

**Expected finding format.**
```
F-3.{n}  [risk: medium]  [confidence: high|medium|low]
  Archive file: <path>
  Caller(s): <list of files calling it>
  Issue: <one-sentence description>
  Recommended action: relocate caller | update caller to non-archive equivalent | move file out of archive
```

**Confidence calibration.**
- `high` — explicit import/require/shell-out reference from active code.
- `medium` — string reference (e.g., a path mentioned in a comment) without confirmed runtime invocation.
- `low` — name resemblance only.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.14` (Stale content as a sub-pattern of the broader cleanup discipline).

---

## Cat 4 — Orphaned test files

**Detection focus.** Test files that target code which no longer exists, or which has been moved without test relocation.

**Scan procedure.** For each test file, identify the module it claims to test (via filename convention, import statements, or top-of-file reference). Verify the target module exists at the expected path. If not found anywhere in the engine, surface as orphaned. If found at a different path, surface as relocation-needed.

**Expected finding format.**
```
F-4.{n}  [risk: low]  [confidence: high|medium|low]
  Test file: <path>
  Target module: <expected | found-at | missing>
  Recommended action: delete test | relocate test | update test imports
```

**Confidence calibration.**
- `high` — target module name matches no file in the engine.
- `medium` — partial name match exists; fuzzy resolution required.
- `low` — test imports are dynamic and target cannot be statically resolved.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.14` (Stale content).

---

## Cat 5 — Configuration drift

**Detection focus.** Drift between declared dependencies/config and actual usage: pyproject.toml or package.json declarations vs. import statements; .gitignore entries vs. actual checked-in state; configured paths vs. existing paths.

**Scan procedure.**
- **Dependency drift:** parse declared dependencies from manifests; cross-check against import statements in source. Surface declared-but-unused dependencies and used-but-undeclared dependencies.
- **.gitignore drift:** for each pattern in .gitignore, check whether matching files are checked in. For each checked-in file in directories that look ignorable (e.g., `node_modules/`, `__pycache__/`, `.venv/`), check whether they should be ignored.
- **Path drift:** for each path referenced in config files, verify the path exists.

**Expected finding format.**
```
F-5.{n}  [risk: low|medium]  [confidence: high|medium|low]
  Drift type: dependency | gitignore | path
  Source: <config file>
  Issue: <one-sentence description>
  Evidence: <quoted line or path>
  Recommended action: <remove | add | update>
```

**Confidence calibration.**
- `high` — exact match between declared and actual state can be computed.
- `medium` — pattern-match drift requiring manual verification.
- `low` — speculative based on naming conventions.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.14` (Stale content).

---

## Cat 6 — Bypass-permission misuse

**Detection focus.** Use of `bypassPermissions: true` or `--dangerously-skip-permissions` outside sandboxed contexts.

**Scan procedure.** Search settings files for `bypassPermissions: true`. Search shell scripts, npm scripts, Makefiles, and CI configs for `--dangerously-skip-permissions`. For each occurrence, evaluate whether the context is sandboxed (containerized, ephemeral, isolated from the user's primary workspace).

**Expected finding format.**
```
F-6.{n}  [risk: high]  [confidence: high|medium|low]
  File: <path>
  Context: <sandbox | non-sandbox | unclear>
  Evidence: <quoted line>
  Recommended action: remove | move to sandbox-only config | document rationale in CLAUDE.md
```

**Confidence calibration.**
- `high` — bypass usage in user-workspace settings (`~/.claude/settings.json`) or project root settings outside an explicit sandbox boundary.
- `medium` — bypass usage in CI or scripts where sandboxing is plausible but not confirmed.
- `low` — bypass usage with explicit sandbox context comments.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.7` (bypassPermissions outside sandbox). Permission modes: `root_CC_ENVIRONMENT_GUIDE.md §1.7`.

---

## Cat 7 — Hook misconfiguration

**Detection focus.** Hooks that reference nonexistent scripts, hooks placed in the wrong mechanism (preference-as-enforcement), or hooks that should exist but don't.

**Scan procedure.**
- For each hook in `.claude/settings.json` (and parent settings files), verify the referenced script path exists and is executable.
- Read CLAUDE.md and `.claude/rules/` for "remember to..." or "always do X" instructions that describe lifecycle guarantees. Surface as enforcement-as-preference candidates that should be hooks.
- For verification-before-completion: check whether a Stop hook exists that runs the test command. Surface absence as a Cat 13 finding (recommendation-only) AND a Cat 7 finding (executable: add Stop hook) when the test infrastructure exists.

**Expected finding format.**
```
F-7.{n}  [risk: medium|high]  [confidence: high|medium|low]
  Hook type: <missing-script | wrong-mechanism | absent-but-warranted>
  Location: <settings file or CLAUDE.md line>
  Evidence: <quoted hook config or instruction text>
  Recommended action: <fix path | extract from prose to hook config | add hook>
```

**Confidence calibration.**
- `high` — script reference produces a `file not found` on direct check; OR enforcement-as-preference language is unambiguous ("always run tests after editing").
- `medium` — wrong-mechanism candidate where the rule could plausibly remain in CLAUDE.md if the team accepts soft enforcement.
- `low` — absent-but-warranted hook where the gap is inferred from missing automation rather than from explicit signal.

**Maps to canonical.** `root_AGENT_ANTI_PATTERNS.md §4.4` (Enforcement-as-preference). Hooks-vs-prompts boundary: `root_CC_ENVIRONMENT_GUIDE.md §6`. Verification before completion: `root_CC_ENVIRONMENT_GUIDE.md §5.2`.

---

## Cat 8 — Subagent definition drift

**Detection focus.** Subagent definitions that reference tools, files, or paths that no longer exist or have moved.

**Scan procedure.** For each subagent definition in `.claude/agents/`, parse the tool list and any embedded file references. Verify each referenced tool is available and each file path exists. Cross-reference subagent invocation in change_log to estimate usage frequency.

**Expected finding format.**
```
F-8.{n}  [risk: low|medium]  [confidence: high|medium|low]
  Subagent: <name>
  Drift type: <missing-tool | missing-file | unused>
  Evidence: <quoted reference or invocation count>
  Recommended action: <update reference | retire subagent | refocus scope>
```

**Confidence calibration.**
- `high` — referenced file does not exist OR subagent has zero invocations across last 90 days of change_log.
- `medium` — referenced tool is present but appears unused inside the subagent's actual prompt body.
- `low` — usage gap inferred without change_log corroboration.

**Maps to canonical.** Subagent overuse: `root_AGENT_ANTI_PATTERNS.md §4.5`. Subagent underuse: `root_AGENT_ANTI_PATTERNS.md §4.6`. Subagent design: `root_CC_ENVIRONMENT_GUIDE.md §1.4 + §3`.

---

## Cat 9 — CLAUDE.md bloat

**Detection focus.** CLAUDE.md drift away from the discipline of being short, always-relevant, file-state-grounded standing context. Five sub-signals: line count over 200, aspirational language, conversational framing, mixed reference material, stale state sections.

**Scan procedure.**
- **Line count:** Count non-blank, non-comment lines. Surface findings when over 200 (per `root_CC_ENVIRONMENT_GUIDE.md §1.1`).
- **Aspirational language:** scan for "we should", "ideally", "in the future", "going forward". Surface each occurrence.
- **Conversational framing:** scan for "you should", "remember to", "don't forget to", "please" — markers of preference-as-enforcement (which is also a Cat 7 candidate).
- **Mixed reference material:** detect blocks of content that match the shape of `.claude/rules/` content (file-pattern-specific guidance) or Skill content (multi-step procedures). Surface as extraction candidates.
- **Stale state sections:** for any "Engine state snapshot" or similar section, cross-reference declared values against current repo state. Surface drift findings.

**Expected finding format.**
```
F-9.{n}  [risk: low|medium]  [confidence: high|medium|low]
  Sub-signal: <line-count | aspirational | conversational | mixed-reference | stale-state>
  Line(s): <line numbers>
  Evidence: <quoted line(s)>
  Recommended action: <remove | extract to .claude/rules/ | extract to Skill | update to current state>
```

**Confidence calibration.**
- `high` — exact pattern match (e.g., "remember to" appears verbatim) OR state value differs from current repo.
- `medium` — fuzzy pattern match requiring author judgment.
- `low` — stylistic concern without clear violation.

**Maps to canonical.** Length discipline: `root_CC_ENVIRONMENT_GUIDE.md §1.1`. Bloated CLAUDE.md / Monolithic standing context: `root_AGENT_ANTI_PATTERNS.md §2.1`. Transcript dump: `§4.1`. Enforcement-as-preference: `§4.4`. Path-scoped rules opportunity: `§4.9`. Auto memory misuse: `§4.10`. Stale CLAUDE.md: `§4.14`.

---

## Cat 10 — Skills directory hygiene

**Detection focus.** Skills in `.claude/skills/` that fail spec compliance or activation discipline.

**Scan procedure.** For each Skill folder, verify:
- Frontmatter parses as valid YAML
- `name` field is kebab-case, ≤64 chars, matches the folder name
- `description` field YAML-parses to ≤1024 chars (parsed length, not raw character count)
- SKILL.md body is under 500 lines / ~5000 tokens
- No XML angle brackets in frontmatter
- No README.md inside the Skill folder
- If `disable-model-invocation: true` is set, `metadata.notes` includes justification
- Description includes verb-based triggers (not just static descriptors)

**Expected finding format.**
```
F-10.{n}  [risk: low|medium]  [confidence: high]
  Skill: <name>
  Issue: <spec-compliance failure type>
  Evidence: <quoted frontmatter or measured value>
  Recommended action: <fix description | trim body | add metadata.notes | rename folder>
```

**Confidence calibration.**
- `high` — all spec checks are deterministic; findings are high confidence by construction.
- `medium` — used only for activation-discipline judgment calls (e.g., "description has descriptors but weak verbs").

**Maps to canonical.** Manual-only Skills: `root_AGENT_ANTI_PATTERNS.md §4.3`. Skills/Commands legacy mix: `§4.12`. Skills > Commands and auto-activation: `root_CC_ENVIRONMENT_GUIDE.md §1.3`.

---

## Cat 11 — File/folder architectural drift (recommendation-only)

**Detection focus.** Files placed in wrong directories, empty directories that should be removed or repurposed, monolithic files that should be split, directory structure that doesn't match the project's documented architecture.

**Scan procedure.** Read the project's architecture documentation (CLAUDE.md "directory structure" section, README, or `.claude/rules/architecture.md` if present). Compare declared structure to actual structure. Surface findings for files in unexpected locations, directories declared but missing, directories present but undeclared, and individual files exceeding reasonable size thresholds for their type (e.g., scripts over 800 lines, configs over 300 lines).

**Expected finding format.**
```
F-11.{n}  [risk: medium]  [confidence: medium]
  Drift type: <wrong-location | empty-dir | monolithic-file | undeclared-dir>
  Path: <path>
  Recommended action: <route to REMEDIATE>
```

**Confidence calibration.** Most Cat 11 findings are `medium` — architectural intent is rarely fully encoded in machine-readable form. `high` only when declared structure explicitly contradicts actual structure.

**Maps to canonical.** General structural drift; routes to REMEDIATE for fix-recipe derivation per `root_AGENT_ANTI_PATTERNS.md §3.4` (structural Kitchen Sink) and the 7-layer placement framework.

---

## Cat 12 — CC environment configuration drift (recommendation-only)

**Detection focus.** CLAUDE.md missing required sections per `root_CC_ENVIRONMENT_GUIDE.md §2.1` (R1–R5: mission, authority matrix, scope authorization, halt-and-escalate triggers, pre-flight checklist). Missing or malformed `change_log.md`, `SHIP_MANIFEST.md`, `halt_notes/` directory. Hooks configuration internally inconsistent. MCP server inventory exceeding the ~20K token threshold.

**Scan procedure.**
- For each R1–R5 required section, verify presence in CLAUDE.md.
- For W1–W3 warranted sections, verify either presence or explicit inclusion-test rationale documented.
- Check for `change_log.md`, `SHIP_MANIFEST.md`, `halt_notes/` at the standard locations.
- Parse `.claude/settings.json` MCP server list; estimate token cost from declared tool schemas. Surface findings if estimate exceeds ~20K tokens.
- Cross-check hooks configuration: every PreToolUse hook should have a corresponding cleanup or pairs symmetrically with a PostToolUse hook where state is touched.

**Expected finding format.**
```
F-12.{n}  [risk: medium|high]  [confidence: high|medium|low]
  Drift type: <missing-required-section | missing-discipline-file | hook-asymmetry | mcp-bloat>
  Location: <file or section>
  Evidence: <measured value or absence proof>
  Recommended action: <route to REMEDIATE>
```

**Confidence calibration.**
- `high` — required section is provably missing (text search produces zero hits).
- `medium` — section is present but incomplete or malformed.
- `low` — judgment-based concerns about quality.

**Maps to canonical.** CLAUDE.md required sections: `root_CC_ENVIRONMENT_GUIDE.md §2.1`. MCP minimalism: `§1.6`. Bloated CLAUDE.md: `root_AGENT_ANTI_PATTERNS.md §2.1`. MCP bloat: `§4.2`. Kitchen-sink session: `§4.13`. Stale CLAUDE.md: `§4.14`.

---

## Cat 13 — Pre-flight infrastructure gaps (recommendation-only)

**Detection focus.** Missing test backstop, missing orchestrator script, missing `change_log.md` discipline, missing SHIP_MANIFEST, missing `halt_notes/`, missing additive-evolution markers — the discipline practices documented in `root_CC_ENVIRONMENT_GUIDE.md` discipline section.

**Scan procedure.**
- **Test backstop:** verify a top-level test command exists and runs (npm test, pytest, make test). If present, verify it actually executes (parse output for test count or pass/fail).
- **Orchestrator:** look for a top-level `run.sh`, `orchestrator.py`, `Makefile`, or equivalent that describes the engine's primary execution surface.
- **change_log.md:** verify presence and recency. Surface findings if absent or if last entry is older than 30 days for an active project.
- **SHIP_MANIFEST.md:** verify presence for projects in distribution stage.
- **halt_notes/:** verify directory exists for projects with autonomous execution surfaces.
- **Additive evolution markers:** scan for explicit additive vs. destructive change markers in change_log entries.

**Expected finding format.**
```
F-13.{n}  [risk: medium]  [confidence: high|medium]
  Gap type: <test-backstop | orchestrator | change-log | ship-manifest | halt-notes | additive-markers>
  Recommended action: <route to REMEDIATE>
```

**Confidence calibration.**
- `high` — discipline file or directory is provably absent.
- `medium` — file is present but the discipline isn't being practiced (e.g., change_log exists but is stale).

**Maps to canonical.** Verification-before-completion absent: `root_AGENT_ANTI_PATTERNS.md §4.11`. Discipline practices: `root_CC_ENVIRONMENT_GUIDE.md` discipline section.

---

## Cat 14 — Token-load abstraction candidates (HIGHEST VALUE — recommendation-only)

**Detection focus.** Recurring work patterns in the project that warrant lifting from "Claude does this manually each session" to a deterministic mechanism (script, Skill, hook, subagent, or MCP server). This is the differentiating value of the Skill — generic linters can't do it.

**Scan procedure.** Five detection signals:

1. **Recurring operations in change_log:** scan for the same shape of work appearing in 3+ change_log entries. Examples: "ran tests, fixed N failures, re-ran tests" pattern; "updated state snapshot in CLAUDE.md" pattern; "regenerated derived artifact X" pattern.

2. **Permission patterns:** scan `.claude/settings.local.json` for multiple permission entries covering the same operation family. Three permissions for `Bash(python tests/*)`, `Bash(python -m pytest*)`, `Bash(python tests/test_*.py*)` are one wrapper script's worth of work.

3. **Repeated multi-step sequences in session_closeouts:** scan session_closeouts (or equivalent retrospective files) for "ran X then Y then Z" sequences appearing across multiple sessions.

4. **Deterministic state queries CC re-derives:** scan change_log and CLAUDE.md state sections for queries that have a single-source-of-truth answer but get re-derived each session. Examples: "what's the current test count," "what was the last fix," "which guides are passing."

5. **Hooks wrapping manual operations:** scan existing hooks for ones that fire and then prompt the user to do a manual step. The manual step is the abstraction candidate.

**Expected candidate format.** Each candidate gets all eight fields:
```
F-14.{n}  [scope: project-local | methodology-generalizable]
  candidate_name: <short descriptive name>
  current_cc_pattern: <what CC does today; rough token estimate per invocation>
  proposed_abstraction: <script | Skill | hook | subagent | MCP>
  estimated_savings_per_invocation: <token delta>
  estimated_invocations_per_month: <from change_log frequency>
  complexity: <trivial | moderate | substantial>
  prerequisites: <what must exist before the abstraction is buildable>
  scope: <project-local | methodology-generalizable>
```

**Scope tag (D8) — decision rules:**
- **`project-local`** — the pattern is specific to this project's data, paths, or workflows. Lifting it produces value here but doesn't transfer.
- **`methodology-generalizable`** — the pattern recurs across projects of similar shape (CC environments, hygiene work, prompt engineering work, etc.). Lifting it produces value here AND queues it as a candidate for shared tooling roadmap.

A candidate is `methodology-generalizable` when:
- The pattern can be described without referencing project-specific identifiers, OR
- The same pattern has been observed in another project the user has worked on, OR
- The pattern matches a generic CC discipline (state-snapshotting, test-result-summarization, permission consolidation).

Otherwise default to `project-local`.

**Confidence calibration.** Cat 14 candidates don't carry confidence tiers. They carry `complexity` instead — `trivial` (under an hour), `moderate` (one work session), `substantial` (multi-session build). Lower-complexity candidates with high invocation frequency rank highest.

**Maps to canonical.** Runtime tooling catalog: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`. Methodology-generalizable candidates queue for the catalog as future runtime tooling entries. Process-abstraction discipline detail in `process-abstraction-detection.md`.

---

## Bootstrap heritage calibration (D6 — applies to Cat 1)

When the active profile contains a `bootstrap_heritage` config block, Cat 1 calibration changes:

1. **Inventory subsection.** Phase 1 produces a "Bootstrap heritage inventory" subsection at the top of the Cat 1 section listing inherited files, inherited directories, and the modified-recently threshold. This is informational; no findings are generated from inventory entries alone.

2. **Sharper detection conditions.** Findings are only surfaced when one of these applies:
   - An inherited file has been modified after `modified_recently_threshold`
   - In-engine code (current project's primary scripts) imports from or shells out to inherited modules
   - In-engine docs reference inherited workflows as if they were the current project's
   - Inherited reference files are cited as authoritative when they are explicitly historical

3. **Confidence floor.** Findings under bootstrap heritage carve-out cannot be `high` confidence unless the modified-recently rule is what triggered them. Other inherited-file findings ceiling at `medium`.

When the `bootstrap_heritage` block is empty or absent, Cat 1 runs without calibration. This is appropriate for repos that were not bootstrapped from a parent project.

The `bootstrap_heritage` block schema and field semantics are documented in design doc §9. The block is part of the profile JSON; see `schema/profile.schema.json`.

---

## Recommendation-only routing (Cat 11–14 + 7-layer leak findings)

Phase 1 always scans Cat 11–14 when the active profile includes them. The findings appear in the report under their category sections. They are NOT executable in Phase 2.

When the report contains Cat 11–14 findings or 7-layer leak findings AND the active profile has `remediate_routing: true` (default), Phase 1 produces a "Routing recommendations" section near the end of the report listing the structural findings and recommending invocation of `rootnode-cc-design` REMEDIATE mode.

Direct text the recommendation uses:

> *These structural findings benefit from the REMEDIATE mode in `rootnode-cc-design`, which derives a fix recipe per anti-pattern and validates against the 7-layer placement framework before executing. To act on these findings, invoke `rootnode-cc-design` REMEDIATE with this report (`HYGIENE_REPORT.md`) as input. To proceed without REMEDIATE, treat these findings as recommendation-only — Phase 2 will skip them.*

**Phase 2 behavior on `[APPROVED]` markers in Cat 11–14 or leak findings.** Phase 2 surfaces a notice naming the marked findings, names the REMEDIATE handoff, and proceeds with Cat 1–10 batches only. The marker is preserved in the report (it's a record of the user's intent) but does not flow into a Phase 2 execution batch.

When the active profile has `remediate_routing: false`, the routing section is omitted. Findings remain in the report as recommendation-only with no automated downstream pathway.

---

## 7-layer leak findings — finding format reference

7-layer leak findings are produced by the cross-category analytical pass documented in `seven-layer-framework.md`. They use the prefix `L-` rather than `F-`:

```
L-{n}  [layer: <1–7>]
  Current placement: <CLAUDE.md | rules | Skills | subagents | hooks | MCP | settings>
  Recommended placement: <target layer>
  Evidence: <quoted content or location>
  Recommended extraction: <one-sentence procedure>
```

Leak findings route to REMEDIATE alongside Cat 11–14 findings. Phase 2 does not execute leaks directly.

---

## Confidence threshold filtering (profile field)

When the active profile sets `confidence_threshold`:
- `high` — only `high`-confidence findings appear in the report. `medium` and `low` are suppressed.
- `medium` — `high` and `medium` findings appear; `low` is suppressed.
- `low` — all findings appear (default for `deep-audit`).

Cat 14 candidates are not subject to confidence threshold filtering — they don't carry confidence tiers. They appear when their category is in the active profile's `categories` list.

---

*End of sweep categories. Cross-references throughout: `root_AGENT_ANTI_PATTERNS.md` for pattern signatures, `root_CC_ENVIRONMENT_GUIDE.md §1` for 7-layer placement, `root_CC_ENVIRONMENT_GUIDE.md §2.1` for CLAUDE.md required sections.*

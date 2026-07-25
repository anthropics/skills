---
name: rootnode-repo-hygiene
description: >-
  Audits Claude Code repositories. Two-phase workflow — Phase 1 sweeps 14
  hygiene categories (permissions, hooks, CLAUDE.md bloat, Skills hygiene,
  process-abstraction, plus structural) and an optional 7-layer leak check.
  Phase 2 executes [APPROVED] markers from the report file. Use for repo
  cleanup, pre-distribution sanity, post-feature hygiene, environment audit,
  process-abstraction discovery. Trigger on "audit my CC repo," "sweep my
  repository for hygiene," "check this CC environment," "find process
  abstraction candidates," "review my CLAUDE.md," "clean up my .claude
  directory," "pre-distribution hygiene check," "find layer leaks in my CC
  setup." Routes structural findings to rootnode-cc-design REMEDIATE. Composes
  with rootnode-critic-gate. CC-only — does not scan Claude Projects. Do NOT
  use for building a Skill (use rootnode-skill-builder), compiling a prompt
  (use rootnode-prompt-compilation), scoring a single prompt (use
  rootnode-prompt-validation), or auditing a Project (use
  rootnode-project-audit).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0"
  original-source: "Synthesized from root_AGENT_ENVIRONMENT_ARCHITECTURE.md (surface-invariant placement discipline), root_CC_ENVIRONMENT_GUIDE.md (7-layer model, discipline practices, hooks-vs-prompts boundary), root_AGENT_ANTI_PATTERNS.md (canonical anti-pattern catalog with surface tags). Production-validated against a CC deployment sweep on 2026-05-04 surfacing 23 findings across 14 categories with three-form authorization use and Path 3 commit-plan adaptation accepted as defer-to-downstream."
  discipline_post: phase-30
---

# rootnode-repo-hygiene

A two-phase Skill for auditing and cleaning up Claude Code repositories. Phase 1 sweeps the repo across 14 categories of hygiene concern plus a cross-category 7-layer placement leak check, producing a `HYGIENE_REPORT.md`. Phase 2 reads `[APPROVED]` markers placed in that file and executes the marked findings under critic-gate composition with halt-on-failure discipline.

The Skill is the operational counterpart to `rootnode-cc-design`: design produces the environment, hygiene maintains it. Structural findings that warrant fix-recipe derivation route to `rootnode-cc-design` REMEDIATE rather than executing here. Process-abstraction candidates that recur across CC environments route as warrant evidence for `rootnode-skill-builder` v2.

## Important — five principles that govern Phase 2 behavior

These five principles override looser interpretations elsewhere in this Skill. They are enforcement-grade.

**1. Authorization is file-state-grounded.** Phase 2 reads `[APPROVED]` markers from the report file. Verbal authorization in chat is never a substitute. The Skill MAY act as a text editor on the user's behalf using the three approval forms (blanket, fragmented, conditional — see "Authorization discipline" below). When acting as editor, the Skill produces the marked file for the user to save; Phase 2 then reads the saved file. There is no verbal-authorization fallback. The discipline guards against the silent execution problem: chat-side intent is high-context but ephemeral; the marked file is the durable contract.

**2. Recommendation-only categories never execute directly.** Categories 11-14 and 7-layer leak findings are recommendation-only. `[APPROVED]` markers on these findings are noted in Phase 2 but produce a "skipped — REMEDIATE recommended" notice rather than an execution batch. The marker is preserved in the report file (it documents user intent) but does not become a file edit. Reason: structural change requires fix-recipe derivation and 7-layer placement validation that single-edit Phase 2 execution cannot perform safely.

**3. Defer-to-downstream is a first-class commit-plan option.** When Phase 1 detects distribution intent + working-tree state + downstream-resolvable findings, it recommends defer-to-downstream over Options A/B/C. Phase 2 accepts deferral and executes file edits without git operations; the cleanup_execution_log substitutes for commit messages as the audit trail. This is the production-validated pattern from a CC deployment where engine-baseline commit hit a permission denial on 207 MB / 883-file scope and Path 3 deferral was the right answer rather than retrying a failed commit.

**4. Bootstrap heritage carve-out calibrates Cat 1.** When the active profile contains a `bootstrap_heritage` block, Cat 1 produces a "Bootstrap heritage inventory" subsection at the top of its findings and applies sharpened detection conditions: findings only surface for inherited content modified after the threshold date, referenced by in-engine code, treated as authoritative in current docs, or otherwise active in the current project. This eliminates false positives on legitimate inherited content while preserving the ability to catch problematic inheritance.

**5. Structural findings route to REMEDIATE.** Cat 11-14 and 7-layer leaks always route to `rootnode-cc-design` REMEDIATE mode. The handoff is named explicitly in the report's "Routing recommendations" section when `remediate_routing: true` (default). REMEDIATE handles fix-recipe derivation and 7-layer placement validation that single-edit Phase 2 execution cannot.

## When to use

Trigger this Skill on:
- "Audit my CC repo" / "sweep my repository for hygiene" / "check this CC environment"
- "Find process-abstraction candidates" / "what work patterns should be lifted to scripts/Skills/hooks"
- "Review my CLAUDE.md" / "clean up my .claude directory"
- "Pre-distribution hygiene check" / "before-shipping cleanup pass"
- "Find layer leaks in my CC setup" / "what's in the wrong layer"
- "Parent-project vestiges" (when the repo was bootstrapped from another project)

Symptom-phrased triggers also apply: "my CLAUDE.md feels bloated," "I have permissions I don't think I use anymore," "my CC environment has accumulated drift," "I want to know what to clean up before I share this repo."

The Skill operates **CC-side only**. It scans Claude Code repositories — `.claude/` directory, CLAUDE.md, hooks, subagents, MCP configurations. It does not audit Claude Projects (CP-side). For Project audits, use `rootnode-project-audit`.

## Two-phase workflow

### Phase 1 — Sweep

Phase 1 walks four steps:

1. **Pre-flight inventory.** Read CLAUDE.md, settings files (`.claude/settings.json`, `.claude/settings.local.json`), Skills (`.claude/skills/`), agents (`.claude/agents/`), hooks, MCP declarations. Detect bootstrap_heritage block in active profile and capture its inventory. Capture working-tree state (informational; never halt). Output: pre-flight summary at the top of the report file.

2. **Category sweep.** Walk categories 1-14 per active profile in numerical order. Each category produces findings in its standard format (`F-{cat}.{n}` ID, risk tag, confidence tag, evidence quote, recommended action). Cat 1 applies bootstrap heritage calibration when active. Cat 2 runs both stale-removal and missing-entry directions (D9). Cat 14 produces 8-field candidate blocks rather than standard findings. See `references/sweep-categories.md` for detection rules per category.

3. **7-layer leak check** (when profile enables it). Cross-category analytical pass after the sweep. Walks the full standing-context inventory and applies six layer-pair tests. Surfaces `L-{n}` findings for content placed in the wrong layer for its concern. Findings appear in their own "7-Layer Leak Findings" section near the end of the report. See `references/seven-layer-framework.md`.

4. **Report assembly.** Produce `output/hygiene_reports/HYGIENE_REPORT_{ISO8601}.md` with: pre-flight summary, per-category findings sections, 7-layer leak findings section (if enabled), "Routing recommendations" section (if `remediate_routing: true`), "Recommended commit plan" section (if `include_commit_plan: true`), and a marking ledger area at the bottom. The marking ledger is empty at Phase 1 end; the user (or the Skill acting as editor) populates it as authorization decisions are made.

### Phase 2 — Execute

Phase 2 walks five steps:

1. **Entry conditions.** Five gate checks: file-state authorization (≥1 `[APPROVED]` marker in report), profile validation (JSON validates against schema), engine baseline coherence (state hasn't drifted since Phase 0), critic-gate availability (when threshold is `required`), marker placement validation (no `[APPROVED]` markers on Cat 11-14 / leak findings — those skip with notice). Failing any condition halts Phase 2 entry with the specific failure surfaced.

2. **Batch construction.** Group `[APPROVED]` Cat 1-10 findings into batches: one category per batch, subdivided by confidence tier and risk tier. Higher-confidence and lower-risk batches execute first. Each batch carries metadata for the verification step: file changes expected, category-specific verification command, finding IDs included.

3. **Per-batch execution.** Plan submission → critic-gate review (when applicable) → execute → post-batch verification → log to `cleanup_execution_log.md`. See `references/execution-discipline.md` for the per-category verification table and full critic-gate composition rules including the 3-cycle REQUEST_CHANGES cap.

4. **Commit plan execution.** Apply the chosen plan (Option A/B/C or defer-to-downstream). The Skill never auto-runs the engine-baseline commit (Step 1 of Options B/C); the user runs it manually pre-Phase-2 because the scope is too large to commit without explicit user review. The Skill runs the cleanup commit (Step 2) using a message built from the cleanup log.

5. **Final verification sweep.** Engine baseline coherence re-check (compare to Phase 0 snapshot), test backstop run (when a test command exists), skipped-findings summary (Cat 11-14 + leak markers grouped by recommended REMEDIATE handoff), closeout summary (totals, commit plan, final test result, REMEDIATE recommendations).

Halt-on-failure discipline applies throughout Phase 2. Verification failure, critic-gate REJECT, REQUEST_CHANGES exceeding 3 cycles, and commit-plan permission denial all halt with a recorded reason; the Skill does not retry automatically. Resolution is user-driven and re-invocation continues with the remaining unmarked work.

## Profile selection

Three profiles ship with the Skill:

- **`default`** — All 14 categories, leak check on, commit plan on, critic-gate optional, REMEDIATE routing on, medium-confidence floor. Standard sweep for periodic maintenance and pre-distribution checks.
- **`quick-scan`** — Cat 1, 2, 6, 9 only. No leak check, no commit plan, high-confidence floor. Fast pre-commit triage when the full sweep is too heavy. Skips structural categories entirely.
- **`deep-audit`** — All 14 categories + Cat 14 extension pass, leak check on, commit plan on, critic-gate **required**, REMEDIATE routing on, low-confidence floor (surfaces everything including speculative findings). Quarterly health check or pre-major-refactor audit.

Custom profiles must validate against `schema/profile.schema.json`. Required fields: `categories`, `include_seven_layer_leak_check`, `include_commit_plan`, `critic_gate_threshold`, `remediate_routing`. Optional: `bootstrap_heritage` (Cat 1 calibration), `confidence_threshold` (suppresses lower-confidence findings), `cat_14_extension_pass` (cross-candidate dependency analysis + build-this-first recommendation).

The `critic_gate_threshold` field controls Phase 2 composition with `rootnode-critic-gate`: `required` halts entry if critic-gate is not installed and submits every batch for review; `optional` allows per-batch user choice when critic-gate is installed.

The `remediate_routing` field controls whether the report includes a "Routing recommendations" section naming `rootnode-cc-design` REMEDIATE handoff for structural findings. When `false`, structural findings remain in the report as recommendation-only with no automated downstream pathway named.

## Authorization discipline

Per Principle 1, authorization is file-state-grounded. The Skill supports three approval forms when acting as text editor on the user's behalf.

**Blanket.** User says "approve all Cat N findings." The Skill marks every finding in the named category `[APPROVED]`. Returns the marked report file for the user to save. Suitable when the category's findings are homogeneous and the user has reviewed them as a group.

**Fragmented.** User says "approve F-X.1 and F-X.3, defer F-X.2." The Skill validates each finding ID exists in the report, then marks per the user's intent (`[APPROVED]` or `[DEFERRED]` per the verb used). Returns the marked file. Suitable for mixed intent within a category — typical for Cat 1 (some parent-vestige findings approve, some defer to downstream migration) and Cat 9 (stale-state findings approve, restructuring findings defer to leak handling).

**Conditional.** User says "approve all medium-and-low risk findings; halt high-risk for review." The Skill walks unmarked findings, applies the predicate (risk filter, category filter, confidence filter, or combination), marks matching findings `[APPROVED]`. Findings failing the predicate remain unmarked. Returns the marked file along with a list of what got marked and what didn't. Suitable for sweeping the long tail of low-stakes findings without naming each.

Every editor action records a marking ledger entry at the bottom of the report file: timestamp, approval form, scope, finding IDs marked, action taken. The ledger is the audit trail; Phase 2's EC-1 check reads from it indirectly (by counting `[APPROVED]` markers in the body), and post-Phase-2 review reads from it directly.

## Commit plan handling

Phase 1 produces a "Recommended commit plan" section. Phase 2 executes the chosen plan after batches complete and pass verification.

**Options:**
- **A — No commits.** File edits remain in working tree. Suitable for one-shot deliverables or evaluation runs.
- **B — Engine baseline + cleanup commit.** User commits engine baseline pre-Phase-2 (manual step the Skill never auto-runs); Skill commits cleanup as one commit post-batches with a message built from the cleanup log.
- **C — Engine baseline + per-domain cleanup commits.** Same as B but cleanup splits into N commits by domain (parent-vestige, permissions, stale code, configuration, standing context). Useful when downstream review needs domain-scoped commits.
- **Defer-to-downstream.** When distribution intent + working-tree state + downstream-resolvable findings detected (D11). File edits accumulate in working tree without git operations; the cleanup_execution_log substitutes for commit messages.

The commit plan is a recommendation; the user can override at Phase 2 invocation by naming a different plan. The Skill warns when the override conflicts with the deferral signal but does not block.

## Bootstrap heritage handling (Cat 1 calibration)

When the active profile's `bootstrap_heritage` block is populated, Cat 1 calibration changes per Principle 4. Block fields:

- `inherited_files` — explicit file paths inherited from parent project
- `inherited_directories` — glob patterns identifying inherited file groups
- `package_json_name` — parent project's package.json name (for identity-string detection)
- `modified_recently_threshold` — ISO 8601 date; files modified after this surface as findings
- `parent_project_name` — parent project name for documentation/code reference detection

When the block is absent or empty, Cat 1 runs without calibration (appropriate for non-bootstrapped repos). The Phase 1 inventory subsection lists inherited files but generates no findings from inventory entries alone — only the modified-recently rule, in-engine reference rule, authoritative-citation rule, or other sharpened conditions surface findings. See `references/sweep-categories.md` Cat 1 section for full calibration semantics including the confidence floor that prevents inherited content from generating high-confidence false positives.

## Process-abstraction candidates (Cat 14)

Cat 14 is the highest-value scan and the differentiating feature versus generic linters. Detection signals: recurring change_log operations (3+ entries with same shape), permission patterns covering the same operation family, repeated multi-step session_closeout sequences (3+ sessions with same 3+ step sequence), deterministic state queries CC re-derives each session, hooks ending in manual prompts.

Each candidate gets all eight fields including a `scope` tag — `project-local` (specific to this project's data, paths, workflows) or `methodology-generalizable` (recurs across CC environments of similar shape; transfers to other projects). Methodology-generalizable candidates are the warrant evidence for shared-tooling promotion: their candidate-block format is compatible with `rootnode-skill-builder` v2 Gate 2 exception clause, so a methodology-generalizable Cat 14 candidate IS the handoff brief for downstream Skill or runtime-tooling builds.

The `deep-audit` profile sets `cat_14_extension_pass: true`, which runs cross-candidate dependency analysis (which candidates unlock which), order-of-build recommendation (lower-complexity + higher-frequency + no-prerequisites first), and a single "build this first" pick.

See `references/process-abstraction-detection.md` for full detection signals, scope categorization rules, and worked examples from the production validation set.

## Composition

**With `rootnode-critic-gate` (Phase 2 batch review).** When `critic_gate_threshold: required`, every Phase 2 batch submits to critic-gate before execution. Verdicts: APPROVE → execute; REQUEST_CHANGES → adjust + resubmit (3-cycle cap, then halt); REJECT → halt with rejection surfaced. When `optional`, critic-gate review is per-batch user choice when critic-gate is installed; the Skill prompts "critic-gate available — invoke?" before each batch.

**With `rootnode-cc-design` REMEDIATE (downstream handoff).** Cat 11-14 findings and 7-layer leak findings route to REMEDIATE rather than executing in Phase 2. The "Routing recommendations" section in the report names this handoff explicitly. REMEDIATE consumes the report as input; this Skill consumes nothing from REMEDIATE in return.

**As Producer for `rootnode-skill-builder` v2 Gate 2.** Methodology-generalizable Cat 14 candidates (the 8-field block format) satisfy skill-builder v2's Gate 2 warrant evidence requirement. The user uploads the candidate block as a process-abstraction handoff brief; skill-builder's Gate 2 exception clause accepts it without requiring the standard 3+ occurrence + design-lineage proof.

## CC-only Skill notice

This Skill operates exclusively on Claude Code repositories. The scan logic walks `.claude/` directory contents, settings files, hooks, subagents, MCP configurations, and CLAUDE.md. None of these surfaces exist on Claude Projects.

For Project audits, use `rootnode-project-audit`. For prompt-level audits (single prompt or system prompt), use `rootnode-prompt-validation`. The CC-only constraint is intentional: cross-surface "audit anything" Skills produce shallow analysis on both sides because the surfaces have different mechanics (CP layers vs. CC layers) and different anti-pattern profiles.

## Examples

### Example 1 — Standard sweep with three-form authorization

The user invokes the Skill at the engine root with `default` profile. Phase 1 produces a report with 23 findings across 14 categories plus 3 leak findings. The user marks via three approval forms in the same session: blanket on Cat 2 ("approve all Cat 2"), fragmented on Cat 1 + Cat 9 ("approve F-1.3, defer F-1.1/F-1.2; approve all stale-state findings, skip line-count and mixed-reference"), conditional on the rest ("approve all medium-and-low risk"). The Skill applies markers via the editor pathway, recording each in the marking ledger. Phase 2 reads the marked file, builds 9 batches, executes with optional critic-gate review on the high-risk-flagged Cat 2 entry (the `Bash(rm -rf*)` permission removal), runs final verification (test backstop passes), and closes out. Total: 18 executed, 2 deferred, 11 + 3 leaks routed to REMEDIATE. See `references/worked-example.md` for the full walkthrough including Phase 1 finding output, marking ledger entries, and per-batch execution log.

### Example 2 — Defer-to-downstream commit plan (Path 3 adaptation)

Same engine as Example 1 but with active distribution intent: the maintainer is planning a fresh-repo migration in the next week. Phase 1 detects distribution intent (in CLAUDE.md), working-tree state (12 modified files), and downstream-resolvable findings (Cat 1 parent-vestige work likely moot under fresh-repo migration). The "Recommended commit plan" section names defer-to-downstream over Options A/B/C with rationale. Phase 2 accepts the deferral: file edits accumulate in the working tree (~30 modified files post-execution); no git operations run; the cleanup_execution_log substitutes for commit messages. The fresh-repo migration session handles baseline + cleanup commit pairing in proper context. This Path 3 case is production-validated: the original Phase 2 attempt under Option B engine baseline commit hit a permission denial on the engine's 207 MB / 883-file scope, which surfaced defer-to-downstream as the right answer rather than retrying the failed commit.

### Example 3 — Quick-scan triage, then deep-audit when slack permits

A maintainer runs `quick-scan` weekly as a pre-commit sanity check: Cat 1, 2, 6, 9 only, high-confidence floor, no leak check, no commit plan. The pass typically completes in minutes and surfaces 0-3 findings — usually a stale permission or a CLAUDE.md state value that drifted. Findings get marked blanket-style and executed without critic-gate. Once a quarter, the maintainer runs `deep-audit` with `cat_14_extension_pass: true`: all 14 categories, low-confidence floor, leak check on, critic-gate required. The deep-audit run typically surfaces 30+ findings including the long tail of speculative items the standard sweep suppresses; the extension pass surfaces dependency chains in Cat 14 (e.g., a state-query script that unlocks a snapshot-update hook). The maintainer batches REMEDIATE-bound findings into a separate session with `rootnode-cc-design`.

## When NOT to use

This Skill is the wrong tool when:
- The work is a single-Skill build → use `rootnode-skill-builder`.
- The work is prompt compilation or scaffolding → use `rootnode-prompt-compilation`.
- The work is single-prompt scoring or evaluation → use `rootnode-prompt-validation`.
- The work is a Claude Project audit → use `rootnode-project-audit`.
- The target is uncertain (could be CC, could be CP) → clarify before invoking.

The Skill is also wrong for non-rootnode CC environments where the canonical references (`root_AGENT_ENVIRONMENT_ARCHITECTURE.md`, `root_CC_ENVIRONMENT_GUIDE.md`, `root_AGENT_ANTI_PATTERNS.md`) are not the audit standard. The Skill bakes in those references as the canonical source of truth; deployments using a different anti-pattern catalog will get findings that don't match their model.

## Troubleshooting

**Phase 2 halts at EC-1 (no `[APPROVED]` markers found).** The user authorized verbally but didn't have the editor pathway invoked, or saved the marked file to a different path than the report. Re-invoke the Skill in editor mode with the user's verbal intent; produce the marked file; user saves; Phase 2 retries.

**Phase 2 halts at EC-4 (critic-gate not installed, threshold required).** Either install `rootnode-critic-gate` or downgrade the profile threshold to `optional`. Silently lowering the threshold to skip the gate is a discipline failure — the threshold was set to `required` for a reason (typically: profile is `deep-audit`, or mode-router conditions like sleeping/unattended map to strict).

**Phase 2 halts at EC-3 (engine baseline coherence drift).** The engine state shifted between Phase 1 and Phase 2 (test count changed, version bumped, branches diverged). Re-run Phase 1 to refresh the baseline; the report regenerates with current state and the user re-marks.

**Phase 2 halts at EC-5 (markers on recommendation-only findings).** The user marked Cat 11-14 or leak findings `[APPROVED]`. Phase 2 surfaces a notice naming the marked findings, names the REMEDIATE handoff, and proceeds with Cat 1-10 markers only. The marker is preserved in the report (it documents user intent) but does not flow into a Phase 2 execution batch.

**Critic-gate REQUEST_CHANGES exceeds 3 cycles on a batch.** The issue is structural; manual user intervention is the right escalation. The Skill halts with the unresolved critic finding surfaced. Three cycles is enough for the critic to surface and confirm a single class of issue but few enough that runaway loops can't develop.

**Verification step fails after batch execution.** The batch's assumptions were wrong. The Skill does not retry automatically. Investigate the verification output, address the cause (typically: a finding's recommended action did not produce the expected post-state), re-invoke Phase 2 with the remaining unmarked work.

**Commit plan execution hits permission denial (e.g., engine baseline commit on a large engine scope).** Accept defer-to-downstream as the right answer; the cleanup log already serves as audit trail. Re-running with Option B/C in the same context will hit the same denial.

**Cat 1 surfaces too many false positives on inherited content.** The active profile is missing the `bootstrap_heritage` block, or the block's `inherited_files` / `inherited_directories` are incomplete. Populate the block with the actual inheritance scope and re-run; the carve-out will eliminate the false-positive cluster.

**Cat 14 surfaces no candidates in a project with obvious recurring work.** The change_log discipline isn't being practiced (entries are too sparse to surface 3+ recurrence) or session_closeouts don't exist. The detection signals depend on documented work history; environments without those artifacts produce empty Cat 14 output. The fix is upstream — establish change_log + session_closeout discipline first.

## References

This SKILL.md carries the activation discipline and the principle layer. Detail content lives in `references/`:

- `references/sweep-categories.md` — 14 categories with detection rules, scan procedures, finding formats, confidence calibration, recommendation-only routing
- `references/anti-pattern-catalog.md` — Skill-relevant anti-pattern subset with audit-time application; CP-only patterns explicitly listed as not-scanned
- `references/seven-layer-framework.md` — 7-layer model, leak-check procedure, leak finding format, profile gating
- `references/execution-discipline.md` — Phase 2 mechanics: entry conditions, batch construction, per-batch execution, critic-gate composition, commit plan execution, cleanup_execution_log format
- `references/process-abstraction-detection.md` — Cat 14 deep dive: detection signals, candidate output structure, scope categorization, routing
- `references/cc-best-practices.md` — 12 convergence patterns this Skill audits against
- `references/worked-example.md` — End-to-end production-validated walkthrough

Schema and profiles:
- `schema/profile.schema.json` — Draft-07 profile validation
- `profiles/default.json`, `profiles/quick-scan.json`, `profiles/deep-audit.json`

## Quality gate

The Skill's Phase 1 output ALWAYS includes a marking ledger area at the bottom of the report file (even when empty). The Skill's Phase 2 output ALWAYS produces a cleanup_execution_log entry per batch and a closeout summary, even when batches halt. These artifacts are the durable audit trail; they are not optional.

When in doubt about whether to execute or recommend: recommend. The cost of a deferred execution is one re-invocation; the cost of an incorrect execution is variable and can include destructive change. Phase 2's halt-on-failure discipline reflects the same principle — the Skill stops cleanly rather than guessing at a recovery the user hasn't authorized.

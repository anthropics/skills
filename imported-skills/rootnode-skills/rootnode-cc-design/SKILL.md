---
name: rootnode-cc-design
description: >-
  Designs Claude Code prompts and CC environments. Produces CLAUDE.md drafts,
  agent topologies, scope-authorization frameworks, halt triggers,
  Skills/hooks/MCP plans, chat-to-CC handoff specs, and EXECUTION_PLAN.md
  remediation plans. Five modes: DESIGN (new CC deployments), EVOLVE (updates
  from friction), RESEARCH (evaluate a CC tool/pattern), TEMPLATE (reusable
  artifacts), REMEDIATE (consume hygiene findings → produce + execute plan).
  Use when user says "design CC for X", "build CC environment", "design
  CLAUDE.md", "build a CC prompt", "design a CC prompt for X", "write a
  session prompt", "we hit X friction in CC", "should we adopt Y for CC",
  "give me a CLAUDE.md skeleton", "remediate the hygiene findings". Do NOT
  use REMEDIATE for direct cleanup (Cat 1–10 — use rootnode-repo-hygiene
  Phase 2; REMEDIATE handles Cat 11–14 + 7-layer leaks). Do NOT use for
  hygiene scanning (use rootnode-repo-hygiene). Do NOT use for chat prompts
  (rootnode-prompt-validation) or chat Projects (rootnode-project-audit).
license: Apache-2.0
metadata:
  author: rootnode
  version: "2.1"
  predecessor: "rootnode-cc-design v2.0"
  original-source: "root.node seed Project KFs (post-Phase 27/28 methodology absorption: root_AGENT_ENVIRONMENT_ARCHITECTURE.md, root_CC_ENVIRONMENT_GUIDE.md, root_AGENT_ANTI_PATTERNS.md) + accumulated CC deployment research (2026-05-04). v2 evolved REMEDIATE acceptance flow (three approval forms, step-level risk tags) and critic-gate composition (required/optional) to align with rootnode-repo-hygiene v1's contracts. Substantive rebuild of cc-anti-patterns.md to canonical numbering. Brand-surface clean (cchq references stripped or restructured; hyge contamination anonymized to \"production CC deployment 2026-05-04\")."
  discipline_post: phase-30
---

# Claude Code Design

Design Claude Code prompts and environments for production delivery projects. This Skill produces paste-ready artifacts — CLAUDE.md drafts, agent topology recommendations, scope-authorization frameworks, halt-and-escalate triggers, Skills/Hooks/MCP plans, and chat-to-Code handoff specifications. The methodology is grounded in tested patterns from a production CC deployment 2026-05-04 (27/27 ship, 18-WI evolution arc), Anthropic primary documentation, and named practitioner consensus (rosmur, obra/superpowers, alexop.dev, Shrivu Shankar, Marc Nuri).

This Skill operates in both chat-based design conversations (CP) and Claude Code (CC). In CP, it focuses on DESIGN, EVOLVE, RESEARCH, and TEMPLATE modes — design conversations, brainstorming, scaffolding, cross-project synthesis. In CC, the same modes work alongside REMEDIATE — the closed-loop mode that consumes a `HYGIENE_REPORT.md` produced by `rootnode-repo-hygiene` and produces (then executes, after explicit user acceptance) an `EXECUTION_PLAN.md` against the actual repo.

The Skill produces design artifacts in all modes. REMEDIATE mode is the only mode that also executes — and only its Phase 2, gated by an explicit user acceptance step that follows Phase 1 plan generation.

## Important

**Source discipline is non-negotiable.** Every substantive claim about Claude Code behavior, MCP capability, or agent design pattern carries an inline source tag — `[Anthropic docs]`, `[<project> §X]`, `[practitioner: name + artifact]`, or `[speculation]`. Tier 5 community sources are signal-only, never authoritative. See `references/source-grading-and-tagging.md` for the full hierarchy.

**Generalizable vs. project-specific tagging.** Every pattern drawn from a production CC deployment or other working examples is tagged inline as `[generalizable]`, `[project-specific]`, or `[generalizable structure, project-specific content]` with a one-line basis for the tag. Default to "may be project-specific until proven otherwise." See `references/source-grading-and-tagging.md`.

**Tool/agent gap discipline.** Never recommend a tool, MCP server, agent role, Skill, or hook without identifying the specific operational gap it fills. "Adding X for completeness" is anti-pattern. The question is always: what concrete failure mode does this address, and is that failure mode actually present in the user's situation?

**The 7-layer placement rule comes first.** Before specifying CLAUDE.md content, place each piece of content in the correct mechanism (CLAUDE.md / rules / Skills / subagents / hooks / MCP / settings). Misplaced content is the single most common cause of agent unreliability. See `references/cc-environment-design-patterns.md`.

**Halt-and-escalate triggers are mandatory.** Every DESIGN MODE deployment plan and every EVOLVE MODE update specifies explicit halt-and-escalate triggers. Autonomous CC iteration without halt triggers is the failure mode that produces the worst outcomes.

**Output complete files.** Per the user's working preference: produce complete files (CLAUDE.md, agent specs, design briefs), never diffs or partial sections — except in EVOLVE MODE where the existing file is in context and a section-level delta is the deliverable.

---

## How to Use This Skill

### Step 1 — Determine the mode

Five modes. Mode is inferred from the request signal; confirm in one line at the start of the response, then proceed. Some modes have natural surfaces (CP vs CC) but all 5 work in both — surface emphasis is a tendency, not a constraint.

| Mode | Trigger signals | Output | Natural surface |
|---|---|---|---|
| **DESIGN** | "design CC for X", "build CC environment for Y", "scaffold a Claude Code repo", new project scaffolding | Complete deployment plan: CLAUDE.md draft + initial prompt + agent topology + scope rules + halt triggers + handoff point + runtime tooling recommendations | CP for greenfield (no repo yet); CC for in-repo new work (new module, new service inside existing repo) |
| **EVOLVE** | "we hit X friction in [project]", "the agent keeps doing Y", "this pattern emerged across sessions", "we need to add Z to existing CLAUDE.md" | Section-level deltas to existing artifacts: CLAUDE.md updates as inserts/replacements, new agent specs, new scope rules, change-log entry template, regression-sweep specification | Both — speculative friction in CP; in-repo friction in CC where the deltas can be applied directly |
| **RESEARCH** | "should we adopt X", "is Y worth using", "what's the landscape for Z", "what tool fills the gap of W" | Structured assessment: gap definition, candidates with source class, fit analysis, decisive recommendation, speculative notes | CP-leaning (web search heavy; polluting a delivery repo's CC session is anti-pattern) |
| **TEMPLATE** | "give me a CLAUDE.md skeleton for X-class projects", "build a reusable prompt template", "produce an agent role template I can reuse" | Complete template with placeholders in `{BRACKETED_CAPS}` + usage notes + filing recommendation | CP-leaning (cross-project synthesis is wrong context inside one delivery's CC) |
| **REMEDIATE** | "remediate the hygiene findings", "fix the audit issues", "close the loop on the report", `HYGIENE_REPORT.md` exists in repo and user invokes this Skill without naming a different mode | **Phase 1:** `EXECUTION_PLAN.md` written to repo (steps + validation per step + summary + addressed-findings list). User reviews and explicitly accepts via one of three approval forms (blanket / fragmented / conditional). **Phase 2:** Skill executes the accepted plan step-by-step, validates each step, halts on failure | CC-native (must read `HYGIENE_REPORT.md` from repo; Phase 2 writes to repo). CP-only invocation requires pasted findings and produces plan without executing |

### Step 2 — Check for or generate the design brief

The Skill operates from a structured **design brief** for the delivery project. The brief captures: mission, current state, tech surface, governance state, runtime tooling state, authority constraints, verification surface, and known friction. It lives at `{project_code}_design_brief.md` in the delivery project's KFs (or filesystem if working at the repo level).

**On first invocation in a new project:** conduct the 5-question interview (mission / current state / tech surface / authority constraints / verification surface), serialize to brief format, offer as a downloadable artifact, and recommend adding to the delivery project's KFs. See `references/cc-methodology-patterns.md` §"The design brief workflow" for the full interview script and brief format.

**On subsequent invocations:** read the existing brief as input. If the brief is stale (front-matter `last_updated` > 90 days, or current state field is wrong), surface this and offer to refresh.

**If brief generation is over-investment for the request:** small focused asks (one CLAUDE.md section, one prompt rewrite, one agent spec review) can proceed without a brief. Use judgment — the brief exists to ground multi-faceted design work, not to bottleneck simple tasks.

### Step 3 — Apply mode-specific reasoning

Read the relevant references before producing output. Each mode draws from a specific subset:

- **DESIGN MODE** consults: cc-methodology-patterns, cc-environment-design-patterns, cc-skills-and-hooks-composition, chat-to-code-handoff-patterns. Optional: cc-prompt-design-patterns (if the deliverable includes a CC initial prompt or session prompt).
- **EVOLVE MODE** consults: cc-anti-patterns (diagnose the friction), cc-methodology-patterns (find the relevant pattern), cc-environment-design-patterns or cc-skills-and-hooks-composition (apply the fix at the correct layer).
- **RESEARCH MODE** consults: source-grading-and-tagging (apply the source authority hierarchy), cc-anti-patterns (verify the candidate doesn't introduce known anti-patterns).
- **TEMPLATE MODE** consults: cc-methodology-patterns (the structural pattern being templated) and the relevant CC pattern reference for the artifact class.
- **REMEDIATE MODE** consults: remediate-mode-execution (the full Phase 1 + Phase 2 protocol, three approval forms, plan format, validation grammar, conflict-resolution rules), cc-anti-patterns (the per-pattern fix recipes — when consuming a finding tagged with a canonical reference like `§4.2`, look up the structural fix here), cc-environment-design-patterns (the 7-layer placement framework — used to validate that proposed fixes land in the correct mechanism). Schema: `schema/execution-plan.schema.json` defines the EXECUTION_PLAN.md structure.

### Step 4 — Apply output standards

- **File naming.** CLAUDE.md drafts for delivery projects use `{delivery_project_code}_CLAUDE.md` (the destination project's prefix). Agent role specs use `{delivery_project_code}_agent_{name}.md`. Design briefs use `{project_code}_design_brief.md` and live in the delivery project's KFs. Templates produced for cross-project reuse use `{project_code}_template_{descriptor}.md` or `shared_template_{descriptor}.md`.
- **Markdown for CLAUDE.md drafts.** CLAUDE.md is consumed by Claude Code, which expects Markdown. Use `##` and `###` headers, fenced code blocks, tables for matrices. Do not use XML tags inside CLAUDE.md drafts — those are for system prompts, which CLAUDE.md is not.
- **Halt triggers and scope authorization.** Every DESIGN MODE plan and every EVOLVE MODE update explicitly includes both. Non-negotiable.
- **Token budgets.** When the deployment plan involves sub-agents or context management, include explicit token budgets that sum to the model's context window. A context plan without numbers is not a context plan.
- **Source-tagged claims.** Every substantive technical claim carries an inline source tag.
- **CC-prompt-specific output discipline.** When the deliverable is a CC initial prompt, session prompt, or autonomous prompt, see `references/cc-prompt-design-patterns.md` § Output discipline for CC prompts for additional output standards (shell-agnostic syntax, pre-flight Skill enumeration, continuation-phrase ambiguity gate, forward-state-aware authoring).

### Step 5 — Surface the chat→Code handoff explicitly

Every DESIGN MODE output identifies the chat→Code handoff point: at what milestone does design work end and Claude Code execution begin? Build the round-trip into the design — also specify what conditions trigger a return to chat (pattern emerges across 2+ sessions, new tool enters consideration, friction with existing CLAUDE.md surfaces, reusable artifact extraction needed).

See `references/chat-to-code-handoff-patterns.md` for the readiness signals, artifact bundle composition, and round-trip pattern.

### Step 6 — Recommend runtime tooling only if it fills a specific gap

The rootnode runtime Skills (handoff-trigger-check, critic-gate, mode-router, profile-builder) are external tooling. When a deployment plan involves autonomous Claude Code execution, evaluate whether one or more of these Skills fills a specific operational gap. If yes, recommend with one-line rationale per Skill and note the deployment target (CP-side runs in the design Project itself; CC-side deploys into the delivery project). If no, do not mention them — the Skill's methodology stays decoupled from any specific tooling.

---

## Reference Files

Read the relevant files based on the mode (Step 3 above). Each file is standalone-readable; load only what the current task needs.

| File | When to read |
|---|---|
| `references/cc-methodology-patterns.md` | Always for DESIGN, EVOLVE, TEMPLATE modes. Contains the project-agnostic distillation of the methodology — authority matrix pattern, scope-authorization framework, change_log discipline, additive evolution, agent-warranted test, design brief workflow. |
| `references/cc-prompt-design-patterns.md` | When the deliverable includes a CC initial prompt, session prompt, autonomous prompt, or subagent delegation prompt. Patterns organized by use case. |
| `references/cc-environment-design-patterns.md` | Always for DESIGN mode. Reference for EVOLVE and REMEDIATE when placement decisions are involved. Contains the 7-layer decomposition framework — what content goes in CLAUDE.md vs `.claude/rules/` vs Skills vs subagents vs hooks vs MCP vs settings — with selection criteria for each layer. |
| `references/cc-skills-and-hooks-composition.md` | When the deployment plan involves Skills, hooks, or both. Skills frontmatter reference, auto-activation patterns, hooks-vs-skills decision tree, the verification "iron law" pattern. |
| `references/cc-anti-patterns.md` | Always for REMEDIATE mode (per-pattern fix recipes). Reference for EVOLVE when diagnosing friction. Reference for DESIGN as a "things to avoid creating" checklist. The 15-pattern catalog using canonical numbering from `root_AGENT_ANTI_PATTERNS.md`, with structural signature, cause, and fix per pattern. **Note:** anti-pattern scanning is rootnode-repo-hygiene's territory; this Skill consumes the catalog as a fix-recipe library, not as an audit checklist. |
| `references/chat-to-code-handoff-patterns.md` | Always for DESIGN mode. When designing how chat work transitions to CC execution. Handoff readiness signals, artifact bundle composition, the round-trip pattern. |
| `references/source-grading-and-tagging.md` | Always for RESEARCH mode. Reference whenever a claim needs source backing. The 5-tier source authority hierarchy and the generalizable-vs-project-specific tagging discipline. |
| `references/remediate-mode-execution.md` | Always for REMEDIATE mode. Full protocol for Phase 1 (plan generation) + Phase 2 (execution): three approval forms (blanket / fragmented / conditional), critic-gate composition (`required` / `optional`), action types, validation grammar, conflict-resolution rules, halt semantics, HYGIENE_REPORT.md input format expectations, EXECUTION_PLAN.md output format. |
| `references/troubleshooting.md` | When the Skill output isn't landing or the user signals a specific problem with how the Skill is being invoked or what it produced. |

The brief schema lives at `schema/cc-design-brief.schema.json`. The execution-plan schema lives at `schema/execution-plan.schema.json`.

---

## Examples

### Example 1: DESIGN MODE — new CC deployment for a delivery project

**Input:** "I'm starting a Claude Code project for a Python CLI tool that ingests CSV files and produces a normalized SQLite DB. Help me design CLAUDE.md and the initial agent topology."

**Actions:**
1. Confirm mode: "DESIGN MODE — building a new Claude Code deployment plan."
2. Check for a design brief; none exists for this project. Conduct the 5-question interview (mission, current state, tech surface, authority constraints, verification surface).
3. Serialize the brief and offer it as a downloadable artifact. Recommend adding to the project's KFs.
4. Apply the 7-layer placement rule (cc-environment-design-patterns) — for a single-script CLI, most concerns collapse to CLAUDE.md + 1-2 hooks; no Skills or subagents warranted yet.
5. Apply the agent-warranted test (cc-methodology-patterns §2) — single-loop iteration; recommend single-agent loop, no sub-agents.
6. Draft the CLAUDE.md with the 5 required sections (R1-R5) and skip W1-W3 (warrant tests fail at day 1).
7. Specify scope authorization (in-scope / in-scope-with-notification / out-of-scope) and halt-and-escalate triggers.
8. Identify the chat→Code handoff point: "Once CLAUDE.md is in place, hand off to CC for the first iteration."
9. Evaluate runtime tooling — handoff-gate is overkill for a single-script project; recommend deferring.

**Output:** Design brief artifact + CLAUDE.md draft (Markdown, paste-ready, < 200 lines) + initial CC prompt + scope authorization clauses + halt triggers + handoff point + a "what to revisit when the project grows" note.

### Example 2: EVOLVE MODE — friction in an existing CC project

**Input:** "In the RT project, the agent keeps re-reading the same files and forgetting what it learned in the previous session. It's also editing files in the migrations directory that it shouldn't touch."

**Actions:**
1. Confirm mode: "EVOLVE MODE — incremental update to the RT CC project."
2. Read the existing RT design brief (or ask if not in context).
3. Diagnose: two distinct frictions. (a) Cross-session memory — likely missing CLAUDE.md notes about durable file artifacts (cc-anti-patterns §4.1 transcript dump if there's also no change_log; or §4.14 stale CLAUDE.md if the relevant info exists but is wrong). (b) Migrations directory edit — §4.4 enforcement-as-preference (rule was probably in CLAUDE.md as advice, not backed by a hook).
4. Design fixes — additive, narrow detection per cc-methodology §4. (a) Add a change_log discipline section to CLAUDE.md + introduce a session-handoff Skill or rule pattern. (b) Add a PreToolUse hook blocking writes to `migrations/**` — prompt-level rule moves to enforcement layer.
5. Specify regression sweep: re-run the 3 most recent deployment scenarios after the changes; verify no false-positive blocks from the hook.

**Output:** Section-level deltas to RT_CLAUDE.md (insert + replacement) + new hook config in `.claude/settings.json` (paste-ready) + change-log entry template + regression-sweep specification.

### Example 3: REMEDIATE MODE — closing the loop on hygiene findings

**Input:** User invokes the Skill in CC. `HYGIENE_REPORT.md` exists in the repo, produced by `rootnode-repo-hygiene` in a prior session. User says: "remediate the hygiene findings."

**Actions (Phase 1 — plan generation):**
1. Confirm mode: "REMEDIATE MODE — Phase 1 (plan generation). I'll read HYGIENE_REPORT.md and produce EXECUTION_PLAN.md for your review."
2. Read `HYGIENE_REPORT.md` from repo root. Parse findings. Filter to in-scope: Cat 11–14 structural findings + 7-layer leak findings. Cat 1–10 direct-cleanup findings are out of scope for REMEDIATE — those route to repo-hygiene Phase 2; surface this routing in the response and skip them.
3. For each in-scope finding, look up the structural fix in `cc-anti-patterns.md` (e.g., a finding tagged `§2.1` bloated CLAUDE.md → trim to <200 lines + extract procedures to Skills + extract path-rules to `.claude/rules/`).
4. Group findings by file affected; resolve conflicts where two findings touch the same file (e.g., both `§2.1` and `§4.14` touch CLAUDE.md — sequence: trim first, then date-stamp).
5. Validate proposed fixes against the 7-layer placement framework (`cc-environment-design-patterns.md` §1) — does each fix land in the correct mechanism?
6. Build `EXECUTION_PLAN.md` per the schema (`schema/execution-plan.schema.json`): plan metadata, addressed-findings list (using `addresses_finding: F-X.Y` references), ordered steps with action/target/payload/risk/validation per step, pre-flight + post-flight validation.
7. Write `EXECUTION_PLAN.md` to repo root.
8. Surface plan summary: "Plan addresses 7 findings, modifies 4 files, creates 2 new files, adds 1 hook. Review EXECUTION_PLAN.md and respond with one of three approval forms — blanket ('execute'), fragmented ('execute steps 1, 2, 4'), or conditional ('execute medium-and-low risk; halt on high-risk') — to proceed to Phase 2, or describe changes you want."
9. Halt and wait for explicit user acceptance. **No execution in Phase 1.**

**Actions (Phase 2 — execution, only after explicit user acceptance):**
1. Confirm mode: "REMEDIATE MODE — Phase 2 (execution). Walking the plan step-by-step."
2. Run pre-flight validation. Halt if any fails.
3. For each step in plan order (filtered by user's acceptance form — blanket walks all; fragmented walks named step IDs; conditional walks steps matching the risk predicate):
   a. (If `critic_gate_threshold: required` and `rootnode-critic-gate` installed) Submit step plan to critic-gate; APPROVE → continue; REQUEST_CHANGES → adjust + re-submit, cap 3 cycles; REJECT → halt.
   b. Apply the action (edit / create / delete / modify / run).
   c. Run the step's validation.
   d. If validation fails, halt and report the failure with current state. Do not auto-rollback.
   e. If validation passes, log step completion and continue.
4. Run post-flight validation.
5. Append a CHANGELOG entry summarizing the remediation cycle.
6. Report: steps approved / total, steps executed / approved, steps skipped (with reason), critic-gate review summary (if applicable), files modified, findings closed, any halts.

**Output:** Phase 1 produces `EXECUTION_PLAN.md`. Phase 2 produces actual repo changes + CHANGELOG entry + execution report. Both phases are gated by explicit user acceptance between them.

---

## When to Use This Skill

Use this Skill when:
- The user is planning a new Claude Code deployment for a delivery project (DESIGN mode)
- An existing Claude Code project has surfaced friction or needs a new pattern added (EVOLVE mode)
- The user is evaluating a tool, MCP server, Skill, hook, or pattern for inclusion in a CC deployment (RESEARCH mode)
- The user wants a reusable artifact for cross-project use — CLAUDE.md skeleton, agent role template, scope-authorization clause template (TEMPLATE mode)
- The user has finished designing a deliverable in chat and is preparing the chat→Code handoff bundle
- A `HYGIENE_REPORT.md` exists in the repo and the user wants to close the loop on it (REMEDIATE mode)

### REMEDIATE routing

REMEDIATE handles the structural and placement-decision portions of a hygiene report. Direct-cleanup findings have a different route. Use this routing rule when a HYGIENE_REPORT.md is in play:

| Finding type | Owner | Action |
|---|---|---|
| Cat 1–10 (permissions, hooks, parent-vestige, stale code, Skills hygiene, etc.) | `rootnode-repo-hygiene` Phase 2 | Direct cleanup. Run repo-hygiene Phase 2 against the `[APPROVED]` markers in the report. **Not** REMEDIATE territory. |
| Cat 11–14 (structural, including process-abstraction candidates) | `rootnode-cc-design` REMEDIATE | Structural fix recipes from `cc-anti-patterns.md`; conflict resolution; 7-layer placement validation. |
| 7-layer leak findings | `rootnode-cc-design` REMEDIATE | Placement-decision required; route to REMEDIATE for layer reassignment. |

Phase 1 surfaces this routing explicitly: when REMEDIATE is invoked on a report containing Cat 1–10 findings, the response names them as out-of-scope and recommends the repo-hygiene Phase 2 path before walking the in-scope findings.

Do NOT use this Skill when:
- The user wants to scan or audit an existing CC environment for hygiene issues / anti-patterns (use rootnode-repo-hygiene if available — that Skill produces the HYGIENE_REPORT.md this Skill consumes)
- The user wants to evaluate or score a chat prompt (use rootnode-prompt-validation if available)
- The user wants to compile a chat prompt or scaffold a chat Project (use rootnode-prompt-compilation if available)
- The user wants to audit a chat-based Claude Project's Custom Instructions or knowledge files (use rootnode-project-audit if available — different surface from CC)
- The user is doing non-CC delivery work that doesn't involve Claude Code at all

---

## Troubleshooting

**Skill produces generic CLAUDE.md not tailored to the project:** The design brief was missing or thin. Generate the brief first via the 5-question interview before producing the deployment plan. The brief is the grounding artifact — without it, output drifts toward generic patterns.

**Skill recommends rootnode runtime tooling for a project that doesn't need it:** The tool/agent gap discipline was skipped. For each runtime Skill, name the specific operational gap it fills in this project. If you can't, don't recommend it. See SKILL.md Step 6.

**Skill outputs are too long / context-heavy:** TEMPLATE mode is a useful pressure release — extract the reusable structural pattern into a `{project_code}_template_*` or `shared_template_*` artifact and reference it from delivery-project briefs. Avoid re-deriving the same pattern across multiple project deployments.

**Skill produces "vibe" recommendations without source backing:** Source discipline was skipped. Every substantive claim about CC behavior, MCP capability, or pattern needs an inline source tag. See `references/source-grading-and-tagging.md`. If a tag is `[speculation]`, that's acceptable as long as it's marked.

**User asks for a quick answer and the brief workflow feels heavy:** Skip the brief for narrow asks (one section, one prompt, one review). The brief grounds multi-faceted design work, not single-shot questions. Use judgment.

**User asks the Skill to "audit my CC project" — the Skill claims this is rootnode-repo-hygiene's territory but the user disagrees:** Different verbs. rootnode-repo-hygiene scans for hygiene issues against the 15-anti-pattern catalog and produces findings. This Skill *consumes* those findings (REMEDIATE mode) or designs new artifacts from scratch (DESIGN/EVOLVE/TEMPLATE). If the user wants a "review" of a draft CLAUDE.md *during design work* (not against a deployed environment), that fits EVOLVE mode framed as "review and propose deltas." If the user wants the deployed-environment scan, route to rootnode-repo-hygiene.

**REMEDIATE mode invoked but no HYGIENE_REPORT.md exists in the repo:** The Skill cannot proceed. Two options: (a) ask the user to run rootnode-repo-hygiene first to produce the report, then re-invoke REMEDIATE; (b) accept findings pasted directly into the conversation, but recommend the file-based workflow for repeatability. Plan generation without source findings is anti-pattern — the loop only closes when there's a defined input to remediate against.

**REMEDIATE Phase 2 step validation fails:** Halt. Do not auto-rollback. Report which step failed, which validation, and the current repo state (what was completed before the halt). The user decides whether to manually revert, fix forward, or re-plan. Safety-via-halt is the v2 discipline; rollback semantics are out of scope.

**Two REMEDIATE conflict resolutions seem reasonable for the same finding cluster:** Phase 1 still produces a plan, but the conflicting steps are marked `requires_user_choice: true` and Phase 2 will halt at those steps for explicit choice. Don't silently choose one — the conflict surfaced because the proper sequencing isn't unambiguous, and that's a user decision, not a Skill decision.

**EVOLVE mode keeps re-deriving the same fix:** This is a signal the fix should be promoted to a TEMPLATE. After the second invocation of the same pattern, extract it as a template and reference from future EVOLVE outputs.

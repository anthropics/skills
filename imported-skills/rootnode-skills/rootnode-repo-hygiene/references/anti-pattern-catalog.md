# Anti-Pattern Catalog (Skill-relevant subset)

The CC-side and surface-invariant anti-patterns this Skill scans for, with audit-time application: signature, structural cause, fix, canonical reference, and example findings shape.

**Canonical source:** `root_AGENT_ANTI_PATTERNS.md` (the unified anti-pattern catalog with surface tags). This file applies the canonical content to Skill-time scanning. It does not duplicate the canonical; it applies the principles to detection and routing inside the sweep.

**Surface scope.** This Skill operates CC-side only. The catalog below covers `[CC]` patterns and the `[both]` cross-surface patterns where they manifest in CC environments. CP-only patterns are listed at the end under "Patterns explicitly NOT scanned" with reasoning.

**Routing convention.** Each pattern entry lists the sweep category that lights it up. Categories 1–10 are executable in Phase 2. Categories 11–14 are recommendation-only and route to `rootnode-cc-design` REMEDIATE mode.

---

## Cross-surface patterns (manifest in CC)

### §2.1 — Monolithic standing context

**Signature.** A single document carrying everything: identity, rules, reference data, examples, history. In CC: CLAUDE.md exceeds 200 lines and mixes authority-matrix content with file-pattern conventions and step-by-step procedures.

**Structural cause.** Layer hierarchy violation — content that belongs in `.claude/rules/` (file-pattern-specific), Skills (multi-step procedures), or hooks (lifecycle guarantees) gets accreted into the always-loaded layer.

**Fix.** Extract by mechanism. File-pattern guidance → `.claude/rules/<scope>.md` with `paths:` frontmatter. Multi-step procedures → Skills. Lifecycle guarantees → hooks. Refactor CLAUDE.md down to mission, authority matrix, scope authorization, halt-and-escalate triggers, pre-flight checklist (R1–R5).

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §2.1`. CLAUDE.md length discipline: `root_CC_ENVIRONMENT_GUIDE.md §1.1`.

**Sweep category.** Cat 9 (line count + mixed reference material sub-signals).

**Example finding shape:** F-9.x flagging line count over 200, mixed reference material blocks identified by line range with extraction targets named.

---

### §4.1 — Transcript dump

**Signature.** Files in the repo that look like dumps of chat conversations — long unstructured prose, "the user said... Claude said..." framing, decisions buried in dialogue rather than declared explicitly. Often filed as `HANDOFF.md`, `notes.md`, or pasted into CLAUDE.md.

**Structural cause.** The chat→file boundary was never properly crossed. The transcript was treated as a context file rather than as material to be distilled into structured content.

**Fix.** Distill the transcript into the canonical chat→Code handoff brief format documented in `root_CC_ENVIRONMENT_GUIDE.md §10`. The brief carries decisions with rationale, not dialogue.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.1`. Chat→Code round-trip: `root_CC_ENVIRONMENT_GUIDE.md §10`.

**Sweep category.** Cat 9 (mixed reference material sub-signal in CLAUDE.md), Cat 12 (CC environment configuration drift when transcripts file as standing references).

**Example finding shape:** F-9.x or F-12.x flagging the file path, line range of dialogue-shaped content, recommended extraction to a structured handoff brief.

---

## CC-only patterns

### §4.2 — MCP bloat

**Signature.** Five or more MCP servers configured. Or MCP tool schemas dominating the standing context budget. Or MCP servers configured but used in fewer than 5% of sessions.

**Structural cause.** MCPs added speculatively for "might need it later" rather than from a confirmed external-data integration need. Each MCP server pays a context cost (tool schema declarations) that compounds across servers.

**Fix.** Remove unused MCPs. Consolidate where one MCP can replace multiple narrow ones. Apply the ~20K token threshold from `root_CC_ENVIRONMENT_GUIDE.md §1.6`: total tool schema cost across all configured MCPs should stay under that ceiling.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.2`. MCP minimalism: `root_CC_ENVIRONMENT_GUIDE.md §1.6`.

**Sweep category.** Cat 12 (recommendation-only).

**Example finding shape:** F-12.x with measured tool schema token estimate, list of low-usage MCPs, recommended removals.

---

### §4.3 — Manual-only Skills

**Signature.** Skills with `disable-model-invocation: true` set without `metadata.notes` justification. Or Skills with descriptions so weak Claude can't activate them automatically (descriptors only, no verb-based triggers).

**Structural cause.** The Skill was authored as if it were a slash-command (always invoked manually) rather than as a Skill (auto-activated by description match). The activation discipline was skipped.

**Fix.** Rewrite the description with verb-based triggers ("use when X," "trigger on Y") and explicit + symptom-phrased trigger phrases. If `disable-model-invocation: true` is genuinely warranted, document the reasoning in `metadata.notes`.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.3`. Auto-activation discipline: `root_CC_ENVIRONMENT_GUIDE.md §1.3`.

**Sweep category.** Cat 10 (Skills directory hygiene).

**Example finding shape:** F-10.x naming the Skill, the spec violation (weak description or unjustified manual-only flag), and a rewrite recommendation.

---

### §4.4 — Enforcement-as-preference

**Signature.** Critical lifecycle guarantees expressed in CLAUDE.md as "remember to..." or "always do X" instructions, when they should be hooks. Examples: "remember to run tests after editing," "always update change_log on session close."

**Structural cause.** The author treated CLAUDE.md as a rule-enforcement layer when it's a context layer. CLAUDE.md text is preference; only hooks enforce.

**Fix.** For each enforcement-as-preference instruction, evaluate whether the guarantee absolutely cannot be missed. If yes: extract to a hook (PreToolUse, PostToolUse, or Stop depending on the trigger point). If no: leave as preference but acknowledge the soft enforcement explicitly in CLAUDE.md.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.4`. Hooks-vs-prompts boundary: `root_CC_ENVIRONMENT_GUIDE.md §6`.

**Sweep category.** Cat 9 (CLAUDE.md bloat, conversational framing sub-signal) and Cat 7 (hook misconfiguration, when extraction is warranted).

**Example finding shape:** F-9.x flagging the instruction line, OR F-7.x recommending hook extraction with the trigger point named.

---

### §4.5 — Subagent overuse

**Signature.** Ten or more subagent definitions in `.claude/agents/` with most being rarely or never invoked. Or subagents whose scope overlaps substantially with the main conversation's natural capability.

**Structural cause.** Subagents authored as a multiplier ("more agents = more capability") rather than as a context-isolation primitive ("subagents preserve main context when a subtask has high token cost").

**Fix.** For each subagent, check 90-day invocation count. Retire unused ones. For overlapping subagents, consolidate or fold back into main conversation prompts.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.5`. Subagent topology: `root_CC_ENVIRONMENT_GUIDE.md §1.4 + §3`.

**Sweep category.** Cat 8 (subagent definition drift, unused sub-signal).

**Example finding shape:** F-8.x naming the subagent, invocation count, retirement or consolidation recommendation.

---

### §4.6 — Subagent underuse

**Signature.** Main conversation context bloated with content that should have been delegated to a subagent (large file analysis pulled into main, repeated multi-step procedures running inline). Zero or one subagent definitions in a project where the work pattern would benefit from isolation.

**Structural cause.** Subagent capability was either unknown to the author or was treated as too much overhead. Main context absorbs work that should have been isolated.

**Fix.** Identify recurring high-token-cost subtasks (file analysis, code review, test debugging) and design subagents for them. Each subagent gets a focused scope, isolated context, and clear handoff format back to main.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.6`. Subagent topology: `root_CC_ENVIRONMENT_GUIDE.md §1.4 + §3`.

**Sweep category.** Cat 8 (subagent definition drift, absent-but-warranted sub-signal).

**Example finding shape:** F-8.x naming the recurring inline pattern, recommended subagent scope, expected token savings.

---

### §4.7 — bypassPermissions outside sandbox

**Signature.** `bypassPermissions: true` in user-workspace or project-root settings. `--dangerously-skip-permissions` in non-sandboxed scripts.

**Structural cause.** Permission friction was treated as a problem to bypass rather than as a graduated trust spectrum to navigate (managed → CLI → local → project → user, per `root_CC_ENVIRONMENT_GUIDE.md §1.7`).

**Fix.** Remove the bypass. Replace with explicit permission grants for the specific operations that produced the friction. If bypass is genuinely needed, scope it to a sandboxed context (containerized, ephemeral).

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.7`. Permission modes: `root_CC_ENVIRONMENT_GUIDE.md §1.7`.

**Sweep category.** Cat 6.

**Example finding shape:** F-6.x with file path, quoted line, sandbox-context evaluation, recommended action.

---

### §4.8 — Missing managed policy where required

**Signature.** Compliance, security, or organizational policy expectations exist (referenced in CLAUDE.md, README, or onboarding docs) but no managed-settings layer enforces them. Or managed settings exist but don't cover the declared expectations.

**Structural cause.** Authority hierarchy gap — policy is declared at the documentation level but never landed in the enforcement layer. Whatever is in user/project settings can override the declared expectation.

**Fix.** For each declared policy expectation, decide whether enforcement is required. If yes, lift to managed settings. If no, downgrade the declared expectation to a recommendation.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.8`. Settings hierarchy: `root_CC_ENVIRONMENT_GUIDE.md §1.7`.

**Sweep category.** Cat 2 (missing-entry sub-direction of permissions scan).

**Example finding shape:** F-2.x with the declared expectation (quoted from where it appears), the gap (managed settings absent or incomplete), recommended permission/policy entry.

---

### §4.9 — Path-scoped rules opportunity missed

**Signature.** Content in CLAUDE.md that applies only to specific file types or directories ("when editing Python files, ..." / "in the `tests/` directory, ..."). The conditional makes the content not always-relevant — so it shouldn't be in always-loaded standing context.

**Structural cause.** `.claude/rules/` with `paths:` frontmatter is the right mechanism, but the author defaulted to CLAUDE.md.

**Fix.** Extract conditional content to `.claude/rules/<scope>.md` with the appropriate `paths:` frontmatter. CLAUDE.md retains the always-relevant material only.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.9`. Path-scoped rules: `root_CC_ENVIRONMENT_GUIDE.md §1.2`.

**Sweep category.** Cat 9 (mixed reference material sub-signal); often surfaces alongside Cat 11 (file/folder architectural drift) when the extracted rules need a new location.

**Example finding shape:** F-9.x with the conditional content quoted, line range, recommended `.claude/rules/` filename, and `paths:` frontmatter draft.

---

### §4.10 — Auto memory misuse

**Signature.** CC-side `auto memory` features used to accrete content into the always-loaded layer without curation. Memory entries that have grown into ad-hoc extensions of CLAUDE.md.

**Structural cause.** The author treated memory as free storage rather than as curated standing context. Auto-accumulation produces stale, noisy, or duplicative content.

**Fix.** Review memory entries on a recurring cadence. Promote durable entries to CLAUDE.md or extract to Skills. Delete stale entries. Document the curation cadence in CLAUDE.md.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.10`.

**Sweep category.** Cat 9 (CLAUDE.md bloat scope when memory bleeds into the always-loaded layer).

**Example finding shape:** F-9.x flagging the auto-memory accretion pattern with recommendation to introduce a curation cadence.

---

### §4.11 — Verification-before-completion absent

**Signature.** Completion claims in change_log entries or session_closeouts without test/lint/type-check evidence cited. No Stop hook running the test command. Test infrastructure exists but is never automatically exercised.

**Structural cause.** The verification-before-completion iron law (per `root_CC_ENVIRONMENT_GUIDE.md §5.2`) was treated as preference rather than as guarantee. Without a Stop hook, the discipline only holds when the agent remembers — which it doesn't, reliably.

**Fix.** Add a Stop hook that runs the test command. Update change_log discipline to require test-result citation in completion entries.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.11`. Iron law: `root_CC_ENVIRONMENT_GUIDE.md §5.2`.

**Sweep category.** Cat 13 (recommendation-only, missing verification infrastructure) AND Cat 7 (executable, when test infrastructure exists and the Stop hook can be added directly).

**Example finding shape:** F-13.x flagging absence; F-7.x recommending Stop hook addition with the test command identified.

---

### §4.12 — Skills/Commands legacy mix

**Signature.** New procedural work being added to `.claude/commands/` rather than `.claude/skills/`. Or both directories present with overlapping coverage and unclear routing rules.

**Structural cause.** Authoring inertia — the author was working in commands before Skills shipped and continued the pattern. Commands are still supported but Skills are the forward-looking mechanism per `root_CC_ENVIRONMENT_GUIDE.md §1.3`.

**Fix.** Migrate commands to Skills where the work is procedural and Claude-facing. Retain commands only for short user-facing slash invocations.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.12`. Skills > Commands: `root_CC_ENVIRONMENT_GUIDE.md §1.3`.

**Sweep category.** Cat 10 (Skills directory hygiene; specifically the migration-needed sub-signal).

**Example finding shape:** F-10.x listing commands that should migrate to Skills, with rationale per command.

---

### §4.13 — Kitchen-sink session (operational)

**Signature.** A single CC session attempting to do everything — design, implementation, testing, deployment, retrospective — without phase boundaries. Change_log entries that mix concerns across categories.

**Structural cause.** Session discipline absent. Without an explicit phase model, work accretes into one continuous stream and verification opportunities get skipped.

**Fix.** Define phase boundaries (Plan → Implement → Verify → Closeout). Each phase has entry conditions, exit conditions, and a verification step. The Stop hook can enforce verification at session boundary.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.13`.

**Sweep category.** Cat 12 (recommendation-only — the structural fix is environment redesign, not a single edit).

**Example finding shape:** F-12.x quoting representative change_log mix, recommended phase model, recommended verification injection points.

---

### §4.14 — Stale CLAUDE.md / Stale content

**Signature.** CLAUDE.md state sections (engine state snapshot, test counts, version numbers) that don't match current repo state. Reference files in `.claude/rules/` or Skills citing outdated paths or commands. README content describing an architecture that no longer matches the directory structure.

**Structural cause.** State drift over time without a refresh discipline. The "Engine state snapshot" pattern only works when something refreshes it.

**Fix.** Two paths:
- **Manual refresh:** define a "before each release" or "weekly" cadence for refreshing state-sensitive sections.
- **Automated refresh:** introduce a script (or hook) that regenerates state-sensitive sections from canonical sources. Often a Cat 14 process-abstraction candidate.

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.14`.

**Sweep category.** Cat 9 (stale-state sub-signal of CLAUDE.md bloat). At validation, this was the most-cited pattern (8 findings).

**Example finding shape:** F-9.x with the stale section quoted, current actual state value, recommended refresh mechanism.

---

## Patterns explicitly NOT scanned (CP-only)

These patterns from `root_AGENT_ANTI_PATTERNS.md §3` apply to chat-side Claude Projects and do not manifest in CC environments. The Skill does not scan for them. Listed here so future maintainers don't re-introduce false-positive scans.

- **§3.1 — Phantom Conversation.** CP-only. The pattern is an artifact of standing system prompts that imply a conversational state. CC has no equivalent surface.
- **§3.2 — Echo Chamber.** CP-only. Result of overlapping knowledge files in a Project. CC's mechanism layering doesn't produce the same overlap.
- **§3.3 — Orphan File.** CP-only. A knowledge file referenced by no instruction. CC's mechanism layering routes content by mechanism, not by instruction-reference.
- **§3.4 — Kitchen Sink (structural).** CP-only structural pattern (a Project with too many overlapping concerns). The CC operational analog is `§4.13` and is scanned.
- **§3.5 — Blurred Layers.** CP-only. Custom Instructions mixed with knowledge file content. CC's separation is enforced by mechanism boundaries — the CC analog is `§2.1 Monolithic standing context` and is scanned.

---

*End of skill-relevant catalog. Cross-reference `root_AGENT_ANTI_PATTERNS.md` for canonical signatures, surface tags, and the cross-surface mapping table.*

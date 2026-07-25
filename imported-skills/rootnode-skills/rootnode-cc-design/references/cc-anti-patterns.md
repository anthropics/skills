# Claude Code Anti-Patterns

A catalog of 15 recurring failure modes in Claude Code deployments, drawn from the convergence of Anthropic primary documentation, named practitioners (rosmur, obra/superpowers, Shrivu Shankar, Marc Nuri, alexop.dev, Daniel Miessler), and community sources. These are the patterns where 3+ independent sources converged.

**This Skill's role with the catalog:** rootnode-cc-design uses this catalog as a **fix-recipe library**. Each pattern includes a structural cause and a structural fix; REMEDIATE mode looks up the fix when consuming a hygiene finding tagged with the pattern's canonical reference. EVOLVE mode references it when diagnosing user-reported friction. DESIGN mode uses it as a "things to avoid creating" checklist.

**The audit-checklist role belongs to rootnode-repo-hygiene.** That Skill scans an existing CC environment for these patterns and produces `HYGIENE_REPORT.md`. This Skill consumes that report — it does not produce it. The two Skills share the catalog; they apply it from opposite directions (scan-for vs. fix). For audit-time signature scanning of these patterns, see `rootnode-repo-hygiene` `references/anti-pattern-catalog.md` if available — that Skill applies the catalog from the scan direction; this file applies it from the fix-recipe direction.

For the placement-rule patterns these anti-patterns relate to, see `cc-environment-design-patterns.md`. For the methodology patterns these complement, see `cc-methodology-patterns.md`.

---

## Catalog

| Canonical reference | Name | Surface | Sweep category mapping |
|---|---|---|---|
| `root_AGENT_ANTI_PATTERNS.md §2.1` + `root_CC_ENVIRONMENT_GUIDE.md §2.4` | Bloated CLAUDE.md / Monolithic standing context | both | Cat 9 |
| `root_AGENT_ANTI_PATTERNS.md §4.1` | Transcript dump | CC | Cat 9, 12 |
| `root_AGENT_ANTI_PATTERNS.md §4.2` | MCP bloat | CC | Cat 12 |
| `root_AGENT_ANTI_PATTERNS.md §4.3` | Manual-only Skills | CC | Cat 10 |
| `root_AGENT_ANTI_PATTERNS.md §4.4` | Enforcement-as-preference | CC | Cat 9 |
| `root_AGENT_ANTI_PATTERNS.md §4.5` | Subagent overuse | CC | Cat 8 |
| `root_AGENT_ANTI_PATTERNS.md §4.6` | Subagent underuse | CC | Cat 8 |
| `root_AGENT_ANTI_PATTERNS.md §4.7` | bypassPermissions outside sandbox | CC | Cat 6 |
| `root_AGENT_ANTI_PATTERNS.md §4.8` | Missing managed policy | CC | Cat 2 |
| `root_AGENT_ANTI_PATTERNS.md §4.9` | Path-scoped rules opportunity missed | CC | Cat 9 |
| `root_AGENT_ANTI_PATTERNS.md §4.10` | Auto memory misuse | CC | Cat 9 |
| `root_AGENT_ANTI_PATTERNS.md §4.11` | Verification-before-completion absent | CC | Cat 13 |
| `root_AGENT_ANTI_PATTERNS.md §4.12` | Skills/Commands legacy mix | CC | Cat 10 |
| `root_AGENT_ANTI_PATTERNS.md §4.13` | Kitchen-sink session (operational) | CC | Cat 12 |
| `root_AGENT_ANTI_PATTERNS.md §4.14` | Stale CLAUDE.md | CC | Cat 9, 12 |

---

## §2.1 — Bloated CLAUDE.md / Monolithic standing context

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §2.1` (surface-invariant); CC-specific manifestation in `root_CC_ENVIRONMENT_GUIDE.md §2.4`.

**Surface tag:** `[both]`

**Sweep category mapping:** Cat 9 (CLAUDE.md hygiene). When repo-hygiene produces a finding tagged `Cat 9 + §2.1`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** > 200 lines, contains multi-step procedures, contains file-pattern-specific rules, contains detailed reference material (full API schemas, complete data dictionaries).

**Cause:** Treating CLAUDE.md as the catch-all; conflating "always-relevant facts" with "everything Claude should know."

**Symptoms in agent behavior:** Important rules get lost; agent ignores some CLAUDE.md sections; responses become generic.

**Fix:** Apply the placement table from `cc-environment-design-patterns.md` §1. Multi-step procedures → Skills. Path-specific rules → `.claude/rules/` with `paths:` frontmatter. Reference material → dedicated files the agent reads on demand. Behavioral guarantees → hooks. Trim CLAUDE.md until only "facts that matter every session" remain. Target < 200 lines.

**Source:** Anthropic primary docs ("under 200 lines"); rosmur; Shrivu Shankar.

---

## §4.1 — Transcript dump

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.1`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 9 (standing-context hygiene), Cat 12 (session management). When repo-hygiene produces a finding tagged `Cat 9 + §4.1` or `Cat 12 + §4.1`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** HANDOFF or onboarding docs that read like pasted chat history. Initial prompts that paste prior conversation. "Remember our conversation about X" prompts.

**Cause:** Chat as source of truth instead of files. Failure to restructure decisions into named-section spec files at session boundaries.

**Symptoms in agent behavior:** Agent context-switches confusingly; references information that doesn't exist in any file; new session starts cold despite "extensive prior work."

**Fix:** Restructure chat decisions into spec files (PLAN.md, SPEC.md, INITIAL.md, HANDOFF.md). The prompt references the spec; the spec is the canonical source. See `cc-prompt-design-patterns.md` §8 for the spec-file shapes.

**Source:** Named identically across all 3 external research reports (Gemini, Perplexity, ChatGPT); also in Daniel Miessler's PAI framing.

---

## §4.2 — MCP bloat

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.2`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 12 (session management — MCP overhead). When repo-hygiene produces a finding tagged `Cat 12 + §4.2`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** `.mcp.json` with 5+ servers; tool schemas exceed roughly 20k tokens in active context; sessions degrade after a few turns; agent forgets earlier instructions.

**Cause:** Adding every available MCP "for completeness" instead of fitting tools to actual workflows.

**Symptoms in agent behavior:** Generic responses; instructions ignored; context-pressure symptoms (forgetting, hitting limits).

**Fix:** Trim to 2-3 essentials per `cc-environment-design-patterns.md` §8 (typically GitHub + logging/observability + browser/devtools as needed). Use deferred tool loading (CC 2026 default). Evaluate each MCP against actual usage: does the work demonstrably need this server's tools? Per-subagent MCP scoping (`mcpServers:` in subagent frontmatter) keeps tool definitions out of the main conversation when only a specialist needs them.

**Source:** Community rule of thumb (~20k token threshold; not Anthropic-published — treat as heuristic). Anthropic acknowledged the problem with deferred tool loading (CC 2026 release).

---

## §4.3 — Manual-only Skills

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.3`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 10 (Skills hygiene). When repo-hygiene produces a finding tagged `Cat 10 + §4.3`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Skills present in `.claude/skills/` but `disable-model-invocation: true` is widespread. Description fields are weak ("helps with X"). No auto-activation hooks. Users have to remember to invoke Skills by name.

**Cause:** Treating Skills as user-triggered commands rather than as Claude-discoverable capabilities. Often a holdover from the `.claude/commands/` legacy mental model.

**Symptoms in agent behavior:** Skills exist but rarely used; investment in Skills doesn't pay off.

**Fix:** Strengthen `description:` so Claude auto-invokes on context match (see `cc-skills-and-hooks-composition.md` §3 — apply the 50-description competition test). Add `UserPromptSubmit` / `PreToolUse` hooks for high-priority Skills that need belt-and-suspenders activation. Reserve `disable-model-invocation: true` for Skills that should genuinely be human-only (deploys, irreversible operations).

**Source:** rosmur "Critical Discovery: Skills need auto-activation"; Marc Nuri framework writeup; convergent practitioner consensus.

---

## §4.4 — Enforcement-as-preference

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.4`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 9 (CLAUDE.md / standing-context hygiene — behavioral rules without enforcement backing). When repo-hygiene produces a finding tagged `Cat 9 + §4.4`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** CLAUDE.md or Skills with rules like "always run tests" or "never modify migrations folder" without a backing hook. The rule is stated as instruction-to-Claude, not as runtime enforcement.

**Cause:** Believing prompt-level instructions are sufficient for invariants. Failing to distinguish "annoying if missed" from "unacceptable if missed."

**Symptoms in agent behavior:** The rule is followed most of the time but missed occasionally — exactly when it matters most. Agent declares done without testing; agent edits a protected path during a long session.

**Fix:** Apply the hooks-vs-Skills decision tree from `cc-skills-and-hooks-composition.md` §1. Move guarantees to hooks (PreToolUse to block, PostToolUse to enforce, Stop to verify-before-completion). Keep CLAUDE.md and Skills for preferences only.

**Source:** Jose Parreño Garcia ("hooks are the missing layer between prompts and production"); obra/superpowers iron law convergence.

---

## §4.5 — Subagent overuse

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.5`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 8 (subagent hygiene). When repo-hygiene produces a finding tagged `Cat 8 + §4.5`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** 10+ custom subagents in `.claude/agents/`; many rarely invoked; agents that duplicate built-in Explore/Plan/general-purpose; subagents created for sequential work that doesn't parallelize.

**Cause:** Treating subagents as a default multiplier instead of a context-isolation primitive. Often: "more agents = better."

**Symptoms in agent behavior:** Auto-delegation becomes unreliable (Anthropic: "flooding Claude with options makes automatic delegation less reliable"); user has to specify subagents manually; coordination overhead exceeds the benefit.

**Fix:** Audit each subagent against the agent-warranted test (`cc-methodology-patterns.md` §1) and the warranted/anti-warranted signals. Deprecate or merge agents that don't meet warrant criteria. Default to built-ins (Explore, Plan, general-purpose) where they suffice.

**Source:** Anthropic primary docs ("flooding Claude with options"); obra/superpowers subagent-driven-development threshold ("plan exists + tasks mostly independent"); rosmur synthesis.

---

## §4.6 — Subagent underuse

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.6`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 8 (subagent hygiene). When repo-hygiene produces a finding tagged `Cat 8 + §4.6`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Main conversations consistently bloat with research; no custom subagents in `.claude/agents/`; built-in Explore not used for codebase queries; sessions routinely fill past 60k tokens.

**Cause:** Unfamiliarity with the subagent feature; or a culture of single-conversation work that predates subagent maturity.

**Symptoms in agent behavior:** Context-pressure symptoms (forgetting, generic responses); long sessions degrade; user has to manually `/clear` and re-explain.

**Fix:** Identify recurring research-heavy patterns; promote them to explicit subagent invocations. Use the built-in Explore subagent for "find me where X is implemented" queries (Haiku, read-only, cheap). Consider 1-2 well-scoped custom subagents for repeated specialist work (security review, test writing, doc proofreading).

**Source:** alexop.dev full-stack post; Anthropic docs on Explore + general-purpose; rosmur.

---

## §4.7 — bypassPermissions outside sandbox

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.7`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 6 (permissions hygiene). When repo-hygiene produces a finding tagged `Cat 6 + §4.7`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** `--dangerously-skip-permissions` in scripts, CI, or default user settings; `bypassPermissions` set in `~/.claude/settings.json` outside containers/VMs/throwaway environments.

**Cause:** Permission fatigue; speed-over-safety in environments where mistakes have real consequences.

**Symptoms when it bites:** Irreversible action taken silently (file deleted, branch force-pushed, credential exposed). The kind of incident that's hard to recover from.

**Fix:** Apply the permission-modes spectrum from `cc-environment-design-patterns.md` §11. Sandboxing for local autonomy (84% prompt reduction per Anthropic). Auto mode with classifier for trusted infrastructure (93% of approvals replaced). `bypassPermissions` ONLY in throwaway environments (containers, VMs, short-lived). Document the reasoning in settings comments.

**Source:** Anthropic sandboxing post (Oct 2025); Anthropic auto-mode post (Mar 2026); convergent community claim (sandboxing > permission skip).

---

## §4.8 — Missing managed policy

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.8`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 2 (settings/managed-policy hygiene). When repo-hygiene produces a finding tagged `Cat 2 + §4.8`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Compliance-sensitive context (regulated industry, enterprise, multi-tenant) but no managed policy CLAUDE.md or settings; security/compliance rules only in project or user files.

**Cause:** Unfamiliarity with the managed-policy hierarchy; assumption that project-level rules are enforceable as a ceiling.

**Symptoms when it bites:** A user (intentionally or not) overrides a project rule with a CLI flag or a `.claude/settings.local.json` override, bypassing a control that should have been enforced organization-wide.

**Fix:** Identify rules that require ceiling-level enforcement (the controls that no one in the org should be able to override). Deploy them to the managed-policy location (the security ceiling per `cc-environment-design-patterns.md` §10). Use `claudeMdExcludes` for monorepo cleanup. Examples: `disableBypassPermissionsMode`, protected-path enforcement, org-wide credential handling.

**Source:** Anthropic primary docs on settings hierarchy; Jim Manico's "Securing Claude Code" OWASP talk.

---

## §4.9 — Path-scoped rules opportunity missed

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.9`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 9 (CLAUDE.md / standing-context hygiene — rules misplaced into always-loaded layer). When repo-hygiene produces a finding tagged `Cat 9 + §4.9`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** CLAUDE.md contains rules like "for files in `src/api/**`, do X" or per-directory conventions baked into one document.

**Cause:** CLAUDE.md predates `.claude/rules/` with path-scoped frontmatter; not yet migrated. Or unfamiliarity with the rules layer.

**Symptoms in agent behavior:** CLAUDE.md is bloated (§2.1 risk); rules apply too broadly when scoped to all sessions instead of matching files; per-directory conventions get diluted.

**Fix:** Extract per-path rules into `.claude/rules/{name}.md` files with `paths:` frontmatter (see `cc-environment-design-patterns.md` §4). CLAUDE.md becomes lighter; rules load on demand when matching files are read.

**Source:** Anthropic primary docs on `.claude/rules/`; alexop.dev customization guide.

---

## §4.10 — Auto memory misuse

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.10`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 9 (CLAUDE.md / standing-context hygiene — auto-memory content that belongs in checked-in CLAUDE.md). When repo-hygiene produces a finding tagged `Cat 9 + §4.10`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Important team conventions or project decisions in `~/.claude/projects/<project>/memory/MEMORY.md` instead of in checked-in CLAUDE.md.

**Cause:** Letting Claude's auto memory write team-relevant content; not realizing auto memory is machine-local and not shared with the team.

**Symptoms when it bites:** Team members get inconsistent agent behavior because the writer of the auto memory has context the rest of the team doesn't. New team members onboard cold.

**Fix:** Audit auto memory periodically. Promote team-relevant entries to CLAUDE.md (which is checked in and shared). Leave only personal preferences and cross-project habits in auto memory. See `cc-environment-design-patterns.md` §12 for the boundary.

**Source:** Anthropic primary docs (CC v2.1.59+ memory feature framing); Shrivu Shankar discipline writeup.

---

## §4.11 — Verification-before-completion absent

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.11`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 13 (verification discipline). When repo-hygiene produces a finding tagged `Cat 13 + §4.11`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** CC outputs use speculative completion language ("should work," "probably fine," "looks good"); no test runs before "done"; no Stop hook blocking completion without evidence.

**Cause:** Default Claude Code behavior drifts toward implementation-first; without verification gates, the "trust-then-verify gap" emerges. Anthropic's own framing names this gap.

**Symptoms when it bites:** Bugs ship; the agent declares done on broken work; the user discovers issues after the session has moved on.

**Fix:** Install the verification iron law (see `cc-skills-and-hooks-composition.md` §5). Either install obra/superpowers' verification-before-completion Skill or write the equivalent. Add a `Stop` hook blocking completion without test evidence. Ban speculative language in Skill prompts and CLAUDE.md.

**Source:** Anthropic ("trust-then-verify gap" framing); obra/superpowers verification-before-completion Skill (the canonical artifact); Marc Nuri Skills framework writeup.

---

## §4.12 — Skills/Commands legacy mix

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.12`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 10 (Skills hygiene). When repo-hygiene produces a finding tagged `Cat 10 + §4.12`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Both `.claude/commands/` and `.claude/skills/` directories present with overlapping content; team confusion about which mechanism to use; commands that have a Skills equivalent but both still exist.

**Cause:** Migration to Skills incomplete; legacy commands still in place after the 2026 unification.

**Symptoms in agent behavior:** Inconsistent activation (sometimes the Skill fires, sometimes the command; sometimes neither); team friction over which to maintain.

**Fix:** Migrate `.claude/commands/` content to `.claude/skills/` with appropriate frontmatter. Use `disable-model-invocation: true` for previously manual-only commands. Delete `.claude/commands/` once migrated. See `cc-skills-and-hooks-composition.md` §7 for the migration table.

**Source:** Anthropic primary docs (Skills as the unified extensibility model); Daniel Miessler "Skills vs Workflows vs Agents" decision framework.

---

## §4.13 — Kitchen-sink session (operational)

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.13` (operational variant; distinct from `§3.4` structural Kitchen Sink for CP).

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 12 (session management). When repo-hygiene produces a finding tagged `Cat 12 + §4.13`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** Single CC sessions spanning 100+ turns mixing unrelated tasks; never use `/clear` or `/compact`; one terminal window kept open for everything.

**Cause:** Habit of keeping one terminal session open for multiple tasks. Failure to use session boundaries as a context-management tool.

**Symptoms when it bites:** Context-pressure symptoms compound; agent confuses unrelated tasks; long sessions become unstable; the cost of any individual change rises with session length.

**Fix:** Use `/clear` between unrelated tasks. Spawn subagents for side investigations rather than dragging the main session through them. Use named sessions (`claude --continue` with descriptive names) for distinct workstreams.

**Source:** Practitioner consensus; Anthropic best-practices guide.

---

## §4.14 — Stale CLAUDE.md

**Canonical:** `root_AGENT_ANTI_PATTERNS.md §4.14`

**Surface tag:** `[CC]`

**Sweep category mapping:** Cat 9 (CLAUDE.md hygiene), Cat 12 (session management — long-untouched standing context). When repo-hygiene produces a finding tagged `Cat 9 + §4.14` or `Cat 12 + §4.14`, REMEDIATE looks up this entry for the fix recipe.

**Signature:** CLAUDE.md last modified months ago; references tools/files/patterns that no longer exist; rules contradicted by current codebase; "Engine state snapshot" (W1) shows old version numbers and stale test counts.

**Cause:** CLAUDE.md treated as set-and-forget, not as evolving context. No discipline for updating CLAUDE.md when the project changes.

**Symptoms in agent behavior:** Agent recommends approaches no longer used; agent references files that have moved or been deleted; agent's mental model of the project diverges from reality.

**Fix:** Audit CLAUDE.md against current codebase quarterly. Remove dead references. Date-stamp the file (or auto-update via the W1 engine state snapshot pattern). Add CLAUDE.md audit as part of the project's repo hygiene routine.

**Source:** Practitioner consensus; tied to the broader "files as primary context" discipline.

---

## How to use this catalog

**In REMEDIATE mode:** the catalog is a fix-recipe library. When consuming a `HYGIENE_REPORT.md` finding tagged with a canonical reference (e.g., `§4.2`), look up the corresponding entry here. The "Fix" line provides the structural remediation; expand it into concrete plan steps in EXECUTION_PLAN.md (e.g., §4.2 fix → step 1: edit `.mcp.json` to remove unused servers; step 2: validate count; step 3: append CHANGELOG entry).

**In EVOLVE mode:** when the user describes friction, scan this catalog for matching signatures. The diagnosis often maps to one or two anti-patterns; the fix is the corresponding remediation. Produce section-level deltas to existing artifacts.

**In DESIGN mode:** use as a "things to avoid creating" checklist when producing the deployment plan. Confirm explicitly that the plan does NOT introduce any of these patterns.

**Catalog completeness note:** these are the 15 patterns where 3+ independent sources converged. Project-specific patterns documented in a project's own design materials complement this catalog. Add new entries via the design Project's methodology evolution discipline; promote to a generalizable catalog only after cross-project recurrence.

**The catalog is shared with rootnode-repo-hygiene.** That Skill uses the same 15 patterns as its scan checklist (audit verb); this Skill uses them as fix recipes (remediate / evolve / avoid verbs). When a new generalizable pattern is added, add to both Skills' references to keep them in sync.

---

## End of CC anti-patterns reference

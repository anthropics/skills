# CC Best Practices (12 convergence patterns)

The bar this Skill audits against. A repo failing to implement these patterns generates findings.

**Canonical sources:**
- `root_CC_ENVIRONMENT_GUIDE.md` — the 7-layer architecture, agent topology, discipline practices, hooks-vs-prompts boundary (cited per-pattern below)
- `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.6` — files-as-context principle (Pattern 2)
- `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §5` — chat→Code round-trip (Pattern 11)

This file applies the canonical content to audit-time scanning. It does not duplicate canonical principle definitions; it cites them and applies the principles to detection.

---

## How to read this file

Each pattern has the same four subsections:
- **What the pattern says** — one-sentence formulation of the principle
- **Audit signal** — what evidence in the repo indicates the pattern is missing
- **Scan procedure** — how to walk the repo to detect the absence
- **Remediation pointer** — what the report's recommended action should name

The 12 patterns are the convergence — what good looks like across Anthropic's design intent, named-practitioner synthesis, and tested production CC deployment experience. The mapping table at the end shows which sweep category each pattern lights up.

---

## Pattern 1 — Plan before code (Explore → Plan → Implement → Verify)

**What it says.** Substantive code work follows a four-phase rhythm: Explore (read the relevant code, understand the surrounding state), Plan (write what will change before changing it), Implement (apply the planned changes), Verify (run tests/lint to confirm).

**Audit signal.** No plan-mode usage in change_log. No `PLAN.md` or equivalent planning artifact for substantive work. No `/plan` command pattern in the project's slash commands. Change_log entries that show "implemented X" without an Explore/Plan cited.

**Scan procedure.** Read change_log entries from the active work period. Look for sequence-evidence: "explored ...", "planned ...", "implemented ...", "verified ...". Surface findings on entries that show implementation jumping directly from problem statement to code change without a plan artifact cited.

**Remediation pointer.** Recommend introducing PLAN.md discipline for substantive changes, or a `/plan` slash command, or a CLAUDE.md instruction requiring plan-before-implement for changes touching N+ files.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §3.1`. Audit category: Cat 13 (recommendation-only).

---

## Pattern 2 — Files as primary context surface, not chat

**What it says.** Decisions, state, and standing context live in files. Chat is the vehicle for writing files; chat history is not the durable record.

**Audit signal.** Decisions documented as "see chat from Tuesday" rather than as files. Standing context that lives in CLAUDE.md as paraphrased dialogue. HANDOFF files that look like transcript dumps (long unstructured prose, "the user said... Claude said..." framing).

**Scan procedure.** Read CLAUDE.md, READMEs, and any files in `.claude/` subdirectories. Search for transcript-shape content (dialogue framing, references to chat sessions as authoritative, paraphrased speaker exchanges). Surface findings.

**Remediation pointer.** Recommend distilling transcript-shape content into structured files (decision logs, state snapshots, structured handoff briefs). Reference the chat→Code round-trip pattern in `root_CC_ENVIRONMENT_GUIDE.md §10` for the canonical handoff brief format.

**Canonical:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.6`. Audit category: Cat 9 (mixed reference material), Cat 12.

---

## Pattern 3 — Verification before completion (iron law)

**What it says.** Completion claims require evidence — test runs, lint runs, type-checks, or equivalent verification — and the evidence is captured in the work record.

**Audit signal.** Completion entries in change_log without test/lint/build evidence cited. No Stop hook running the test command. Test infrastructure exists but is never automatically exercised at session close.

**Scan procedure.** Read recent change_log completion entries. For each, look for verification evidence (test count, lint output, build status). Read `.claude/settings.json` hooks — check for a Stop hook that runs the test command. Surface findings on completion-without-verification patterns and on absent Stop hooks.

**Remediation pointer.** Recommend adding a Stop hook that runs the test command. Recommend updating change_log discipline to require test-result citation in completion entries.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §5.2`. Audit category: Cat 13 (when infrastructure absent), Cat 7 (when adding the Stop hook is the executable fix).

---

## Pattern 4 — Subagents are context-isolation primitives, not multipliers

**What it says.** Subagents exist to preserve main context when a subtask has high token cost. They are not a "more agents = more capability" mechanism.

**Audit signal.**
- **Underuse:** main conversation absorbing high-token subtasks (large file analysis, code review, test debugging). Zero or one subagent definitions in a project where work patterns warrant isolation.
- **Overuse:** ten or more subagent definitions with most rarely invoked, or scope overlap among subagents.

**Scan procedure.** List subagent definitions in `.claude/agents/`. Cross-reference with change_log invocation counts (last 90 days). Compute usage profile. Read main conversation patterns (where available) for inline high-token work that wasn't delegated.

**Remediation pointer.** For underuse: name the recurring inline pattern; recommend a subagent scope. For overuse: identify low-usage subagents for retirement; identify overlapping scopes for consolidation.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.4 + §3`. Audit category: Cat 8.

---

## Pattern 5 — Hooks for enforcement, not preference

**What it says.** Critical lifecycle guarantees that absolutely cannot be missed go in hooks. CLAUDE.md instructions are preference; only hooks enforce.

**Audit signal.** "Remember to..." or "always do X" instructions in CLAUDE.md describing lifecycle guarantees. Failures in production where the instruction was followed inconsistently because CLAUDE.md text doesn't enforce.

**Scan procedure.** Read CLAUDE.md and all `.claude/rules/*.md` files. Search for enforcement-shaped language: "remember to", "always", "before/after Y", "don't forget to". For each match, evaluate whether the guarantee absolutely cannot be missed. If yes, the instruction is a hook candidate.

**Remediation pointer.** For each enforcement-as-preference instruction, recommend extraction to a hook with the trigger point named (PreToolUse, PostToolUse, Stop, etc.). For instructions that don't need hard enforcement, recommend acknowledging the soft enforcement explicitly.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §6`. Audit category: Cat 9 (CLAUDE.md bloat) and Cat 7 (when extraction to hook is warranted).

---

## Pattern 6 — Skills > Commands

**What it says.** New procedural Claude-facing work goes in `.claude/skills/`, not `.claude/commands/`. Commands remain valid for short user-facing slash invocations; Skills are the forward-looking mechanism for procedure encoding.

**Audit signal.** New procedures being added to `.claude/commands/` rather than Skills. Both directories present with overlapping coverage and unclear routing rules. Commands containing multi-step procedures that fit the Skill model.

**Scan procedure.** List `.claude/commands/` and `.claude/skills/`. For each command, evaluate: is it a short user-facing slash invocation, or is it a multi-step procedure? Surface multi-step procedures as migration candidates.

**Remediation pointer.** Recommend migrating multi-step commands to Skills. Retain commands only for short user-facing invocations. Document the routing convention in CLAUDE.md if unclear.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.3`. Audit category: Cat 10.

---

## Pattern 7 — Skills need auto-activation

**What it says.** Skills auto-activate based on the description field. A Skill with a weak description, or with `disable-model-invocation: true` set without justification, will never activate when needed.

**Audit signal.** Skills with `disable-model-invocation: true` and no `metadata.notes` justification. Skills with descriptions that are static descriptors rather than verb-based triggers ("This Skill helps with X" vs. "Use when X; trigger on Y").

**Scan procedure.** For each Skill in `.claude/skills/`, parse the frontmatter. Check `disable-model-invocation` flag and `metadata.notes`. Evaluate the description against the activation discipline: does it have verb-based triggers? Both explicit and symptom-phrased? Negative triggers naming adjacent Skills?

**Remediation pointer.** For weak descriptions, recommend rewrite with explicit triggers, symptom-phrased triggers, and negative triggers. For unjustified manual-only flags, recommend either adding `metadata.notes` justification or removing the flag.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.3`. Audit category: Cat 10.

---

## Pattern 8 — MCP minimalism (~20K token threshold)

**What it says.** MCP servers pay a context cost (tool schema declarations) that compounds across servers. Total tool schema cost stays under ~20K tokens. Each MCP earns its place by confirmed integration need, not speculation.

**Audit signal.** Five or more MCP servers configured. Tool schemas dominating standing context budget. MCP servers configured but used in fewer than 5% of sessions.

**Scan procedure.** Parse `.claude/settings.json` MCP server list. For each server, estimate token cost from declared tool schemas. Cross-reference change_log for MCP usage events. Surface findings: total token cost over ~20K threshold; individual servers with low usage.

**Remediation pointer.** Recommend removing low-usage MCPs. For overlapping MCPs, recommend consolidation. Surface the threshold breach explicitly with the measured token cost.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.6`. Audit category: Cat 12 (recommendation-only).

---

## Pattern 9 — Permission modes as graduated trust spectrum

**What it says.** Permission modes are a spectrum (default → auto → bypass). The right mode for a context is the one that matches the trust boundary — `bypassPermissions` is for sandboxes only, not for "I just don't want to be asked."

**Audit signal.** `bypassPermissions: true` in non-sandbox settings. `--dangerously-skip-permissions` in scripts that aren't containerized. `auto` mode without an explicit trusted-repo declaration.

**Scan procedure.** Search settings files for `bypassPermissions`. Search scripts for `--dangerously-skip-permissions`. For each occurrence, evaluate the context against sandboxing criteria.

**Remediation pointer.** For non-sandbox bypasses, recommend removal and replacement with explicit permission grants. For `auto` mode without trusted-repo declaration, recommend adding the declaration.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.7`. Audit category: Cat 6.

---

## Pattern 10 — Hierarchical config: managed → CLI → local → project → user

**What it says.** Settings have a hierarchy. Managed settings (organization policy) win. Then CLI flags. Then `.claude/settings.local.json` (machine-local). Then `.claude/settings.json` (project). Then user-level. The hierarchy is a feature — declared organizational expectations land in managed; project conventions land in project; per-machine overrides land in local.

**Audit signal.** Compliance or organizational policy expectations declared in CLAUDE.md or README without managed-settings enforcement. Managed settings missing where the project's documentation declares policy expectations. Per-machine settings drift between local files of different team members (when observable).

**Scan procedure.** Read CLAUDE.md, README, and onboarding docs for declared policy expectations. Cross-reference managed settings (if accessible) and project settings. Surface gaps where declaration exists without enforcement.

**Remediation pointer.** For each declared expectation, recommend either lifting to managed (when enforcement is required) or downgrading the declaration to a recommendation.

**Canonical:** `root_CC_ENVIRONMENT_GUIDE.md §1.7`. Audit category: Cat 2 (missing-entry direction), Cat 12.

---

## Pattern 11 — Chat → file-backed spec → CC execution

**What it says.** When work moves from chat-side design to CC-side execution, the handoff goes through a structured file. The file carries decisions with rationale; the chat's transcript does not travel.

**Audit signal.** Files in the repo that look like raw transcript dumps. Standing context (CLAUDE.md, rules, Skills) that paraphrases chat dialogue rather than declaring decisions. Implementation work that frequently surfaces "the user said in chat last week..." as authoritative.

**Scan procedure.** Read repo content for transcript-shape patterns (covered by Pattern 2 scanning). Look additionally for HANDOFF.md or equivalent files; check whether they follow the structured handoff brief format from `root_CC_ENVIRONMENT_GUIDE.md §10` or whether they are unstructured dumps.

**Remediation pointer.** Recommend distillation of transcript dumps into structured handoff briefs. The chat→Code round-trip pattern in `root_CC_ENVIRONMENT_GUIDE.md §10` defines the brief format.

**Canonical:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §5`. Audit category: Cat 9, Cat 12.

---

## Pattern 12 — Decomposition by concern (the 7-layer architecture)

**What it says.** Different kinds of content belong in different mechanisms. Always-relevant facts → CLAUDE.md. File-pattern conventions → `.claude/rules/`. Multi-step procedures → Skills. Focused specialists → subagents. Lifecycle guarantees → hooks. External data → MCP. Trust boundaries → settings. This is the meta-pattern — the layer fit decision underlies all the others.

**Audit signal.** Content in the wrong layer for its concern. Always-loaded mechanisms carrying conditional content. Reference layers carrying procedural content. Procedural layers carrying enforcement-guarantee content.

**Scan procedure.** Run the full 7-layer leak check (see `seven-layer-framework.md`). The leak check IS the scan procedure for Pattern 12.

**Remediation pointer.** Each leak finding is its own remediation pointer — extract content to the layer whose contract supports it. Per the recommendation-only routing rule, leak findings route to `rootnode-cc-design` REMEDIATE for fix-recipe derivation.

**Canonical:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.1 + §4.2`; `root_CC_ENVIRONMENT_GUIDE.md §1`. Audit handling: see `seven-layer-framework.md`.

---

## Pattern-to-category mapping

Reference table for cross-walking patterns and sweep categories.

| Pattern | Primary category | Secondary categories |
|---|---|---|
| 1. Plan before code | Cat 13 | — |
| 2. Files as context surface | Cat 9 | Cat 12 |
| 3. Verification before completion | Cat 13 | Cat 7 |
| 4. Subagents as isolation primitives | Cat 8 | — |
| 5. Hooks for enforcement | Cat 9 | Cat 7 |
| 6. Skills > Commands | Cat 10 | — |
| 7. Skills need auto-activation | Cat 10 | — |
| 8. MCP minimalism | Cat 12 | — |
| 9. Permission graduated trust | Cat 6 | — |
| 10. Hierarchical config | Cat 2 | Cat 12 |
| 11. Chat → file → CC handoff | Cat 9 | Cat 12 |
| 12. Decomposition by concern | (7-layer leak check) | All structural cats |

---

*End of CC best practices. Pattern definitions in `root_CC_ENVIRONMENT_GUIDE.md`. Files-as-context principle in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.6`. Chat→Code round-trip in `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §5`.*

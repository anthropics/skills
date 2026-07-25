# Chat-to-Code Handoff Patterns

Patterns for the handoff from chat-based design work (where this Skill operates) to Claude Code execution (where the design ships). The handoff is one-way and explicit: chat designs → Claude Code executes. The reverse — when to return from CC to chat for re-design — is also explicit.

This reference is for DESIGN mode (every deployment plan identifies the handoff point) and for EVOLVE mode (when an existing CC project surfaces friction that warrants returning to chat).

For prompt design at the CC side of the handoff, see `cc-prompt-design-patterns.md`. For environment design that the handoff produces, see `cc-environment-design-patterns.md`.

---

## Table of contents

1. The handoff direction (chat → Code, with explicit return triggers)
2. Handoff readiness signals
3. The artifact bundle (what to ship across the handoff)
4. The round-trip pattern
5. Anti-patterns at the handoff boundary
6. Handoff in DESIGN mode (forward direction)
7. Return triggers (CC → chat)

---

## 1. The handoff direction (chat → Code, with explicit return triggers)

The design Project is a chat-based design hub. It produces artifacts that get deployed *into* Claude Code on the delivery project. The handoff direction is one-way: chat designs → CC executes.

The reverse direction (CC → chat) is also explicit, with named triggers:
- A pattern emerges across 2+ sessions (EVOLVE MODE invocation)
- A new tool/MCP server enters consideration (RESEARCH MODE invocation)
- Friction with the existing CLAUDE.md surfaces (EVOLVE MODE for direct fixes; rootnode-repo-hygiene scan + REMEDIATE for systematic cleanup)
- The user wants a reusable artifact extracted from project-specific work (TEMPLATE MODE)

**Design with the round-trip in mind.** Every chat-design output identifies both the forward handoff point (when execution leaves chat for CC) and the conditions for returning to chat. Without the return triggers, work accumulates in CC indefinitely and design drift goes uncaught.

---

## 2. Handoff readiness signals

The handoff happens when the design is ready for autonomous execution at CC. "Ready" has 7 conditions, drawn from the rootnode-handoff-trigger-check Skill if available (see §6 below for how this Skill composes with the gate).

**The 7 conditions:**

1. **Spec stability.** The design is stable enough that CC won't have to re-derive it. Concretely: a PLAN.md, SPEC.md, or design brief exists; the user is not actively editing it; no major decisions are still open.

2. **Verification surface.** There's a way to check whether CC's work is correct. Tests, manual review checkpoints, smoke scripts, an LLM judge, or a human review gate. "I'll know it when I see it" is not a verification surface.

3. **Invariants.** The authority constraints (what CC must NOT modify) are documented in CLAUDE.md or equivalent. Without invariants, autonomous execution drifts into out-of-scope changes.

4. **Pump primer.** The first work item has been done manually (or in an interactive session) to validate the workflow. The autonomous run picks up from item 2. This catches misconfiguration before unsupervised execution.

5. **Work decomposition.** The work decomposes into discrete units that can be executed sequentially or in parallel. "Build the whole thing" is not decomposed; "process each guide in the queue" is.

6. **Rollback cost.** If the autonomous run produces something wrong, the cost of rolling back is bounded and known. Version control with clean atomic commits per work item satisfies this; in-place mutation of irreversible state does not.

7. **Token budget headroom.** The expected context usage per work item plus standing CLAUDE.md context plus loaded Skills/rules fits comfortably within the model's context window.

**Conversational signals during chat design that indicate the handoff is approaching:**

- Decomposition language: "there are N more like this," "we'll do this for each X"
- Pump-primer language: "we did the first one manually," "the rest follow the same pattern"
- Copy-paste loops: the user is performing the same edit-then-confirm cycle multiple times in chat
- Multi-instance edits being discussed: "I need to do this across all the files in X/"
- Repetition: "I keep doing this," "this is getting tedious"
- Explicit CC mentions: "let's just run this in Claude Code"
- Impatience: "let's just run it"

**When 2+ signals cluster, offer the handoff readiness check.** A single weak signal isn't enough — but a cluster indicates the work has shifted from design to execution.

---

## 3. The artifact bundle (what to ship across the handoff)

A clean handoff bundles the artifacts CC needs to execute autonomously. The bundle composition depends on the work, but the canonical shape is:

| Artifact | Required? | Purpose |
|---|---|---|
| `CLAUDE.md` | Always | Standing context (mission, authority matrix, scope rules, halt triggers, pre-flight) |
| `PLAN.md` or `SPEC.md` | When the work has a defined scope | The execution plan or the artifact specification |
| `WORK_QUEUE.md` | For decomposed work | Ordered list of work items the agent processes |
| `change_log.md` (initial entry) | When the project is past day 1 | Institutional memory for the agent to read |
| `{project_code}_design_brief.md` | Optional but recommended | Project context for next chat-design session |
| Initial CC prompt | Always | The prompt that kicks off the first execution session |
| Hooks config (`.claude/settings.json`) | When enforcement is needed | Verification iron law, sensitive-path blocks, auto-formatters |
| Custom subagents (`.claude/agents/*.md`) | When the agent-warranted test passes | Specialist roles for the work |
| Skills (`.claude/skills/{name}/`) | When reusable procedures emerge | Multi-step procedures with triggering conditions |
| Path-scoped rules (`.claude/rules/*.md`) | When per-directory conventions exist | On-demand context that loads with matching files |

**The bundle is shipped at the handoff** — Aaron pastes the artifacts into the delivery project's repo, runs the initial prompt, and CC takes over from there.

**For "design handoff bundle" patterns from the broader ecosystem,** see Anthropic's Claude Design launch (April 2026) which formalized the bundle pattern for design-to-code handoffs. The composition above is consistent with that pattern, adapted for general CC delivery work.

---

## 4. The round-trip pattern

Most CC projects have multiple chat→Code→chat cycles over their lifetime. The round-trip pattern names the touchpoints:

```
[Chat: DESIGN]  →  [CC: execute]  →  [Chat: EVOLVE/RESEARCH | CC: hygiene+REMEDIATE]  →  [CC: execute]  →  ...
                                                ↑
                                     return triggers fire here
```

**Forward direction (chat → CC) outputs:**
- Initial deployment plan (DESIGN mode)
- Section-level updates to existing CLAUDE.md (EVOLVE mode)
- Tool/MCP/Skill addition recommendations (RESEARCH mode)
- Specific fix prescriptions (rootnode-repo-hygiene findings → REMEDIATE mode plan + execution)

**Reverse direction (CC → chat) signals:**
- Pattern across 2+ sessions: "this same friction has come up multiple times" → EVOLVE
- New tool consideration: "should we add MCP server X" → RESEARCH
- Friction with existing CLAUDE.md: "the agent keeps doing Y, the rule isn't sticking" → EVOLVE for one-off; rootnode-repo-hygiene + REMEDIATE for systematic cleanup
- Reusable artifact extraction: "we've built this same pattern in 3 projects now" → TEMPLATE

**The round-trip output discipline:** every chat-design output names BOTH the forward handoff point (what triggers execution at CC) AND the return triggers (what would bring the user back to chat). Without the return triggers, the chat→CC arrow points one-way and the user has to identify return moments in the field.

---

## 5. Anti-patterns at the handoff boundary

**AB-1 — Premature handoff.** The user pivots to CC before the design is stable. Symptoms: CC asks "what should I do" repeatedly; the agent makes decisions the user wanted to make; the design drifts from what was intended.

**Fix:** apply the 7 readiness conditions (§2 above). If 3+ are missing, defer the handoff and finish the design in chat.

**AB-2 — Late handoff.** The user keeps designing in chat past the point where execution would be more efficient. Symptoms: copy-paste loops; user performs the same operation manually multiple times; chat session bloats with execution detail that should be CC's responsibility.

**Fix:** when 2+ readiness signals cluster (§2), proactively offer the handoff. Don't wait for the user to call it.

**AB-3 — Transcript-as-handoff.** The "handoff" is "go read this chat conversation." The conversation has the decisions; CC has no spec file.

**Fix:** restructure the chat decisions into a PLAN.md / SPEC.md / HANDOFF.md spec file before pivoting to CC. See `cc-anti-patterns.md` §4.1 (transcript dump).

**AB-4 — Bundle missing the verification surface.** The handoff includes CLAUDE.md and the initial prompt but no specification of how the agent's work will be verified. CC executes, but there's no way to know if it executed correctly.

**Fix:** every handoff bundle specifies the verification surface (tests to run, smoke checks, review checkpoints). If the project has no verification surface, that's a Tier-1 design gap to fix in chat before handing off.

**AB-5 — One-way handoff with no return triggers.** Forward arrow (chat→CC) is documented; no return triggers specified. Friction at CC accumulates because there's no named moment to come back to chat.

**Fix:** every chat-design output names the return triggers explicitly. See §1 and §4 above.

---

## 6. Handoff in DESIGN mode (forward direction)

Every DESIGN mode output explicitly identifies the chat→Code handoff point.

**Standard pattern in DESIGN mode output:**

```markdown
## Chat → Claude Code handoff

**Handoff point:** Once {CLAUDE.md, scope rules, initial prompt, verification gates} are
in place, hand off to Claude Code for {first iteration}.

**Bundle to ship:**
- `{project}_CLAUDE.md` (paste into project root)
- `.claude/settings.json` with the verification iron law hook (paste into `.claude/`)
- `prompts/initial.md` with the kickoff prompt (paste into `prompts/`)
- `{project_code}_design_brief.md` (file in delivery project's KFs for next chat session)

**First CC invocation:**
```bash
cd /path/to/delivery-project
claude < prompts/initial.md
```

**Return triggers (when to come back to chat):**
- A pattern emerges across 2+ CC sessions (EVOLVE mode)
- A new tool/MCP enters consideration (RESEARCH mode)
- Friction with the CLAUDE.md surfaces (EVOLVE mode for direct deltas; rootnode-repo-hygiene + REMEDIATE for full audit-and-remediate cycle)
- A reusable artifact emerges that should become a template (TEMPLATE mode)
```

**The rootnode-handoff-trigger-check Skill (CP-side) implements the formal readiness gate** for chat→CC handoffs. When the deployment plan involves autonomous execution, recommend running the gate before launch — especially for autonomous runs that will execute more than ~5 work items.

The Skill has three invocation modes:
- **Mode 1 — deliberate:** caller provides full work_context; Skill returns JSON verdict
- **Mode 2 — proactive sensing:** Skill detects readiness signals in chat conversation and offers the gate
- **Mode 3 — conversational walkthrough:** Skill walks the 7 conditions one at a time as discussion topics

For most chat-design conversations in this Skill, Mode 2 is the default behavior of this Skill. Mode 3 is appropriate when the user explicitly asks to talk through readiness. Mode 1 is for fully-formed work_context payloads (rare in design conversations).

---

## 7. Return triggers (CC → chat)

When CC execution surfaces conditions that warrant returning to chat for design work, the trigger names are:

**Return for EVOLVE mode when:**
- The same friction surfaces in 2+ CC sessions (the pattern is real, not noise)
- An anti-pattern from `cc-anti-patterns.md` is detected and the fix requires CLAUDE.md restructuring
- A new agent role or scope rule is needed
- The change_log discipline reveals a recurring shape that should become an additive engine improvement

**Return for RESEARCH mode when:**
- The user is considering adopting a new MCP server, Skill, hook, or tool
- A practitioner publishes a pattern that might apply
- The user is comparing tools (e.g., "should we use X or Y for this")

**Run rootnode-repo-hygiene scan + REMEDIATE when:**
- Quarterly project audit is due (run hygiene to produce HYGIENE_REPORT.md, then REMEDIATE to close the loop)
- The CLAUDE.md hasn't been touched in months and behavior is drifting (hygiene catches §4.14 stale CLAUDE.md; REMEDIATE proposes the fix)
- A new team member is onboarding and the project structure needs a fresh systematic review (hygiene's full scan beats ad-hoc inspection)
- A pattern has been EVOLVE-fixed multiple times across sessions (signal that hygiene + REMEDIATE would catch the underlying class of issue)

**Return for TEMPLATE mode when:**
- The same pattern has been built in 2+ projects (extract to template)
- A reusable artifact would save derivation cost on future projects

**Anti-pattern (return-trigger absence):** the user keeps fixing the same issue in CC every time it appears, never extracting the fix to a generalizable pattern at chat. The 2+ session rule catches this.

---

## End of chat-to-Code handoff patterns reference

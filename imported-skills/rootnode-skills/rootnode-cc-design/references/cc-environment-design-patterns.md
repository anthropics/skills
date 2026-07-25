# Claude Code Environment Design Patterns

Patterns for designing the Claude Code environment around a project — what content goes in CLAUDE.md, what becomes a Skill, what's a hook, what's an MCP server, what's a subagent, what's a setting, what's a path-scoped rule. This is the load-bearing decomposition for DESIGN mode and a cross-reference for EVOLVE and REMEDIATE modes when placement decisions are involved.

The 7-layer model below is the master mental model. Misplaced content is the single most common cause of agent unreliability — putting enforcement in CLAUDE.md as preference (when it should be a hook), putting reusable procedures in CLAUDE.md (when they should be Skills), putting per-directory rules in the global CLAUDE.md (when they should be `.claude/rules/`).

For prompt design (not environment design), see `cc-prompt-design-patterns.md`. For Skills authoring and hooks composition specifically, see `cc-skills-and-hooks-composition.md`.

---

## Table of contents

1. The 7-layer decomposition (placement table)
2. The placement rule (decision procedure)
3. Layer 1 — CLAUDE.md (always-loaded standing context)
4. Layer 2 — `.claude/rules/` (path-scoped on-demand context)
5. Layer 3 — Skills (`.claude/skills/`)
6. Layer 4 — Subagents (`.claude/agents/`)
7. Layer 5 — Hooks (`.claude/settings.json`)
8. Layer 6 — MCP servers (`.mcp.json`)
9. Layer 7 — Settings and permission modes
10. The settings hierarchy (managed → CLI → local → project → user)
11. Permission modes as a graduated trust spectrum
12. Auto memory vs CLAUDE.md (the boundary that matters)

---

## 1. The 7-layer decomposition (placement table)

| Concern | Mechanism | Load profile | Why this layer |
|---|---|---|---|
| Stable always-relevant facts | **CLAUDE.md** | Loaded every session, full content | Facts that affect every decision belong in standing context |
| File-pattern-specific conventions | **`.claude/rules/`** with `paths:` frontmatter | Loaded on demand when matching files are read | Per-directory or per-extension rules don't belong in always-on context |
| Reusable multi-step procedures | **Skills** (`.claude/skills/`) | Loaded on demand when description matches task | Procedures with multiple steps and triggering conditions are Skills, not CLAUDE.md content |
| Focused specialists with isolated context | **Subagents** (`.claude/agents/`) | Spawned with own context window | Work that would pollute main context belongs in subagents |
| Lifecycle guarantees | **Hooks** (`.claude/settings.json`) | Run deterministically on lifecycle events | If failure is unacceptable, the rule must be a hook (not a CLAUDE.md "remember to...") |
| External data and APIs | **MCP servers** (`.mcp.json`) | Tool schemas in context, data fetched on demand | External integrations belong in MCP, not pasted into context |
| Trust and permission boundaries | **`settings.json` + permission modes** | Enforced by the runtime, not the model | Permission decisions are enforcement, not advice |

This decomposition appears in every authoritative source on CC environment design (Anthropic primary documentation, alexop.dev's full-stack post, rosmur, obra/superpowers, Daniel Miessler). It is the framework for thinking about CC environments. **[generalizable]**

---

## 2. The placement rule (decision procedure)

For every piece of content you'd put in a CC environment, walk this procedure:

**Q1. Does the content load on every session, or only when needed?**
- Every session, no exceptions → CLAUDE.md or settings.json
- Only when reading specific file types → `.claude/rules/` with `paths:` frontmatter
- Only when a specific task is being done → Skills
- Only when explicitly invoked → custom subagent

**Q2. What enforces the guarantee?**
- The model reading and following the instruction → CLAUDE.md / Skills (preference layer)
- The runtime intercepting the action → hooks (enforcement layer)
- The permission system blocking the operation → settings.json permission rules
- An external data fetch → MCP server

**Q3. Does this content belong in *every* session, or only when a specific subagent needs it?**
- Every session → main CLAUDE.md
- Only when a specialist runs → subagent's frontmatter or its own loaded context
- Only when a task triggers it → Skill

**The placement test:** ask "what mechanism enforces this guarantee?" before "what should I write?" If the answer is "CLAUDE.md plus Claude reading and following it," consider whether a more deterministic mechanism is the better home. CLAUDE.md is for context that genuinely needs to be in every session.

**Common misplacements (the placement-validation checklist used by REMEDIATE for fix proposals and by rootnode-repo-hygiene for scan findings):**

| You see this in CLAUDE.md | It probably belongs in |
|---|---|
| "Always run `npm test` before committing" | A pre-commit hook (deterministic enforcement) |
| "When working in `migrations/`, never delete tables" | `.claude/rules/migrations.md` with `paths: ["migrations/**"]` |
| "How to add a new API endpoint: 1. ... 2. ... 3. ..." | A Skill (`.claude/skills/add-api-endpoint/`) |
| "When investigating bugs, search these files first" | A Skill or a custom subagent (depending on whether multi-step work is involved) |
| "Never write to /etc/" | A PreToolUse hook (or a settings.json deny rule) |
| The full schema of an internal API | A reference file the agent reads on demand, not always-loaded context |
| Detailed credentials handling procedure | Hook + settings.json (enforcement, not preference) |

---

## 3. Layer 1 — CLAUDE.md (always-loaded standing context)

CLAUDE.md is the standing context CC reads on every session. Anthropic's primary documentation recommends targeting **under 200 lines per CLAUDE.md file**. Longer files reduce adherence — important rules get lost in the noise.

**Required sections in every CLAUDE.md** (failure modes apply universally):

| Section | Purpose |
|---|---|
| **R1. Mission statement** | One paragraph: what the project produces, who it's for, what "shipped" means |
| **R2. Authority matrix** | Tiered table of what content classes the agent has authority to modify vs mirror vs originate (see `cc-methodology-patterns.md` §2) |
| **R3. Bug-fixing authorization scope** | Explicit in-scope and out-of-scope lists for autonomous iteration (see `cc-methodology-patterns.md` §3) |
| **R4. Halt-and-escalate triggers** | The conditions under which the agent must stop and surface to a human (see `cc-methodology-patterns.md` §8) |
| **R5. Pre-flight checklist** | What every agent must do before making changes (read change_log tail, run test backstop, verify build is clean) |

**Warranted sections** (add only when the inclusion test passes):

| Section | Inclusion test |
|---|---|
| **W1. Engine state snapshot** | Project has measurable state that changes session-to-session AND agent behavior should differ based on that state. Auto-updated. Skip on day-1 deployments. |
| **W2. Common bug patterns to recognize** | Project has accumulated 3+ distinct, recurring bug patterns from real debugging history. Do not pre-fill speculative patterns. |
| **W3. Agent dispatch matrix** | 3+ distinct agent types are in regular use. Below threshold, the matrix is decorative. |

**The migration trigger:** when CLAUDE.md exceeds 200 lines, audit each section against the placement table (§1). Multi-step procedures move to Skills. Path-specific rules move to `.claude/rules/`. Reference material moves to dedicated files. Behavioral guarantees move to hooks.

**Anti-patterns specific to CLAUDE.md** (see `cc-anti-patterns.md` §2.1, §4.4, §4.14 for full catalog):

- **Bloat** — > 200 lines, multi-step procedures inline, file-pattern-specific rules
- **Conversational framing** — "Hi Claude, in this project you'll be helping with..." reduces perceived authority. Write declaratively.
- **Reference material mixed with rules** — Detailed reference belongs in separate files
- **Aspirational language** — "Strive for excellence" doesn't constrain behavior
- **Stale state sections** — Auto-update or delete; never leave a 6-month-old "Engine state snapshot"
- **Pre-filled warranted sections** — W1/W2/W3 with placeholder content because structure feels incomplete
- **Enforcement-as-preference** — "Always run tests" without a backing hook (move to hook layer)

---

## 4. Layer 2 — `.claude/rules/` (path-scoped on-demand context)

`.claude/rules/{name}.md` files with `paths:` frontmatter load only when the agent reads or edits files matching the paths. They eliminate a major source of CLAUDE.md bloat: per-directory or per-file-type conventions that don't belong in always-on context.

**Frontmatter pattern:**

```markdown
---
paths:
  - "src/api/**/*.ts"
  - "src/api/**/*.tsx"
---

# API conventions

- Use `Result<T, E>` for fallible operations; never throw.
- Endpoints must include OpenAPI documentation in JSDoc.
- ...
```

**When to use rules instead of CLAUDE.md:**
- The rule applies to a specific subset of files (a directory, an extension)
- The rule is detailed (multiple specifics) and would crowd out other CLAUDE.md content
- Different parts of the codebase have different conventions

**When to use rules instead of a Skill:**
- The content is convention/rules (always-on for matching files), not a multi-step procedure with triggering conditions
- The agent should follow the rule whenever editing matching files, not only when explicitly invoked

**Common rule files:**
- `.claude/rules/api-conventions.md` (paths: `src/api/**`)
- `.claude/rules/test-conventions.md` (paths: `**/*test*`, `**/*spec*`)
- `.claude/rules/migrations-safety.md` (paths: `migrations/**`)
- `.claude/rules/security-sensitive.md` (paths: `**/auth/**`, `**/secrets/**`)
- `.claude/rules/style-frontend.md` (paths: `**/*.tsx`, `**/*.css`)

**Anti-pattern:** stuffing path-specific rules into CLAUDE.md (see §4.9 in `cc-anti-patterns.md`). Migrate them to `.claude/rules/` to lighten the always-on context.

---

## 5. Layer 3 — Skills (`.claude/skills/`)

Skills are reusable multi-step procedures with triggering conditions. They're loaded on demand when their `description:` field matches the active task. Skills replaced commands as the unified extensibility model in 2026; new work goes in `.claude/skills/`. **[Anthropic primary docs]**

**When to make something a Skill (vs CLAUDE.md content vs a rule):**
- The procedure has multiple steps
- The procedure has triggering conditions ("when the user asks for X")
- The procedure is reusable across contexts (not specific to one path or one session)
- Loading the procedure into context only when needed saves CLAUDE.md budget

**Skill anatomy:** a folder with `SKILL.md` (required), optional `references/` subdirectory, optional `scripts/`, optional `assets/`. The frontmatter `description:` field is the activation trigger; getting it right is the highest-leverage decision.

**Skills authoring is covered in detail in `cc-skills-and-hooks-composition.md`.** This section is the placement-rule pointer: when something is a multi-step reusable procedure with triggering conditions, it's a Skill — not CLAUDE.md content, not a rule, not a subagent.

---

## 6. Layer 4 — Subagents (`.claude/agents/`)

Subagents are spawned with their own context window. They isolate context that would pollute the main session — research-heavy investigations, fresh-perspective reviews, parallel pipeline phases.

**Built-in subagents (use these first):**

| Subagent | Model | Tools | Use for |
|---|---|---|---|
| **Explore** | Haiku | Read-only | Codebase search, "find me where X is implemented", cheap context-gathering |
| **Plan** | (planning-mode) | Read-only | Used in plan mode for research before plan production |
| **general-purpose** | (default) | Full tools | Complex multi-step work that requires context isolation |

**When to add a custom subagent:** when the same kind of subagent keeps getting requested (a security reviewer, a test writer, a docs proofreader), define it once. **[Anthropic docs framing]**

**A custom subagent needs three things to be reliable:**
1. **Specific `description:` field.** Claude uses this to decide auto-delegation. "Reviews code for security issues before commits" routes better than "security expert."
2. **Restricted tool access.** Read-only for review roles, full tools for implementation roles. Tool restriction is the cheapest reliability gain available.
3. **Focused system prompt.** One expertise area per subagent; not "general-purpose plus also security plus also testing."

**Anti-patterns** (see `cc-anti-patterns.md` §4.5, §4.6):
- **Overuse:** 10+ custom subagents, many rarely invoked, agents that duplicate built-ins
- **Underuse:** main conversations bloated with research, no Explore use, sessions filling past 60k tokens

**The agent-warranted test before adding a custom subagent:** see `cc-methodology-patterns.md` §1.

---

## 7. Layer 5 — Hooks (`.claude/settings.json`)

Hooks run deterministically on CC lifecycle events. They are the enforcement layer — when a guarantee absolutely cannot be missed, it goes here, not in CLAUDE.md as preference.

**The framing from Jose Parreño Garcia:** "hooks are the missing layer between prompts and production." **[practitioner: Jose Parreño Garcia, Substack post 2026-02-24]**

**The decision rule:** "if failure is annoying, prompt or skill; if failure is unacceptable, hook." **[obra/superpowers + rosmur convergence]**

**Hook lifecycle events** (from Anthropic primary docs at https://code.claude.com/docs/en/hooks):

| Event | When it fires | Common uses |
|---|---|---|
| `UserPromptSubmit` | Before CC processes the user's prompt | Auto-inject Skill instructions, log prompts, validate prompt format |
| `PreToolUse` | Before a tool call executes | Block dangerous operations, require confirmation, modify tool inputs |
| `PostToolUse` | After a tool call completes | Auto-format edited files, run linters, log changes |
| `Stop` | Before CC declares work complete | Verify-before-completion gates (run tests, check evidence) |

**Hook authoring is covered in detail in `cc-skills-and-hooks-composition.md`.** This section is the placement-rule pointer: enforcement guarantees go in hooks; preferences go in CLAUDE.md.

**Common hook patterns:**
- **PreToolUse blocking sensitive paths:** `migrations/**`, `secrets/**`, `.env*` — block writes; require explicit confirmation
- **PostToolUse auto-formatter:** run `prettier --write` or `black .` on edited files
- **PostToolUse auto-linter:** run `eslint`/`pylint` and surface output
- **Stop verify-before-completion:** require `pytest` or `npm test` evidence before "done"

---

## 8. Layer 6 — MCP servers (`.mcp.json`)

MCP servers expose external data and APIs to CC. Each server's tool schemas consume context for their definitions. Heavy MCP usage is a named anti-pattern.

**The MCP minimalism discipline:**
- Start a new project with **2-3 essential MCP servers** (typically GitHub + a logging/observability server + browser/devtools as needed for UI work)
- Add additional MCPs only when ROI is concrete — the work demonstrably needs the server's tools
- When MCP tool schemas approach **~20k tokens** in the active context, CC has too little room to think effectively. **[community rule of thumb, not Anthropic-published; treat as heuristic]**
- Anthropic's **deferred tool loading** (default in CC 2026) reduces but does not eliminate this concern

**MCP selection criteria** (from research synthesis):
- **Tool schema density** — prefer servers with concise tool descriptions
- **Output summarization** — prefer servers that return summarized output, not raw JSON dumps
- **State-awareness** — prefer indexed/queryable interfaces over those that return large payloads on every call

**Per-subagent MCP scoping:** specify `mcpServers:` in a subagent's frontmatter to keep tool definitions out of the main conversation when only the specialist needs them. Reduces main-session context pressure.

**Audit trigger:** if a project's `.mcp.json` has 5+ servers and sessions are showing context pressure symptoms (Claude forgetting earlier instructions, generic responses, hitting context limits), audit MCP usage. See `cc-anti-patterns.md` §4.2.

---

## 9. Layer 7 — Settings and permission modes

Settings (`settings.json`) and permission modes are the trust/permission boundary. They are enforced by the runtime, not the model — settings are not "advice the model can ignore."

**Permission modes** (from Anthropic primary docs at https://code.claude.com/docs/en/permission-modes):

| Mode | Behavior | When to use |
|---|---|---|
| `plan` | Plan mode active; edit tools disabled | Default during plan production; Shift+Tab toggles |
| `default` | Standard interactive mode; permission prompts on edits | Interactive sessions, default for most work |
| `acceptEdits` | Auto-accept file edits without prompting | Trusted local development with version control as safety net |
| `auto` | Classifier-based approval (replaces prompts the user usually approves) | Trusted infrastructure with low-stakes operations |
| `dontAsk` | Skip prompts for a specific allowlisted operation set | Specific narrow operations where prompting is friction |
| `bypassPermissions` | Skip all permission prompts | **Containers/VMs/throwaway environments only.** Never on a developer machine with real credentials. |

**Selection rule:** environment-driven, not preference-driven. The mode reflects the trust environment, not the user's tolerance for prompts.

**Anthropic data points:**
- **Sandboxing** reduces permission prompts by ~84%; the safer alternative to indiscriminate permission skip
- **Auto mode classifier** approves ~93% of permission prompts users were going to approve anyway

**Anti-pattern:** `bypassPermissions` (or `--dangerously-skip-permissions`) in scripts, CI, or default user settings outside containers. See `cc-anti-patterns.md` §4.7.

---

## 10. The settings hierarchy (managed → CLI → local → project → user)

Settings have a layered authority hierarchy. Higher-tier settings override lower-tier ones.

| Tier | Location | Authority |
|---|---|---|
| **Managed policy** | (org-deployed) | The security ceiling. Cannot be overridden by CLI flags or local files. Used for `disableBypassPermissionsMode`, protected-path enforcement, org-wide policies. |
| **CLI flags** | Command line at invocation | Override project/user/local settings for the session. |
| **Local** | `.claude/settings.local.json` | Per-working-tree overrides. Often gitignored. Use for experiments and transient overrides. |
| **Project** | `.claude/settings.json` | Repo standards, tool allowlists. Checked into version control. |
| **User** | `~/.claude/settings.json` | Personal defaults across all projects. Not checked in. |

**Common patterns:**
- **Managed policy** → org-wide rules (what no one is allowed to do)
- **Project settings.json** → repo standards (what this codebase expects)
- **User settings.json** → personal defaults (what I prefer across projects)
- **Local settings.json** → experimental overrides for this work tree (transient)

**For regulated industries or enterprise contexts:** managed policy is required for any rule that must hold organization-wide. See `cc-anti-patterns.md` §4.8 for the missing-managed-policy pattern.

---

## 11. Permission modes as a graduated trust spectrum

Permission modes are not a "choose your favorite" preference. They reflect the trust environment of the work:

```
←  more constrained                           more autonomous  →
plan  →  default  →  acceptEdits  →  auto  →  dontAsk  →  bypassPermissions
```

**Calibrating the right mode** is environment-driven:

| Environment | Recommended default mode |
|---|---|
| Production code with real credentials, irreversible operations possible | `default` (every edit prompted) |
| Active development, version control is the safety net, edits are reversible | `acceptEdits` |
| Trusted infrastructure with low-stakes operations | `auto` (classifier handles the 93%) |
| CI / scripted runs in a sandboxed VM or container | Sandboxing + `auto`, OR `bypassPermissions` if and only if the environment is fully throwaway |
| Local developer machine with no isolation | Never `bypassPermissions`. Use sandboxing for autonomy. |

**The strongest community claim:** sandboxing > permission skip. If you want autonomy without prompts, isolate the environment so a mistake is contained, then run in `auto` or `acceptEdits` inside the isolation. **[community consensus]**

---

## 12. Auto memory vs CLAUDE.md (the boundary that matters)

Claude Code 2.1.59+ writes auto memory to `~/.claude/projects/<project>/memory/MEMORY.md`. Auto memory is machine-written, machine-local, per-working-tree. CLAUDE.md is human-authored, version-controlled, team-shared.

**They complement each other but are not interchangeable.**

| Property | CLAUDE.md | Auto memory |
|---|---|---|
| Author | Human | Claude (machine) |
| Version control | Yes (committed) | No (local) |
| Visibility | Team-shared | Per-developer machine |
| Use for | Deliberate team-shared context, rules, mission, authority | Incidental learnings Claude discovers session-to-session |

**The hygiene rule:** audit auto memory periodically. Auto memory entries that prove team-relevant should be **promoted to CLAUDE.md**; otherwise teammates can't see them. Leave only personal preferences and cross-project habits in auto memory.

**Anti-pattern:** important team conventions or project decisions stuck in auto memory (which only the writer sees) instead of in checked-in CLAUDE.md. See `cc-anti-patterns.md` §4.10.

---

## End of CC environment design patterns reference

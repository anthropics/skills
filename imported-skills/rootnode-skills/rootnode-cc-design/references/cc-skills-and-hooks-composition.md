# Skills and Hooks Composition

Patterns for designing Skills and hooks together. Skills are the unified extensibility model for reusable multi-step procedures (the layer that replaced commands). Hooks are the deterministic enforcement layer. They compose: hooks can auto-activate Skills, Skills can recommend hooks, and the boundary between them is the question "is failure annoying or unacceptable?"

This reference is for DESIGN mode when the deployment plan involves Skills, hooks, or both, and for EVOLVE mode when the friction is "the agent doesn't follow this rule" (often a sign that a CLAUDE.md preference should be promoted to a hook).

For the placement-rule context (when something belongs in Skills vs CLAUDE.md vs rules vs subagents), see `cc-environment-design-patterns.md`. For the anti-patterns this reference helps prevent, see `cc-anti-patterns.md` (especially §4.3, §4.4, §4.11, §4.12).

---

## Table of contents

1. The hooks-vs-Skills decision tree
2. Skills frontmatter reference
3. Skills auto-activation patterns
4. Hooks lifecycle reference
5. The verification iron law (as hook)
6. Common composition patterns
7. The Skills/Commands legacy boundary

---

## 1. The hooks-vs-Skills decision tree

The boundary between Skills (preference layer) and hooks (enforcement layer):

```
"What happens if Claude doesn't do X?"
│
├─ "Annoying / suboptimal / wastes time" → Skill or CLAUDE.md preference
│
└─ "Unacceptable / corrupts data / violates policy / breaks production" → Hook
```

**The rule:** "if failure is annoying, prompt or skill; if failure is unacceptable, hook." **[obra/superpowers + rosmur convergence; Jose Parreño Garcia framing]**

**Examples:**

| Want | Failure mode if missed | Mechanism |
|---|---|---|
| "Use 2-space indentation" | Code reviewer asks for re-indent | Skill or CLAUDE.md preference |
| "Add tests for new functions" | Coverage drops; tech debt | Skill (with optional Stop hook for coverage threshold) |
| "Never delete `migrations/*.sql`" | Production data loss | PreToolUse hook blocking deletion |
| "Format Markdown with prettier" | Inconsistent formatting | PostToolUse hook running prettier |
| "Run tests before declaring done" | Bugs ship | Stop hook requiring test evidence |
| "Don't commit secrets" | Credential leak | PreToolUse hook + gitleaks |

**The decision rule applied:** if a missed instruction has compounding cost (corrupts production, leaks credentials, irreversible), it's a hook. If the cost is bounded and recoverable, a Skill is sufficient.

---

## 2. Skills frontmatter reference

Skills are folders with `SKILL.md` containing YAML frontmatter. The frontmatter controls activation behavior. **[Anthropic primary docs at https://code.claude.com/docs/en/skills]**

**Required fields:**

```yaml
---
name: skill-name              # kebab-case, max 64 chars, must match folder name
description: |                # max 1024 chars (YAML-parsed); see Step 2a in skill-builder
  What it does. When to use it. Trigger phrases users would say.
  Negative triggers when overlap with other Skills is possible.
---
```

**Activation-control optional fields:**

| Field | Effect |
|---|---|
| `disable-model-invocation: true` | Skill cannot be auto-activated; only explicit user invocation. Use for human-only operations (deploys, irreversible). |
| `user-invocable: false` | Skill is background knowledge only; never directly invoked. Used for Skills that compose with other Skills. |
| `context: fork` | When invoked, runs in a forked subagent context (isolation). Used when the Skill's context is heavy and shouldn't pollute the parent session. |

**Other useful frontmatter:**

```yaml
license: MIT                   # or Apache-2.0, etc.
metadata:
  author: <name>
  version: "1.0"
  original-source: <reference>
compatibility: |               # 1-500 chars; environment requirements
  Requires Python 3.11+, pdfplumber, Playwright.
```

**Skill folder layout:**

```
your-skill/
├── SKILL.md                   # required
├── references/                # optional; loaded on demand
│   └── *.md
├── scripts/                   # optional; executable code
│   └── *.py / *.sh
├── assets/                    # optional; templates, fonts, icons
└── (NO README.md)             # README.md inside skill folder is rejected
```

**Constraints:**
- `SKILL.md` filename is case-sensitive
- Skill folder name must match the `name:` field
- No README.md inside the skill folder (use SKILL.md or references/ for docs)
- Skill names containing "claude" or "anthropic" are reserved
- SKILL.md body should be < 500 lines / ~5000 tokens

---

## 3. Skills auto-activation patterns

**The strong practitioner consensus:** manual-only Skills are often ignored. **[rosmur "Critical Discovery: Skills need auto-activation"; convergence across multiple sources]**

Two activation mechanisms make Skills reliable:

### Mechanism A — Strong description-field auto-activation

Claude decides whether to load a Skill based almost entirely on the description field. A Skill with perfect methodology and a vague description will never activate.

**Description structure:**
```
[What the Skill does] + [When to use it] + [Trigger phrases] + [Negative triggers]
```

**Specificity rules:**
- Include trigger phrases users would actually say ("Use when user says 'audit my CLAUDE.md'")
- Cover both explicit and implicit user requests
- Be slightly "pushy" — Claude has an undertriggering bias
- Add explicit negative triggers when overlap with adjacent Skills is possible ("Do NOT use for X — use other-skill instead")

**Test the description with the 50-description competition test:** "If Claude sees this description alongside 50 other Skill descriptions, will it correctly activate this Skill (and ONLY this Skill) for the right tasks?"

### Mechanism B — Hook-driven activation

Hooks can inject Skill instructions into the active context regardless of description matching:

```json
// .claude/settings.json
{
  "hooks": {
    "UserPromptSubmit": [
      {
        "matchers": [{"prompt_contains": "audit"}],
        "command": "cat .claude/skills/audit-helper/SKILL.md"
      }
    ]
  }
}
```

This is the "if this prompt looks like X, definitely load Skill Y" pattern. Use sparingly — over-injection bloats context — but when a Skill must activate on a specific signal, hook injection is more reliable than description matching alone.

**When to use which mechanism:**

| Scenario | Mechanism |
|---|---|
| Skill should activate for a broad range of related tasks | Description-field (Mechanism A) |
| Skill must activate on a specific signal that's hard to capture in description | Hook injection (Mechanism B) |
| Skill is critical and missing it is unacceptable | Hook injection + description-field (belt-and-suspenders) |
| Skill is for human-only operations (deploys) | `disable-model-invocation: true` (no auto-activation by design) |

**For the Skill description discipline at full depth, see `rootnode-skill-builder` if available** — it's the canonical reference for description-field construction, length validation, and the 5-dimension publication review.

---

## 4. Hooks lifecycle reference

Four lifecycle events, from Anthropic primary docs at https://code.claude.com/docs/en/hooks:

### `UserPromptSubmit`
Fires before CC processes the user's prompt. The hook can read or modify the prompt before CC sees it.

**Common uses:**
- Auto-inject Skill instructions when prompt matches a trigger
- Log prompts to a session telemetry file
- Validate prompt format (e.g., reject prompts that don't reference a spec file when a spec is required)
- Pre-compose context (e.g., always include the change_log tail in prompts about subsystem X)

### `PreToolUse`
Fires before a tool call executes. The hook can block the call or modify the inputs.

**Common uses:**
- Block writes to sensitive paths (`migrations/**`, `secrets/**`, `.env*`)
- Require explicit confirmation for destructive operations
- Log tool calls before they execute
- Modify tool inputs (e.g., append `--dry-run` to commands the user wants to preview)

**Exit code 1 from a PreToolUse hook blocks the tool call.** The hook's stderr becomes the explanation surfaced to Claude.

### `PostToolUse`
Fires after a tool call completes. The hook can run follow-up actions.

**Common uses:**
- Auto-format files after edits (`prettier --write {file}`, `black .`, `gofmt`)
- Auto-lint and surface warnings (`eslint`, `pylint`)
- Update a session log with what changed
- Trigger a smoke test after a significant edit

### `Stop`
Fires before CC declares work complete. The hook can block the completion if verification gates aren't met.

**Common uses:**
- Verification iron law: require evidence that tests passed before "done"
- Coverage gate: require coverage threshold met
- Lint-clean gate: require lint output empty
- Documentation gate: require CHANGELOG entry exists for the change

**Exit code 1 from a Stop hook blocks completion.** The hook's stderr explains what's missing.

**Hook authoring format** (one example, see Anthropic docs for the full schema):

```json
// .claude/settings.json
{
  "hooks": {
    "PreToolUse": [
      {
        "matchers": [{"tool_name": "edit", "path_pattern": "migrations/**"}],
        "command": "echo 'Migrations directory is protected. Use a migration tool.' >&2; exit 1"
      }
    ],
    "PostToolUse": [
      {
        "matchers": [{"tool_name": "edit", "path_pattern": "**/*.py"}],
        "command": "black {file_path}"
      }
    ],
    "Stop": [
      {
        "command": ".claude/hooks/verify-tests.sh"
      }
    ]
  }
}
```

---

## 5. The verification iron law (as hook)

The verification-before-completion pattern (named in obra/superpowers, Marc Nuri's writeup, and rosmur) is the highest-leverage hook to install in any CC project that has runnable tests.

**The pattern:** a `Stop` hook that blocks completion unless the agent provides evidence of test passage.

**Implementation sketch (`.claude/hooks/verify-tests.sh`):**

```bash
#!/bin/bash
# Stop hook: require recent test evidence before allowing completion.
# Looks for a fresh test report file (e.g., .pytest_cache/last_report or
# a custom telemetry file written by the agent's test command).

EVIDENCE_FILE=".claude/state/last-test-evidence.json"

if [ ! -f "$EVIDENCE_FILE" ]; then
  echo "No verification evidence found. Run the test suite and ensure" >&2
  echo "the agent records the result before declaring done." >&2
  exit 1
fi

# Check evidence freshness (last 5 minutes)
EVIDENCE_AGE=$(($(date +%s) - $(stat -f %m "$EVIDENCE_FILE" 2>/dev/null || stat -c %Y "$EVIDENCE_FILE")))
if [ "$EVIDENCE_AGE" -gt 300 ]; then
  echo "Verification evidence is stale (>5 min old). Re-run tests." >&2
  exit 1
fi

# Check evidence indicates pass
PASS=$(jq -r '.pass' "$EVIDENCE_FILE")
if [ "$PASS" != "true" ]; then
  echo "Verification evidence indicates test failure. Resolve before done." >&2
  exit 1
fi

exit 0
```

**Combined with a CLAUDE.md prompt rule:**

```markdown
## Verification

Before declaring done, run the test suite. Record the result to
`.claude/state/last-test-evidence.json` in the format:
{ "pass": true|false, "tests_run": <n>, "duration_s": <n>, "timestamp": "<iso>" }

The Stop hook will block completion without fresh, passing evidence.
Banned phrases at completion: "should work", "probably fine", "looks good".
```

**Why both prompt and hook:** the prompt teaches the agent the evidence format and the convention; the hook enforces that the convention is followed even on adversarial or careless agent runs. Belt and suspenders. **[obra/superpowers iron law]**

---

## 6. Common composition patterns

### Pattern A — Skill + auto-activation hook

A Skill that's critical for a class of work, plus a UserPromptSubmit hook that injects the Skill when the prompt matches a trigger.

**When to use:** the Skill's description-field auto-activation is unreliable (broad domain, vocabulary overlap with other Skills) but the activation needs to be near-deterministic.

### Pattern B — Skill + Stop hook

A Skill that defines a complex multi-step procedure, plus a Stop hook that enforces the procedure's completion criteria.

**When to use:** the Skill teaches HOW to do something; the hook enforces THAT it was done.

**Example:** a `release-checklist` Skill that walks the agent through pre-release steps; a Stop hook that blocks completion until each checklist item has been recorded as complete in a state file.

### Pattern C — `.claude/rules/` + PreToolUse hook

A path-scoped rule file that loads when matching files are read, plus a PreToolUse hook that blocks edits to those files unless additional conditions are met.

**When to use:** the rule explains the policy; the hook enforces the boundary.

**Example:** `.claude/rules/security-sensitive.md` documents the security review requirements for `auth/` code; a PreToolUse hook blocks writes to `auth/**` unless a recent security review marker exists.

### Pattern D — Subagent + per-subagent MCP scoping

A custom subagent that needs a specific MCP server, with the MCP scoped to that subagent's frontmatter so it doesn't pollute the main session's context.

**When to use:** an MCP is needed only for a specific specialist role; loading it always costs main-session context budget.

**Example:** a `database-investigator` subagent with `mcpServers: ["postgres-mcp"]` in its frontmatter; main sessions don't see the postgres MCP tools unless they delegate to this subagent.

---

## 7. The Skills/Commands legacy boundary

`.claude/commands/` was the predecessor to `.claude/skills/`. As of 2026, Skills replaced commands as the unified model. Both directories still work, but **new work goes in Skills**.

**Migration pattern:**

| Legacy commands behavior | Skills equivalent |
|---|---|
| Manual-only command (typed by user) | Skill with `disable-model-invocation: true` |
| Auto-suggested command | Skill with strong description-field |
| Command that runs a shell script | Skill that points to `scripts/{name}.sh` in the Skill's own folder |
| Project-scoped commands | Skills under `.claude/skills/` (project-scoped by default) |
| User-scoped commands | Skills under `~/.claude/skills/` (user-scoped) |

**The migration trigger:** if a project has both `.claude/commands/` and `.claude/skills/` with overlapping content, that's `cc-anti-patterns.md` §4.12. Migrate commands to Skills with appropriate frontmatter; delete the commands folder once migrated.

---

## End of Skills and Hooks composition reference

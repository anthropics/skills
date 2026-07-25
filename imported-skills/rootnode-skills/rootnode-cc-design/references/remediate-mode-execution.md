# REMEDIATE Mode Execution

The full protocol for REMEDIATE mode — the closed-loop mode that consumes a `HYGIENE_REPORT.md` (produced by `rootnode-repo-hygiene`) and produces (then optionally executes) an `EXECUTION_PLAN.md` against the actual repo.

REMEDIATE has two phases gated by an explicit user acceptance step. Phase 1 generates the plan; Phase 2 executes the accepted plan. The Skill produces design artifacts in all other modes; REMEDIATE Phase 2 is the only mode that writes to the repo beyond the plan file itself.

This reference is the operational source for REMEDIATE mode. Read in full when invoked.

---

## Table of contents

1. Two-phase architecture
2. Phase 1 — plan generation
3. Phase 2 — execution
4. EXECUTION_PLAN.md format (and the schema reference)
5. Action types
6. Validation grammar
7. Conflict resolution
8. Halt semantics (and what v1 does NOT do)
9. HYGIENE_REPORT.md input expectations
10. CP-only invocation (without repo access)

---

## 1. Two-phase architecture

```
[user invokes REMEDIATE]
        │
        ▼
[Phase 1: read HYGIENE_REPORT.md → generate EXECUTION_PLAN.md → write to repo]
        │
        ▼
[surface plan summary, halt, wait for explicit user acceptance]
        │
        ▼ "execute"
[Phase 2: walk plan steps → apply action → run validation → halt on failure]
        │
        ▼
[append CHANGELOG entry → report results]
```

**The acceptance step between phases is not optional.** Phase 1 always halts at the surface-and-wait step regardless of how confident the plan looks. This preserves the no-auto-execution guarantee from the rootnode-repo-hygiene SH (line 227): findings → recommendations → human review → action.

**Phase 1 is idempotent.** Running it twice produces the same plan (modulo timestamp) given the same input. If the user wants to revise the plan before executing, they can ask for changes; REMEDIATE re-generates Phase 1 with the constraints applied.

**Phase 2 is non-idempotent.** It mutates the repo. It must not be run twice on the same plan without intervening verification — or the repo state assumed by step N won't match reality after step N has already executed.

---

## 2. Phase 1 — plan generation

**Inputs:**
- `HYGIENE_REPORT.md` (read from repo root in CC; pasted in CP)
- The repo state (read access in CC; descriptive context in CP)
- `cc-anti-patterns.md` (the fix-recipe library)
- `cc-environment-design-patterns.md` (the 7-layer placement framework — used to validate proposed fixes land in the correct mechanism)

**Procedure:**

1. **Confirm mode.** "REMEDIATE MODE — Phase 1 (plan generation). I'll read HYGIENE_REPORT.md and produce EXECUTION_PLAN.md for your review."

2. **Parse findings.** Read `HYGIENE_REPORT.md`. Extract each finding's: identifier (e.g., `F-1.1`), associated canonical reference (e.g., `§4.2`), severity (`high` / `medium` / `low`), affected file(s), evidence (the specific lines, files, or counts that support the finding).

3. **Look up fix recipe per finding.** For each finding, consult `cc-anti-patterns.md`. Each canonical-numbered entry has a `Fix:` line specifying the structural remediation (e.g., §4.2: "Trim to 2-3 essentials per cc-environment-design-patterns.md §8 ... Per-subagent MCP scoping ..."). Map the structural fix to concrete plan steps.

4. **Build per-finding step set.** Each step has: action type (see §5), target (file path), payload (action-type-specific content), validation (post-step verification — see §6).

5. **Resolve conflicts.** When two findings touch the same file, sequence the steps in dependency order. See §7 for conflict resolution rules. Surface unresolved conflicts in the plan summary for user decision.

6. **Validate proposed fixes against the 7-layer placement framework.** Each proposed step that adds or modifies CC governance content must land in the correct mechanism (CLAUDE.md / `.claude/rules/` / Skills / subagents / hooks / MCP / settings). Steps that propose to put enforcement in CLAUDE.md as preference, or path-specific rules in CLAUDE.md, are rejected and re-routed to the correct layer.

7. **Order steps.** Default ordering: pre-flight validation → high-severity findings first → low-blast-radius before high-blast-radius within severity → CHANGELOG entry as final step. Rebalance if dependency requires (e.g., create file X before edit file Y that references X).

8. **Construct EXECUTION_PLAN.md.** Per the schema at `schema/execution-plan.schema.json`. See §4 for the format.

9. **Write to repo.** In CC, write to `EXECUTION_PLAN.md` at repo root. In CP, output as a downloadable artifact and instruct user to save to repo root before invoking Phase 2.

10. **Surface plan summary.** One-paragraph summary: "Plan addresses N findings, modifies F files, creates C new files, adds H hooks, removes R items. Estimated diff size: ~L lines. Highest-impact findings: [F-1.1, F-12.1]. Conflicts requiring user decision: [list, or 'none']. Review EXECUTION_PLAN.md and respond with one of three approval forms — blanket ('execute'), fragmented ('execute steps 1, 2, 4'), or conditional ('execute medium-and-low risk') — to proceed to Phase 2, or describe changes you want." See §2.1 below for the full acceptance grammar.

11. **Halt.** Wait for explicit user acceptance. Phase 1 ends here.

**Output of Phase 1:** `EXECUTION_PLAN.md` (written to repo or surfaced as artifact) + plan summary in chat. **No repo mutation beyond writing the plan file itself.**

### 2.1 Acceptance forms

After Phase 1 surfaces the plan summary, the user accepts via one of three forms:

**Blanket approve.** Verbs: "execute," "execute all," "proceed," "apply the plan." Phase 2 walks every step in the plan.

**Fragmented approve.** Verbs combined with step references: "execute steps 1–3, skip step 4," "execute steps 1, 3, 5," "execute except step 4." Granularity is **step IDs.** Phase 2 walks only the approved steps; skipped steps are recorded in the final report with reason "deferred by user."

**Conditional approve.** Verbs combined with risk conditions: "execute all medium-and-low risk; halt on high-risk for review," "execute everything except high-risk." Granularity is **step-level `risk:` tags** (every step carries one — see schema). Phase 2 walks all steps matching the conditional, halting on steps that don't match (recorded as "deferred by conditional approval").

**Anti-condition.** Ambiguous responses do not parse to acceptance. Examples that DO NOT enter Phase 2:
- "looks good" without action verb
- "what about X" — that's a revision request, re-enter Phase 1
- "let me think about it" — explicit hold

The parser permissively interprets action-verb + step-reference combinations ("run 1–4," "do steps 1, 2, 3"). It does not infer acceptance from agreement language alone.

### 2.2 Critic-gate composition

The Skill composes with `rootnode-critic-gate` via the profile-level field `critic_gate_threshold: required | optional`.

**With `critic_gate_threshold: required`:** before each step, submit the step plan to critic-gate. Verdicts:
- APPROVE → execute step; run validation; continue.
- REQUEST_CHANGES → adjust step per findings; re-submit. Cap: 3 cycles. After 3 without APPROVE, halt and surface to user.
- REJECT → halt; surface to user; user decides override or accept halt.

**Critic-gate not installed AND `required`:** halt at Phase 2 entry. Do not silently downgrade.

**With `critic_gate_threshold: optional`:** the Skill prompts "critic-gate available — invoke for this step?" before each step (when critic-gate is installed); user choice per step. If critic-gate not installed and threshold is `optional`, REMEDIATE works alone.

The threshold name and semantics align with `rootnode-repo-hygiene` §11.1.

---

## 3. Phase 2 — execution

**Pre-condition:** Phase 1 has completed for this plan, the user has reviewed `EXECUTION_PLAN.md`, and the user has explicitly invoked Phase 2 (typically by saying "execute," "proceed," "apply the plan," or similar).

**Anti-condition:** if the user's response after Phase 1 is anything other than explicit acceptance, **do not enter Phase 2.** Examples of NOT-acceptance: "looks good" without "execute" — surface the ambiguity; "what about X" — that's a revision request, re-enter Phase 1; "let me think about it" — explicit hold.

**Procedure:**

1. **Confirm mode.** "REMEDIATE MODE — Phase 2 (execution). Walking the plan step-by-step. Halts on any validation failure."

2. **Run pre-flight validation.** Execute the plan's `pre_flight_validation` array. If any fails, halt and report. Do not proceed to step 1 of the plan.

3. **For each step in plan order:**
   - **3a.** Apply the action (`edit` / `create` / `delete` / `modify` / `run` — see §5).
   - **3b.** Run the step's `validation`. See §6 for validation grammar.
   - **3c.** If validation fails: halt. Report which step, which validation, the current repo state (what was completed before the halt), and the validation error. Do NOT auto-rollback in v1 (see §8).
   - **3d.** If validation passes: log step completion. Continue to next step.

4. **Run post-flight validation.** Execute the plan's `post_flight_validation` array. If any fails, halt and report. The repo is in a state where most of the plan ran but the final cross-cutting check failed.

5. **Append CHANGELOG entry.** Single entry summarizing the remediation cycle: which findings were addressed, which steps ran, any halts. The entry follows the change_log discipline (`cc-methodology-patterns.md` §5).

6. **Report results.** Steps approved / total (across blanket / fragmented / conditional approval), steps executed / approved, steps skipped (with `skip_reason` per step: `deferred by user`, `deferred by conditional approval`, or `halt-on-validation-failure`), critic-gate review summary if applicable (steps approved on first pass / approved after revision / rejected), files modified, files created, files deleted, hooks added, findings closed, any halts.

**Output of Phase 2:** actual repo changes + CHANGELOG entry + execution report in chat.

---

## 4. EXECUTION_PLAN.md format (and the schema reference)

The plan file is Markdown with a YAML front-matter block. The full schema is at `schema/execution-plan.schema.json` (JSON Schema draft-07). Below is the human-readable shape; see the schema for the authoritative spec.

```markdown
---
plan_id: <uuid or short identifier>
generated_at: <ISO-8601 timestamp>
generated_by: rootnode-cc-design v2.0
input_report: HYGIENE_REPORT.md
addresses_findings: [F-1.1, F-12.1, F-13.1, ...]
summary: |
  One-paragraph summary of what the plan does, suitable for the chat surface message.
estimated_diff_size_lines: <integer>
conflicts_requiring_user_decision: []
---

## Pre-flight validation
- check: file_exists path=HYGIENE_REPORT.md
- check: file_exists path=CLAUDE.md
- check: command_succeeds cmd="git status --porcelain | wc -l" expect_lt=10

## Steps

### Step 1 — <human-readable title>
**addresses_finding:** F-1.1 (§2.1 bloated CLAUDE.md / monolithic standing context)
**Action:** edit
**Target:** CLAUDE.md
**Payload:**
\`\`\`diff
- (lines 47-89 — multi-step procedure for adding API endpoints)
+ Procedure moved to .claude/skills/add-api-endpoint/SKILL.md (added in Step 4).
\`\`\`
**Validation:**
- check: file_lines path=CLAUDE.md max=200
- check: file_contains path=CLAUDE.md substring=".claude/skills/add-api-endpoint"
**On failure:** halt

### Step 2 — Extract API conventions to path-scoped rule
**addresses_finding:** F-9.1 (§4.9 path-scoped rules opportunity missed)
**Action:** create
**Target:** .claude/rules/api-conventions.md
**Payload:**
\`\`\`markdown
---
paths:
  - "src/api/**/*.ts"
---
# API conventions
- Use Result<T, E> for fallible operations; never throw.
- ...
\`\`\`
**Validation:**
- check: file_exists path=.claude/rules/api-conventions.md
- check: yaml_parses path=.claude/rules/api-conventions.md
**On failure:** halt

### Step 3 — Add verification hook
**addresses_finding:** F-13.1 (§4.11 verification-before-completion absent)
**Action:** modify
**Target:** .claude/settings.json
**Payload:**
\`\`\`json-pointer
op: add
path: /hooks/Stop
value:
  - command: ".claude/hooks/verify-tests.sh"
\`\`\`
**Validation:**
- check: json_parses path=.claude/settings.json
- check: json_path path=.claude/settings.json pointer=/hooks/Stop/0/command equals=".claude/hooks/verify-tests.sh"
**On failure:** halt

[... more steps ...]

### Step N — Append CHANGELOG entry
**Addresses:** all
**Action:** edit (or create if not exists)
**Target:** CHANGELOG.md
**Payload:** [entry per the change_log discipline]
**Validation:**
- check: file_contains path=CHANGELOG.md substring="<plan_id>"
**On failure:** halt

## Post-flight validation
- check: file_lines path=CLAUDE.md max=200
- check: command_succeeds cmd="bash .claude/hooks/verify-tests.sh" expect_exit=0
- check: command_succeeds cmd="git status --porcelain | wc -l" expect_gt=0
```

---

## 5. Action types

Five action types. Each has specific payload requirements (see schema for full spec).

| Action | Payload | Use for |
|---|---|---|
| `edit` | Diff (unified format), or old_str + new_str pair | Modify content within an existing file |
| `create` | Full file content | Create a new file |
| `delete` | (none — target path is sufficient) | Remove a file. **Note:** v1 does not preserve original content for rollback; use with caution. |
| `modify` | JSON-pointer or YAML-path operation (op + path + value) | Atomic structured-config changes (e.g., `.claude/settings.json`, `.mcp.json`) |
| `run` | Shell command | Side effects that aren't file mutations: `chmod +x`, `git init`, `mkdir -p`, etc. **Note:** restricted to allowlisted commands; arbitrary shell is not permitted in v1. |

**v1 allowlist for `run` action:** `chmod`, `mkdir`, `touch`, `git init`, `git add`, `git commit` (with message). Anything outside the allowlist is rejected at Phase 1; the user must restructure the step or accept the limitation.

---

## 6. Validation grammar

Validations are post-step assertions. Each validation is one of:

| Check | Arguments | Semantics |
|---|---|---|
| `file_exists` | `path` | The file at `path` exists |
| `file_not_exists` | `path` | The file at `path` does NOT exist (after a delete step) |
| `file_lines` | `path`, `max` and/or `min` | Line count is within bounds |
| `file_contains` | `path`, `substring` | The file contains the substring |
| `file_not_contains` | `path`, `substring` | The file does NOT contain the substring |
| `yaml_parses` | `path` | The file parses as valid YAML |
| `json_parses` | `path` | The file parses as valid JSON |
| `json_path` | `path`, `pointer`, `equals` | JSON-pointer query equals expected value |
| `command_succeeds` | `cmd`, `expect_exit` (default 0) | Command runs and exits with expected code |
| `command_output` | `cmd`, `contains` or `equals` | Command output matches |

Validations are evaluated in order. First failure halts the step.

---

## 7. Conflict resolution

When two findings produce steps that touch the same file, the steps must be sequenced. Default rules:

1. **Create-before-modify.** If finding A creates a file and finding B modifies it, A's step runs first.
2. **Trim-before-add.** If finding A trims content from a file and finding B adds content, A runs first (smaller diff to apply B against).
3. **Structural-before-stylistic.** Schema/config changes before formatting/lint changes.
4. **Lower-blast-radius first within severity.** A change to one line before a change to many.
5. **CHANGELOG entry last.** Always.

When the default rules can't sequence a conflict (e.g., two findings both modify CLAUDE.md lines 50-60 in incompatible ways), surface the conflict in the plan's `conflicts_requiring_user_decision` array. Phase 1 still produces a plan, but the conflicting steps are marked `requires_user_choice: true` and Phase 2 will halt at those steps for explicit choice.

---

## 8. Halt semantics (and what v1 does NOT do)

**v1 halt-on-failure semantics:** any step validation failure halts Phase 2 immediately. The repo is left in whatever state the completed steps produced. The user reviews and decides:
- Manually revert (using git or filesystem operations)
- Fix forward (resolve the validation failure manually, then optionally re-run the remaining steps)
- Re-plan (invoke Phase 1 again with the current state as the new starting point)

**v1 does NOT:**
- Auto-rollback completed steps on failure
- Snapshot file content before edits for restoration
- Wrap execution in a transaction
- Continue past a failed step

**Why:** safety-via-halt prioritizes the user's ability to inspect and decide over the convenience of automated cleanup. Auto-rollback is fragile (especially with the `run` action and external side effects); snapshotting is heavyweight; transactions are not natively supported by the filesystem operations CC uses.

**v2 candidates** (not in scope for v1):
- Pre-step content snapshots stored in `.claude/state/remediate-snapshots/<plan_id>/`
- Rollback action: `remediate rollback --plan <id>` walks completed steps in reverse
- Continue-on-failure mode: collect all failures rather than halting on first
- Dry-run mode: run validations only, don't apply actions

---

## 9. HYGIENE_REPORT.md input expectations

REMEDIATE expects `HYGIENE_REPORT.md` to be parseable. The format is owned by `rootnode-repo-hygiene`; this Skill consumes it. Required structural elements REMEDIATE looks for:

- A list of findings, each with:
  - Stable identifier (e.g., `F-1.1`)
  - Associated anti-pattern from the catalog by canonical reference (e.g., `§4.2`)
  - Severity (`high` / `medium` / `low`)
  - Affected file(s) (paths relative to repo root)
  - Evidence (the specific lines, files, or counts that support the finding)
- (Optional) per-finding suggested-fix hints from the hygiene Skill — REMEDIATE uses these as inputs to plan generation but its own placement-validation can override

If `HYGIENE_REPORT.md` doesn't exist or doesn't parse:
- In CC: halt Phase 1 with a clear message: "REMEDIATE requires HYGIENE_REPORT.md at repo root. Run rootnode-repo-hygiene first to generate it, then re-invoke."
- In CP (no repo access): allow the user to paste findings directly. Recommend the file-based workflow for repeatability, but accept the inline format for one-shot use.

**Coordination note:** as the rootnode-repo-hygiene Skill matures, the HYGIENE_REPORT.md format may evolve. REMEDIATE should accommodate format versions via a `report_version` field in the report's front-matter; v1 of REMEDIATE supports format v1.

---

## 10. CP-only invocation (without repo access)

When REMEDIATE is invoked in CP (chat interface, no repo file access), Phase 2 cannot execute — there's no repo to mutate. The CP-only flow:

1. User pastes findings (or HYGIENE_REPORT.md content) into the conversation.
2. Phase 1 runs normally and produces EXECUTION_PLAN.md as a downloadable artifact.
3. User saves the plan to their repo.
4. User invokes the Skill again, but in CC this time, with the saved plan visible.
5. Phase 2 runs in CC and executes the plan against the actual repo.

This is workable but adds friction. **Recommend CC-native invocation when possible** — in CC, both phases run in the same session against the actual files, eliminating the save-and-pivot step.

The CP-only flow is documented because design conversations sometimes happen in CP where the user wants to think through a remediation strategy before pivoting to CC for the actual changes. Don't over-engineer for it; the primary REMEDIATE surface is CC.

---

## End of REMEDIATE mode execution reference

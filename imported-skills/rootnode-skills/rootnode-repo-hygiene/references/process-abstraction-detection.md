# Process-Abstraction Detection (Cat 14 deep dive)

The differentiating value of this Skill. Detection signals, candidate output structure, scope categorization rules, routing for methodology-generalizable candidates, and worked examples from production validation.

**Canonical source:** `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6` — the rootnode runtime tooling catalog. Methodology-generalizable candidates queue as future entries here.

This file applies the canonical content to detection. Process-abstraction is the highest-value scan because generic linters cannot do it — recognizing that "Claude does X manually each session" is a process to lift requires understanding what work patterns CC environments accumulate.

---

## What process-abstraction detection is for

CC environments accumulate work patterns. The first time Claude does something, it's bespoke session work. The third time, it's a recurring operation. The tenth time, it's a tax — context spent re-deriving state, re-running permission gymnastics, re-walking multi-step sequences that have a single deterministic answer.

Cat 14 finds these patterns and surfaces them as abstraction candidates: lift the work from "Claude does it manually each session" to a deterministic mechanism (script, Skill, hook, subagent, MCP server). The mechanism runs once per invocation; Claude reads the result.

The framing matters: this is not generic optimization. It's specifically about **token-load abstraction** — the work being lifted is work that consumed Claude's context budget each session and now consumes near-zero.

---

## Five detection signals

### Signal 1 — Recurring operations in change_log

Scan change_log entries (or equivalent retrospective files) for the same shape of work appearing in 3+ entries.

**Examples:**
- "ran tests, fixed N failures, re-ran tests, all green" — appearing across multiple session closeouts.
- "updated state snapshot in CLAUDE.md (test count: X → Y)" — appearing weekly.
- "regenerated derived artifact X from source Y" — appearing every time source Y changes.

**Threshold.** 3+ entries with the same shape, within the project's recent work period (last 90 days for a steady project; last 30 for an active project).

### Signal 2 — Permission patterns

Scan `.claude/settings.local.json` for multiple permission entries covering the same operation family.

**Examples:**
- `Bash(python tests/*)`, `Bash(python -m pytest*)`, `Bash(python tests/test_*.py*)` — three permissions for what one wrapper script could expose as a single permission.
- `Bash(git log --oneline*)`, `Bash(git log -<N>*)`, `Bash(git log --pretty=*)` — three permissions for a unified `git log` invocation pattern.

**Threshold.** 2+ permissions covering the same operation family, where a wrapper script or subcommand consolidation would reduce the count.

### Signal 3 — Repeated multi-step sequences in session_closeouts

Scan session_closeouts (or equivalent retrospective files) for "ran X then Y then Z" sequences appearing across multiple sessions.

**Examples:**
- "ran lint, fixed lint issues, ran tests, fixed test failures, ran build, committed."
- "regenerated catalog, validated catalog against schema, updated CLAUDE.md catalog reference, committed catalog update."

**Threshold.** Same sequence of 3+ steps, 3+ sessions.

### Signal 4 — Deterministic state queries CC re-derives

Scan change_log and CLAUDE.md state sections for queries that have a single-source-of-truth answer but get re-derived each session.

**Examples:**
- "what's the current test count" — derivable from `npm test --silent | grep '<N> passing'`.
- "what was the last fix shipped" — derivable from `git log -1 --pretty='%s'`.
- "which Skills are present" — derivable from `ls .claude/skills/`.

**Threshold.** Query gets re-derived 3+ times. The derivation is deterministic (same input → same output).

### Signal 5 — Hooks wrapping manual operations

Scan existing hooks for ones that fire and then prompt the user (or Claude) to do a manual step. The manual step is the abstraction candidate — the hook detected the need but didn't complete the loop.

**Examples:**
- A PostToolUse hook that fires after edit and prints "remember to run tests" — the test run itself is the abstraction candidate.
- A Stop hook that fires at session close and prints "remember to update change_log" — the change_log update is the abstraction candidate.

**Threshold.** Any hook that ends in a manual prompt rather than a completed action.

---

## Candidate output structure

Each candidate gets all eight fields:

```
F-14.{n}  [scope: project-local | methodology-generalizable]
  candidate_name: <short descriptive name>
  current_cc_pattern: <what CC does today; rough token estimate per invocation>
  proposed_abstraction: <script | Skill | hook | subagent | MCP>
  estimated_savings_per_invocation: <token delta>
  estimated_invocations_per_month: <from change_log frequency or signal data>
  complexity: <trivial | moderate | substantial>
  prerequisites: <what must exist before the abstraction is buildable>
  scope: <project-local | methodology-generalizable>
```

**Field semantics:**

- `candidate_name` — 3–6 words, descriptive enough to disambiguate. Avoid generic names like "test runner" — prefer "current-test-count state query."
- `current_cc_pattern` — what CC does today, with a rough token estimate per invocation. Example: "Claude reads test output, parses pass/fail counts, formats summary string into CLAUDE.md state section. ~800 tokens per invocation."
- `proposed_abstraction` — the mechanism that should replace the manual pattern. Choices: `script` (shell or Python wrapper), `Skill` (multi-step procedure), `hook` (lifecycle guarantee), `subagent` (focused specialist with isolated context), `MCP` (external integration).
- `estimated_savings_per_invocation` — token delta between current and abstracted. Order-of-magnitude is fine; precision is not the point.
- `estimated_invocations_per_month` — derived from the signal data (change_log frequency, session closeout count). Provides the "is this worth building" signal.
- `complexity` — `trivial` (under an hour to build), `moderate` (one work session), `substantial` (multi-session build).
- `prerequisites` — what must exist before the abstraction is buildable. Example: "test command must be standardized across sub-projects" or "permission to run subprocess must be granted in settings."
- `scope` — `project-local` or `methodology-generalizable` (decision rules below).

---

## Scope categorization (D8)

The `scope` field is the highest-leverage tag in the candidate output. It determines downstream routing.

### `project-local`

The pattern is specific to this project's data, paths, or workflows. Lifting it produces value here but doesn't transfer to other projects.

**Examples:**
- A wrapper script that consolidates this project's specific test commands.
- A Skill that orchestrates this project's specific deployment sequence.
- A subagent specialized for this project's specific data shape.

**Routing.** Project-local candidates flow into the user's local backlog. The user builds (or doesn't) the abstraction within this project.

### `methodology-generalizable`

The pattern recurs across projects of similar shape (CC environments, hygiene work, prompt engineering work, etc.). Lifting it produces value here AND queues it as a candidate for the shared tooling roadmap (`root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`).

**Examples:**
- A state-query script that reads "current test count" — every CC engine with tests benefits.
- A CLAUDE.md snapshot auto-update mechanism — every CC environment with a state snapshot pattern benefits.
- A subagent registry pattern — every CC environment with multiple subagents benefits.

**Routing.** Methodology-generalizable candidates surface as a recommendation in the report's "Routing recommendations" section. The user decides whether to:
- Act on the candidate locally first (build a project-specific version, validate, then promote)
- Route directly to shared tooling consideration (build once at the rootnode runtime tooling level)
- Defer the candidate (queue but don't act)

### Decision rules

A candidate is `methodology-generalizable` when at least one of the following holds:

1. **Generic description test.** The pattern can be described without referencing project-specific identifiers, paths, or data shapes.
2. **Cross-project recurrence test.** The same pattern has been observed in another project the user has worked on.
3. **Generic discipline test.** The pattern matches a generic CC discipline: state-snapshotting, test-result-summarization, permission consolidation, change_log automation, session-handoff structuring.

When none of these hold, default to `project-local`. Marking too many candidates as methodology-generalizable inflates the shared-tooling backlog with low-leverage entries.

---

## Routing for methodology-generalizable candidates

Methodology-generalizable candidates are themselves the warrant evidence for promoting work into the runtime tooling catalog. The candidate output structure is **the handoff brief format** consumed by `rootnode-skill-builder` v2's Gate 2 exception clause: when the user provides a process-abstraction brief from this Skill, Gate 2 passes automatically.

**Format compatibility.** The 8-field candidate format provides what skill-builder v2 needs to satisfy Gate 2:
- The `current_cc_pattern` and `estimated_invocations_per_month` fields are the warrant evidence (recurrence + frequency).
- The `proposed_abstraction` field is the mechanism decision input for skill-builder's Gate 1 (decomposition check).
- The `prerequisites` and `complexity` fields scope the build.
- The `scope: methodology-generalizable` tag is the qualifying flag.

**Handoff procedure.** When the user accepts a methodology-generalizable candidate for shared-tooling promotion:
1. Extract the candidate's full 8-field block from the report.
2. Save as a standalone file (typical naming: `{code}_process_abstraction_handoff_{slug}.md`, per User Preferences file-prefixing convention).
3. Upload that file to the conversation invoking `rootnode-skill-builder` v2 (or whichever tooling-build pathway is being used).

The handoff brief format is owned by THIS Skill (Cat 14 candidate format). Downstream consumers (skill-builder v2, future runtime tooling) consume the format. If the format evolves, the change lives here and propagates downstream.

---

## Examples from production validation

The production CC deployment sweep run on 2026-05-04 surfaced 5 Cat 14 candidates. Anonymized examples below illustrate the scope tag application.

### Example 1 — F-14.1: state-query script

```
F-14.1  [scope: methodology-generalizable]
  candidate_name: current-state-query script
  current_cc_pattern: Claude reads test output + git log + skill inventory each session,
    parses values, updates CLAUDE.md state snapshot. ~1200 tokens/invocation.
  proposed_abstraction: script
  estimated_savings_per_invocation: ~1100 tokens (script returns formatted state block)
  estimated_invocations_per_month: ~12 (one per active session)
  complexity: trivial
  prerequisites: test command standardized; git installed; bash available
  scope: methodology-generalizable
```

Rationale for `methodology-generalizable`: every CC engine with a state-snapshot pattern benefits; the script itself is data-shape-agnostic.

### Example 2 — F-14.4: CLAUDE.md snapshot auto-update

```
F-14.4  [scope: methodology-generalizable]
  candidate_name: CLAUDE.md snapshot auto-update hook
  current_cc_pattern: Claude regenerates Engine state snapshot section manually
    on session close, prompted by closeout discipline. ~600 tokens/invocation.
  proposed_abstraction: hook (Stop)
  estimated_savings_per_invocation: ~600 tokens
  estimated_invocations_per_month: ~10
  complexity: moderate
  prerequisites: state-query script (F-14.1) shipped; CLAUDE.md sentinel
    markers in place around state section
  scope: methodology-generalizable
```

Rationale: the hook depends on the state-query script (prerequisite) but is itself generic — every CC environment with a snapshot section benefits.

### Example 3 — F-14.3: per-instance audit harness consolidation

```
F-14.3  [scope: project-local]
  candidate_name: per-instance audit harness consolidation
  current_cc_pattern: Claude walks per-instance audit data structures across
    three project-specific data files, computes summary metrics manually.
    ~2000 tokens/invocation.
  proposed_abstraction: script
  estimated_savings_per_invocation: ~1900 tokens
  estimated_invocations_per_month: ~4
  complexity: moderate
  prerequisites: the three data file schemas remain stable
  scope: project-local
```

Rationale for `project-local`: the data files and schema are specific to this project's audit work; the script wouldn't transfer.

### Example 4 — F-14.5: subagent registry

```
F-14.5  [scope: methodology-generalizable]
  candidate_name: subagent registry generator
  current_cc_pattern: Claude lists subagents from .claude/agents/ each session,
    summarizes scope per agent. ~400 tokens/invocation.
  proposed_abstraction: script
  estimated_savings_per_invocation: ~400 tokens
  estimated_invocations_per_month: ~8
  complexity: trivial
  prerequisites: subagent definitions follow consistent frontmatter convention
  scope: methodology-generalizable
```

Rationale: every CC environment with multiple subagents benefits.

### Example 5 — F-14.2: permission consolidation

```
F-14.2  [scope: project-local trivial — covered by Cat 2]
  candidate_name: pytest permission consolidation
  current_cc_pattern: 3 permission entries cover the same pytest invocation family
  proposed_abstraction: settings consolidation (no script)
  estimated_savings_per_invocation: ~50 tokens (smaller permission schema)
  estimated_invocations_per_month: per-session
  complexity: trivial
  prerequisites: none
  scope: project-local
```

Rationale: this is small enough that the executable Cat 2 finding will cover it; Cat 14 surfaces it for completeness but doesn't add work.

---

## Cat 14 extension pass (deep-audit profile)

When the active profile has `cat_14_extension_pass: true` (the `deep-audit` profile sets this), Cat 14 runs an extra pass after the main scan:

1. **Cross-candidate dependency analysis.** Look at prerequisites across surfaced candidates. Surface dependency chains (e.g., F-14.4 depends on F-14.1) so the user can see which candidates unlock which.
2. **Order-of-build recommendation.** Among the candidates, recommend an order based on complexity, frequency, and dependency. Lower-complexity + higher-frequency + no-prerequisites first.
3. **Build-this-first single recommendation.** Pick one candidate as the "build this first" answer if the user wants to act on Cat 14 immediately. Default heuristic: trivial complexity + methodology-generalizable + 5+ invocations/month.

The extension pass is opt-in because it consumes additional context and is only worth running when the user is treating Cat 14 as the primary actionable surface (typical for `deep-audit`).

---

*End of process-abstraction detection. Runtime tooling catalog: `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §6`. Compatible handoff format consumer: `rootnode-skill-builder` v2 Gate 2 exception clause.*

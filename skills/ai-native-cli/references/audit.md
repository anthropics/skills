---
name: audit
description: >
  Audit a CLI against the Agent-Friendly CLI Spec. Takes a CLI name,
  runs it with various inputs, and produces a structured compliance report.
  Use when you need to verify a CLI meets the spec before certification.
---

# CLI Spec Audit Protocol

You are auditing a CLI tool against the Agent-Friendly CLI Spec v0.1.
Follow this protocol exactly. Use Bash to call the CLI, Read/Glob to check files.

## Input

User provides: `<cli>` — the CLI command name or path.
Optional: `--layer <core|recommended|ecosystem>` to limit scope.
Optional: `--priority <p0|p1|p2>` to limit scope.

## Step 1: Discovery

Run these commands and record the results:

```bash
<cli> --help
<cli> --brief
<cli> --version
```

From `--help` output, extract:
- List of commands (name + description)
- Which commands are destructive (delete/remove/destroy/drop/purge)
- Which commands accept parameters (and which params are required)
- Whether output is JSON

Also check:
```bash
ls <cli-project-root>/agent/
ls <cli-project-root>/agent/rules/
ls <cli-project-root>/agent/skills/
ls <cli-project-root>/AGENTS.md
```

Save all discovery results. You'll reference them throughout the audit.

## Step 2: Audit by Dimension

Work through each dimension in order. For each rule:
- Run the check described
- Record: `pass`, `fail`, or `skip` (with reason)
- On `fail`, record the evidence (actual output) and suggestion

### Dimension 01: Discoverability (D1-D18)

**D1 [P1] --help outputs structured JSON with commands[]**
→ Check: `<cli> --help` output parses as JSON and has `commands` array.

**D3 [P1] Schema has required fields**
→ Check: --help JSON has `help` (string) and `commands` (array) fields.

**D4 [P1] All parameters have type declarations**
→ Check: In --help JSON, every item in `commands[].parameters[]` has a `type` field.

**D7 [P1] Parameters annotated as required/optional**
→ Check: Every parameter has a `required` field (boolean).

**D9 [P1] Every command has a description**
→ Check: Every item in `commands[]` has a non-empty `description`.

**D11 [P1] --help JSON includes help, rules, skills, commands**
→ Check: --help JSON has all four top-level keys.

**D12 [P1] agent/brief.md exists**
→ Check: File exists at `<project-root>/agent/brief.md`.

**D13 [P1] agent/rules/ has trigger.md, workflow.md, writeback.md**
→ Check: All three files exist.

**D15 [P1] --brief outputs agent/brief.md content**
→ Check: `<cli> --brief` output matches content of `agent/brief.md`.

**D16 [P1] Default is JSON, --human for human-friendly**
→ Check: `<cli> <any-command>` outputs JSON. `<cli> <any-command> --human` outputs non-JSON.

**D17 [P1] agent/rules/*.md have YAML frontmatter (name, description)**
→ Check: Read each file, verify frontmatter has both fields.

**D18 [P1] agent/skills/*.md have YAML frontmatter (name, description)**
→ Check: Read each file, verify frontmatter has both fields.

**D2 [P2] Per-command help available**
→ Check: `<cli> <command> --help` returns structured info for at least one command.

**D5 [P2] Enum parameters list allowed values**
→ Check: Any enum-type parameter has `enum` or `allowed_values` field.

**D6 [P2] Parameters have default values documented**
→ Check: Parameters with defaults have a `default` field.

**D8 [P2] --help includes output schema**
→ Check: Commands have `output_schema` or similar field.

**D10 [P2] --version outputs semver**
→ Check: `<cli> --version` output matches semver pattern `X.Y.Z`.

**D14 [P2] agent/skills/ directory + skills subcommand**
→ Check: Directory exists and `<cli> skills` returns a list.

### Dimension 02: Output (R1-R3, O1-O10)

**R1 [P1] Every response includes rules[]**
→ Check: Run any normal command, check JSON output has `rules` array.

**R2 [P1] Every response includes skills[]**
→ Check: Same output has `skills` array.

**R3 [P1] Every response includes issue**
→ Check: Same output has `issue` string.

**O1 [P0] Default output is JSON**
→ Check: `<cli> <command>` (no flags) outputs valid JSON.

**O2 [P0] JSON passes jq validation**
→ Check: Pipe output through `jq .` — must exit 0.

**O3 [P0] JSON schema stable within version**
→ Check: Run same command twice, compare top-level keys. Must match.

**O4 [P2] --fields for field filtering**
→ Check: `<cli> <command> --fields id,name` returns only those fields.

**O5 [P2] Empty result returns [], not error**
→ Check: Run a list command that returns no results. Must get `[]` or `{"result":[]}`, not an error.

**O6 [P2] --human flag for human-friendly output**
→ Check: `<cli> <command> --human` outputs non-JSON formatted text.

**O7 [P2] Multiple results in JSON array**
→ Check: List command returns array, not single object.

**O8 [P2] Pagination includes total/page/has_more**
→ Skip if CLI has no pagination. Otherwise check those fields.

**O9 [P2] NDJSON for streaming**
→ Skip if not applicable. Otherwise check each line is valid JSON.

**O10 [P2] Auto-detect TTY**
→ Check: Pipe `<cli> <command> | cat` — must get JSON even without --agent flag.

### Dimension 03: Error (E1-E8)

**E1 [P0] Errors → structured JSON to stderr**
→ Check: Trigger an error (e.g. invalid command), capture stderr, verify JSON with `error`, `code`, `message` fields.

**E4 [P0] Error has machine-readable code**
→ Check: Error JSON `code` field exists and is a string like `MISSING_REQUIRED`.

**E5 [P0] Error has human-readable message**
→ Check: Error JSON `message` field exists and is non-empty.

**E7 [P0] Never enter interactive mode on error**
→ Check: Trigger error, verify CLI exits immediately (doesn't hang).

**E8 [P0] Error codes are stable API contracts**
→ Check: Trigger same error twice, verify `code` is identical.

**E6 [P1] Error includes suggestion field**
→ Check: Error JSON has `suggestion` field.

**E2 [P2] All errors go to stderr**
→ Check: On error, stdout is empty, stderr has the error JSON.

**E3 [P2] Error JSON is valid JSON**
→ Check: Parse error stderr output with jq.

### Dimension 04: Input (I1-I9)

**I1 [P1] All flags use --long-name format**
→ Check: In --help JSON, all parameter names use `--kebab-case`.

**I2 [P1] No positional argument ambiguity**
→ Check: Commands don't rely on positional arg order for different meanings.

**I4 [P1] Missing required param → structured error**
→ Check: Call a command missing a required param. Must get structured error, not a prompt.

**I5 [P1] Type mismatch → exit 2 + structured error**
→ Check: Pass wrong type (string where number expected). Must exit 2.

**I8 [P1] No implicit state**
→ Check: --help doesn't reference hidden state files that change behavior.

**I9 [P1] Non-interactive auth**
→ Check: If auth is needed, it's via flag/env, not interactive prompt.

**I3 [P2] --json-input for batch operations**
→ Check: `echo '{"items":[...]}' | <cli> <command> --json-input` works.

**I6 [P2] Boolean flags explicit: --verbose / --no-verbose**
→ Check: Boolean params in schema have --no-X counterpart.

**I7 [P2] Array params: --tag a --tag b**
→ Check: Array-type params accept repeated flags.

### Dimension 05: Safety (S1-S8)

**S1 [P1] Destructive ops require --yes**
→ Check: Run destructive command WITHOUT --yes. Must reject (non-zero exit).

**S4 [P1] Reject path traversal**
→ Check: Pass `../../etc/passwd` as a path-type argument. Must reject.

**S8 [P1] --sanitize flag for external input**
→ Check: --help schema mentions --sanitize flag.

**S2 [P2] Destructive default deny**
→ Check: Same as S1, verify error message mentions --yes.

**S3 [P2] --dry-run previews without executing**
→ Check: `<cli> <command> --dry-run` exits 0 without side effects.

**S5 [P2] CLI must not auto-update itself**
→ Check: No `update` or `self-update` command in --help.

**S6 [P2] Schema marks destructive commands**
→ Check: --help JSON `commands[]` has `destructive: true` on delete-type commands.

**S7 [P2] --quiet doesn't skip --yes requirement**
→ Check: Destructive command with `--quiet` but no `--yes` still fails.

### Dimension 06: Exit Code (X1-X9)

**X3 [P0] Parameter/usage errors exit 2**
→ Check: Pass invalid flag. Must exit 2.

**X9 [P0] Failures exit non-zero**
→ Check: Trigger any failure. Exit code must not be 0.

**X1 [P1] 0 = success**
→ Check: Successful command exits 0.

**X2 [P2] 1 = general error**
**X4 [P2] 10 = auth failure**
**X5 [P2] 11 = permission denied**
**X6 [P2] 20 = resource not found**
**X7 [P2] 30 = conflict/precondition**
→ Check: If you can trigger these error types, verify the exit code matches.

**X8 [P2] Exit code corresponds to JSON error code**
→ Check: Error JSON `code` and process exit code are semantically consistent.

### Dimension 07: Composability (C1-C7)

**C1 [P0] stdout is for data ONLY**
→ Check: Successful command stdout contains only JSON data, no logs or warnings.

**C2 [P0] Logs, progress, warnings go to stderr ONLY**
→ Check: Any non-data output (if present) goes to stderr.

**C6 [P1] No interactive prompts in pipe mode**
→ Check: Pipe input to the CLI (`echo | <cli> <command>`), must not hang.

**C3 [P2] stdout can be piped**
→ Check: `<cli> list | jq .` works.

**C4 [P2] --quiet suppresses non-essential stderr**
→ Check: `<cli> <command> --quiet 2>/dev/null` produces less stderr.

**C5 [P2] Upstream output feeds downstream input**
→ Check: If --json-input exists, test pipe chain.

**C7 [P2] Idempotent**
→ Check: Run same read command twice, compare output.

### Dimension 08: Naming (N1-N6)

**N4 [P1] Reserved flags present**
→ Check: --help schema supports --agent, --human, --brief, --help, --version, --yes, --dry-run, --quiet, --fields.

**N1 [P2] Consistent verb/noun pattern**
→ Check: All commands follow same pattern (e.g., all `noun verb` or all `verb noun`).

**N2 [P2] Flags use kebab-case**
→ Check: No camelCase or snake_case flags in schema.

**N3 [P2] Max 3 command levels**
→ Check: No command deeper than `cli level1 level2`.

**N5 [P2] --version outputs semver**
→ Same as D10.

**N6 [P2] --version exists**
→ Check: `<cli> --version` doesn't error.

### Dimension 09: Meta (M1-M3)

**M1 [P2] AGENTS.md at project root**
→ Check: File exists.

**M2 [P2] MCP tool schema export**
→ Check: `<cli> --mcp-schema` or similar exists. Skip if not applicable.

**M3 [P2] Changelog marks breaking changes**
→ Check: CHANGELOG.md exists and mentions breaking changes if any.

### Dimension 10: Feedback (F1-F8)

**F1 [P2] issue subcommand exists**
→ Check: `<cli> issue --help` or `<cli> issue list` works.

**F2 [P2] Structured submission**
→ Check: `<cli> issue create --type bug --message "test"` returns structured JSON.

**F3 [P2] Categories: bug/requirement/suggestion/bad-output**
→ Check: --type accepts all four values.

**F4 [P2] Issues stored locally**
→ Check: After creating an issue, a file appears in the issues directory.

**F5 [P2] issue list / issue show queryable**
→ Check: Both commands return JSON.

**F6 [P2] Issues have status tracking**
→ Check: `<cli> issue transition <id> --status in-progress` works.

**F7 [P2] Issue JSON has required fields**
→ Check: id, type, status, message, created_at, updated_at all present.

**F8 [P2] All issues have status field**
→ Check: Every issue in `issue list` has `status`.

### Dimension 11: Guardrails (G1-G9)

**G1 [P1] Unknown flags rejected with exit 2**
→ Check: `<cli> <command> --nonexistent-flag-xyz` exits 2.

**G2 [P1] Detect API key patterns, reject**
→ Check: Pass `sk-abc123secretkey456789012345678901` as an argument value. Must reject.

**G3 [P1] Reject sensitive file paths**
→ Check: Pass `.env` or `id_rsa.key` as a file argument. Must reject.

**G6 [P1] Precondition checks**
→ Check: If a command needs preconditions (e.g., config exists), missing precondition → structured error.

**G8 [P1] Reject shell metacharacters**
→ Check: Pass `; rm -rf /` or `$(whoami)` as argument value. Must reject.

**G9 [P1] Fail-closed**
→ Check: If guardrail logic itself errors, CLI denies rather than allows.

**G4 [P2] Operation whitelist**
→ Check: --help schema has permission/scope annotations.

**G5 [P2] Output redacts PII**
→ Check: If output contains emails/phones, they should be masked.

**G7 [P2] Batch limits**
→ Check: If batch operations exist, there's a max limit.

## Step 3: Progress Reporting

After completing each dimension, report a progress line:

```
[03/11] Error: 5/8 pass, 2 fail (E6, E3), 1 skip (E8)
```

## Step 4: Final Report

After all dimensions are checked, produce a summary:

```markdown
# Audit Report: <cli-name>

## Summary
- Total rules: <N>
- Pass: <N>  Fail: <N>  Skip: <N>
- Certification: <Agent-Friendly | Agent-Ready | Agent-Native | None>

## By Dimension
| Dimension | Pass | Fail | Skip |
|-----------|------|------|------|
| Discoverability | ... | ... | ... |
| Output | ... | ... | ... |
| ... | ... | ... | ... |

## Failures
| Rule | Evidence | Suggestion |
|------|----------|------------|
| E6 | Error output missing `suggestion` field | Add `suggestion` key to error JSON |
| ... | ... | ... |

## Certification Gate
- core (Agent-Friendly): <pass/fail> — <N>/<total> rules
- + recommended (Agent-Ready): <pass/fail> — <N>/<total> rules
- + ecosystem (Agent-Native): <pass/fail> — <N>/<total> rules
```

## Notes

- If a rule cannot be tested (e.g., no destructive commands exist), mark it `skip` with reason.
- For behavioral checks, always capture both stdout and stderr separately: `<cli> cmd 2>/tmp/stderr.txt`
- Prefer testing with real commands from --help, not made-up command names.
- If the CLI has a test/sandbox mode, use it for destructive operation testing.
- Time-box: if a command hangs for more than 5 seconds, kill it and mark the relevant rule as `fail` (likely E7/C6 violation).

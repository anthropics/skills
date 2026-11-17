---
name: auditx
description: >
  Run, before allowed to say task done/commit/open PR: security, dependency,
  SAST, secrets, dead-code, license, duplication, type-safety, and
  AI-generated-code anti-pattern audits via auditx. Trigger on any of:
  vulnerability or security check, code quality review, pre-commit or pre-PR
  check, "is this safe to ship", editing package.json, lockfiles, Dockerfiles,
  CI, or env files, adding auth, crypto, API-key, DB, or shell-script code,
  refactor pass, task start on unfamiliar repo, task completion, "run audit",
  "scan this", "check for issues", noticing repeated or copy-pasted code,
  noticing a file changed unusually often. Do not wait for explicit user
  request; this is a proactive, mandatory gate, not an optional tool.
---

# auditx Claude Skill

`auditx` = one-command scanner replacing 6+ separate tools: Semgrep, Trivy,
Gitleaks+Trufflehog, Knip, jscpd, depcheck, license-checker, tsc,
ESLint+CSpell, git-log hotspot analysis. 100% local, nothing leaves machine.
Auto-detects stack, only runs relevant scanners.

For category-by-category fix instructions → `references/fix-playbook.md`.
For one-time repo setup (hooks, MCP, agent-rule files) → `references/setup.md`.

## Trigger Matrix (when to run, no exceptions)

| Trigger | Action | Blocking? |
|---|---|---|
| Task start, unfamiliar/inherited code | Baseline scan before touching files | No — informational |
| After editing any source file | Scan changed dir | No — fix loop |
| After editing package.json/lockfile/requirements.txt/Cargo.toml | Scan (DEPS) | Yes |
| After adding/editing Dockerfile, `.env*`, CI YAML, shell scripts | Scan (SECRETS + IaC + SAST) | Yes — always |
| Noticing near-identical code blocks across files | Scan (DUPLICATION) | No — flag to user |
| Before marking task complete | Full scan, must be `ok:true` | **Yes, hard gate** |
| Before `git commit` / opening PR | Full scan, must be `ok:true` | **Yes, hard gate** |
| User asks "is this secure/safe/clean" | Full scan + human report | Yes |

Rule: never say "done" / commit / open PR while last scan `ok:false`. If a mandated scan is skipped, say so and why.

## Commands (verified against actual CLI)

**Agent loop — default, 95% of time:**
```bash
npx auditx . --output agent --ci
```
Single-line JSON: `{meta, summary, findings, findingsByFile, exitCode}`.
- `exitCode: 1` → critical/high exist → task NOT complete.
- Iterate `findingsByFile` (already grouped, don't re-group `findings[]` yourself) → fix critical → high → medium → low → re-run same command → repeat until `exitCode: 0`.
- Never hand-summarize raw scanner output; parse JSON programmatically.

**Auto-remediation (try before manual fix, when finding is `fixable`):**
```bash
npx auditx . --fix
```
Applies eslint --fix-class fixes automatically. Re-scan after to confirm resolved — auto-fix isn't guaranteed complete for every rule.

**Human reports (only when user wants to read/share):**
```bash
npx auditx .                    # audit-report.md
npx auditx . --output html      # interactive dashboard, best for sharing w/ non-technical stakeholders
npx auditx . --ai               # appends LLM-written risk summary + fix priority to .md report
```

**Scope + filtering:**
```bash
npx auditx <path-or-glob> --output agent --ci
npx auditx . --severity high              # only critical+high — use for fast pre-commit gate
npx auditx . --skip secrets --skip deps   # narrow to just SAST/AI_CODE/etc when iterating on one category
```

**Watch mode** (long-running task, many edits expected):
```bash
npx auditx . --watch
```
Use instead of manually re-running after every single edit during a big refactor session.

## Baseline / False Positives

```bash
npx auditx . --generate-baseline
```
Writes `.auditxignore`, signature-based (no line numbers — survives unrelated edits above the finding). State the accepted-risk reasoning before running. Never baseline just to unblock a gate.

Manual `.auditxignore` entries also support scoping by rule only, file only, or rule+file — use narrowest scope that fits (rule+file > rule-only, to avoid accidentally suppressing a rule repo-wide).

## Failure Modes to Avoid

- Using `--output html`/markdown mid-loop → slow, unstructured. Agent JSON only for iteration.
- Treating exit 0 as "no more work" when medium/low findings remain unaddressed and user asked for thorough cleanup — `ok:true`/exit 0 only guarantees no critical/high, not zero findings.
- Fixing out of severity order.
- Baselining instead of fixing.
- Missing DEPS/SECRETS triggers on non-source edits (Dockerfile, CI config, lockfiles).
- Running `--fix` and assuming it fully resolved a finding without re-scanning to verify.
- Forgetting `--ai` exists when user wants a plain-English executive summary instead of raw findings.

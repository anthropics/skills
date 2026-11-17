---
name: ci-yaml
description: Generate or audit GitHub Actions workflow YAML files for Python and Node.js projects. Use when the user asks to write, review, refactor, or improve a `.github/workflows/*.yml` file — for example "create a CI workflow for this project", "review my ci.yml", "why is my CI slow", "is this workflow secure". Detects the project's package manager (pip, uv, poetry, npm, pnpm, yarn) from manifest and lock files, applies a 30+ rule audit covering security (action pinning, permissions, secret handling), performance (caching, concurrency, timeouts), and correctness (matrix testing, deprecated APIs, action major-version pins). Distinct from runtime debugging skills that read `gh run` logs — this skill operates on the YAML source.
license: Apache-2.0
metadata:
  author: r0bin2u
  version: "0.1.0"
---

# CI YAML — Author and Audit GitHub Actions Workflows

## What this skill does

Two modes, picked from the user's request:

| Mode | Trigger phrasing | Output |
|------|------------------|--------|
| **Generate** | "write/create/scaffold a CI workflow for this project" | A new `.github/workflows/ci.yml` tailored to the detected stack |
| **Audit** | "review/audit/improve/check my CI workflow", or paths like `.github/workflows/*.yml` mentioned | A prioritized findings list with rule citations and concrete diffs |

If the request is ambiguous, **inspect the repo first** — if `.github/workflows/` exists, default to Audit; otherwise default to Generate.

---

## Decision tree

```
User request → does .github/workflows/*.yml exist?
    │
    ├─ Yes → AUDIT mode (default)
    │         │
    │         └─ User explicitly says "rewrite from scratch"? → also generate
    │
    └─ No  → GENERATE mode
              │
              ├─ Detect project type (see "Project detection")
              ├─ Pick template from references/templates/
              ├─ Adapt to project specifics (versions, lock file, lint tool)
              └─ Write to .github/workflows/ci.yml + show diff
```

---

## Generate mode

### 1. Project detection

Read these files in order; the first that exists wins:

| File | Stack | Sub-tooling check |
|------|-------|-------------------|
| `pyproject.toml` | Python | Look for `[tool.uv]` / `uv.lock` → uv. `[tool.poetry]` → poetry. Otherwise → pip. |
| `requirements.txt` (no pyproject) | Python (legacy pip) | — |
| `package.json` | Node.js | `pnpm-lock.yaml` → pnpm. `yarn.lock` → yarn. `package-lock.json` → npm. |
| `Cargo.toml` | Rust | — (not yet templated; see "Out of scope") |
| `go.mod` | Go | — (not yet templated) |

**If multiple detected** (e.g., a polyglot repo with both `pyproject.toml` and `package.json`), ask the user which one to scaffold for, or generate one workflow file per stack.

### 2. Version matrix selection

- **Python**: read `requires-python` in `pyproject.toml`. Pick all stable minor versions in range. Example: `>=3.10` on a project as of 2026 → matrix `["3.10", "3.11", "3.12", "3.13"]`. **Cap at 4 versions** (cost vs coverage trade-off).
- **Node.js**: read `engines.node` in `package.json` if present, otherwise default to `["20", "22"]` (current LTS pair). **Cap at 3 versions**.
- **Rust**: stable + the MSRV declared in `Cargo.toml`'s `rust-version` field, if present.

### 3. Template adaptation

Load the appropriate template from `references/templates/` (see that directory for the canonical, audited yaml). Substitute:

- The detected python/node version matrix.
- The detected lint tool (ruff if found in dev deps, otherwise flake8/pylint; eslint for Node, biome if `biome.json` exists).
- The detected test runner (pytest if `pytest` in dev deps; jest/vitest based on `package.json`).
- The lock file path (uv.lock vs requirements.txt vs pnpm-lock.yaml etc.).

### 4. Validation before writing

After producing the yaml, mentally trace it through these gates:

1. Does it conform to GitHub Actions schema? (Look for typos in step keys: `with`, `run`, `env`.)
2. Is `actions/checkout` pinned to `@v4` or later?
3. Does the cache key include the lock file hash?
4. Is `permissions:` declared at workflow or job level (not inheriting org defaults)?
5. Is there a `timeout-minutes` on every job?
6. Is `concurrency:` set to cancel in-progress runs on the same ref?

If any of these is missing, **fix before showing the diff**. Do not ship a yaml that you would flag in audit mode.

---

## Audit mode

### 1. Read all workflow files

```bash
ls .github/workflows/*.yml .github/workflows/*.yaml 2>/dev/null
```

For each file, read the full contents.

### 2. Apply the rule checklist

Load the full rule list from `references/checklist.md` (30+ rules across four categories). Walk every rule against every workflow file.

For each rule violation, record:

```
[severity] [rule-id]  rule short name
  file: .github/workflows/ci.yml
  line: 12
  excerpt: |
        - uses: actions/checkout@v3
  why:    v3 is deprecated since 2024-11; v4 fixes Node 20 runner compatibility.
  fix:    Replace with `uses: actions/checkout@v4`.
```

Severity levels:

- **Critical** — security vulnerability or PR-breaking bug. Must fix.
- **High** — clear correctness or performance issue. Should fix.
- **Medium** — best practice, no immediate harm. Recommended.
- **Low** — style or future-proofing. Nice to have.

### 3. Report format

Output to the user as:

```markdown
# CI Audit Report — N findings

## Critical (X)
1. **[GHA-SEC-01] Untrusted action without SHA pin** — `.github/workflows/release.yml:5`
   ...

## High (Y)
2. **[GHA-PERF-03] No dependency cache** — `.github/workflows/ci.yml:18`
   ...

(...)

## Suggested fix order
1. Apply Critical findings #1, #3 (5 min)
2. Apply High findings #2, #4, #6 (10 min)
3. Apply Medium findings (optional)
```

End with **a single combined diff** that fixes all Critical + High findings, ready to apply.

---

## Worked example (audit)

See `examples/before-bad.yml` (a deliberately mediocre workflow) and `examples/after-good.yml` (the result of applying audit findings).

The diff between the two is the canonical reference for what a correct skill output looks like. When in doubt, compare your audit recommendations against this example.

---

## Out of scope (v0.1.0)

- **Workflow runtime debugging** (`gh run` logs, failed steps) — use `steeef/claude-skill-github-actions` or similar.
- **Reusable workflows / composite actions authoring** — only top-level workflows for now.
- **Self-hosted runners** — assume GitHub-hosted.
- **GitLab / Circle / Buildkite YAML** — only GitHub Actions.
- **Rust / Go / Java templates** — Python and Node.js only for v0.1.0; rules in audit mode still apply to any GitHub Actions yaml.

---

## File map for this skill

```
ci-yaml/
├── SKILL.md                          # This file
├── references/
│   ├── checklist.md                  # 30+ rule audit reference (loaded on demand)
│   └── templates/
│       ├── python-uv.yml             # Python with uv (recommended)
│       ├── python-pip.yml            # Python with pip + requirements.txt
│       └── node.yml                  # Node.js (works for npm/pnpm/yarn)
└── examples/
    ├── before-bad.yml                # Deliberately mediocre workflow
    └── after-good.yml                # Same project after audit fixes
```

Reference and template files are intentionally **not loaded into context until needed**. Read them only when a specific rule citation, template, or example is required.

---

## Quick reference: the 7 rules that catch most real workflows

If short on time and only checking a few things, hit these first (see `references/checklist.md` for the full list and rule IDs):

1. **All `uses:` actions pinned to at least `@v4`** (and SHA-pin for any third-party action that handles secrets).
2. **`permissions:` block declared explicitly** (defaults to write for many tokens, which violates least privilege).
3. **`timeout-minutes:` set on every job** (otherwise a hung job burns up to 6 hours of compute).
4. **`concurrency:` block to cancel superseded runs** (saves cost on repeated pushes).
5. **Dependency cache enabled** via `setup-uv`, `setup-python`, or `setup-node` with their respective cache flags.
6. **`fail-fast: false` on matrix jobs** (one Python version failing shouldn't hide failures in others).
7. **No deprecated commands**: `set-output` → `$GITHUB_OUTPUT`, `save-state` → `$GITHUB_STATE`.

These seven account for >80% of audit findings on real-world workflows.

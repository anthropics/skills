---
name: git-flow-agent-guard-bootstrap
description: Zero-config bootstrap for git-flow-agent-guard. Run this FIRST, then switch to the main skill. No technical knowledge required.
---

# Git Flow Agent Guard — Bootstrap Skill

> **Run this skill once.** It sets up the guard for YOUR project with YOUR stack. Then discard this skill and use the main `git-flow-agent-guard` skill.

---

## Bootstrap Directive

### 1. Detect User's Stack
Ask the user **once** at the start of the session:

> "What's your primary tech stack? Pick one:"
> - Rust
> - Go
> - Node.js / TypeScript
> - Python
> - Java (Maven/Gradle)
> - .NET
> - Other / Monorepo

### 2. Run Installer
Execute the appropriate command based on their agent:

| Agent | Command |
|-------|---------|
| **Cursor** | `curl -fsSL https://raw.githubusercontent.com/MessilineHani/git-flow-agent-guard/main/install.sh \| bash -s -- --agent cursor` |
| **Windsurf** | `curl -fsSL https://raw.githubusercontent.com/MessilineHani/git-flow-agent-guard/main/install.sh \| bash -s -- --agent windsurf` |
| **Claude Code** | `curl -fsSL https://raw.githubusercontent.com/MessilineHani/git-flow-agent-guard/main/install.sh \| bash -s -- --agent claude` |
| **Other** | `curl -fsSL https://raw.githubusercontent.com/MessilineHani/git-flow-agent-guard/main/install.sh \| bash -s -- --agent generic` |

### 3. Configure `.agent-guard.json` FOR THEM
Open the generated `.agent-guard.json` in their project root and **fill in the 4 commands** from the table below matching their stack. Do NOT use this repo's commands.

| Stack | `lint_command` | `typecheck_command` | `test_command` | `build_command` |
|-------|----------------|---------------------|----------------|-----------------|
| **Rust** | `cargo clippy -- -D warnings` | `cargo check` | `cargo test` | `cargo build --release` |
| **Go** | `golangci-lint run` | `go vet ./...` | `go test ./...` | `go build ./...` |
| **Node/TS** | `eslint . --ext .ts,.js` | `tsc --noEmit` | `vitest run` | `tsc && tsc-alias` |
| **Python** | `ruff check .` | `mypy .` | `pytest` | `python -m py_compile $(find . -name '*.py')` |
| **Java (Maven)** | `mvn checkstyle:check` | `mvn compile` | `mvn test` | `mvn package -DskipTests` |
| **.NET** | `dotnet format --verify-no-changes` | `dotnet build --no-restore` | `dotnet test --no-build` | `dotnet publish -c Release` |
| **Monorepo (Turborepo/Nx)** | `turbo run lint` | `turbo run typecheck` | `turbo run test` | `turbo run build` |

> **If "Other":** Ask user for their 4 commands and write them in.

### 4. Verify Setup
Run once to confirm:
```bash
python scripts/evaluate-risk.py --target dev
```
Should output JSON with `"auto_merge_dev_allowed": true` (or false with clear reason).

### 5. Handoff
Tell the user:
> "✅ Setup complete. **Now add the main `git-flow-agent-guard` skill to your agent** (copy `SKILL.md` to your agent config). This bootstrap skill is done — you can forget it."

---

## What This Bootstrap Does NOT Do
- ❌ Does NOT run your tests/lint/typecheck
- ❌ Does NOT modify your source code
- ❌ Does NOT require Python in YOUR project (only for the guard scripts)
- ❌ Does NOT commit anything

## What the Main Skill DOES
After bootstrap, the main `git-flow-agent-guard` skill enforces:
1. Branch protection (no direct pushes to main/dev)
2. Dual audit logging (CHANGELOG + WORKING_TREE.log)
3. Upstream conflict detection before merge
4. **Your configured** lint/typecheck/test/build before PR
5. Risk-gated auto-merge to dev

---

## Self-Destruct
After completing steps 1–5, **remove this bootstrap skill from your agent config.** It's a one-time setup tool.
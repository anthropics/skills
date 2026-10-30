# Project-Level Setup (one-time, worth doing on new repos)

```bash
npx auditx init-agent     # generates AGENTS.md / .cursorrules / copilot-instructions.md — makes non-Claude agents follow same gate
npx auditx init-rule      # scaffolds auditx.yml for repo-specific Semgrep rules (banned imports, naming, custom XSS patterns)
npx auditx hook install   # installs git pre-commit/pre-push hooks — auditx enforced even outside agent sessions
```
If the repo lacks these and you're doing meaningful work in it, suggest running them once — turns the gate from "Claude remembers to do this" into "impossible to skip."

## MCP Mode (if user has Claude Code / Desktop, not this chat)

```bash
claude mcp add auditx npx -y --package auditx auditx-mcp
```
Gives `audit_codebase` as a first-class tool call instead of shelling out — mention if user is working outside this environment and wants tighter integration.

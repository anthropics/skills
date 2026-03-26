# Release Notes

## v1.0.0 — 2026-03-26

Initial release of `pre-deploy-validator` as an Anthropic Agent Skill and npm package
(`@anthropic-community/pre-deploy-validator`).

### What's included

**Five validation checks** (all toggleable via `.pre-deploy-config.json`):

| Check | What it does |
|---|---|
| Code quality | Runs `npm run lint`; flags linting errors |
| Security | Scans for hardcoded secrets — API keys, tokens, passwords |
| Tests | Runs `npm test`; fails on non-zero exit |
| Dependencies | Runs `npm audit --audit-level=moderate`; warns on known vulnerabilities |
| Documentation | Verifies `README.md` and `LICENSE.txt` are present |

**Structured report output** categorised as Passed / Warnings / Failures / Errors, with a final
`READY FOR DEPLOYMENT ✅` or `DEPLOYMENT BLOCKED ❌` status and a numeric exit code.

**Two usage modes**: CLI (`node index.js`) and programmatic API.

### Installation

```bash
# As a skill (via Claude Code plugin marketplace)
/plugin install example-skills@anthropic-agent-skills

# As an npm package
npm install @anthropic-community/pre-deploy-validator
```

### Known limitations

- Dependency audit only covers npm projects (Python `requirements.txt` is detected but not audited)
- Security scan uses static regex patterns; does not perform deep AST analysis
- No built-in support for monorepo workspaces in this release (planned for v1.1.0)

### Upgrade path

This is the initial release — no migration required.

### What's next (v1.1.0 — planned)

- Monorepo / multi-workspace support
- Configurable secret-scanning patterns
- JSON report output mode
- Branch-aware check skipping
- Coverage threshold enforcement

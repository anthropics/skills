# Changelog

All notable changes to `pre-deploy-validator` will be documented in this file.

Format follows [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
Versioning follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

---

## [1.0.0] — 2026-03-26

### Added
- `PreDeployValidator` class with configurable validation checks
- **Code quality** check — runs `npm run lint` and reports linting errors
- **Security** check — regex-based scan for hardcoded secrets (OpenAI keys, AWS keys, GitHub tokens, passwords, generic API key fields)
- **Test suite** check — runs `npm test` and fails on non-zero exit
- **Dependency audit** check — runs `npm audit --audit-level=moderate`; warns on known vulnerabilities
- **Documentation** check — verifies `README.md` and `LICENSE.txt` are present
- Structured validation report with four output categories: Passed, Warnings, Failures, Errors
- Overall deployment status: `READY FOR DEPLOYMENT ✅` or `DEPLOYMENT BLOCKED ❌`
- Exit codes: `0` all clear · `1` failures · `2` config error · `3` skipped
- CLI usage via `node index.js`
- Programmatic API: `new PreDeployValidator(config)` → `await validator.validate()`
- JSON-based configuration via `.pre-deploy-config.json`
- All checks individually toggleable via config
- `failOnWarnings` option to treat warnings as failures
- SKILL.md with at-a-glance comment block covering checks, deliverable, exit codes, and quick-start
- Registered in `example-skills` marketplace plugin
- MIT license

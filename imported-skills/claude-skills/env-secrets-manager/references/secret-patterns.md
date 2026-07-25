# Secret Pattern Reference

## Detection Categories

### Critical

- OpenAI-like keys (`sk-...`)
- GitHub personal access tokens (`ghp_...`)
- AWS access key IDs (`AKIA...`)

### High

- Slack tokens (`xox...`)
- Private key PEM blocks
- Hardcoded assignments to `secret`, `token`, `password`, `api_key`

### Medium

- JWT-like tokens in plaintext
- Suspected credentials in docs/scripts that should be redacted

## Severity Guidance

- `critical`: immediate rotation required; treat as active incident
- `high`: likely sensitive; investigate and rotate if real credential
- `medium`: possible exposure; verify context and sanitize where needed

## Response Playbook

1. Revoke or rotate exposed credential.
2. Identify blast radius (services, environments, users).
3. Remove from code/history where possible.
4. Add preventive controls (pre-commit hooks, CI secret scans).
5. Verify monitoring and access logs for abuse.

## Preventive Baseline

- Commit only `.env.example`, never `.env`.
- Keep `.gitignore` patterns for env and key material.
- Use secret managers for staging/prod.
- Redact sensitive values from logs and debug output.

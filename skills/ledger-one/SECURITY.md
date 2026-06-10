# Security

## Supported Version

Security fixes are applied to the latest `main` branch only.

## Reporting

If you discover a vulnerability:

1. Do not open a public issue with live secrets, exploit details, or reproduction data from a real account.
2. Use GitHub's private vulnerability reporting for this repository if it is enabled.
3. If private reporting is unavailable, open a minimal public issue that says you have a security report and omit sensitive details.

## Secret Handling

Treat these values as credentials:

- `SIMPLEFIN_ACCESS_URL`
- SimpleFIN setup tokens / claim URLs
- `DATABASE_URL`
- `ANTHROPIC_API_KEY`

If any of them are exposed:

1. Rotate them immediately.
2. Assume any data reachable by the leaked credential may be compromised.
3. Remove the leaked value from logs, screenshots, shell history, and commits where possible.

## Operational Notes

- Keep `.env` and `.env.test` local only. Do not commit them.
- Prefer a dedicated local test database for destructive test runs.
- If you use a remote isolated test database, opt in from the shell for a single session rather than storing the bypass in `.env.test`.
- Review dependency updates before changing `requirements.lock` or broadening version constraints in secret-bearing automation.

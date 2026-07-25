# Redaction Checklist

> Redact any sensitive information, such as API keys, passwords, or personally identifiable information.

The `redaction_linter.py` script automates the regex-catchable patterns. This document covers (1) what the regex patterns look for, (2) the manual-review step for what regex cannot catch, and (3) the whitelist mechanism for true false positives.

## Regex patterns the linter catches

| Pattern | Example | Severity |
|---|---|---|
| AWS access key | `AKIAIOSFODNN7EXAMPLE` | high |
| AWS secret key assignment | `aws_secret_access_key=...` | high |
| GitHub token | `ghp_...`, `gho_...`, `ghs_...`, `ghr_...` | high |
| OpenAI key | `sk-...` | high |
| Anthropic key | `sk-ant-...` | high |
| Slack token | `xoxb-...`, `xoxp-...`, etc. | high |
| Google API key | `AIza...` | high |
| Stripe key | `sk_live_...`, `pk_test_...` | high |
| Private key block | `-----BEGIN RSA PRIVATE KEY-----` | high |
| JWT | `eyJ...` three-part | high |
| Env-style secret assignment | `PASSWORD=hunter2` | high |
| DB connection string with creds | `postgres://user:pw@host/db` | high |
| Authorization Bearer header | `Authorization: Bearer eyJ...` | high |
| Email address | `name@example.com` | medium |
| Phone number | various formats | low |
| URL with token query param | `https://api/?token=...` | high |
| Private IP / CIDR | `10.0.1.5`, `192.168.1.0/24` | low |

The phone-number regex has high false-positive rate (version strings, long IDs); it is intentionally low-severity and surfaced for review rather than automatic block.

## What regex cannot catch — manual review

These categories require human judgement. Walk them every time before save:

### Names and customer references

- Did you mention a customer or partner by name? Redact unless they are a public reference.
- Did you mention a specific deal, contract value, or pricing? Redact if not yet public.
- Did you mention an unreleased feature by codename? Redact if not yet announced.

### Internal infrastructure

- Did you paste an internal hostname (`internal-db-01.corp.example`)? Redact.
- Did you mention an internal IP range or VPC ID? Redact.
- Did you reference a non-public Slack channel name? Replace with the topic ("the on-call channel").

### Free-form narrative leakage

- "Last week Ann from FinCo asked us to..." — both Ann and FinCo are PII/customer references.
- "The DB password is in `~/.env` on my laptop" — leaks both the location and the existence of the secret.
- "We're behind on the Acme contract because..." — leaks customer + risk status.

### Cross-system references

- IDs that look innocuous but join across systems (e.g., a customer's external ID + your internal tenant ID) can re-identify them.
- Stack traces that include filesystem paths leak usernames (e.g., `/home/jdoe/work/...`).

## Whitelist mechanism

If the linter flags a true false positive — e.g., an example AWS key in documentation — whitelist that specific line by appending the marker:

```
Example key: AKIAIOSFODNN7EXAMPLE <!-- handoff:allow secret -->
```

Rules for whitelisting:

1. The marker applies only to the line it's on.
2. Add a one-line comment above the marker explaining *why* this is safe.
3. Never whitelist a real secret. Move the value out of the doc instead.
4. The whitelist is auditable: search for `handoff:allow secret` to find every whitelisted match.

## Mode behaviour

| Mode | Linter exit code on findings | Save behaviour |
|---|---|---|
| `strict` (default) | 1 | Blocked. Resolve findings or whitelist. |
| `warn` | 0 | Saved. Findings printed for review. |
| `off` | 0 (no scan) | Saved. No scan. Not recommended. |

Mode is set in config (`/cs:handoff-setup`).

## When the linter has done its job

A handoff is "redaction-clean" when:

1. Linter exits 0 (clean) or all findings are explicitly whitelisted with a reason.
2. Manual-review categories above have been walked.
3. You are willing to share the file with anyone who might receive it (teammate, replacement agent, external reader).

If the third point makes you hesitate, redact more.

## Sources

- David Dworken (Anthropic), *PreToolUse security reminder hook* (MIT) — the precedent for inline rule whitelisting via comment markers.
- OWASP, *Cheat Sheet: Secrets Management* — what counts as a secret in modern apps.
- NIST SP 800-53, *AC-3 Access Enforcement* — least-privilege principles applied to documentation artifacts.
- GitGuardian, *State of Secrets Sprawl* (2024) — the empirical taxonomy of secrets that leak into developer artifacts.
- Truffle Security, *TruffleHog detector list* — the canonical reference for high-precision secret patterns.
- ICO (UK), *Personal data definition* — what counts as PII under GDPR.

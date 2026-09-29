# Secret pattern catalog

Authoritative list of patterns the scanner recognises. Every pattern
here must have a matching entry in `scripts/scan.sh` (the `PATTERNS`
array) and, if practical, a fixture line in the `--self-test` block.

Patterns are chosen for **precision over recall**. If a regex would
match arbitrary base64, unanchored hex, or "any 32-character string,"
it does not belong here — that is entropy-scanner territory. Every
entry below has a distinguishing prefix, structural marker, or
context anchor.

| Pattern name | What it matches | Rough FP rate | Known-safe fixture |
|---|---|---|---|
| AWS access key ID | `AKIA` or `ASIA` + 16 uppercase alnum | Very low | `AKIAIOSFODNN7EXAMPLE` (AWS docs) |
| AWS secret access key (assignment) | `aws_secret_access_key` assigned to a 40-char base64/hex-ish value | Low; anchored to variable name | `wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY` |
| GitHub PAT (classic) | `ghp_` + 36 alnum | Very low | `ghp_` followed by 36 alnum chars |
| GitHub fine-grained PAT | `github_pat_` + 82 alnum/underscore | Very low | n/a — no published dummy |
| GitHub OAuth token | `gho_` + 36 alnum | Very low | n/a |
| GitHub app/refresh token | `ghu_`, `ghs_`, `ghr_` + 36 alnum | Very low | n/a |
| Slack bot/user token | `xox[baprs]-` + payload | Low | n/a |
| Slack webhook URL | `https://hooks.slack.com/services/T.../B.../...` | Very low | n/a |
| Stripe live secret key | `sk_live_` + 24+ alnum | Very low | n/a — do not commit even dummies |
| Stripe live restricted key | `rk_live_` + 24+ alnum | Very low | n/a |
| OpenAI API key | `sk-` (optional `proj-`) + payload with `T3BlbkFJ` anchor | Very low | n/a |
| Anthropic API key | `sk-ant-api##-` or `sk-ant-admin##-` + long payload | Very low | n/a |
| Google API key | `AIza` + 35 alnum/underscore/hyphen | Low; also matches embed keys | `AIza` followed by 35 chars of `[A-Za-z0-9_-]` |
| GCP service account (JSON header) | `"type": "service_account"` | Low; the JSON itself is the credential | n/a |
| OpenSSH / RSA private key | `-----BEGIN ... PRIVATE KEY-----` | Very low | n/a |
| PKCS#8 encrypted private key | `-----BEGIN ENCRYPTED PRIVATE KEY-----` | Very low | n/a |
| JWT (three-part) | `eyJ` header + two more base64url parts | Medium — many JWTs are non-secret (e.g. ID tokens in test fixtures). Triage manually. | `eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiJ0ZXN0In0.abcdefg…` |
| Generic secret-shaped assignment | `password`/`secret`/`api_key`/`access_token`/`auth_token` assigned to a quoted string ≥ 16 chars | Highest of the set. Triage: if the value is `os.getenv(...)`, `process.env.X`, or a placeholder like `<REDACTED>`, it is safe. | `password = "correct-horse-battery-staple-42"` |

## Not in the catalog (and why)

These *look* like they belong but produce too many false positives to
be useful in a first-pass scanner:

- **Bare 32/40/64-char hex strings.** Match rate is too high — commit
  hashes, digests, hashes-of-hashes. Route through `gitleaks` if you
  need entropy detection.
- **Base64 blobs.** Same problem. Everything is base64.
- **UUIDs.** Not secrets. Fixtures rely on them.
- **Twilio/SendGrid API keys without their prefixes.** The prefixed
  forms (`SK...`, `SG.`) are safe to add later; the un-prefixed
  variants are indistinguishable from noise.
- **Personal data (emails, phone numbers, addresses).** Different
  problem, different skill.

## Adding a pattern

1. Come with a fixture: a real example of the format (redacted or
   dummy) that must match, and one plausible non-match that must not.
2. Add a row to the table above with all four columns filled.
3. Add the pattern to the `PATTERNS` array in `scripts/scan.sh`,
   preserving the order used here.
4. Add a `# HIT:` fixture line to the `--self-test` block. If the
   pattern is prone to false positives, also add a `# MISS:` line
   showing what it must ignore.
5. Run `bash scripts/scan.sh --self-test` and confirm 0 failures.

## Triage cheatsheet

When the scanner flags a match:

- **Live-service credential** (AWS/GCP/GitHub/Slack/Stripe/OpenAI/
  Anthropic) → rotate at the source *first*, then remove from file.
  Assume compromised the moment the file was written; force-pushing
  the commit away does not help.
- **Private key block** → rotate the keypair. Add `*.pem`,
  `id_rsa*`, and `*.key` to `.gitignore` if not already.
- **Generic assignment** → check the value:
  - `os.getenv(...)` / `process.env.X` / `Deno.env.get(...)` → not a
    secret, it is a reference. Safe. Add an inline allowlist if the
    scanner keeps flagging.
  - Placeholder like `changeme`, `xxx`, `<your-key-here>` → safe but
    should still not ship. Replace with an env var read.
  - Actual value → treat as a live credential (see above).
- **JWT** → check the payload (base64-decode the middle segment) to
  see whether it is a user ID token (usually fine; short-lived) or a
  long-lived service token. Rotate if the latter.

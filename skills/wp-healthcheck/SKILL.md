---
name: wp-healthcheck
description: Diagnoses WordPress site health from public information only. Detects WordPress version and active theme, validates SSL/TLS certificate expiry and issuer, checks recommended security headers (X-Frame-Options, HSTS, CSP, X-Content-Type-Options, Referrer-Policy), verifies robots.txt and sitemap.xml, measures top-page response time, probes xmlrpc.php / wp-json / wp-cron.php exposure, and flags installed plugins with historical CVEs. Produces a Markdown report graded OK / WARNING / CRITICAL / UNKNOWN. Use this skill whenever the user asks to check, audit, diagnose, scan, or review a WordPress site, mentions wp-healthcheck, asks why a WordPress site is slow or insecure, requests a maintenance report, or provides a URL and asks whether it looks healthy. Works on any public WordPress site without credentials. For internal audits requiring database, file integrity, or admin state, recommend a dedicated WordPress maintenance plugin instead.
license: Complete terms in LICENSE
---

# wp-healthcheck

## Overview

`wp-healthcheck` runs an external, credential-less diagnostic against any WordPress site
and produces a Markdown maintenance report. It probes only publicly accessible surfaces
(HTML, headers, well-known endpoints, TLS certificate) and grades each finding on a
four-tier scale: **OK / WARNING / CRITICAL / UNKNOWN**.

This skill is intended for first-pass health checks before deeper internal audits.

## When to use this skill

Activate this skill when the user:

- Asks to "check / audit / diagnose / scan / review" a WordPress site.
- Mentions `wp-healthcheck`, "WP healthcheck", or "WordPress health check".
- Provides a URL and asks whether it looks safe, secure, up to date, or healthy.
- Reports that a WordPress site feels slow, insecure, or unmaintained and wants a quick
  external assessment.
- Wants a maintenance report they can share with a client without server access.

Do **not** activate for: internal-only audits requiring database access, plugin code
review, theme development, or general WordPress how-to questions.

## Usage

The user typically says one of:

- "Run a healthcheck on https://example.com"
- "Can you audit example.com? I think they're on an old WordPress."
- "Use wp-healthcheck on https://example.com"

Claude should:

1. Confirm the target URL with the user (and confirm `https://` if they typed a bare
   domain).
2. Run `bash scripts/check_wp.sh <url>` (or pass `--output <file>` if the user wants the
   report written to disk).
3. Present the Markdown output to the user, then highlight the most important findings
   (CRITICAL first, then WARNING) and suggest next steps.

## Workflow

```text
User provides URL
        |
        v
[ scripts/check_wp.sh <url> ]
        |
        +--> fetch_wp_meta.sh   (curl: HTML, /wp-json/, /readme.html, /xmlrpc.php,
        |                        /wp-cron.php, /robots.txt, /sitemap.xml, TLS info)
        |
        +--> 8 diagnostic checks (version, theme, SSL, headers, robots/sitemap,
        |                        response time, API surface, plugin fingerprints)
        |
        +--> format_report.sh   (renders findings as Markdown)
        |
        v
Markdown report on stdout (or written to --output file)
```

### Command reference

```bash
# Print report to stdout
bash scripts/check_wp.sh https://example.com

# Write report to a file
bash scripts/check_wp.sh https://example.com --output ./report.md
```

### Requirements

- `bash`, `curl`, `jq`, `awk`, `sed`, `grep`, `mktemp`, `date` (all present on macOS and
  most Linux distributions by default).
- Network access to the target site.
- No API keys or credentials.

## Output format

The report has three sections:

1. **Header** — target URL, generation timestamp, overall verdict.
2. **Summary table** — one row per diagnostic item with status and one-line summary.
3. **Findings (detail)** — per-item explanation with raw evidence.

Overall verdict is one of:

- `Action required` — at least one CRITICAL finding.
- `Attention recommended` — at least one WARNING (and no CRITICAL).
- `Healthy on observable surfaces` — only OK / UNKNOWN.
- `Could not assess (site unreachable or non-responsive)` — no OK results, only UNKNOWN.

See `examples/sample-report.md` for a real run.

## Limitations

This skill examines **only publicly accessible information**. It cannot:

- Determine the actual installed version of detected plugins.
- See plugins that are active only in the WordPress admin (SEO, cache, backup, security
  managers). Front-end-invisible plugins leave no fingerprint in public HTML, so the
  detected plugin count is a **lower bound**, not a complete inventory.
- Inspect the database, `wp-config.php`, file integrity, or admin-only state.
- Detect compromised content not exposed on the front page.
- Replace a WAF, vulnerability scanner, or full security audit.

For deeper checks (file diffs, scheduled cron, user roles, transient state), use a
dedicated WordPress maintenance plugin that runs inside the site.

## References

- `references/checklist.md` — full judgement criteria for each diagnostic item.
- `examples/sample-report.md` — an example report produced by this skill.
- `docs/skill-spec-research.md` — the Anthropic Agent Skills specification research that
  informed this skill's design.

---
name: arc-sentinel
description: Security monitoring and infrastructure health checks for OpenClaw agents. Run breach monitoring (HaveIBeenPwned), SSL certificate expiry checks, GitHub security audits, credential rotation tracking, secret scanning, git hygiene, token watchdog, and permission audits. Use when performing security scans, checking credential rotation status, auditing repos for leaked secrets, or monitoring SSL certificates and infrastructure health.
---

# Arc Sentinel

Security monitoring toolkit for OpenClaw agents. Runs automated checks against your infrastructure and reports issues.

## Configuration

Before first use, create `sentinel.conf` in the skill directory:

```bash
cp sentinel.conf.example sentinel.conf
```

Edit `sentinel.conf` with your values:
- **DOMAINS** — Space-separated list of domains to check SSL certificates
- **GITHUB_USER** — GitHub username for repo audits
- **KNOWN_REPOS** — Space-separated list of expected repo names (unexpected repos trigger warnings)
- **MONITOR_EMAIL** — Email address for HaveIBeenPwned breach checks
- **HIBP_API_KEY** — Optional; HIBP v3 API key ($3.50/mo) for automated breach lookups

Also customize `credential-tracker.json` with your own credentials and rotation policies. A template is provided.

## Quick Start

### Full scan
```bash
cd <skill-dir>
bash sentinel.sh
```

### Output
- Formatted report to stdout with color-coded severity
- JSON report saved to `reports/YYYY-MM-DD.json`
- Exit codes: `0` = all clear, `1` = warnings, `2` = critical

## Checks

### 1. SSL Certificate Expiry
Check certificate expiry for configured domains. Warns at <30 days, critical at <14 days.

### 2. GitHub Security
- List repos and check Dependabot/vulnerability alert status
- Review recent account activity for anomalies
- Flag unexpected repositories

### 3. Breach Monitoring (HaveIBeenPwned)
- Query HIBP API for breached accounts (requires API key)
- Falls back to manual check URL if no key is set

### 4. Credential Rotation Tracking
Read `credential-tracker.json` and flag credentials that are overdue, approaching expiry, or never rotated. Supports policies: `quarterly` (90d), `6_months` (180d), `annual` (365d), `auto`.

## Additional Scripts

| Script | Purpose |
|--------|---------|
| `scripts/secret-scanner.sh` | Scan repos/files for leaked secrets and API keys |
| `scripts/git-hygiene.sh` | Audit git history for security issues |
| `scripts/token-watchdog.sh` | Monitor token validity and expiry |
| `scripts/permission-auditor.sh` | Audit file and access permissions |
| `scripts/skill-auditor.sh` | Audit installed skills for security |
| `scripts/full-audit.sh` | Run all scripts in sequence |

## Agent Usage

During heartbeats or on request:
1. Run `bash sentinel.sh` from the skill directory
2. Review output for WARN or CRITICAL items
3. Report findings to the human if anything needs attention
4. Update `credential-tracker.json` when credentials are rotated

## Cron Setup
```bash
# Weekly Monday 9am
0 9 * * 1 cd /path/to/arc-sentinel && bash sentinel.sh >> reports/cron.log 2>&1
```

## Requirements
- `openssl` (SSL checks)
- `gh` CLI authenticated (GitHub checks)
- `curl` (HIBP)
- `python3` (JSON processing)

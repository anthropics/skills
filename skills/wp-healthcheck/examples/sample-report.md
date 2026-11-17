<!--
This file is a real sample produced by:

    bash scripts/check_wp.sh https://n-pc.jp --output examples/sample-report.md

Re-run the same command to refresh it.
-->

# WordPress Healthcheck Report

- Target: https://n-pc.jp
- Generated: 2026-04-28 05:31:38 UTC
- Skill: wp-healthcheck (Phase 1, standalone external probe)

## Summary

- Overall: **Action required**
- OK: 6 / WARNING: 1 / CRITICAL: 1 / UNKNOWN: 0

| Item | Status | Summary |
|---|---|---|
| WordPress version | OK | WordPress 6.9.4 appears reasonably current. |
| Active theme | OK | Active theme: npc-abc-theme |
| SSL / TLS certificate | OK | Certificate valid for 68 more days. |
| Security headers | CRITICAL | 0 of 5 recommended security headers present. |
| robots.txt and sitemap | OK | Both robots.txt and sitemap are present. |
| Top page response time | OK | Top page time_total: 0.166054s |
| Public API surface | OK | xmlrpc / wp-json / wp-cron probed. |
| Plugin fingerprints | WARNING | Plugins with historical CVEs detected: contact-form-7  |

## Findings (detail)

### WordPress version — OK

WordPress 6.9.4 appears reasonably current.

- Detected version: 6.9.4

### Active theme — OK

Active theme: npc-abc-theme

- Theme path detected from HTML.

### SSL / TLS certificate — OK

Certificate valid for 68 more days.

- Subject: CN=www.n-pc.jp
- Issuer: C=US; O=Let's Encrypt; CN=R13
- Valid from: Apr  6 23:29:06 2026 GMT
- Expires: Jul  5 23:29:05 2026 GMT
- Days remaining: 68

### Security headers — CRITICAL

0 of 5 recommended security headers present.

- Present: none
- Missing: X-Frame-Options X-Content-Type-Options Strict-Transport-Security Content-Security-Policy Referrer-Policy 

### robots.txt and sitemap — OK

Both robots.txt and sitemap are present.

- robots.txt status: 200
- sitemap URL tried: https://n-pc.jp/sitemap.xml
- sitemap status: 200

### Top page response time — OK

Top page time_total: 0.166054s

- Single-sample measurement; treat as indicative only.

### Public API surface — OK

xmlrpc / wp-json / wp-cron probed.

- xmlrpc.php: OK (disabled, status 404)
- /wp-json/: OK (REST API reachable)
- wp-cron.php: OK (status 404)

### Plugin fingerprints — WARNING

Plugins with historical CVEs detected: contact-form-7 

- Front-end visible plugins (4): akismet cf7-google-analytics contact-form-7 google-site-kit 
- Note: Plugins active only in the WordPress admin (SEO, cache, backup, security tools) typically leave no front-end fingerprint and cannot be detected from outside.
- Action: verify each flagged plugin is up to date. Versions cannot be determined externally.

## Limitations

This report is built **only from publicly accessible information** (HTML, headers, well-known
endpoints, TLS certificate). It cannot:

- Determine actual installed plugin versions (only slugs visible in HTML).
- See plugins that are active only in the WordPress admin (SEO, cache, backup, security
  managers). Front-end-invisible plugins leave no fingerprint in public HTML, so the
  detected plugin count is a **lower bound**, not a complete inventory.
- Inspect database, wp-config.php, or admin-only state.
- Detect exploited backdoors or compromised content not exposed on the front page.

For an internal audit (file integrity, cron schedule, user roles, transient state, full
plugin inventory), use a dedicated WordPress maintenance plugin that runs inside the site.

## References

See `references/checklist.md` in the skill directory for the full judgement criteria.

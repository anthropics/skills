# WordPress Healthcheck Diagnostic Checklist

This document defines the diagnostic items used by `scripts/check_wp.sh`.
Each item is judged on a four-tier scale: **OK / WARNING / CRITICAL / UNKNOWN**.

---

## 1. WordPress version detection

### Method
- Extract `<meta name="generator" content="WordPress X.X.X">` from the HTML of the top page.
- Probe `/readme.html` (HTTP HEAD).
- Probe `/wp-json/` and parse the `name` field.

### Judgement
| Status | Condition |
|---|---|
| OK | Version detected and matches the latest stable major release (>= 6.4) |
| WARNING | Version detected but is older than the latest stable major release |
| CRITICAL | Version detected and is older than 6.0, or `/readme.html` is publicly accessible (typical sign of a long-unmaintained site) |
| UNKNOWN | No version can be detected (generator meta removed, REST disabled) |

### Notes
- A missing generator meta is not necessarily bad (often a hardening choice). Combine with other signals.
- `/readme.html` exposure is itself a soft fingerprinting risk and a maintenance smell.

---

## 2. Active theme detection

### Method
- Find the first occurrence of `/wp-content/themes/<theme-name>/` in the HTML and report `<theme-name>`.

### Judgement
| Status | Condition |
|---|---|
| OK | A theme name was detected |
| UNKNOWN | No theme path appears in the HTML (rare, may indicate full caching layer or non-WP) |

### Notes
- This is informational. The skill does not flag specific themes as risky; detection alone is the goal.

---

## 3. SSL / TLS certificate

### Method
- Run `curl -vI --max-time 30 https://<host>/` and parse the certificate's notBefore / notAfter / issuer.
- Compute days remaining until expiry.

### Judgement
| Status | Condition |
|---|---|
| OK | Valid certificate, more than 30 days until expiry |
| WARNING | Less than 30 days until expiry |
| CRITICAL | Already expired, hostname mismatch, or self-signed |
| UNKNOWN | HTTPS not reachable / certificate chain could not be parsed |

---

## 4. Security headers

### Method
- `curl -sI --max-time 30 https://<host>/` and check presence of:
  - `X-Frame-Options`
  - `X-Content-Type-Options`
  - `Strict-Transport-Security`
  - `Content-Security-Policy`
  - `Referrer-Policy`

### Judgement
| Status | Condition |
|---|---|
| OK | 4 or 5 headers present |
| WARNING | 2 or 3 headers present |
| CRITICAL | 0 or 1 headers present |
| UNKNOWN | The site did not respond to a HEAD request |

### Notes
- HSTS (`Strict-Transport-Security`) is the most impactful for HTTPS sites.
- CSP is hard to retrofit; its absence is common and not always critical, but worth flagging.

---

## 5. robots.txt and sitemap.xml

### Method
- HTTP GET `/robots.txt` and `/sitemap.xml` (and `/wp-sitemap.xml` as fallback).
- Check status code 200 and basic content sanity (non-empty, contains expected keywords).

### Judgement
| Status | Condition |
|---|---|
| OK | Both robots.txt and a sitemap are present and look valid |
| WARNING | One of them is missing or returns a non-200 status |
| CRITICAL | Both missing |
| UNKNOWN | Network errors prevented fetching |

---

## 6. Top-page response time

### Method
- `curl -o /dev/null -s -w '%{time_total}' https://<host>/` (single sample, HTTP/2 if available).

### Judgement
| Status | Condition |
|---|---|
| OK | time_total < 1.5 seconds |
| WARNING | 1.5 to 3.0 seconds |
| CRITICAL | > 3.0 seconds |
| UNKNOWN | The request failed |

### Notes
- Single-sample timing is indicative only; for serious performance work, use a dedicated tool.

---

## 7. Public API surface

### Method
- `/xmlrpc.php`: HTTP HEAD or GET, check status code.
  - 200 / 405 means xmlrpc is reachable (405 is what WordPress returns to GET; POST would be the real call).
- `/wp-json/`: HTTP GET, check status and JSON parseability.
- `/wp-cron.php`: HTTP HEAD, check status code.

### Judgement
| Item | OK | WARNING | CRITICAL |
|---|---|---|---|
| xmlrpc.php | Returns 403 / 404 / 410 (disabled) | Returns 405 (default WP) | Returns 200 with rsd link |
| /wp-json/ | Reachable JSON | Reachable but partial | 500 errors |
| wp-cron.php | Returns 200 / 404 | Returns 5xx | Times out |

### Notes
- `xmlrpc.php` being open is no longer "always critical" but it remains a brute-force and pingback amplification surface. We mark default state as WARNING.
- Disabling `wp-cron.php` and using a real cron is best practice but cannot be detected externally; we only check reachability.

---

## 8. Known vulnerable plugin fingerprints

### Method
- Extract every `/wp-content/plugins/<plugin-name>/` path that appears in the HTML.
- Compare each detected `<plugin-name>` against the known-issue list below (case-insensitive exact match on slug).

### Known-issue plugin slugs (Phase 1 conservative list)
The following slugs have had widely reported CVEs in recent years and warrant manual verification of installed version:

- `wp-file-manager` — RCE in versions <= 6.8 (CVE-2020-25213)
- `revslider` — Slider Revolution arbitrary file upload (older versions)
- `wp-statistics` — historical SQLi
- `duplicator` — historical arbitrary file download
- `loginizer` — historical SQLi (versions < 1.6.4)
- `elementor` — multiple historical XSS / auth bypass; verify latest
- `all-in-one-seo-pack` — historical privilege escalation (older versions)
- `wpforms-lite` — historical XSS
- `contact-form-7` — historical unrestricted file upload (versions < 5.3.2)
- `ninja-forms` — historical code injection
- `updraftplus` — historical info disclosure
- `wpbakery-page-builder` — historical XSS (formerly visual-composer)
- `mailpoet` — historical SQLi (very old versions)
- `wp-super-cache` — historical RCE
- `social-warfare` — historical RCE (CVE-2019-9978)

### Judgement
| Status | Condition |
|---|---|
| OK | No fingerprints from the known-issue list were found |
| WARNING | One or more known-issue plugins detected (version cannot be determined externally; manual check required) |
| CRITICAL | (reserved — Phase 1 cannot reliably detect exploited versions externally) |
| UNKNOWN | Plugin paths could not be enumerated (no plugins in HTML, or full-page caching strips them) |

### Detection scope (important)

This check detects **only plugins whose CSS/JS assets are enqueued on the front page** —
roughly, plugins that visibly affect the public site. Plugins that operate only inside
the WordPress admin (SEO meta managers like Yoast, caching plugins like WP Super Cache,
backup plugins like UpdraftPlus, security plugins like SiteGuard, etc.) do not emit
`/wp-content/plugins/<slug>/` paths into the front HTML and **cannot be detected from
outside**.

Treat the count as a **lower bound**. Many WordPress sites have 2–4× more plugins
active than this check can see. For a complete plugin inventory, use a dedicated
WordPress maintenance plugin (internal audit) or check the WP admin Plugins screen.

### Notes
- This list is intentionally short and high-signal. Phase 2 (with API access) can integrate with the WPScan vulnerability database for accurate version-aware checks.
- "Detected" never means "exploitable". The skill flags candidates for the human reviewer.

---

## Severity summary mapping

The final report aggregates per-item statuses:

- **CRITICAL** count > 0 → overall "Action required"
- **WARNING** count > 0 → overall "Attention recommended"
- All OK / UNKNOWN → overall "Healthy on observable surfaces"

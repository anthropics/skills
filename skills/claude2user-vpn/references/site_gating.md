# Site Response Reference

Last sweep: **2026-05-14** from a US residential IP, macOS Safari 17.4 headers, no logged-in cookies.

Re-test with `scripts/site_test.sh <url1> <url2> ...` before relying on this snapshot. Sites change response policy frequently and the matrix dates fast.

## Status legend

- ✅ **200** — Page returned content
- 🔒 **401 / 403** — Authentication required (paywall, subscription, registration)
- 🧱 **503 / 000 / JS-challenge HTML stub** — Page served via JavaScript challenge; `curl` cannot render it. Open in a real browser.
- ⚠️ **varies** — Inconsistent across requests

## Sites tested

| Site | Default curl | With `fetch_as_user.sh` | Notes |
|---|---|---|---|
| reuters.com | 🔒 401 | 🔒 401 | Subscription required — needs user's cookies |
| bloomberg.com | 🔒 403 | 🔒 403 | Subscription required — needs user's cookies |
| wsj.com | 🔒 401 | 🔒 401 | Subscription required — needs user's cookies |
| ft.com | 🔒 401 | 🔒 401 | Subscription required — needs user's cookies |
| seekingalpha.com | 🔒 403 | 🔒 403 | Registration required — needs user's cookies |
| kitco.com | 🧱 503 | 🧱 000 | JS challenge — open in a real browser |
| yahoo.com finance | ⚠️ varies | ⚠️ 500 | Full content needs session cookies; for prices, use a market-data API |
| bls.gov | ⚠️ varies | ⚠️ 403 | Inconsistent across endpoints |
| bullionvault.com | ✅ 200 | ✅ 200 | Works either way |
| investing.com | ✅ 200 | ✅ 200 | Works either way |
| cnbc.com | ⚠️ varies | ✅ 200 | Wrapper more reliable for headlines |
| marketwatch.com | ⚠️ varies | ✅ 200 | Wrapper more reliable for headlines |
| barrons.com | ⚠️ varies | ✅ 200 | Headlines OK; full articles often gated |
| mining.com | ✅ 200 | ✅ 200 | Reliable for sector news |
| federalreserve.gov | ✅ 200 | ✅ 200 | Open access |
| sec.gov / EDGAR | ✅ 200 | ✅ 200 | Open access — preferred for filings |

## When the wrapper isn't enough

- **The user has a subscription** but the site returns 401/403: ask them to export cookies via Safari/Chrome devtools or a "Get cookies.txt" browser extension. Save under `~/.claude/secrets/cookies/<site>.txt` and pass to curl via `-b`. Cookies expire on a ~30-90 day cadence.
- **The site serves content via JavaScript**: this wrapper cannot help; `curl` doesn't execute JS. Use the user's real browser, or look for an underlying JSON API the page calls.

## When to re-test

- Quarterly, as routine maintenance
- When a previously-working site starts returning errors
- After a previously-stable response pattern changes site-wide (typically a few times per year)

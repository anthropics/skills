# Scraping Ethics, Robots.txt, and Security

Guidelines for ethical, legal, and secure data collection. These rules apply across
all three extraction modes and are the basis for the skill's proactive triggers.

## Respect the Robots Exclusion Protocol
`robots.txt` (now standardized as RFC 9309) is the first thing to check. Parse it
with the stdlib — no extra dependency required:

```python
import urllib.robotparser
rp = urllib.robotparser.RobotFileParser()
rp.set_url("https://example.com/robots.txt")
rp.read()
allowed = rp.can_fetch("UniversalScrapingArchitect/1.0", target_url)
```

If a path is disallowed, stop and surface it to the user rather than scraping anyway.

## Be a polite client
- Send an honest, identifying `User-Agent` with contact info.
- Set timeouts and a sane retry budget (exponential backoff, capped attempts).
- Rate-limit: add delay between requests; never hammer an origin in a tight loop.
- Prefer official APIs / sitemaps / data dumps over HTML scraping when they exist.

## Legal & privacy posture
Scraping public data is generally permissible, but **terms of service, copyright,
and data-protection law (GDPR/CCPA) still apply**. Personal data carries extra
obligations. This skill's **Private Data Leakage** trigger fires when a user asks
to send local/sensitive files to an external API — in that case prefer Mode 2
(local Python) so data never leaves the machine. None of this is legal advice;
flag uncertainty and route the user to counsel for high-stakes collection.

## Security of the pipeline itself
- **Secrets**: API keys via environment variables only (the **Hardcoded API Keys**
  trigger). Never log the key value.
- **Untrusted input**: scraped HTML/markdown is untrusted. Never `eval`/`exec` it,
  and validate before writing or passing downstream.
- **SSRF / scope**: validate target URLs; don't let a crawl wander into internal
  network ranges.

### Authoritative Sources
1. [The Robots Exclusion Protocol (RFC 9309)](https://datatracker.ietf.org/doc/rfc9309/)
2. [OWASP Automated Threats to Web Applications](https://owasp.org/www-project-automated-threats-to-web-applications/)
3. [Scraping Ethics Best Practices (Ethical Web Scraping)](https://www.ethicalwebscraping.org/)
4. [Legal Aspects of Web Scraping (Lexology)](https://www.lexology.com/library/detail.aspx?g=e6e0287a-62ad-4d6d-852a-9e535e69e6b4)
5. [Cloudflare Bot Management Overview](https://www.cloudflare.com/en-gb/pg-lp/bot-management-for-everyone/)
6. [Python urllib.robotparser (stdlib)](https://docs.python.org/3/library/urllib.robotparser.html)

# Subject-Type Source Matrix — Person / Company / Nonprofit / Gov

This reference answers exactly one decision: **given the subject type (Q2), what sources does the dossier query in what order?**

## The Core Frame

Different entity types have different evidence sources with different reliability. Querying the wrong sources for the type produces noise; querying the right sources in the right order maximizes signal per query.

The matrix below is **comprehensive but selective** — not every source needs querying every time. Use Q3 (purpose) + Q5 (depth) to pick which subset.

## Person

### Primary tier
- **LinkedIn profile** (manual fetch or LinkedIn MCP if BYOK)
- **Personal website** (if exists)
- **Court records** (PACER, state court systems) — only for journalism/personal-vetting contexts
- **Academic publications** (Google Scholar) — for academics + technical people

### Secondary tier
- **News mentions** (WebSearch + WebFetch)
- **GitHub profile** (if technical subject)
- **Conference talks** (YouTube, conference sites)
- **Podcasts they appeared on** (WebSearch)
- **Books / articles they authored** (Amazon, JSTOR)

### Tertiary tier
- **Twitter/X** (rate-limited; degrade gracefully)
- **Reddit mentions**
- **Glassdoor reviews if they're a manager** (peers anonymous)
- **Personal blog posts**

### Subject-specific paths

| Purpose | Priority sources |
|---|---|
| Investment diligence on founder | LinkedIn + GitHub + court records + news |
| Interview prep for hiring | LinkedIn + GitHub + their public talks + writing |
| Personal vetting (date) | LinkedIn + news + court records (with Q6 exclusions) |
| Sales prep for pitch meeting | LinkedIn + recent public statements + their writing |

### Anti-patterns

- LinkedIn scraping without BYOK MCP — usually blocked; degrade gracefully
- Citing tertiary social media as primary signal (high noise)
- Ignoring publication / talk history for technical subjects (highest-signal source)

## Company

### Primary tier
- **Official website** (about, leadership, news, careers, pricing pages)
- **SEC EDGAR** (public companies) — 10-K, 10-Q, 8-K filings
- **Form 990** if foundation-affiliated
- **Court records** (litigation, regulatory) — federal + state
- **Patent filings** (USPTO + Google Patents) — for tech companies

### Secondary tier
- **Crunchbase free tier** (or Crunchbase MCP if BYOK)
- **News coverage** (WebSearch + WebFetch — major outlets)
- **Trade press** (TechCrunch, The Information, Stratechery for tech; Modern Healthcare for healthcare; etc.)
- **Investor letters / shareholder communications** (Berkshire, ARK, etc.)
- **Industry analyst reports** (if accessible)

### Tertiary tier
- **Glassdoor + Comparably** (employee sentiment — noisy but signal-y for trends)
- **Reddit / HN** (technical / startup sentiment)
- **LinkedIn company page**
- **GitHub** (for tech companies — repo activity signals)

### Subject-specific paths

| Purpose | Priority sources |
|---|---|
| Sales pitch | Official site + recent news + leadership + product launches |
| Investment diligence | SEC filings + Crunchbase + news + patent activity + financial trends |
| Acquisition diligence | SEC + court records + patent portfolio + Glassdoor (cultural fit) |
| Competitive intelligence | SEC + product launches + hiring patterns + patent activity |
| Journalism | Court records + SEC + regulatory actions + sources |

### Critical: SEC EDGAR for public companies

For US-listed companies, SEC EDGAR is **always primary tier** and **always free**:

```bash
curl 'https://data.sec.gov/submissions/CIK<10-digit-CIK>.json' \
  -H 'User-Agent: dossier-skill <user-email>'
```

- 10-K = annual report (audited financials)
- 10-Q = quarterly report
- 8-K = material event (CEO change, M&A, etc.)

Going-concern notes in 10-Ks are critical red-flag signal.

## Nonprofit

### Primary tier
- **ProPublica Nonprofit Explorer** (free; Form 990s + 990-T) — the canonical source
- **GuideStar** (if accessible)
- **Official website** + their published impact reports
- **State Attorney General nonprofit registry** (state-specific)

### Secondary tier
- **News coverage**
- **Charity Navigator ratings**
- **GiveWell / EA evaluations** (if EA-adjacent)
- **Board affiliations** (LinkedIn + foundation database)

### Tertiary tier
- **Social media coverage**
- **Donor forums**
- **Reviews sites** (Charity Watch, etc.)

### Subject-specific paths

| Purpose | Priority sources |
|---|---|
| Donor diligence | Form 990 + impact reports + board + financial trends |
| Board diligence | Form 990 + board members + governance docs |
| Journalism | Form 990 + court records + state AG actions + sources |

### Form 990 key metrics

- **Overhead ratio** (program / total expenses) — but beware: too-low can signal misclassification
- **Executive compensation** (Form 990 Schedule J)
- **Independent board %** — for governance signal
- **Related-party transactions** (Schedule L)
- **Going-concern notes** if any

## Government Org

### Primary tier
- **Official .gov website**
- **Federal Register notices** (regulations, rules)
- **GAO reports** (Government Accountability Office)
- **OIG reports** (Office of Inspector General per agency)
- **Congressional testimony / hearings**

### Secondary tier
- **News coverage** (especially WaPo, ProPublica federal beat)
- **ProPublica federal agency tracking**
- **Think tank reports** (Brookings, AEI, Heritage, etc.)

### Tertiary tier
- **Reddit / forum coverage**
- **Op-eds**

### Subject-specific paths

| Purpose | Priority sources |
|---|---|
| Federal contractor diligence | SAM.gov + agency procurement records + GAO + news |
| Journalism | GAO + OIG + Congressional + court records + sources |
| Lobbying targeting | LDA filings + agency contacts + hearings |

## BYOK MCP Enhancement

Paid MCPs (Apollo, Pitchbook, SimilarWeb, LinkedIn) add data but **must be flagged in audit log**:

| MCP | What it adds |
|---|---|
| LinkedIn | Person profile completeness, employment history accuracy |
| Crunchbase | Funding rounds, board, M&A activity for private companies |
| Apollo | Contact data, intent signals for sales contexts |
| Pitchbook | Deep private-market data, comparables |
| SimilarWeb | Traffic + competitive intelligence for digital businesses |

The audit log marks every BYOK-sourced finding with `[BYOK: <MCP-name>]` so the reader knows the provenance and can request verification through their own MCP access if needed.

## Sequential vs Parallel Discipline

Per research-pack convention: **sequential** with 1 q/sec etiquette. WebSearch + WebFetch tolerate higher rates than Consensus, but sequential keeps the skill robust to provider rate-limit shifts.

For multi-query subjects (companies with many available sources), Phase 4 might run 8-15 sequential queries. Total wall-clock: 10-20 seconds for queries; longer for fetches.

## Degradation Strategy

When a source fails:

| Source | If unavailable |
|---|---|
| LinkedIn | Fall back to WebSearch for headline facts; suggest user verify manually |
| SEC EDGAR | Retry once; if still down, note "public filings not retrieved" |
| Crunchbase | Use news + LinkedIn + WebSearch for funding rounds |
| ProPublica | Direct IRS query (slower); or note nonprofit data partial |
| Twitter/X | Skip; note in audit |

Never fabricate coverage when source is blocked. Always document the gap.

## Citations (7 sources)

1. **SEC EDGAR API documentation — https://www.sec.gov/edgar/sec-api-documentation.** Source for the public-company primary-tier discipline. EDGAR is the only free source for audited financial truth on US public companies.

2. **ProPublica Nonprofit Explorer — https://projects.propublica.org/nonprofits/.** Authoritative free source for Form 990 data. The primary tier source for any US nonprofit research.

3. **Federal Information Processing Standards (FIPS) + open-data.gov.** Source for government-org querying patterns. Federal Register + GAO + OIG are publicly-accessible primary sources.

4. **Heydon Pickering, *Inclusive Design Patterns* (2016).** Source for the "degrade gracefully when source fails" pattern. The skill applies progressive enhancement: query best source first, fall back to lower tiers when blocked.

5. **Bruce Schneier, *Beyond Fear* (2003).** Source for the BYOK-MCP audit-log flagging discipline. Provenance matters; users have a right to know which data came from which provider.

6. **OWASP Web Security Testing Guide.** Source for the user-agent + rate-limit etiquette in API calls. SEC EDGAR specifically requires User-Agent header with contact info; respecting these terms prevents access loss.

7. **Charity Navigator + GiveWell methodology pages.** Source for nonprofit-evaluation metrics (overhead ratio, exec comp, independent board %). The skill mirrors their established metric set rather than inventing new criteria.

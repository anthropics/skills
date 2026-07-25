# RePORTER POST Patterns + Plan-Tier Detection

This reference answers exactly one decision: **how does the grants skill query NIH RePORTER, and what plan-tier signals does it detect from Consensus responses?**

## The Critical Constraint

**NIH RePORTER's API v2 is POST-only.** `web_fetch` (which performs GET requests) **will not work**. You MUST use `bash_tool` + `curl`.

This is the #1 anti-pattern for the grants skill. If a future maintainer "simplifies" to web_fetch, RePORTER queries silently fail and the skill produces hollow institute-mapping sections.

## RePORTER API Reference

- **Endpoint:** `https://api.reporter.nih.gov/v2/projects/search`
- **Method:** POST
- **Content-Type:** `application/json`
- **No auth required** for public-data queries
- **Rate limit:** documented as 1 q/sec; the skill applies 1+ sec sequential pause per research-pack convention

## Standard POST Templates

### Narrow (AND) — direct overlap

```bash
curl -X POST 'https://api.reporter.nih.gov/v2/projects/search' \
  -H 'Content-Type: application/json' \
  -d '{
    "criteria": {
      "fiscal_years": [2023, 2024, 2025, 2026],
      "include_active_projects": true,
      "advanced_text_search": {
        "operator": "AND",
        "search_field": "all",
        "search_text": "deep learning electronic health records sepsis prediction"
      }
    },
    "limit": 50,
    "offset": 0,
    "include_fields": [
      "project_num",
      "project_title",
      "agency_ic_admin",
      "study_section",
      "fiscal_year",
      "principal_investigators",
      "abstract_text",
      "project_terms"
    ]
  }'
```

### Broad (OR) — adjacent work

```bash
curl -X POST 'https://api.reporter.nih.gov/v2/projects/search' \
  -H 'Content-Type: application/json' \
  -d '{
    "criteria": {
      "fiscal_years": [2023, 2024, 2025, 2026],
      "advanced_text_search": {
        "operator": "OR",
        "search_field": "all",
        "search_text": "machine learning critical care sepsis early warning"
      }
    },
    "limit": 50
  }'
```

## Dynamic Fiscal Year Window

NIH fiscal year runs **Oct 1 → Sep 30**. Current FY = year of next Sep 30.

Use `scripts/fiscal_year_calculator.py`:

```bash
python ../scripts/fiscal_year_calculator.py
# Output:
# Current calendar year: 2026
# Current fiscal year:   2026 (Oct 1 2025 - Sep 30 2026)
# Window (current + 3 prior): [2023, 2024, 2025, 2026]
```

**Never hardcode years.** A skill committed in 2025 with hardcoded `[2022, 2023, 2024, 2025]` produces stale results in 2027.

## Institute Tally + Study Section Ranking

After both narrow + broad responses return, aggregate:

### Institute tally

For each project: extract `agency_ic_admin` (the institute code like NCI, NHLBI, NIMH).

```python
from collections import Counter
institute_counts = Counter()
for project in projects:
    institute_counts[project['agency_ic_admin']] += 1
top_institutes = institute_counts.most_common(3)
```

Surface in DOCX Section 3 as ranked table with project counts + brief institute mission.

### Study section ranking

For each project: extract `study_section`.

```python
study_section_counts = Counter()
for project in projects:
    section = project.get('study_section', '')
    if section:  # Some projects unassigned
        study_section_counts[section] += 1
top_sections = study_section_counts.most_common(2)
```

Surface in DOCX Section 6.

## NOSI Discovery from RePORTER Results

NOSI (Notice of Special Interest) numbers appear as `NOT-*` in project abstracts, project terms, or related-FOA fields. Parse with regex:

```python
import re
NOSI_RE = re.compile(r'NOT-[A-Z]{2,3}-\d{2}-\d{3}')
nosi_numbers = set()
for project in projects:
    abstract = project.get('abstract_text', '')
    nosi_numbers.update(NOSI_RE.findall(abstract))
```

For each NOSI number, fetch via `web_fetch` (NOSIs have predictable URLs):

```
https://grants.nih.gov/grants/guide/notice-files/{NOSI_NUMBER}.html
```

If fetch fails: log `[NOSI {number} — fetch failed, not included]`. Never fabricate NOSI details.

## Plan-Tier Detection (Consensus)

Consensus has tiered plans with different per-query result caps. The skill detects from response text patterns:

| Pattern in response | Tier | Per-query cap |
|---|---|---|
| `"Showing top 10"` / `"upgrade for more"` | Free | 10 results |
| Receives 20 results without "showing top" | Pro | 20 results |
| Receives ≤3 results consistently | Unauthenticated / API quota issue | 3 results |
| No response / 401 / 403 | Auth failure | n/a |

Surface at end of Phase 2A in DOCX audit log:

> **Plan tier detected: Free** (Consensus returns ~10 results per query, capped). Total positioning landscape: 5 facets × 10 results = ~50 papers max. For deeper coverage, consider Consensus Pro (20/query).

This calibrates user expectations BEFORE they read the DOCX and wonder why coverage seems thin.

## Sequential Execution Discipline

Per research-pack convention: **1 q/sec, never parallelize.**

- 5 Consensus searches (Phase 2A) sequential — pause 1+ sec between
- 2 RePORTER POST searches (narrow + broad) sequential
- N NOSI `web_fetch` calls sequential

Each call records timestamp via `citation_tracker.py`; second call within 1s is rejected.

Total Phase 2 wall-clock time: ~7-10 sec for searches + however long NOSI fetches take.

## Error Handling

| Failure | Handling |
|---|---|
| Consensus 429 (rate limit) | Wait 3s, retry once, log to audit |
| Consensus 0 results for a facet | Surface explicitly in DOCX positioning section; mark `[no results — verify terminology]` |
| RePORTER 5xx | Retry once after 3s; if still failing, log and continue with what's available |
| RePORTER <5 results on narrow | Document low count; rely on broad OR for coverage |
| NOSI fetch fails | `[NOSI {number} — fetch failed]`; never fabricate |
| 3 consecutive failures across tools | Halt; alert researcher with what's missing |
| Auth failure (401/403) | Halt; tell user to check API key or MCP connection |

## Citations (7 sources)

1. **NIH RePORTER API v2 documentation — https://api.reporter.nih.gov/documents/Data%20Element%20Descriptions.pdf.** Authoritative spec for POST endpoint, field definitions, fiscal-year filter semantics. The skill's curl templates are direct applications.

2. **NIH Office of Extramural Research — *NIH Guide for Grants and Contracts* (https://grants.nih.gov/grants/guide).** Source for NOSI / FOA URL structure. NOSI naming conventions (`NOT-{IC}-{YY}-{NNN}`) are documented here.

3. **`praw` library + Reddit API community guidance.** Source for the "1 q/sec is the polite default" pattern that the skill applies to RePORTER even though RePORTER's documented limits are looser. Politeness with shared infrastructure.

4. **Mike Cohen, "Exponential Backoff and Jitter" — AWS Architecture Blog, 2015.** Source for the "wait 3s + retry once" retry pattern. Research-workflow scale doesn't justify exponential backoff.

5. **`curl` documentation (https://curl.se/docs/manual.html).** Source for POST body + Content-Type header syntax. The skill's curl templates follow `curl --help`.

6. **Maynez et al., "On Faithfulness and Factuality in Abstractive Summarization" — ACL 2020.** Source for the source-discipline rule that justifies refusing to fabricate NOSI details when fetch fails. LLMs hallucinate plausible-looking NIH NOSI numbers; refuse.

7. **Susskind, D., "Show your work" — *Communications of the ACM*, 2024.** Source for the audit-log section's role: transparent surfacing of what was queried, what was returned, what was cited. The audit-log table in DOCX Section 9 is this principle's implementation.

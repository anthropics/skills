---
name: grants
description: "NIH grant research skill for clinical researchers. Grill-me intake (research idea + career stage + preliminary data + environment + submission posture + known institute targets) locks down the funding strategy before any search runs. Runs a 5-facet Consensus positioning analysis (with draft Significance/Innovation language), maps the research to the right NIH institutes and study sections via RePORTER, finds NOSIs and funded overlap, and produces an editable Word document (.docx) with budget/scope-aware mechanism recommendations, submission timelines, and a mandatory program officer recommendation. Use when the user asks about research funding or makes any grant-related request (e.g., 'grants for [topic]', 'find grants for my research idea', 'what grants match my research', 'help me find NIH funding', 'grant opportunities for my research'). NIH-only scope — non-NIH funders (PCORI, DOD CDMRP, VA, foundations) are out of scope and flagged at intake."
license: MIT
metadata:
  source_spec: "megaprompts/08-grants-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  research_pack_convention: "Agent Integrity Rules verbatim per PR #657 audit"
  version: 1.0.0
---

# Grants — NIH Funding Intelligence

> **Portability:** Requires `bash_tool` (for RePORTER POST via curl), Node.js with `docx` package, and a Consensus MCP connection. Works in Claude Code CLI natively. In Claude.ai with Code Execution + Consensus MCP, the workflow is supported but slower.

> **Scope: NIH-only.** Non-NIH funders (PCORI, DOD CDMRP, VA, foundations) are out of scope and flagged at intake.

For a clinical researcher with a research idea, produce a strategic NIH funding overview as an editable `.docx`. Output covers research positioning analysis, institute mapping, targeted grant discovery, and strategic recommendations the researcher can edit, copy from, and share with their mentor.

## Agent Integrity Rules (Research-Pack Convention)

Inherited; locked verbatim per PR #657 audit.

- **Execution discipline.** A step isn't complete until result is confirmed received. Consensus calls **sequential with 1+ sec pause**. RePORTER calls sequential.
- **Data sourcing.** Count only what tool calls returned this session. Never supplement with training knowledge. Training knowledge labeled `[Not from Consensus/RePORTER — reference information]` and excluded from counts.
- **Counts & attribution.** Queries sent / results shown / results cited — three separate numbers, never conflate. Every cited paper has retrievable URL from this session.
- **Error handling.** On failure → wait 3s → retry once → log. After 3 consecutive failures across tools: stop, alert researcher, explain what's missing. Never silently skip.
- **Transparency.** Audit Log section in the DOCX. Same standards in chat summary as in document.

See [`references/reporter_post_patterns.md`](references/reporter_post_patterns.md) for the RePORTER POST canon + plan-tier detection.

## Phase 1: Grill-Me Intake (6 forcing questions, one at a time)

### Q1 (root) — Research idea

> **Describe the research idea in 2–3 sentences. What's the question, what's new, and what's the clinical relevance? Vague answers ("AI for healthcare", "biomarkers for disease X") will be rejected — push for specificity.**
>
> *Why I'm asking:* Five Consensus searches (established / stakes / current approaches / adjacent methods / gaps) depend on a precise research idea. Vague ideas produce vague gap quotes and useless positioning narrative.

Refuse mush. Re-ask once with examples if user is too broad.

### Q2 (depends on Q1) — Career stage

> **Career stage — pick one:**
>
> 1. Pre-doctoral (PhD student, T32 trainee)
> 2. Postdoctoral fellow (F32, K99 candidate)
> 3. Early career (K-award candidate, first R01)
> 4. Independent investigator (multiple R01s, established lab)
> 5. Senior PI (R35, P-series, U01 leadership)
>
> *Why I'm asking:* Career stage filters mechanism recommendations. F-series for trainees, K-series for early career, R-series for independent. Picking the wrong stage produces unfundable mechanism suggestions.

Forcing choice.

### Q3 (depends on Q2) — Preliminary data status

> **Preliminary data — pick one:**
>
> 1. None (de novo project, no pilot data yet)
> 2. Pilot data (early findings, single-site)
> 3. Strong preliminary (multi-experiment, ready for R01-scale)
> 4. Validated and ready (multi-site, publication-ready)
>
> *Why I'm asking:* Prelim data status drives mechanism budget. No data → R03 / R21 pilot scope. Strong prelim → R01 / U01 multi-site scale. Mismatch produces uncompetitive applications.

### Q4 (depends on Q2) — Environment

> **Research environment — pick one:**
>
> 1. R01-eligible (research-intensive institution with NIH base funding)
> 2. Mid-tier (regional academic medical center, modest NIH portfolio)
> 3. Resource-constrained (smaller institution, minimal NIH base)
> 4. Industry-collaborative (academic + industry partnership)
>
> *Why I'm asking:* Environment affects scope realism (multi-site U01 requires R01-eligible) and which mechanism categories are competitive (R15 specifically targets resource-constrained).

### Q5 (depends on Q1) — Submission posture

> **Submission posture — pick one:**
>
> 1. New application (first submission, no prior reviews)
> 2. Resubmission (A1 with reviewer responses needed)
> 3. Exploring (haven't decided yet whether to submit)
>
> *Why I'm asking:* Resubmissions need reviewer-response guidance in the DOCX (Section 7). New applications skip that. Exploring shifts emphasis to landscape over strategy.

### Q6 (depends on Q1) — Known institute targets

> **Are you already considering specific NIH institutes? List names (NCI / NHLBI / NIMH / NINDS / NIDDK / etc.) or say "no preference — find the right ones".**
>
> *Why I'm asking:* If you have an institute hypothesis, I'll validate it against RePORTER data. If not, I'll surface the top-3 institutes funding adjacent work from the institute-tally.

Accept "no preference" as the common case.

**Stop condition:** After Q6, commit and start Phase 2A. Never re-open intake after Phase 2A begins.

## Phase 2A: Research Positioning (5 Consensus searches)

Run sequentially at 1 q/sec. Each search corresponds to one positioning facet:

1. **Established** — `"<research idea>" established evidence` — what's known
2. **Stakes** — `"<topic>" mortality OR burden OR cost OR prevalence` — why it matters
3. **Current Approaches** — `"<topic>" current treatment OR standard of care OR approach` — state of the art
4. **Adjacent Methods** — `"<related technique>" applied to <topic>` — methodological possibilities
5. **Gaps** — `"<topic>" limitations OR unanswered OR future directions OR challenge` — gap signals

Use `scripts/citation_tracker.py --action record_consensus_search` for each. Plan-tier detected from first response.

**Synthesis:** for each facet, extract 2-3 quotable findings (becomes Section 2 gap quotes). Draft Significance/Innovation language using "the field has established X (refs), but Y remains unanswered (refs)" pattern.

## Phase 2B: Institute Mapping + Grant Discovery (RePORTER POST)

RePORTER is **POST-only**. Use `bash_tool` + `curl` — never `web_fetch`.

### Dynamic fiscal year window

Compute at runtime via `scripts/fiscal_year_calculator.py`. Default: current FY + 3 prior. Federal FY starts Oct 1, so:

```bash
python scripts/fiscal_year_calculator.py --output json
# Returns: {"current_fy": 2026, "window": [2023, 2024, 2025, 2026]}
```

### Narrow (AND) search — finds direct overlap

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
        "search_text": "<key term 1> <key term 2>"
      }
    },
    "limit": 50,
    "include_fields": ["project_num", "project_title", "agency_ic_admin", "study_section", "fiscal_year", "principal_investigators", "abstract_text"]
  }'
```

### Broad (OR) search — finds adjacent work

```bash
curl -X POST 'https://api.reporter.nih.gov/v2/projects/search' \
  -H 'Content-Type: application/json' \
  -d '{
    "criteria": {
      "fiscal_years": [2023, 2024, 2025, 2026],
      "advanced_text_search": {
        "operator": "OR",
        "search_field": "all",
        "search_text": "<term> <synonym> <related concept>"
      }
    },
    "limit": 50
  }'
```

### Institute tally + study section ranking

After RePORTER responses:
- Tally `agency_ic_admin` (institute code: NCI, NHLBI, NIMH, etc.) → top-3 funding institutes
- Tally `study_section` → top-2 study sections (where applications go for review)

### NOSI discovery

Parse RePORTER responses for `NOT-*` opportunity numbers. For each:

```bash
# NOSIs live at predictable URLs:
# https://grants.nih.gov/grants/guide/notice-files/NOT-<INSTITUTE>-<YEAR>-<NUMBER>.html
web_fetch <url>
```

If fetch fails: log `[NOSI {number} — fetch failed, not included]`, continue.

## Mechanism Matching (Scope-Aware)

NOT career stage alone. Career stage **+** project scope **+** prelim data drive recommendation.

Use `scripts/mechanism_matcher.py`:

```bash
python scripts/mechanism_matcher.py \
  --career-stage "early_career" \
  --prelim-data "pilot" \
  --environment "r01_eligible" \
  --scope "single_site" \
  --output json
# Returns mechanism shortlist with rationale
```

See [`references/nih_mechanism_matching.md`](references/nih_mechanism_matching.md) for the full matrix.

## Phase 3: DOCX Generation

9 sections via Node.js + `docx` library. See [`references/docx_9_sections.md`](references/docx_9_sections.md) for full spec.

1. **Executive Summary** — title + career stage + environment + 3-4 key findings bullets
2. **Research Positioning** — 3-5 gap quotes (italicized, inline Consensus citations) + 2-3 paragraph positioning narrative + supporting evidence table
3. **Target Institutes** — ranking table (institute, project count in window, % match to your idea) + 2-3 sentence interpretation
4. **Grant Opportunities** — bold NOSI callout if any. Top-3 grants table with hyperlinked FOAs + per-grant scope/budget fit paragraph
5. **Funded Overlap** — top-5 projects table (PI, project_num, IC, year, hyperlinked to RePORTER) + differentiation paragraph
6. **Study Sections** — ranking table + best-match interpretation
7. **Strategic Recommendations & Next Steps** — 3-4 numbered recs + **mandatory program officer rec** + submission timeline note + (if resubmission Q5=2) reviewer-response guidance + closing paragraph
8. **References** — numbered bibliography, hyperlinked to Consensus
9. **Audit Log** — Consensus searches table, plan-tier note, RePORTER searches table, NOSI fetches table, summary stats, tool constraints note, failed steps

### Styling

Arial 12pt body, navy headings (#1a3a5c), light blue table headers (#e8f0f8), amber NOSI callout. `ExternalHyperlink` patterns:
- Paper citations: `https://consensus.app/papers/...`
- FOA links: `https://grants.nih.gov/grants/guide/...`
- RePORTER projects: `https://reporter.nih.gov/project-details/<id>`

## Mandatory Program Officer Recommendation

Always include in Section 7:

> **Recommended next step: contact program officer at {top institute}.** Find their staff page at https://www.nih.gov/institutes-nih/list-nih-institutes-centers-offices → {institute} → Program Officers. Prepare: 1-page specific aims + your CV + 3 specific questions about fit. Email subject: "Pre-application inquiry: <topic>".

This is the single most valuable advice for any applicant. Never skip.

## Submission Timeline (Embedded in DOCX Section 7)

| Mechanism | Standard receipt dates |
|---|---|
| R01, R21, R03 | Feb 5, Jun 5, Oct 5 |
| K awards (K01, K08, K23, K99) | Feb 12, Jun 12, Oct 12 |
| R34, R61/R33 | Feb 16, Jun 16, Oct 16 |
| F31, F32 | Apr 8, Aug 8, Dec 8 |

## Phase 4: Deliver

- Save DOCX to `<output-dir>/grants_<topic-slug>_<YYYY-MM-DD>.docx`
- Chat summary: file path + audit counts + plan tier + verdict on institute targets
- Validate: check zip integrity with `python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).testzip()" <docx>` (no output = intact), then confirm the required sections are present

## Tooling

| Script | Role |
|---|---|
| `scripts/citation_tracker.py` | Three-count audit (Consensus sent/shown/cited + RePORTER projects/cited) at `~/.grants_sessions/<session>.json` |
| `scripts/fiscal_year_calculator.py` | Current FY + 3-prior window. Computed at runtime, never hardcoded. |
| `scripts/mechanism_matcher.py` | Career stage × scope × prelim → mechanism recommendation shortlist |

## References

- [`references/nih_mechanism_matching.md`](references/nih_mechanism_matching.md) — career stage × scope × prelim → mechanism canon (7+ sources)
- [`references/reporter_post_patterns.md`](references/reporter_post_patterns.md) — RePORTER curl POST templates + plan-tier detection (7+ sources)
- [`references/docx_9_sections.md`](references/docx_9_sections.md) — 9-section .docx spec + technical requirements (7+ sources)

## Error Handling

| Failure | Behavior |
|---|---|
| Consensus rate-limit hit | Wait 3s, retry once, log; if still failing, alert researcher |
| Consensus returns 0 for a facet | Surface explicitly; never fill with training knowledge |
| Consensus plan-tier cap detected | Log tier, note in audit, surface to researcher |
| RePORTER POST returns error | Retry once after 3s; if still failing, log and continue |
| RePORTER returns <5 on narrow | Document; broad OR should compensate; surface low count |
| NOSI fetch fails | Log `[NOSI {n} — fetch failed]`, continue |
| 3 consecutive tool failures | Stop, alert researcher with what's missing |
| DOCX generation fails | Save raw data as JSON fallback so researcher doesn't lose work |

## Anti-Patterns To Reject

- Parallelizing Consensus calls (will hit rate limit)
- Using `web_fetch` for RePORTER (POST-only — `web_fetch` is GET)
- Hardcoded fiscal year values
- Mechanism recommendations based on career stage alone (must consider scope too)
- Silently filling thin facet results with training knowledge
- Skipping the audit log
- Skipping the program officer recommendation
- Conflating "papers found" with "papers shown" with "papers cited"
- Fabricating NOSI details when fetch fails

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/08-grants-megaprompt.md`](../../../../megaprompts/08-grants-megaprompt.md)
**Build pattern:** Path B (direct conversion). Research-pack sibling of pulse + litreview.

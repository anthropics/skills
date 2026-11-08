---
name: consensus-grant-finder
description: "Consensus-powered NIH grant research skill. Use when someone wants to find grants for their research idea. Runs a 5-facet positioning analysis via Consensus (with draft Significance/Innovation language), maps the research to the right NIH institutes and study sections, finds NOSIs and funded overlap, and produces an editable Word document (.docx) with budget/scope guidance, submission timelines, and program officer recommendations. Trigger on: 'find grants for my research idea', 'what grants match my research', 'help me find NIH funding', 'grant opportunities for my research', or any grant-related request where speed and clarity matter."
---

# Consensus Grant Research

## Overview

This skill helps clinical researchers scope the NIH funding landscape for a research idea. It currently focuses on NIH funding — other funders (PCORI, DOD, VA, foundations) are not yet covered. It does three things:
1. **Research positioning analysis** — 5-facet Consensus search that produces gap quotes and draft positioning language for the grant's Significance/Innovation sections
2. **Institute mapping** — identifies which NIH institutes are actually funding this area
3. **Targeted grant discovery** — NOSIs, open FOAs, and funded overlap filtered by the mapped institutes

Output: a Word document (.docx) the researcher can edit, annotate, and build on — not a static PDF.

---

## Agent Integrity Rules

These rules govern every step of this skill. They exist because grant applicants make real decisions based on this output — a fabricated citation or silently skipped search can waste months of effort.

### Execution discipline
- A step is not complete until its result is confirmed received. Never mark a search or API call "done" based on intent — only on a confirmed response.
- Run Consensus searches **sequentially, one at a time**, with a minimum 1-second pause between calls. The Consensus API enforces a 1 query/second rate limit — parallel calls will fail or be throttled. After each search, confirm results were received before proceeding to the next.
- Run RePORTER API calls sequentially as well — wait for each response before sending the next.

### Data sourcing
- Count only what was returned by tool calls in this session. Never supplement with information from training knowledge, prior conversations, or any source other than the current Consensus or RePORTER response.
- If a search returns fewer results than expected (e.g., 0–2 papers for a facet), surface that gap explicitly to the researcher. Do not fill it silently with training knowledge.
- If training knowledge is included for any reason (e.g., mechanism budget ranges, submission dates), label it `[Not from Consensus/RePORTER — reference information]` and exclude it from paper counts and citation lists.

### Counts & attribution
- Track three separate numbers per search facet: **queries sent**, **results received** (actually shown/returned in the response), and **results cited** in the final document. Never conflate them.
- Every cited paper must have a retrievable URL (Consensus link or DOI) from this session. No URL = not citable.
- **Detect Consensus plan-tier caps.** Consensus responses include language like "Found 20 papers, showing top 10." Parse this for every search. The number *shown* (not found) is your actual result count — you can only cite what was shown. Typical caps by tier:
  - **Unauthenticated / not logged in**: ~3 results shown
  - **Free plan**: ~10 results shown (out of ~20 found)
  - **Premium plan**: ~20 results shown
  If you detect a cap (e.g., "showing top 10" when 20 were found), log it in the audit log and surface it to the researcher: "Consensus found [N] papers but returned [M] due to plan limits. Citations are drawn only from the [M] shown." This is critical — the researcher needs to know whether sparse results reflect a genuine gap in the literature or just a plan-tier ceiling.
- Report all tool constraints that affect coverage: Consensus result caps per query, RePORTER pagination limits, and any rate-limit-induced gaps. The researcher should understand the ceiling on what this analysis can find.

### Error handling
- On any tool failure (Consensus search error, RePORTER timeout, web fetch failure): wait 3 seconds, retry once, and log the failure.
- After 3 consecutive failures across any combination of tools: stop and alert the researcher before proceeding. Explain what failed and what data will be missing.
- Never silently skip a failed step. If a search couldn't be completed, note it in the output with `[Search failed — not included in analysis]`.

### Transparency & audit log
- Include an **Audit Log** section in the .docx (Section 9, after References) documenting: each tool call made, the query or endpoint used, how many results were returned, and how many were cited. This lets the researcher (and their mentor) understand exactly what the analysis is based on.
- Apply the same sourcing and attribution standards to the chat summary message as to the formal document. Don't cite papers in chat that aren't traceable to a tool response.

---

## Workflow

### Phase 1: Intake

First, ask the researcher to describe their research idea in a few sentences. Before the follow-up questions, set expectations:

> "Just so you know — this analysis focuses on NIH funding (institutes, mechanisms, NOSIs, RePORTER data). If you're also considering PCORI, DOD CDMRP, VA Merit, or foundation grants, I won't cover those here, but I can help you think through them separately."

Then ask 3 quick follow-up questions to tailor the analysis. Use a multi-select format so it feels fast, not like a bureaucratic form.

**Question 1 — Career stage & mechanism fit**
> "Which best describes your current position? (This determines which grant mechanisms to prioritize.)"
> - Trainee (pre-doctoral or postdoc) — F31, F32, T32
> - Early-career faculty (pre-tenure, no major grants yet) — K01, K08, K23, K99/R00, R21
> - Mid-career (have or had a K or first R01) — R01, R21, R34
> - Senior investigator — R01, R35, P01, U01

**Question 2 — Preliminary data & prior submissions**
> "Where are you in the process?"
> - Starting from scratch — no preliminary data yet
> - Have some pilot data or related publications
> - Resubmission — previously submitted and received a score
> - Resubmission — previously submitted but not scored (triaged)

This matters because it changes the strategic recommendation: someone with no preliminary data needs an R21 or pilot funding path first, while someone resubmitting needs differentiation guidance.

**Question 3 — Institutional environment**
> "What best describes your research environment?"
> - Major research university (R1) with relevant core facilities
> - Academic medical center / teaching hospital
> - Smaller institution or community-based setting
> - VA or military-affiliated

This affects which mechanisms are realistic (e.g., VA-affiliated researchers may have access to VA Merit Awards) and how to frame the Environment section of a grant.

Once you have the research idea + these 3 answers, proceed immediately:

> "Running your analysis now — novelty search, institute mapping, and grant matching."

---

### Phase 2A: Research Positioning Analysis (5 Consensus searches)

The goal of this phase is NOT to answer "is this novel?" — it's to produce **positioning language** the researcher can use in their grant application. The output should read like a draft of their Significance and Innovation sections: "The field has established X and Y, but no one has done Z in this population — that's the gap this project fills."

Run 5 searches using `Consensus:search` **sequentially** (one at a time, with at least a 1-second pause between each call). After each search, confirm results were received and log the count before moving to the next. If a search fails, wait 3 seconds, retry once, and log the outcome. Each search builds a different part of the positioning argument.

**Search 1 — What's established (the foundation)**
What does the field already agree on? This becomes the "what is known" setup in a Significance section.
```
query: "<the core research concept as a focused academic query>"
year_min: 2019
```

**Search 2 — The problem's importance (the stakes)**
Why does this matter? Prevalence, burden, outcomes, disparities. This is the "why now" and "why this matters" argument.
```
query: "<disease or condition prevalence outcomes burden in [target population]>"
year_min: 2019
```

**Search 3 — Current approaches and their limits (the competition)**
What interventions, methods, or solutions exist today? Understanding current practice reveals what's insufficient — which is the researcher's opening.
```
query: "<current clinical management interventions guidelines for [condition or domain]>"
year_min: 2019
```

**Search 4 — The proposed method in adjacent contexts (the innovation angle)**
Has anyone applied this specific approach elsewhere? If yes, that's validation. If no, that's novelty. Either way, it's useful positioning.
```
query: "<methodological approach or technique applied to [similar problems or populations]>"
year_min: 2019
```

**Search 5 — What researchers say is missing (the gap — most important)**
This is the highest-value search. Explicitly look for language where researchers call out gaps, limitations, and future directions. These quotes become the backbone of the positioning argument.
```
query: "<research gaps limitations unmet needs future directions in [the field]>"
year_min: 2019
```

**After all 5 complete, verify and then build the positioning brief:**

Before synthesizing, verify completeness. For each of the 5 searches, confirm you have a response with a result count. If any search returned 0 results or failed, note it explicitly — this is a gap the researcher needs to know about. Initialize a running audit log tracking: search facet, query used, results received, and results that will be cited.

The synthesis is the most important output of this entire skill. Don't just list counts — build an argument.

1. **Deduplicate** papers across all 5 searches by title/DOI. Papers found in multiple facets are high-signal. Record the pre- and post-deduplication counts.

2. **Extract gap quotes first** — scan abstracts for language like "future research should", "remains unclear", "no studies have", "limited evidence", "further investigation needed", "critical gap". Pull 3–5 of these with full citations. These are the centerpiece.

3. **Write a positioning narrative** (2–3 paragraphs) that the researcher could adapt for their Significance/Innovation sections:
   - Paragraph 1: "The field has established [X, Y, Z — from Searches 1-2]. The burden is significant because [stakes from Search 2]."
   - Paragraph 2: "Current approaches include [Search 3 findings], but they fall short because [gap quotes from Search 5]. Specifically, [quote 1] and [quote 2]."
   - Paragraph 3: "This project proposes [researcher's idea]. [Search 4 findings] suggest this approach is feasible, and the gap identified above shows it has not been applied to [this population/context]. This represents a [novel/underexplored] intersection."

4. **Build a supporting evidence table** — this is secondary to the narrative above:
   - Facet | Query Used | Results Received | Results Cited | Coverage Level (Minimal/Moderate/Substantial) | Key takeaway for positioning
   - If any facet received 0 results, include it in the table with a note: "No results returned — gap in coverage"

5. **Build the master paper list** with: title, authors, year, journal, citation_count, url — this feeds the bibliography

---

### Phase 2B: Institute Mapping + Grant Discovery (run after 2A)

#### Step 1: RePORTER funded project search

**IMPORTANT: The NIH RePORTER API requires POST requests. Always use `bash_tool` with `curl` — never `web_fetch`, which only supports GET.**

Run two searches via `bash_tool` — narrow (AND) and broad (OR):

Compute the fiscal year window dynamically: use the current year and the 3 preceding years (e.g., if running in 2026, use `[2023, 2024, 2025, 2026]`). This keeps results current without manual updates.

```bash
# Narrow search — 3-4 core terms with AND
CURRENT_YEAR=$(date +%Y)
FY_RANGE="[$((CURRENT_YEAR-3)), $((CURRENT_YEAR-2)), $((CURRENT_YEAR-1)), $CURRENT_YEAR]"

curl -s -X POST "https://api.reporter.nih.gov/v2/projects/search" \
  -H "Content-Type: application/json" \
  -d '{
    "criteria": {
      "advanced_text_search": {
        "operator": "and",
        "search_field": "projecttitle,terms,abstract",
        "search_text": "NARROW KEYWORDS"
      },
      "fiscal_years": '"$FY_RANGE"',
      "include_active_projects": true
    },
    "limit": 20,
    "offset": 0,
    "include_fields": ["ProjectTitle","AbstractText","ActivityCode","AwardAmount","FiscalYear","PrincipalInvestigators","Organization","OpportunityNumber","AgencyIcAdmin","ProjectNum","ProjectNumSplit","StudySection"]
  }'

# Broad search — 5-6 related terms with OR
curl -s -X POST "https://api.reporter.nih.gov/v2/projects/search" \
  -H "Content-Type: application/json" \
  -d '{
    "criteria": {
      "advanced_text_search": {
        "operator": "or",
        "search_field": "projecttitle,terms",
        "search_text": "BROADER KEYWORDS"
      },
      "fiscal_years": '"$FY_RANGE"',
      "include_active_projects": true
    },
    "limit": 20,
    "offset": 0,
    "include_fields": ["ProjectTitle","AbstractText","ActivityCode","AwardAmount","FiscalYear","PrincipalInvestigators","Organization","OpportunityNumber","AgencyIcAdmin","ProjectNum","ProjectNumSplit","StudySection"]
  }'
```

Run the narrow search first. Confirm a valid JSON response before running the broad search. If either call fails, wait 3 seconds and retry once. Log both outcomes (success with result count, or failure).

Parse both responses in Python, combine results, and deduplicate by `project_num`. Record: narrow results received, broad results received, total after dedup.

#### Step 2: Institute Mapping

From the combined results, tally `agency_ic_admin.abbreviation` across all projects. The top 2–3 institutes by count are the **target institutes** for this researcher. Example output:

> "NIAMS is funding 8 projects in this space, NIA is funding 5, NIDDK is funding 3 → primary target: NIAMS, secondary: NIA"

This is one of the most actionable findings for the researcher — surface it clearly so they know exactly where to direct their application.

#### Step 3: Study Section Mapping

From the combined project results, tally `study_section` values. This tells the researcher which review panels are evaluating work in their space — a critical strategic decision that most applicants don't think about systematically.

For the top 2–3 study sections by count, include:
- Study section abbreviation and full name
- Number of projects from the results reviewed there
- A note on fit: "This panel has a track record of reviewing [type of work] — your application would be in familiar territory here."

If study section data is missing or sparse in the results, note that honestly rather than guessing. The researcher can verify assignments via the CSR study section roster pages at `https://public.csr.nih.gov/studysections`.

#### Step 4: NOSI Detection

From the project results, extract all unique `opportunity_number` values. Filter for any that start with `NOT-` — these are Notices of Special Interest. For each NOSI found:

```
GET https://grants.nih.gov/grants/guide/notice-files/{NOSI_NUMBER}.html
```

Fetch each NOSI one at a time (respect the sequential execution rule). Parse the response for:
- Notice title (in `<h1>` or `<title>` tag)
- Institute (paragraph text near top)
- Purpose/scope (first substantive paragraph)
- Expiration or deadline if present

If a NOSI fetch fails, log it as `[NOSI {number} — fetch failed, not included]` and move on. If no NOSIs are found in project results, note this honestly — don't fabricate.

#### Step 5: Grant mechanism matching (career stage + project scope)

From the funded project results, extract unique `opportunity_number` values that are FOAs (start with `PA-`, `PAR-`, `PAS-`, or `RFA-`).

Mechanism selection isn't just about career stage — it's about whether the *project scope* fits the mechanism. Use both career stage and project characteristics to recommend mechanisms.

**Mechanism reference (career stage + budget + scope):**

| Mechanism | Typical budget | Duration | Best for | Prelim data needed? |
|-----------|---------------|----------|----------|-------------------|
| F31/F32 | Stipend + tuition/fees | 1–3 yrs | Trainees (pre-doc / postdoc) | Some |
| T32 | Institutional training grant | 2–5 yrs | Trainees via mentor's program | N/A |
| R03 | ~$50K/yr direct | 2 yrs | Small, self-contained projects; pilot studies | Minimal |
| R21 | ~$275K total direct | 2 yrs | Exploratory/developmental; new directions | Minimal to moderate |
| K01/K08/K23 | $100–250K/yr (includes salary) | 3–5 yrs | Early-career mentored development | Moderate |
| K99/R00 | K99: ~$100K/yr; R00: ~$250K/yr | 2+3 yrs | Postdoc → faculty transition | Moderate |
| R01 | ~$250K+/yr modular direct | 3–5 yrs | Full research project, the workhorse | Strong |
| R34 | ~$450K total direct | 3 yrs | Clinical trial planning (no execution) | Moderate |
| R61/R33 | Phased, varies | 2+3 yrs | High-risk ideas with milestone gates | Moderate for R61 |
| R35 | ~$750K/yr direct | 7 yrs | Outstanding investigator, broad program | Extensive track record |
| P01 | Multi-component, $1M+/yr | 5 yrs | Multi-PI program projects | Extensive |
| U01 | Varies, often $500K+/yr | 3–5 yrs | Cooperative agreements with NIH involvement | Strong |
| DP1/DP2 | ~$500K/yr direct | 5 yrs | Director's awards for bold, high-risk ideas | Varies |

**How to match:**
- Filter first by career stage (matching intake categories)
- Then filter by project scope: Does the researcher's idea fit in a 2-year $275K R21, or does it need a 5-year R01? If they described a large multi-site study, an R21 won't cover it. If they described a pilot, an R01 is overkill.
- Consider preliminary data from intake: "starting from scratch" → R21, R03, or R61. "Have pilot data" → R01 may be realistic. "Resubmission" → match the original mechanism unless the score suggests a mismatch.

For the top 3 FOAs, construct the link:
- PA/PAR/PAS types: `https://grants.nih.gov/grants/guide/pa-files/{FOA}.html`
- RFA types: `https://grants.nih.gov/grants/guide/rfa-files/{FOA}.html`

---

### Phase 3: Generate the DOCX

**Read the DOCX skill first** at `/mnt/skills/public/docx/SKILL.md` for setup patterns and best practices. The output is a Word document so the researcher can edit it, copy sections into grant applications, and add their own notes.

Generate the .docx using JavaScript with the `docx` library. Install via bash_tool:

```bash
npm install -g docx
```

Write the full document generation as a Node.js script and execute it with `bash_tool`.

#### Report structure

**Section 1 — Executive Summary**
- Title: "Grant Research Overview: [research topic]"
- Date, career stage, institutional environment
- Executive Summary: 3–4 bullet points covering novelty level, top institute, top grant, key differentiator

**Section 2 — Research Positioning**
- Heading: "Your Positioning in the Field"
- **Lead with the gap quotes** (3–5 italicized quotes with inline citations hyperlinked to Consensus). These are the most valuable part of the entire document — they give the researcher citable evidence that the gap they're targeting is real and recognized.
- **Positioning narrative** (2–3 paragraphs): the draft Significance/Innovation argument from Phase 2A. Write this in a tone the researcher can adapt directly into their grant. Use phrases like "The field has established..." / "Current approaches fall short because..." / "This project addresses an unmet need by..."
- **Supporting evidence table**: Facet | Query Used | Results Received | Results Cited | Coverage Level | Key Takeaway — this is context for the narrative above, not the main event. If any facet returned 0 results, include it with a note explaining the gap.

**Section 3 — Target Institutes**
- Heading: "Where NIH Is Funding This Work"
- Institute ranking table: Institute | Full Name | Projects Found | Primary Mechanism
- 2–3 sentence interpretation: "NIAMS is the primary home for this work, with consistent R01 funding. NIA represents a secondary opportunity particularly for aging-related angles."

**Section 4 — Grant Opportunities**
- Heading: "Recommended Funding Opportunities"
- If NOSIs found: bold callout at top — "Active Notice of Special Interest: [title] ([number]) — [1-sentence summary]"
- Top 3 grants table: Mechanism | FOA Number (hyperlinked) | Institute | Budget & Duration | Career Stage Fit
- For each recommended grant, include a short paragraph: why this mechanism fits the *project scope* (not just career stage), what the budget allows, and whether the researcher's preliminary data situation is a good match. E.g., "An R21 ($275K over 2 years) would let you establish [specific aim] as proof-of-concept before pursuing a full R01. Your pilot data on [X] is sufficient for this mechanism."

**Section 5 — Funded Overlap**
- Heading: "Similar Funded Research"
- Top 5 projects table: Title (hyperlinked to NIH Reporter) | PI | Institution | Award | Year
- Differentiation paragraph: "Your idea differs from existing funded work in [2–3 specific ways]"

**Section 6 — Study Sections**
- Heading: "Where This Work Gets Reviewed"
- Table: Study Section | Full Name | Projects Found | Fit Notes
- 1–2 sentence interpretation on which panel is the best match and why

**Section 7 — Strategic Recommendations & Next Steps**
- 3–4 numbered recommendations (e.g., "Target NIAMS with an R21 to establish preliminary data before an R01 submission")
- **Always include a program officer recommendation.** This is the single most valuable piece of advice for any grant applicant. Format it as: "Contact the program officer at [institute] before submitting. POs can confirm your idea fits the institute's priorities, suggest the right FOA, and flag potential issues. Find staff contacts at https://www.nih.gov/institutes-nih/list-nih-institutes-centers-offices → [specific institute] → 'Staff' or 'Program Officers' page."
- If the researcher indicated "resubmission" in intake, include guidance on how to frame the response to reviewers and what changed
- **Include a submission timeline note** based on the recommended mechanism. NIH standard receipt dates rarely change — include the relevant ones so the researcher can plan backwards:

  | Mechanism | Standard receipt dates |
  |-----------|----------------------|
  | R01, R21, R03 | Feb 5, Jun 5, Oct 5 |
  | K awards (K01, K08, K23, K99) | Feb 12, Jun 12, Oct 12 |
  | R34, R61/R33 | Feb 16, Jun 16, Oct 16 |
  | F31, F32 | Apr 8, Aug 8, Dec 8 |

  Note which upcoming cycle is realistic given how much work remains (e.g., "If you have pilot data ready, the October cycle is feasible. If you still need preliminary results, targeting February gives you more runway.")
- One-paragraph closing on positioning

**Section 8 — References**
- Numbered list of all papers cited anywhere in the report
- Format: `[N] Authors (Year). Title. Journal.` with title hyperlinked to its Consensus URL
- Group by section if more than 15 papers: "Novelty Analysis Sources", "Funded Project Sources"
- Include every paper referenced by an inline citation — no citations without a bibliography entry

**Section 9 — Audit Log**
- Heading: "Data Sources & Methodology"
- This section provides full transparency on what tools were called, what was returned, and what made it into the report. It helps the researcher and their mentor assess the completeness of the analysis.
- **Consensus searches table**: Search # | Facet Name | Query Used | Papers Found (per tool response) | Papers Shown/Returned | Results Cited | Status (Success/Failed/Retried)
- **Consensus plan-tier note**: If any search response indicates a cap (e.g., "Found 20 papers, showing top 10"), call this out explicitly: "Consensus plan limit detected: [M] of [N] papers returned per query. Only the [M] shown papers are citable. A higher-tier plan would surface more results." If all found papers were shown, note that too — it confirms full coverage.
- **RePORTER searches table**: Search Type (Narrow/Broad) | Keywords Used | Results Received | Status
- **NOSI fetches table** (if applicable): NOSI Number | Fetch Status | Included in Report (Yes/No)
- **Summary stats**: Total unique papers shown (post-dedup), total cited, total RePORTER projects found, total cited. Distinguish "found by Consensus" from "shown to us" from "cited in this report."
- **Tool constraints note**: "Consensus returned up to [M] results per query (plan limit: [tier if detectable]). RePORTER queries were limited to 20 results each. These caps mean this analysis covers the most relevant results, not an exhaustive literature search. If results seem sparse for a facet, it may reflect plan limits rather than a genuine gap in the literature."
- **Failed steps** (if any): List any searches or fetches that failed and were not recoverable, so the researcher knows where coverage is incomplete

#### Link construction

Every citation and FOA reference must be a clickable hyperlink using `docx` ExternalHyperlink:
```javascript
// Paper citation link (to Consensus)
new ExternalHyperlink({ link: "https://consensus.app/papers/{paper_id}", children: [new TextRun({ text: "[1]", style: "Hyperlink" })] })

// FOA link
new ExternalHyperlink({ link: "https://grants.nih.gov/grants/guide/pa-files/PA-24-184.html", children: [new TextRun({ text: "PA-24-184", style: "Hyperlink" })] })

// NIH Reporter project link
new ExternalHyperlink({ link: "https://reporter.nih.gov/project-details/{project_num}", children: [new TextRun({ text: "View Project", style: "Hyperlink" })] })
```

#### Styling notes

- Use Arial font throughout, 12pt body text, navy (#1a3a5c) headings
- Tables: light blue (#e8f0f8) header row background, alternating white/#f5f8fc rows
- NOSI callout (if present): bold text with amber highlight — make it visually stand out
- Keep it clean and professional — this document may end up in front of a department chair or mentor

---

### Phase 4: Deliver

Save the .docx to `/mnt/user-data/outputs/grant-research-overview.docx` and present with `present_files`.

Close with a brief summary:

> "Here's your grant research overview as a Word doc — you can edit it, pull sections into your application, or share it with your mentor. Key findings:
> - **Positioning:** [1 sentence on the gap and how the researcher's idea fills it]
> - **Best-fit institute:** [institute] — [N] active projects in your area
> - **Top grant:** [FOA] ([mechanism]) — [1 sentence why]
> - **Recommended study section:** [abbreviation] — [1 sentence on fit]
> - **Next step:** Contact the program officer at [institute] before submitting
> - [If NOSI found]: ⚠️ Active NOSI: [number] — deadline [date if found]
>
> Clickable links throughout — citations go to Consensus, FOAs go to NIH Guide, and funded projects go to NIH Reporter.
>
> This is a starting point, not a final product. As you refine your specific aims, come back and run this again — the positioning narrative will sharpen as your idea gets more specific."

---

## Notes

- **NIH RePORTER API requires POST — always use `bash_tool` with `curl`, never `web_fetch`**: `https://api.reporter.nih.gov/v2/projects/search` — no auth required
- **DOCX generation uses JavaScript with the `docx` library via `bash_tool`** — read the DOCX skill for setup patterns. Write a Node.js script and execute it.
- **Consensus rate limit**: 1 query per second. Run searches sequentially with a `sleep 1` or equivalent pause between calls. Never run Consensus searches in parallel.
- **Consensus plan-tier detection**: After each search, parse the response for language like "Found X papers, showing top Y." The *shown* count is what you can actually cite. Typical caps: unauthenticated ~3, free ~10, premium ~20. If you see a cap, tell the researcher — sparse results on a facet might be a plan limit, not a literature gap. Log the detected tier in the audit log.
- NOSI files are fetchable via `web_fetch` at `https://grants.nih.gov/grants/guide/notice-files/{number}.html`
- If RePORTER returns fewer than 5 results, the broad OR search should compensate — combine and deduplicate both. Surface the low count to the researcher.
- If no NOSIs surface from project results, skip that section — don't fabricate
- Career stage filtering is a signal, not a hard filter — mention if a grant is a stretch for their stage
- The transparency about *which institute* and *why* is the most actionable part of the report — don't rush past it
- Every inline citation `[N]` must have a corresponding bibliography entry — track all cited papers from the start. No URL from this session = not citable.
- Keep the document concise and actionable — aim for 6–9 pages including bibliography and audit log. Do not expand into full appendices.
- **Never pad results with training knowledge.** If a search returns sparse results, say so. If you include reference information (e.g., mechanism budgets, submission dates), label it as such — it's not from a tool call in this session.

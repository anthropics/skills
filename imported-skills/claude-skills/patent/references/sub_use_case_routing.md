# Sub-Use-Case Routing — The 5 Patent Search Strategies

This reference answers exactly one decision: **given the user's Q2 commitment, which search strategy / ranking heuristic / DOCX emphasis applies?**

The patent skill refuses to be a generic "patent search". Q2 is mandatory. The 5 sub-use-cases use **fundamentally different** strategies — running a novelty search and calling it FTO produces wrong answers in dangerous ways.

## Why Sub-Use-Case Commitment Matters

| Sub-use-case | Wrong-strategy danger |
|---|---|
| Novelty | Generic search misses claim-text proximity → false negatives ("looks novel, isn't") |
| FTO | Generic search includes expired/abandoned patents → false positives ("looks blocked, isn't") |
| Landscape | Generic search misses CPC class trends → incomplete competitive picture |
| Diligence | Generic search misses assignment chain → ownership-verification gaps |
| Litigation | Generic search includes art after priority date → useless for invalidation |

The 5 strategies are **not interchangeable**. The skill enforces commitment to prevent strategy mismatches.

## Strategy 1: Novelty Search

### Question being answered

"Am I novel enough to file? Is there art that anticipates or makes obvious my invention?"

### Search emphasis

- **Narrow** queries on invention-specific terminology (don't drown in adjacent art)
- **Claims-text focused** (the legal test is claim-by-claim anticipation)
- **Pre-filing date irrelevant** — anything published before user's filing is potential art

### Query plan

1. 3 narrow Google Patents queries on invention-specific terms
2. 2 broad concept queries with synonyms (Google Patents + Espacenet)
3. 1 CPC class-restricted query (after class identification from initial hits)
4. (Optional Lens.org) forward citations from any closest art

**Total: 6-7 sequential queries.**

### Ranking heuristic

Rank by **claim-text overlap** with user's invention description (Q1). Top hits are those whose claim 1 most overlaps in technical terminology. Surface independent claim 1 verbatim for each top-5 hit.

### Verdict scale

- **NOVEL** — closest hit has <30% claim-text overlap; clear differentiation possible
- **POTENTIALLY NOVEL** — 30-60% overlap; differentiation possible but requires careful claim drafting
- **NOT NOVEL** — >60% overlap; invention as described is anticipated by closest art

### DOCX emphasis

- Section 2 (Closest Prior Art): expanded — 8-10 hits with full claim-1 text
- Section 7 (Strategy): claim-differentiation suggestions
- Sections 3 + 5 (Landscape + Geographic): abbreviated
- Mandatory legal disclaimer footer

## Strategy 2: Freedom-to-Operate

### Question being answered

"If I ship in jurisdiction X, will I get sued for infringement?"

### Search emphasis

- **Active patents only** — expired/abandoned patents can't sue
- **Jurisdiction-filtered** — FTO only matters where user sells
- **Date filter:** priority date < today (no pending applications without published claims)
- **Independent + dependent claims** — both relevant to infringement analysis

### Query plan

1. Per jurisdiction (Q3): 2-3 queries with jurisdiction filter (US: USPTO; EP: Espacenet; etc.)
2. Active-status filter applied to all
3. CPC class follow-up after initial hits
4. (Optional) assignment chain check for active assignee context

**Total: 8-15 sequential queries (scales with # of jurisdictions).**

### Ranking heuristic

Rank by **claim-by-claim infringement risk**. For each active patent: which independent claims would the user's product practice? High risk = at least one independent claim covers user's product as designed.

### Verdict scale (per jurisdiction)

- **CLEAR** — no active patents pose infringement risk
- **FLAGGED** — 1-2 active patents may pose risk; design-around viable
- **HIGH RISK** — 3+ active patents pose risk; design changes required OR licensing path needed

### DOCX emphasis

- Section 6 (FTO Flags): expanded — per-flag risk per jurisdiction
- Section 5 (Geographic Coverage): expanded
- Section 7 (Strategy): design-around hints + jurisdiction strategy
- Mandatory legal disclaimer footer

## Strategy 3: Competitive Landscape

### Question being answered

"Who else plays in this technology space? What are the trends?"

### Search emphasis

- **Broader queries** on the technology space (NOT the specific invention)
- **CPC class identification** drives the analysis
- **Top filer tally** — who files most patents in the space
- **10-year filing trend** by year per top-5 filer

### Query plan

1. 2-3 broad queries on the technology space
2. CPC class extraction from top hits
3. 1 query per top-5 filer to gauge their portfolio
4. (Optional Lens.org) citation graph for foundational patents

**Total: 8-10 sequential queries.**

### Ranking heuristic

Rank by filer count + recency. Top-5 filers + 3 emerging entrants (filers with first patent in last 2 years).

### Verdict scale

- **CONCENTRATED** — top-3 filers own >60% of patents in the space
- **COMPETITIVE** — top-10 filers own 60-90%; mature competitive market
- **EMERGING** — long tail of filers; market is still defining itself

### DOCX emphasis

- Section 3 (Patent Landscape): expanded — top filers table + 10-yr trend + CPC distribution
- Section 5 (Geographic Coverage): expanded
- Sections 2 + 4 (Closest Art + Citation Graph): abbreviated
- Section 7 (Strategy): who-to-watch list + emerging-entrants signal
- Legal disclaimer optional (lower legal exposure)

## Strategy 4: Acquisition Diligence

### Question being answered

"Does target company actually own the patents they claim? Is there portfolio depth?"

### Search emphasis

- **Specific assignee searches** — target company + subsidiaries + named inventors
- **Assignment chain check** — USPTO assignment recordation
- **Family resolution** — deduplicate same-invention across jurisdictions
- **Portfolio scope** — are patents in core business areas or peripheral?

### Query plan

1. 2-3 assignee-name queries (Google Patents + USPTO assignee search)
2. Subsidiary searches if user provides org chart
3. Inventor searches for key named inventors
4. Assignment recordation lookups for ownership verification
5. Family resolution across all hits

**Total: 6-12 sequential queries.**

### Ranking heuristic

Group by family. Within family, surface earliest priority. Across families, rank by:
- Citation count (foundational vs niche)
- Filing recency (active R&D vs legacy)
- Claim breadth (broad coverage vs narrow)

### Verdict scale

- **PORTFOLIO VERIFIED** — claimed patents owned, assignment chains clean, no orphans
- **PARTIAL VERIFICATION** — some claimed patents not found OR assignment chain unclear
- **OWNERSHIP RISK** — significant claimed patents not owned by target OR major assignment gaps

### DOCX emphasis

- Section 3 (Patent Landscape): expanded as portfolio table
- Section 5 (Geographic Coverage): expanded
- Section 7 (Strategy): red flags in portfolio + ownership-verification flags
- Legal disclaimer optional but recommended (M&A context)

## Strategy 5: Litigation Prior-Art

### Question being answered

"Can I invalidate this specific patent? What art exists before its priority date?"

### Search emphasis

- **Target patent input required** (number)
- **Priority date extraction** — sets the prior-art cutoff
- **Search before priority date in same CPC classes**
- **Adjacent-claim-language search** — art that uses similar claim language

### Query plan

1. Fetch target patent (extract priority date + claims + CPC classes)
2. CPC class queries with date filter (priority < target's priority)
3. Keyword queries on independent claim language with date filter
4. (Optional Lens.org) forward citations from target's cited art

**Total: 5-8 sequential queries.**

### Ranking heuristic

Rank by **knock-out potential** — claim-by-claim anticipation/obviousness. Highest rank: art that anticipates ALL elements of target's broadest independent claim.

### Verdict scale

- **KNOCK-OUT FOUND** — art clearly anticipates all elements of broadest claim
- **STRONG OBVIOUSNESS COMBINATION** — multiple pieces of art combine to cover all elements
- **WEAK OBVIOUSNESS** — art relevant but anticipation/obviousness argument is uphill
- **NO MATERIAL ART FOUND** — patent appears strong against this prior-art set

### DOCX emphasis

- Section 2 (Closest Prior Art): expanded — ranked knock-out candidates with claim-language overlap
- Section 7 (Strategy): per-claim invalidity analysis
- Sections 3 + 5 (Landscape + Geographic): abbreviated
- Legal disclaimer optional but recommended (litigation context)

## Out-of-Scope Topics (Flagged at Intake)

| Topic | Why out of scope |
|---|---|
| Trademark | Different legal regime, different sources (USPTO TESS not Patent Office) |
| Copyright | No formal search system; rights attach automatically |
| Trade secret | By definition, not in public records |

If user asks for any of these → halt at intake, recommend appropriate skill or attorney.

## Operational Checklist

- [ ] Q2 sub-use-case picked (no "all of them")
- [ ] `scripts/sub_use_case_router.py` returns query plan + ranking heuristic + DOCX flags
- [ ] Search emphasis matches sub-use-case (not generic)
- [ ] Verdict scale per sub-use-case applied
- [ ] DOCX emphasis adjusted (not all 8 sections expanded for every sub-use-case)
- [ ] Legal disclaimer mandatory for novelty + FTO; optional for landscape/diligence/litigation but recommended

## Citations (7 sources)

1. **MPEP (Manual of Patent Examining Procedure) — USPTO.** Source for the legal definitions of novelty (35 USC §102) vs FTO (no explicit USC; case law) vs anticipation/obviousness. The verdict scales follow MPEP terminology.

2. **35 USC §102 + §103 — US patent statute.** Source for the priority-date-as-cutoff rule for novelty (§102) and the obviousness combination doctrine (§103) that drives litigation prior-art ranking.

3. **WIPO Patent Cooperation Treaty (PCT) procedural docs.** Source for the cross-jurisdiction family discipline. PCT applications generate national-phase entries in many jurisdictions; the family resolver follows WIPO's family-id taxonomy.

4. **EPO Guidelines for Examination — European Patent Office.** Source for the EP-specific FTO discipline. EP active-status filtering uses EPO's "in force" status field.

5. **USPTO Patent Public Search documentation.** Source for the USPTO PPS query syntax and assignment-recordation lookup endpoints used in acquisition diligence.

6. **Google Patents search documentation + advanced operators.** Source for the keyword + CPC class + date filter syntax. Google Patents indexes all PCT national-phase entries plus most jurisdictions' grant data.

7. **Lens.org API documentation (https://docs.api.lens.org).** Source for the citation-graph queries. Lens.org's citation API exposes forward + backward citations with citation-count thresholds for foundational-patent identification.

# DOCX Research Guide — 8 Sections + Technical Requirements

This reference answers exactly one decision: **what are the 8 sections of the litreview research guide, and what does each contain to function as a "launching pad" for a researcher entering an unfamiliar field?**

## The Core Frame

The output is a **launching pad**, not a finished review. Frame each section as: "what would a generous colleague tell you over coffee if they knew the field and you didn't?"

That framing rules out:
- Exhaustive coverage (a launch pad is finite)
- Comprehensive synthesis (the user will read the papers)
- Defensible-publishable form (this is orientation, not submission-ready)

And rules in:
- Clear ordering (read these papers in this order)
- Honest gaps (here's what's underdeveloped)
- Practical entry points (here's how to keep searching)

## Section 1: Topic Overview

**Length:** 4-6 sentences, single tight paragraph.

**Contents:**
- What the field is (1 sentence)
- Why it matters (1 sentence)
- Framework used (PICO / SPIDER / Decomposition / hybrid) (1 sentence)
- Characterization of the evidence landscape (1-2 sentences)
- Honest caveat or limitation (1 sentence) — e.g., "mostly Western data" or "RCTs are scarce"

**Tone:** Confident but caveated. A colleague summarizing, not a textbook authority.

## Section 2: Start Here — Priority Reading Order

**Length:** 5-7 papers, ordered.

**Order:**
1. Best recent review (sets the field context)
2. Foundational paper(s) — 1-2, ranked by repeat-hits + cited-per-year
3. Frontier papers — 2-3 (most-recent that surfaced multiple times)
4. Gap / controversy paper — 1 (surfaces what's contested)

**Per paper:**
- Hyperlinked title (clickable — PubMed URL or DOI from the free lane; Consensus URL if Consensus-sourced)
- Authors + year
- One sentence: contribution
- One sentence: "what to look for"

**Example entry:**
> 1. **[A systematic review of LLM clinical reasoning](https://pubmed.ncbi.nlm.nih.gov/<PMID>/)** — Singhal et al. 2024 — Most comprehensive synthesis of LLM diagnostic performance through 2023. Look for: section on prompting strategy (the field's main tunable variable).

## Section 3: How the Field Got Here

**Length:** 1-2 paragraphs narrative + timeline table.

**Narrative:** chronological story of the field's evolution. 3-5 sentences. What changed, when, why.

**Timeline table:** 5-8 milestones.

| Year | Milestone | Significance |
|---|---|---|
| 2015 | First paper applying X to Y | Established the question |
| 2018 | Method Z introduced | Made evaluation tractable |
| 2020 | Large-scale dataset W released | Enabled benchmarking |
| 2023 | Breakthrough result by Group A | Set current state-of-the-art |

**Terminology evolution note:** "Field used 'X' through 2018; now standardly called 'Y'. Older searches must include the older term."

This section is what makes a literature review for the researcher: the linear story plus the moments of inflection. Build it from era-gated search results.

## Section 4: Sub-area Guides

**Length:** One per sub-area (4-5 total), 4 parts each.

### 4a. What the Research Shows

2-3 sentence synthesis with inline citations.

Example:
> LLMs achieve 70-85% accuracy on clinical reasoning benchmarks (Singhal et al. 2023, Liévin et al. 2024) but performance degrades sharply on novel case presentations (Toma et al. 2024). The variance across model families and prompting strategies is the field's central open question.

Every fact is hyperlinked. Every inline citation matches a bibliography entry (Section 7).

### 4b. Key Papers

3-5 hyperlinked papers. Per paper:
- Title (hyperlinked)
- Citation count + year
- One-sentence importance

### 4c. Key Search Terms

6-10 keywords for the sub-area:
- Modern preferred terms
- Synonyms (especially historical)
- MeSH headings if applicable
- Domain-specific terms (e.g., "USMLE-style" for clinical reasoning)

### 4d. Boolean Search Strings

2-3 ready-to-paste strings:
```
("clinical reasoning" OR "diagnostic reasoning") AND ("large language model" OR LLM OR GPT) AND (evaluation OR benchmark)
```

User pastes into PubMed / OpenAlex / Scopus (or Consensus, if they use it) to continue searching beyond what the skill ran.

## Section 5: Key Research Groups

**Length:** 3-5 groups.

**Source:** `scripts/cross_search_aggregator.py` recurring-authors output.

**Per group:**
- Lead author (or 2-3 authors if collaborative)
- Affiliation (institution)
- Sub-areas they cover (from cross-search analysis)
- Representative paper (hyperlinked, with year)
- Why they matter (1 sentence)

**Example:**
> **Singhal, K. et al. (Google DeepMind / Med-PaLM)** — Coverage: clinical reasoning, multimodal medical AI. Representative: ["Towards Generalist Biomedical AI" (2023)](https://...). Why they matter: built the Med-PaLM line; their benchmark methodology defines current state-of-the-art evaluation.

## Section 6: Open Questions & Gaps

**Length:** 3 categories, each with 1-3 gaps.

**Categories:**

1. **Methodological gaps** — what's hard to measure, what we don't have good methods for
2. **Population / context gaps** — who isn't being studied, where the data isn't
3. **Conceptual / theoretical gaps** — what we don't understand about the underlying mechanism

**Per gap:**
- One sentence stating the gap
- One sentence on *why it matters* — what's downstream of this gap being filled

Example:
> **Methodological gap:** No standardized benchmark for novel-case clinical reasoning (only retrospective USMLE-style). *Why it matters:* current "85% accuracy" claims may not generalize to real practice where novel cases dominate.

The "why it matters" sentence is what distinguishes a gap list from a complaint list.

## Section 7: Bibliography

**Length:** All cited papers, alphabetical by first author.

**Per entry:**
- Full citation (author list, title, journal, year, volume/issue, pages)
- Hyperlinked source link, full URL never truncated (PubMed URL or DOI from the free lane; "View on Consensus" for Consensus-sourced papers)
- Inline-citation key matching Section 4 references (e.g., "Singhal et al. 2024")

**Discipline:**
- Every inline citation in Sections 1-6 appears in Bibliography
- Every Bibliography entry is cited at least once
- No phantom entries (cited but no bib) or orphan entries (bib but never cited)
- Source URLs preserved in full (never `...` truncation)

## Section 8: Audit Log

**Length:** Search summary table + counts block + coverage notes.

**Search summary table:**

| # | Query | Filters | Results | Status |
|---|---|---|---|---|
| 1 | broad recon | none | 10 | OK |
| 2 | sub-area 1 | year_min: 2018 | 10 | OK |
| ... | ... | ... | ... | ... |
| 10 | follow-up on Singhal | year_min: 2024 | 7 | thin |

**Counts block:**

```
Searches executed: 10
Unique papers received: 47 (after deduplication)
Papers cited in this guide: 22
Search lane: free (PubMed + OpenAlex; ~20 results per query per source)
Theoretical ceiling: 200 papers per source; received 47 unique (typical deduplication)
```

**Coverage notes:**
- Which sub-areas surfaced thin results
- Search-lane impact on coverage (free lane vs free+Consensus)
- Suggested manual supplementation (PubMed, Scholar, etc.)
- Era-gated search yields (terminology shifts detected)

The audit log makes the entire review reproducible and falsifiable. A future reader can rerun the searches and check the work.

## DOCX Technical Requirements

Document the key `docx` library patterns (Node.js):

### Page setup

```js
const page = {
  size: "LETTER",
  margins: { top: 1440, right: 1440, bottom: 1440, left: 1440 }, // 1 inch in twips
};
```

### Lists (NEVER unicode bullets)

```js
new Paragraph({
  children: [new TextRun(text)],
  numbering: { reference: "default-bullet", level: 0 },
});
// Defined in document numbering config with LevelFormat.BULLET
```

### Hyperlinks (full URL, "Hyperlink" style)

```js
new ExternalHyperlink({
  link: "https://pubmed.ncbi.nlm.nih.gov/full-url-never-truncated/",
  children: [new TextRun({ text: paperTitle, style: "Hyperlink" })],
});
```

### Tables (dual widths)

```js
new Table({
  columnWidths: [3000, 4000, 2000], // EMU
  rows: rows.map(r => new TableRow({
    children: r.cells.map(c => new TableCell({
      width: { size: c.width, type: WidthType.DXA },
      shading: { type: ShadingType.CLEAR, color: "auto", fill: "auto" },
      children: [new Paragraph(c.text)],
    })),
  })),
});
```

### Validation

After save:
```bash
python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).testzip()" output.docx
```

If validation fails: unpack DOCX (it's a ZIP), fix the offending XML, repack.

Reference the **docx skill** (`docx/SKILL.md` in this repo if installed) for full setup patterns.

## Anti-Patterns

- **Truncating source URLs in hyperlinks** — breaks reproducibility
- **Phantom bibliography entries** — cited paper missing from bib
- **Generic "Future Work" section** — Section 6 must be *specific* gaps, not "more research is needed"
- **No timeline table in Section 3** — narrative-only loses the milestone structure
- **Unicode bullets (• ‣ ▶)** instead of `LevelFormat.BULLET` — breaks DOCX list rendering in some viewers
- **Single-width tables** (only `columnWidths` or only cell `width`) — renders inconsistently across Word / LibreOffice / Google Docs
- **Skipping validation step** — invalid DOCX silently fails to open or renders broken
- **Audit log without theoretical ceiling** — user can't calibrate "is this comprehensive?"

## Operational Checklist

- [ ] All 8 sections present in DOCX
- [ ] Section 1: 4-6 sentence paragraph
- [ ] Section 2: 5-7 papers in priority order
- [ ] Section 3: narrative + timeline table + terminology note
- [ ] Section 4: one sub-section per sub-area, 4 parts each
- [ ] Section 5: 3-5 groups from cross-search aggregator
- [ ] Section 6: 3 categories with "why it matters" per gap
- [ ] Section 7: alphabetical, hyperlinked, no phantoms / orphans
- [ ] Section 8: search table + counts + search lane + coverage notes
- [ ] All source URLs full (no truncation)
- [ ] `LevelFormat.BULLET` for lists (no unicode bullets)
- [ ] Tables have both `columnWidths` AND cell `width`
- [ ] `python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).testzip()" output.docx` PASSes

## Citations (7 sources)

1. **`docx` Node.js library — github.com/dolanmiu/docx (MIT).** Authoritative API source. The technical patterns (Paragraph, ExternalHyperlink, Table, LevelFormat.BULLET) come from its documentation.

2. **OOXML (Office Open XML) Specification — ECMA-376 (4th ed., 2016).** The underlying XML schema for DOCX. Source for the dual-width table pattern (DOCX renderers respect both column widths and cell widths; missing either causes layout inconsistencies).

3. **PRISMA 2020 Statement — Page, M. J. et al., *BMJ* 372, 2021.** Source for the audit-log section requirements (every reported search must include query, filters, results count, status). PRISMA is the international standard for systematic-review reporting.

4. **Cochrane Handbook — Higgins, J. P. T. et al. (Wiley, 2019).** Chapter 4 + Chapter 7 on data extraction and synthesis. Source for the sub-area guide structure (synthesis + key papers + search terms + boolean strings) — Cochrane's standard data-extraction template.

5. **Lipsey, M. W. & Wilson, D. B., *Practical Meta-Analysis* (Sage, 2001).** Source for the bibliography discipline (every inline citation has bib entry; every bib entry is cited). Essential for review integrity.

6. **Tufte, E., *Visual Display of Quantitative Information* (Graphics Press, 1983, 2001 ed.).** Source for the timeline-table pattern (5-8 milestones, not 20+; "milestones" not "events"). Tufte's "small multiples" + "data-ink ratio" principles inform the audit-log table design.

7. **William Strunk Jr. & E. B. White, *The Elements of Style* (Macmillan, multiple eds.).** Source for the "Open Questions & Gaps" voice discipline. Gaps must be specific and consequential, not "more research is needed" filler. Strunk's "omit needless words" applies directly: every gap statement should pass the "why it matters" test.

---
name: litreview
description: "Academic literature orientation skill that searches papers via free keyless APIs (PubMed E-utilities + OpenAlex) by default — with the Consensus MCP as an optional enhancement lane when connected — builds a strategic search plan using PICO (default) or SPIDER / Decomposition / hybrid as fallbacks, and synthesizes findings into a formatted Word (.docx) research guide. Grill-me intake (research question specificity + framework hint + tentative depth) before the recon search; a second forcing checkpoint after Phase 2 confirms framework + sub-areas + depth before searches consume budget. Configurable depth (5/10/20 queries) controls coverage vs. speed. Output is a 'launching pad' — an orientation guide that lets a researcher dive in confidently, not a finished review. Use when the user starts literature-oriented research (e.g., 'litreview on [topic]', 'literature review on [topic]', 'I'm starting a literature review on X', 'I'm writing a paper on X', 'help me research X', 'I'm doing research on X', 'can you help me research X'). Do NOT use for single one-off paper searches wanting a quick list — that's a plain PubMed/OpenAlex (or Consensus) query."
license: MIT
metadata:
  source_spec: "megaprompts/09-litreview-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  research_pack_convention: "Agent Integrity Rules verbatim per PR #657 audit; sibling of pulse"
  version: 1.1.0
---

# Litreview — Academic Literature Orientation

> **Portability:** Works anywhere with outbound HTTPS — the default search lane is **free keyless APIs** (PubMed E-utilities + OpenAlex, no account, no key, no MCP). The **Consensus MCP is an optional enhancement lane** used only when connected in this session. Node.js with `docx` package is required for document generation, and (in CLI) `bash_tool`. Works in Claude Code CLI natively and in Claude.ai with Code Execution.

Produce a **launching pad** — not a finished literature review, but an orientation document that gives a researcher entering an unfamiliar field everything they need to start reading and searching with confidence. Think: what a generous colleague who knows the field would tell you over coffee.

## Search Lanes

| Lane | When | How |
|---|---|---|
| **Free lane (default)** | Always available; no key, no plan, no MCP | PubMed E-utilities + OpenAlex via `scripts/free_search.py` or direct HTTPS (URL templates below) |
| **Consensus lane (optional enhancement)** | Only when Consensus MCP tools are available in this session | Run Consensus queries *in addition to* the free lane for its synthesized answer cards |

**Lane check (one runtime check — replaces all tier detection):** if the Consensus MCP tools are **not** available in this session, use the free lane — **do not attempt tier detection**, do not parse marketing copy, do not ask the user about their Consensus plan. If Consensus IS available, additionally run its searches and merge results (dedupe by DOI/title).

### Free-lane URL templates (exact)

**PubMed E-utilities** (keyless; etiquette: ≤3 requests/second):

1. Search → PMIDs: `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=<urlencoded-query>&retmode=json&retmax=20&sort=relevance`
   — read `esearchresult.idlist` (PMIDs) and `esearchresult.count`.
2. PMIDs → metadata: `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=pubmed&id=<pmid1,pmid2,...>&retmode=json`
   — per `result[<pmid>]` read `title`, `authors[].name`, `pubdate`, `fulljournalname`, `articleids[]` (the `idtype: "doi"` entry).
3. Era-gating: append `&datetype=pdat&mindate=2021&maxdate=3000` (recent) or `&maxdate=2015` (historical).
4. Paper URL: `https://pubmed.ncbi.nlm.nih.gov/<PMID>/`.

**OpenAlex** (keyless; add `&mailto=<email>` for the polite pool — faster + more reliable):

1. Search: `https://api.openalex.org/works?search=<urlencoded-query>&per-page=20&mailto=<email>`
   — per `results[]` read `display_name` (title), `publication_year`, `cited_by_count`, `doi`, `id` (OpenAlex URL), `authorships[].author.display_name`, `primary_location.source.display_name` (venue).
2. Era-gating: `&filter=from_publication_date:2021-01-01` or `&filter=to_publication_date:2015-12-31`.
3. Review articles: `&filter=type:review`.

OpenAlex's `cited_by_count` is the citation-count source for the cross-search intelligence layer (PubMed esummary returns no counts).

## Agent Integrity Rules (Research-Pack Convention)

Inherited from the research-pack convention; locked verbatim per PR #657's cross-skill consistency audit.

- **Source discipline.** Only cite papers returned by THIS session's searches (free lane and/or Consensus). Training knowledge labeled `[Not from search — model knowledge]` and excluded from cited count. Sparse results stated explicitly, never silently filled.
- **Counting discipline.** Three numbers tracked: searches executed / unique papers received (deduplicated by DOI/title) / papers cited. Every cited paper has a retrievable URL from this session (PubMed, DOI, OpenAlex, or Consensus). Use `scripts/citation_tracker.py` for deterministic counts.
- **Rate-limit etiquette.** PubMed E-utilities: ≤3 requests/second keyless. OpenAlex: polite pool via `mailto`. Consensus (if connected): 1 query/sec, sequential execution mandatory. Default discipline: **sequential, 1 query/sec across all lanes.**
- **Retry policy.** On failure → wait 3s → retry once → log. After 3 consecutive failures: stop, alert user, share what was collected.
- **Lane check.** One runtime check at session start: Consensus MCP tools available or not. No tier detection, ever.

See [`references/search_budget_allocation.md`](references/search_budget_allocation.md) for the sequential-execution rationale + budget ceilings.

## Error Handling

| Failure | Behavior |
|---|---|
| Rate-limit / HTTP error on any lane | Wait 3s, retry once, log outcome |
| Search returns 0 results | Note explicitly; "either niche terminology or genuine gap"; never silently fill |
| Network unavailable (free lane exits 2) | Stop, alert user — the free lane needs outbound HTTPS; nothing to detect or upgrade |
| 3 consecutive failures | Stop searching, alert user, share what's collected, ask how to proceed |
| Sub-area returns thin results (<5 papers) | Flag in audit; suggest manual Google Scholar / Scopus supplementation |
| User wants to adjust sub-areas | Update table, re-confirm before searching |
| DOCX validation fails | Unpack XML, fix, repack |

## Phase 0: Grill-Me Intake (3 forcing questions, one at a time)

Each question carries explicit "why I'm asking". Stop condition: max 3 before Phase 1.

### Q1 (root) — Research question specificity

> **State the research question in 1–2 sentences. Specific is better — "How do LLMs perform on clinical reasoning tasks compared to physicians?" beats "AI in medicine". Vague questions produce vague reviews.**
>
> *Why I'm asking:* The reconnaissance search hinges on precise terminology. Vague questions produce thin recon results that don't yield a useful framework breakdown.

**Refuse mush.** Re-ask once with examples if user is too broad. If still vague, deliver with explicit "broad-scope orientation, not depth review" caveat.

### Q2 (depends on Q1) — Framework hint

> **Framework — pick one or say "you pick":**
>
> 1. **PICO** (Population / Intervention / Comparison / Outcome — most clinical questions)
> 2. **SPIDER** (Sample / Phenomenon / Design / Evaluation / Research-type — social/qualitative)
> 3. **Decomposition** (Problem / Solution / Evaluation / Limitations — technology-focused)
> 4. **Hybrid** (you pick which components from which framework)
> 5. **You pick** — analyze Q1 and recommend
>
> *Why I'm asking:* PICO is the default for ~70% of clinical questions but maps poorly to qualitative work or technology evaluation. Picking upfront saves the recon search from suggesting a misaligned framework.

Forcing choice with default ("you pick"). The skill surfaces its own framework recommendation after the recon search so user can override. Use `scripts/framework_recommender.py` for the heuristic.

See [`references/framework_selection.md`](references/framework_selection.md) for PICO / SPIDER / Decomposition canon.

### Q3 (depends on Q1) — Tentative depth

> **Tentative depth — pick one. Final confirmation comes after the framework breakdown:**
>
> 1. **Quick scan** (5 searches)
> 2. **Standard review** (10 searches)
> 3. **Deep dive** (20 searches)
>
> *Why I'm asking:* I ask this twice — once now to calibrate the recon search emphasis, once after the framework breakdown to confirm. Tentative answer affects which sub-areas to surface first; final answer drives search budget allocation.

Forcing choice. **Re-asked** at the post-Phase-2 checkpoint after the user has seen the framework breakdown.

**Stop condition:** 3 questions max before Phase 1. The post-Phase-2 checkpoint is its own grill-me moment (framework table + sub-area-adjustment + depth-reconfirmation).

## Phase 1: Initial Reconnaissance

**One broad recon search** to map themes, terminology, methodological distinctions.

- Run the lane check (Consensus available or not), then:
  - Free lane: `python scripts/free_search.py --query "<broad version of Q1>" --source both --max 20` (or the esearch/works URL templates above)
  - **If Consensus is available, additionally** run one broad Consensus search and merge
- Query: broad version of Q1 (terminology variants are okay; first search casts wide)
- Record: `citation_tracker.py --action record_search --session NAME --query "..."`
- Record received count: `citation_tracker.py --action record_papers_received --session NAME --count N`

Synthesize for the checkpoint:
- Themes that surfaced
- Terminology variations (e.g., "LLM" vs "large language model" vs "GPT-style model")
- Methodological distinctions (clinical trials vs benchmark eval vs case study)
- Coverage gaps (sub-questions absent from recon results)

## Phase 2: Framework Selection + Sub-area Generation

Choose framework (from Q2 OR override based on recon):
- **PICO** — most clinical questions (~70% default)
- **SPIDER** — social / qualitative
- **Decomposition** — technology focus (Problem / Solution / Evaluation / Limitations)
- **Hybrid** — explicit cross-framework mapping

Generate **4-5 sub-area questions** mapped to framework components. Each becomes a targeted Phase 3 search.

## Checkpoint (grill-me forcing-options moment)

After Phase 2, halt and present:

### 3-4 sentence recon summary
- What themes surfaced
- Terminology landscape
- Evidence landscape characterization

### Framework breakdown table

| Framework Component | How It Maps to This Topic | Proposed Sub-area to Explore |
|---|---|---|
| (Component 1) | ... | Sub-area 1 |
| (Component 2) | ... | Sub-area 2 |
| (Component 3) | ... | Sub-area 3 |
| (Component 4) | ... | Sub-area 4 |
| Cross-cutting theme | ... | Sub-area 5 |

### Depth re-confirmation (forcing choice)

Surface the **practical constraint**: search lane in use (free / free+Consensus) + approximate ceiling at ~20 results per query per source.

- Quick scan (5 searches × ~20 results = ~100 papers max per source)
- Standard review (10 searches × ~20 = ~200 papers per source)
- Deep dive (20 searches × ~20 = ~400 papers per source)

### Sub-area forcing options

- "Looks good — proceed with these sub-areas"
- "Adjust: add sub-area on [X]"
- "Adjust: remove and replace [Y] with [Z]"
- "Restart with different framework"

### Why I'm asking (the rationale)

> A wrong framework or sub-area set wastes the search budget. This is the **last cheap moment** to correct course.

**Wait for user response before Phase 3.** Refuse to start Phase 3 without explicit user choice.

## Phase 3: Targeted Searches

Sequential (1 query/sec), budget per depth tier. Every search runs on the free lane (`free_search.py` or the URL templates); **if Consensus is available, additionally** run the same query there and merge. See [`references/search_budget_allocation.md`](references/search_budget_allocation.md) for full canon.

### Quick scan (5 searches)
- 5 sub-area searches (one per sub-area)
- Skip era-gated + review-specific

### Standard review (10 searches)
- 5 sub-area searches
- 2 review article searches (top 2 sub-areas): `"systematic review [topic]"` / `"meta-analysis [topic]"` (OpenAlex: add `&filter=type:review`)
- 2 era-gated searches (most important sub-area): historical (PubMed `&maxdate=2015` / OpenAlex `to_publication_date:2015-12-31`) + recent (PubMed `&mindate=2021` / OpenAlex `from_publication_date:2021-01-01`)
- 1 follow-up on highest-cited paper using its key terms + a from-date after its publication year

### Deep dive (20 searches)
- 5 sub-area searches
- 5 review article searches (one per sub-area)
- 4 era-gated searches (top 2 sub-areas, old + new each)
- 3 follow-ups on top 3 highest-cited papers
- 3 spare for emerging threads (surprising findings to chase)

Throughout: 1 q/sec rate limit. Sequential. Confirm response before next call. Record each via `citation_tracker.py`.

## Cross-Search Intelligence

Three trackers across ALL search results — run `scripts/cross_search_aggregator.py --session NAME` after Phase 3 completes:

1. **Repeat-hit papers** — same paper appearing in 3+ sub-area searches = likely foundational
2. **Recurring authors** — same author in multiple searches = dominant research group; top 3-5 most frequent matter
3. **Citation-per-year heuristic** — a 2023 paper with 150 citations >> 2008 paper with 150 citations. Use OpenAlex `cited_by_count` for seminal-work identification.

These feed the "Start Here" + "Key Research Groups" + "Bibliography" DOCX sections.

## Phase 4: DOCX Research Guide

Generate via Node.js + `docx` library. 8 sections (see [`references/docx_8_sections.md`](references/docx_8_sections.md) for full spec):

1. **Topic Overview** — single tight paragraph (4-6 sentences)
2. **Start Here — Priority Reading Order** — 5-7 papers ordered: best recent review → foundational → 2-3 frontier → gap/controversy. Each: hyperlinked title + authors/year + 1-sentence contribution + 1-sentence "what to look for"
3. **How the Field Got Here** — chronological narrative (1-2 paragraphs) + timeline table (5-8 milestones: Year / Milestone / Significance) + terminology evolution note
4. **Sub-area Guides** (one per sub-area, 4 parts each)
   - 4a. What the Research Shows (2-3 sentence synthesis with inline citations)
   - 4b. Key Papers (3-5 hyperlinked papers with citation count, year, 1-sentence importance)
   - 4c. Key Search Terms (6-10 keywords, synonyms, MeSH, historical terms)
   - 4d. Boolean Search Strings (2-3 ready-to-paste strings)
5. **Key Research Groups** — top 3-5 authors/groups with affiliations, sub-area coverage, representative paper link (from cross-search aggregator)
6. **Open Questions & Gaps** — three categories: methodological / population-context / conceptual-theoretical. Each gap explains *why it matters*.
7. **Bibliography** — alphabetical by first author. Every entry has a clickable link: PubMed URL or DOI (free lane) / "View on Consensus" (Consensus-sourced). Every inline citation matches a bibliography entry.
8. **Audit Log** — search summary table (#, query, filters, papers returned, status), counts block, coverage notes including which search lane was used (free / free+Consensus)

### DOCX Technical Requirements

Document the key `docx` library patterns:

- Page: US Letter, 1-inch margins
- Lists: `LevelFormat.BULLET` (never unicode bullets)
- Hyperlinks: `ExternalHyperlink` with `style: "Hyperlink"`, full URL (never truncated)
- Tables: dual widths (`columnWidths` + cell `width`), `ShadingType.CLEAR`
- Validation step after save (zip-integrity check: `python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).testzip()" output.docx` — no output = intact — then confirm the required sections are present)

Reference the **docx skill** for setup patterns and best practices.

## Output

```
research_guide_<topic-slug>_<YYYY-MM-DD>.docx
```

Plus:
- Chat summary block: "Saved: <path>. Audit: N searches × M unique papers / K cited. Search lane: <free | free+Consensus>."
- Audit log printed inline if user asks for it

## Tooling

| Script | Role |
|---|---|
| `scripts/free_search.py` | Free keyless search lane — PubMed E-utilities + OpenAlex via stdlib urllib (`--query`, `--source pubmed|openalex|both`, `--max`, `--json`, `--mailto`; exits 2 with a clear message when offline) |
| `scripts/citation_tracker.py` | JSON-backed three-count audit at `~/.litreview_sessions/<session>.json` |
| `scripts/framework_recommender.py` | Heuristic PICO/SPIDER/Decomposition suggestion from research question |
| `scripts/cross_search_aggregator.py` | Repeat-hits + recurring-authors + citation-per-year ranking after Phase 3 |

## References

- [`references/framework_selection.md`](references/framework_selection.md) — PICO / SPIDER / Decomposition canon (7+ sources)
- [`references/search_budget_allocation.md`](references/search_budget_allocation.md) — depth tiers + cross-search intelligence + sequential execution rationale (7+ sources)
- [`references/docx_8_sections.md`](references/docx_8_sections.md) — research guide DOCX spec + technical requirements (7+ sources)

## Anti-Patterns To Reject

- Parallelizing search calls (any lane)
- Skipping the interactive checkpoint (running all searches without user confirmation)
- Padding thin results with training knowledge
- Defaulting to non-PICO framework without justification
- Citing papers in chat that didn't come from this session's searches
- Attempting Consensus plan-tier detection (deleted — the only runtime check is "are the Consensus MCP tools available in this session?")
- Treating Consensus as required (it's an optional enhancement; the free lane is the default)
- Skipping era-gated searches in standard/deep budgets
- Skipping cross-search intelligence (repeat-hits, recurring authors)
- Truncating source URLs in hyperlinks

---

**Version:** 1.1.0
**Source spec:** [`megaprompts/09-litreview-megaprompt.md`](../../../../megaprompts/09-litreview-megaprompt.md)
**Build pattern:** Path B (direct conversion). Sibling of `pulse` (research-pack shape). v1.1.0: free keyless APIs (PubMed + OpenAlex) became the default search lane; Consensus demoted to optional enhancement; plan-tier detection deleted per the 2026-06 newgen audit + ClawHub rule #3 (no paid-service dependencies).

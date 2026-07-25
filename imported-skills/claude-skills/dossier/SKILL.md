---
name: dossier
description: "Decision-grade entity research skill — produces a hypothesis-tested dossier on a specific company, person, nonprofit, or government org, not a generic profile. Forcing intake makes the user state their hypothesis upfront (what they already believe and want to verify or disprove) so the dossier tests it rather than confirms it. Output is an editable Word document (.docx) with verdict on the hypothesis, identity facts, 12-month activity timeline, network and reputation signals, red flags, conversation hooks tied to specific findings, and source-provenance audit log. Uses WebSearch + WebFetch + free APIs (SEC EDGAR, GitHub, ProPublica) as workhorses; optional BYOK MCPs enhance coverage. Use when the user asks for background research, diligence, or meeting prep on a specific entity (e.g., 'prep me for a meeting with [person/company]', 'due diligence on [company]'). Honors sensitivity exclusions for journalism + personal-vetting contexts."
license: MIT
metadata:
  source_spec: "megaprompts/12-dossier-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  research_pack_convention: "Agent Integrity Rules verbatim per PR #657 audit; hypothesis-testing variant"
  version: 1.0.0
---

# Dossier — Decision-Grade Entity Research

> **Portability:** Requires `WebSearch` + `WebFetch`, Node.js with `docx` package, and optionally `bash_tool` + `curl` for free APIs (SEC EDGAR, GitHub, ProPublica). BYOK MCPs (LinkedIn, Crunchbase, Apollo, Pitchbook, SimilarWeb) are optional enhancements. Works in Claude Code CLI natively.

## Non-Generic Framing — The Differentiator

This skill is **decision-grade entity research with hypothesis-testing**. It **refuses** to be "tell me about Microsoft". Every invocation forces the user to expose their hypothesis upfront (Q4) so the dossier *tests* it rather than confirms it.

The use case shape:

> "I'm pitching Microsoft Tuesday. My hypothesis is they're consolidating AI spend on their first-party Foundry platform. Validate or disprove, and give me three conversation hooks tied to what you find."

**NOT:**

> "Tell me about Microsoft."

The forcing Q4 — the hypothesis question — is the non-generic anchor. Skip it and the skill produces a Wikipedia summary.

See [`references/hypothesis_testing_discipline.md`](references/hypothesis_testing_discipline.md) for the canon.

## Agent Integrity Rules (Research-Pack Convention)

Locked verbatim per PR #657 audit.

- **Execution discipline.** Sequential search calls. WebSearch + WebFetch have looser rate limits than Consensus but still apply 1 q/sec etiquette. Confirm response received before next call.
- **Source discipline.** Cite only sources returned by this session's tool calls. Wikipedia / training knowledge labeled `[Background — verify before quoting]` and excluded from primary findings count.
- **Three-count tracking.** Queries sent / sources received / sources cited. Plus **per-tier breakdown** (primary / secondary / tertiary) unique to dossier. Surfaced in audit log.
- **Retry policy.** On failure → wait 3s → retry once → log. After 3 consecutive failures: stop, alert user.
- **Source reliability tier.** Each citation tagged primary (official, SEC, court records) / secondary (mainstream news, trade press) / tertiary (blogs, forums). DOCX surfaces tier on every flag.

## Phase 1: Grill-Me Intake (6 forcing questions, one at a time)

### Q1 (root) — Subject identity

> **Who is the subject? Give me the exact name and, if a company, the website or LinkedIn URL. If a person, their LinkedIn URL or a unique identifier (company affiliation + role).**
>
> *Why I'm asking:* Disambiguation. There are 47 John Smiths. There are three companies called "Atlas". I need a specific entity to research.

If user gives only a name, push for a second identifier. **Refuse to proceed on ambiguous names.**

### Q2 (depends on Q1) — Subject type

> **What kind of subject is this? Pick one: person / company / nonprofit / government org / other.**
>
> *Why I'm asking:* Different source matrices apply. For people I check LinkedIn, GitHub, Scholar, news; for companies I check SEC EDGAR (if public), Crunchbase, news, GitHub for tech orgs; for nonprofits I check Form 990s on ProPublica.

Forcing choice. "Other" requires a one-line description.

### Q3 (depends on Q2) — Purpose

> **What are you preparing for? Pick one:**
>
> 1. Sales meeting / partnership pitch
> 2. Investment diligence
> 3. Acquisition diligence
> 4. Journalism / due diligence
> 5. Job interview prep
> 6. Competitive intelligence
> 7. Personal vetting (date, hire, business partner)
> 8. Other (specify)
>
> *Why I'm asking:* The purpose dictates the angle, the depth, and the red-flag sensitivity. Sales prep needs conversation hooks. Investment diligence needs traction signals. Personal vetting needs careful sensitivity boundaries.

### Q4 (depends on Q3) — **Hypothesis — MANDATORY**

> **What's your hypothesis going in? What do you already believe about this subject, and what do you want to verify or disprove?**
>
> *Why I'm asking:* This is the critical question. A dossier that just confirms what you already think is worthless. By stating your hypothesis upfront, I can search for evidence that would *disprove* it as well as evidence that supports it — and give you a verdict you can actually use.
>
> Examples:
> - "I believe Microsoft is consolidating AI spend on first-party Foundry. Verify or disprove."
> - "I think the CEO is over their head — too much TAM talk, no traction. Test that."
> - "I believe this nonprofit's overhead ratio is sketchy. Check the 990s."
> - "I think this person is technical enough to handle a CTO role. Verify."

**MANDATORY.** If user says "I don't have one", push back **once**: "Then guess. Commit to a position you can update later. The dossier needs a hypothesis to test, otherwise it's a generic profile and won't help you make a decision."

If still refused: fall back to implicit hypothesis "what's the most surprising thing I could find?" and **flag the fallback in audit log**.

This question is **the non-generic anchor**. Skip it and the skill becomes a Wikipedia summary.

### Q5 (depends on Q3) — Depth

> **Time horizon: 5-minute brief or 15-minute decision-grade dossier?**
>
> *Why I'm asking:* Brief mode caps at ~10 searches and skips the network + reputation passes. Decision-grade goes deeper on every section. Pick based on how much skin you have in this decision.

Forcing choice.

### Q6 (asked only if Q3 ∈ {journalism, personal vetting}) — Sensitivities

> **Anything sensitive to exclude? E.g., personal medical, family details, political history, or specific topics off-limits?**
>
> *Why I'm asking:* Some research contexts have ethical constraints. I'd rather know upfront than surface something you'd never share.

Skip for sales/investment/acquisition/competitive intel (low sensitivity); ask for journalism/personal vetting (high sensitivity).

**Stop condition:** After Q6 (or earlier with dependency skips), commit and start Phase 2. Never re-open intake after Phase 2 begins.

## Phase 2: Subject Disambiguation

Before Phase 3, resolve the subject to a specific entity:

- For people: confirm LinkedIn URL OR (employer + role + city)
- For companies: confirm domain OR (legal name + incorporation jurisdiction)
- For nonprofits: confirm EIN OR (legal name + state)
- For government orgs: confirm official .gov URL

If still ambiguous after Q1 push-back: **halt and re-ask Q1** with disambiguating identifiers. Refuse to proceed.

## Phase 3: Source Matrix Selection

Routed by Q2 subject type. See [`references/subject_type_source_matrix.md`](references/subject_type_source_matrix.md) for the full canon.

### Person

- LinkedIn (manual fetch or LinkedIn MCP if BYOK)
- Personal website
- Twitter/X (rate-limited; degrade gracefully)
- GitHub (if technical subject)
- Google Scholar (if academic)
- News (WebSearch + WebFetch)
- Conference talk transcripts, podcasts (WebSearch)

### Company

- Official website (about, leadership, news, careers)
- SEC EDGAR (free API; 10-Ks, 10-Qs, 8-Ks for public co's)
- Crunchbase free tier (or Crunchbase MCP if BYOK)
- News (WebSearch + WebFetch)
- GitHub (for tech orgs)
- Glassdoor + Comparably (sentiment; degrade gracefully if scraping blocked)
- LinkedIn company page

### Nonprofit

- ProPublica Nonprofit Explorer (free; Form 990s)
- Official website
- News
- GuideStar (if accessible)

### Government org

- Official .gov sites
- News
- ProPublica (for federal agencies)

If a paid MCP is connected (Apollo, Pitchbook, SimilarWeb), use it but mark findings as **BYOK-sourced** in the audit log.

## Phase 4: Hypothesis-Driven Search

Every Phase 4 search MUST be classified as either:

- **Supporting evidence** (confirms hypothesis), OR
- **Disconfirming evidence** (would refute hypothesis)

**≥30% of search budget allocated to disconfirming queries.** Enforced via `scripts/disconfirming_evidence_balance.py`.

Example for hypothesis "Microsoft is consolidating AI spend on Foundry":

- **Supporting:** "Microsoft Foundry adoption 2026", "Microsoft AI infrastructure consolidation"
- **Disconfirming:** "Microsoft OpenAI deal renegotiation", "Microsoft AI vendor diversification", "Microsoft third-party model partnerships 2026"

This is what makes the dossier **decision-grade** rather than confirmation-biased.

For each search:
- Record via `citation_tracker.py` with classification (supporting / disconfirming)
- Apply source tier from `source_tier_classifier.py` to each result URL

## Phase 5: 12-Month Activity Timeline

Default 12-month window for activity timeline; deeper for foundational identity.

Categories:
- News (acquisitions, hires, departures, product launches)
- Funding rounds / financial events
- Controversies / legal events
- Public statements / strategy shifts

Reverse chronological. Each entry hyperlinked + tiered.

## Phase 6: Network + Reputation Signals

### Network

- **Companies:** investors (in/out), customers (named), partners
- **People:** co-founders, advisors, mentors, employers, board roles
- **Nonprofits:** funders, board, leadership

5-10 entries, ranked by **relevance to hypothesis**.

### Reputation

- Sentiment from news (recent 12 months)
- Glassdoor for companies (overall rating + 3 representative reviews)
- Peer mentions for people
- Caveat: reputation data is noisy; tier accordingly

## Phase 7: Red-Flag Pass

Surface but don't sensationalize:

- Litigation (court records → primary tier)
- Regulatory actions (SEC, DOJ, agency actions → primary)
- Unusual departures (key personnel exits within 90 days)
- Financial signals (going-concern notes in 10-Ks → primary)
- Reputation hits (sustained negative coverage → secondary)

**Each flag tiered.** Tier shows up next to every flag in the DOCX.

## Phase 8: Conversation Hook Generation

3-5 specific hooks tied to **actual findings**, not generic talking points.

See [`references/conversation_hook_quality.md`](references/conversation_hook_quality.md) for the canon.

| ❌ Generic | ✅ Finding-tied |
|---|---|
| "Ask about their roadmap" | "Mention their recent acquisition of [X] — it signals they're investing in vertical Y. Suggested framing: 'Saw the [X] announcement — how does that change your roadmap on Y?'" |
| "Ask about hiring" | "Their VP Engineering left 3 weeks ago (LinkedIn). Suggested framing: 'I noticed [name] moved on — what's the eng leadership plan?'" |
| "Talk about their values" | "They updated their pricing page last week (their official site). Suggested framing: 'Saw the pricing refresh — what drove that?'" |

Each hook:
- **The hook** (one sentence)
- **The finding it's tied to** (with hyperlink + tier)
- **Suggested framing** (verbatim phrasing user can adapt)

## Phase 9: DOCX Generation (9 Sections)

Via Node.js + `docx` library.

1. **Executive Summary** — one paragraph: who they are + why they matter + **verdict on the hypothesis** (SUPPORTED / PARTIALLY SUPPORTED / DISPROVEN / INCONCLUSIVE) + 3 things-you-should-know bullets.
2. **Identity Facts Table** — founded/born, location, size/stage, current role, key affiliations. All cells sourced; hover-text tier.
3. **Hypothesis Test** — user's hypothesis stated verbatim. Supporting evidence (3-5 bullets with hyperlinked citations). Disconfirming evidence (3-5 bullets with hyperlinked citations). Verdict paragraph (2-3 sentences explaining the weight).
4. **12-Month Activity Timeline** — News, funding, hires, departures, product launches, controversies. Reverse chronological. Each entry hyperlinked.
5. **Network Signals** — Collaborators / investors / associates. 5-10 entries, ranked by relevance to hypothesis.
6. **Reputation Signals** — Sentiment from news, Glassdoor for companies, peer mentions for people. Caveat: reputation data is noisy.
7. **Red Flags + Hidden Patterns** — Litigation, regulatory actions, unusual departures, financial signals, reputation hits. Tiered.
8. **Conversation Hooks** — 3-5 specific hooks tied to findings. Each: hook + finding + suggested framing.
9. **Source Provenance + Audit Log** — Per-source list with tier. Search summary table (#, query, classification, sources returned, sources cited). Three counts + per-tier counts. Failed searches. BYOK-MCP usage flag.

### Styling

Arial 12pt body, navy headings (#1a3a5c), light blue table headers (#e8f0f8), red red-flag callout, green conversation-hook callout.

### Hyperlink patterns

```js
new ExternalHyperlink({
  link: "https://...",
  children: [new TextRun({ text: title, style: "Hyperlink" })],
});
```

## Phase 10: Deliver

- Save: `<output-dir>/dossier_<entity-slug>_<YYYY-MM-DD>.docx`
- Chat summary: file path + **verdict on hypothesis** + audit counts + tier breakdown + BYOK MCPs used (if any)
- Validate: check zip integrity with `python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).testzip()" <docx>` (no output = intact), then confirm the required sections are present

## Tooling

| Script | Role |
|---|---|
| `scripts/citation_tracker.py` | Three-count audit + supporting/disconfirming classification + source-tier tagging at `~/.dossier_sessions/<session>.json` |
| `scripts/disconfirming_evidence_balance.py` | Verifies ≥30% of search budget allocated to disconfirming queries; warns if biased |
| `scripts/source_tier_classifier.py` | URL → primary / secondary / tertiary classification via domain heuristics |

## References

- [`references/hypothesis_testing_discipline.md`](references/hypothesis_testing_discipline.md) — ≥30% rule + decision-grade vs encyclopedic (7+ sources)
- [`references/subject_type_source_matrix.md`](references/subject_type_source_matrix.md) — person/company/nonprofit/gov source matrices (7+ sources)
- [`references/conversation_hook_quality.md`](references/conversation_hook_quality.md) — finding-tied hook discipline (7+ sources)

## Error Handling

| Failure | Behavior |
|---|---|
| Subject name ambiguous | Refuse to proceed. Re-ask Q1 with disambiguating identifier. |
| User refuses to state hypothesis | Push back once. If still refused, fall back to "what's the most surprising thing I could find?" implicit hypothesis. Flag in audit. |
| Subject has zero public footprint | Surface explicitly. Suggest different name or early-stage. Don't fabricate. |
| LinkedIn scrape blocked | Note in audit; fall back to WebSearch; suggest user verify manually. |
| SEC EDGAR fails | Retry once. If still failing, note "public filings not retrieved" and continue. |
| Sentiment data sparse | Mark reputation section as "limited public signal"; don't infer from training. |
| Sensitive topic surfaces (Q6 exclusion) | Exclude from DOCX. Note in chat (not in DOCX) so user knows the exclusion was honored. |
| 3 consecutive tool failures | Stop, alert user, share collected so far. |
| DOCX generation fails | Save raw data as JSON fallback. |

## Anti-Patterns To Reject

- Producing a dossier without forcing Q4 hypothesis
- Allocating <30% of search budget to disconfirming evidence
- Batching intake questions
- Accepting ambiguous subject names
- Generic conversation hooks ("ask about their roadmap")
- Sensationalizing red flags (tier them, don't editorialize)
- Skipping the source-reliability tier on flags
- Fabricating coverage when LinkedIn or scraping is blocked
- Using BYOK-MCP data without flagging in audit log
- Including sensitive topics user excluded in Q6
- Confirmation-biased verdict ("SUPPORTED" without engaging with disconfirming evidence)

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/12-dossier-megaprompt.md`](../../../../megaprompts/12-dossier-megaprompt.md)
**Build pattern:** Path B (direct conversion). Research-pack sibling, hypothesis-testing variant.

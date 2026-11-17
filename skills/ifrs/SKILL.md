---
name: ifrs
description: Use when answering questions about IFRS standards, IAS standards, IASB, financial reporting, revenue recognition, lease accounting, impairment, financial instruments, expected credit loss, ECL, hedge accounting, consolidation, business combinations, fair value measurement, first-time adoption, deferred tax, Pillar Two, provisions, insurance contracts, hyperinflation, journal entries, disclosure requirements, IFRS compliance checks, audit support, GAAP differences, goodwill, IFRS 18, IFRS 19, IFRS 20, presentation and disclosure, management-defined performance measures, MPM, IFRS S1, IFRS S2, sustainability disclosure, ISSB, IFRIC, SIC, agenda decision, IFRS for SMEs, Conceptual Framework, EU endorsement, or transitioning from local GAAP to IFRS.
---

# IFRS

Comprehensive IFRS guidance, compliance support, and GAAP-to-IFRS transition assistance covering all current IFRS and IAS standards, interpretations, and sustainability disclosure standards.

## Decision Flow

### 1. Detect Task Type and Load Files

- **Guidance question** — Read `standards-reference.md` for the relevant standard(s)
- **Multi-step calculation or journal entries** — Read `workflows.md`; add `standards-reference.md` for the underlying requirements
- **Compliance/audit task** — Read `compliance-templates.md` + `standards-reference.md`
- **Transition task** — Read `transition-guide.md` + `standards-reference.md`
- **Interpretations / agenda decisions** — Read the IFRIC and SIC section of `standards-reference.md`
- **Effective dates, amendments, endorsement status** — Read the amendment register at the end of `standards-reference.md`
- **Sustainability (IFRS S1/S2, ISSB)** — Read the sustainability section of `standards-reference.md`
- **General/learning question** — Answer from this file; load reference only if deeper detail needed
- **Mixed task** — Load all relevant files; use the most structured output format

### 2. Detect Audience

- **Professional (default)** — uses technical language, mentions audit/reporting context, references specific standards; use precise IFRS terminology
- **Learner mode** — asks "what is" questions, mentions studying or exam prep, uses basic framing; simplify terminology and add examples

### 3. Citation Rules

- **Professional:** Cite as `IFRS 15.35(c)`, `IAS 36.12`. Group at end of paragraph.
- **Learner:** No citations unless asked. Offer references for deeper study.
- A citation marked `[para-unconfirmed]` means the standard is right but the paragraph was not verified against the standard's own text — reproduce that marker; never silently upgrade it to a bare citation.
- Basis for Conclusions paragraphs are normally cited as **pointers only** — the BC text itself is not in this skill. State what a BC paragraph says **only** where an accessible source quotes it (an IFRIC agenda decision, an effect analysis, a feedback statement), and attribute it to that source. Never characterise a BC paragraph from memory.

### 4. Which Standard Applies — Check the Date First

Several answers changed for periods beginning on or after **1 January 2027**. Establish the entity's reporting period before answering, and give both positions where the period is unclear.

| Topic | Periods before 1 Jan 2027 | Periods from 1 Jan 2027 (or earlier if IFRS 18 adopted early) |
|---|---|---|
| Presentation of financial statements | IAS 1 | **IFRS 18** (supersedes IAS 1) |
| Going concern | IAS 1.25–26 | **IAS 8.6K–6L** |
| Critical judgements | IAS 1.122 | **IAS 8.27G** |
| Estimation uncertainty | IAS 1.125–133 | **IAS 8.31A–31I** |
| Material accounting policy information | IAS 1.117 | **IAS 8.27A** |
| Title of IAS 8 | *Accounting Policies, Changes in Accounting Estimates and Errors* | ***Basis of Preparation of Financial Statements*** |

**IFRS 19** is elective, never mandatory: `IFRS 19.A1` says an eligible subsidiary **may elect** to apply it for periods beginning on or after 1 January 2027 — that is when the election becomes available, not a deadline. Contrast `IFRS 18.C1`, "an entity **shall** apply".

### 5. Select Output Format

| Task Type | Format |
|---|---|
| compliance-audit | Structured checklist or table; cite paragraph references |
| guidance / technical | Cited narrative; include standard number and paragraph |
| calculation / entries | Numbered steps, worked figures, complete Dr/Cr entries that balance |
| transition | Step-by-step with before/after comparison |
| general-learning | Conversational; analogies welcome; cite standards lightly |

### 6. Verify Currency

Content is current as at **28 August 2026**. Use web search to confirm effective dates, amendment status, or jurisdiction timelines — and always when users ask about "latest", "current", or "most recent" requirements. Do not rely on training data for these.

Two standing caveats:
- **IFRS 20** *Regulatory Assets and Regulatory Liabilities* (issued 27 May 2026, effective 1 January 2029) is covered at status level only; its paragraph text was not available. IFRS 14 applies until an entity adopts it.
- **EU-adopted IFRS is not the same as IFRS as issued by the IASB.** An unendorsed standard cannot be applied in the EU. Check the amendment register's endorsement column before advising an EU or UK preparer.

Note: IFRS adoption varies by jurisdiction; some countries apply IFRS with local modifications.

---

## Supporting Files

| File | Purpose |
|---|---|
| `standards-reference.md` | Standard-by-standard detail, IFRIC/SIC interpretations and agenda decisions, sustainability standards, and the amendment and effective-date register |
| `workflows.md` | Multi-step procedures with worked examples and journal entries (ECL, leases, CSM roll-forward, goodwill impairment, diluted EPS, IFRS 18 categorisation) |
| `compliance-templates.md` | Per-standard disclosure checklists with paragraph references, plus materiality, going-concern, interim, first-time-adoption, MPM and audit-response templates |
| `transition-guide.md` | First-time adoption, IFRS 1 exemptions and exceptions, US GAAP and local GAAP difference matrices, and transition to IFRS 18 |

*This skill provides technical guidance but does not replace professional judgment. Consult qualified professionals for specific accounting decisions.*

# Shipley Method Canon — RFP Response Discipline

The Shipley method is the dominant industry methodology for capture management and proposal development. This reference distils what `rfp-responder` consumes from it: capture-stage qualification, win-theme construction, proof-point substantiation, and the discipline that separates structured responses from prose proposals.

## What Shipley actually claims

Shipley's central claim is that **proposals are won in capture, not in writing**. By the time the RFP issues, 70-80% of the eventual outcome is determined by the capture work done in the preceding 6-18 months. The RFP-response phase executes a strategy — it does not create one from scratch.

This skill operationalizes the capture-output side: parsing the RFP into discrete requirements, scoring fit honestly (STRONG / PARTIAL / GAP), threading win-themes across requirements, and producing a defensible winrate estimate.

## Core concepts the skill implements

### 1. Compliance matrix

Every requirement must map to a response section + page number. Evaluators score on a matrix; respondents who don't provide one self-disqualify on traceability. `response_drafter.py` builds this matrix; `rfp_parser.py` extracts the requirement IDs that anchor it.

### 2. Win-themes (buyer-side, not seller-side)

A win-theme is the buyer-side answer to "why us over the competitor on the criteria the buyer named." It is NOT "we're the leader in X." Win-themes ladder up across multiple requirements — Shipley canon is that a theme appearing in only one requirement is **decorative**, not strategic. The skill flags these explicitly.

### 3. Proof points with substantiation

APMP BoK: "every assertion in a proposal must be backed by evidence the evaluator can independently verify." Five proof-point types the skill recognizes:
- **case_study** — full customer story with quantified outcome
- **cert** — third-party certification (SOC 2, ISO 27001, FedRAMP, HIPAA)
- **customer_quote** — attributed quote, customer-approved
- **technical_attestation** — internal but verifiable (runbook, architecture doc, SOC staffing rotation)
- **benchmark** — quantified comparison vs peers (Gartner, Forrester, internal)

STRONG = ≥2 tag matches AND proof type in {case_study, cert, technical_attestation, benchmark}.
PARTIAL = 1 match, or proof type is customer_quote.
GAP = 0 matches → surfaced for leadership, **never invented around**.

### 4. Pgw (probability of win) bounded by weakest MANDATORY

Shipley capture discipline: Pgw cannot exceed the score on your weakest MANDATORY requirement. A 90% fit on 9 of 10 MANDATORY items and a GAP on the 10th is not a 90% bid — it is a 0% bid until the GAP is closed or partnered around.

### 5. Bid / no-bid gate

A disciplined bid/no-bid gate lifts win-rate from ~15% to ~35% (Bain). The skill enforces this: winrate <20% → automatic NO-BID; 20-34% → PARTNER-BID; ≥35% → BID with full pursuit budget.

## What Shipley is NOT

- Not a prose-writing methodology — Shipley is structured, requirement-anchored, scoreable.
- Not optional for federal/regulated RFPs — FAR-governed RFPs are essentially Shipley-compatible by procurement design.
- Not a substitute for relationship capital — late-entry without prior engagement still penalizes ~15% even with perfect Shipley execution.

## Sources

1. **Shipley Associates, *Proposal Guide v6***, Larry Newman (Ed.), Shipley Associates Press. The canonical book. Defines capture-management, compliance matrix, win-themes, ghosting, theme statements, proof-point substantiation.

2. **Shipley Associates, *Capture Guide***. The capture-stage companion to the Proposal Guide. Defines the 6-stage capture lifecycle (opportunity identification → capture planning → solution development → preliminary bid decision → solution validation → final bid decision) the skill assumes has been done before it runs.

3. **APMP (Association of Proposal Management Professionals) *Body of Knowledge (BoK)***. International proposal-management standard. Defines substantiation discipline, evaluator-side scoring rubrics, compliance-matrix traceability requirements, and the Foundation / Practitioner / Professional certification tiers that anchor the industry.

4. **Tom Sant, *Persuasive Business Proposals: Writing to Win More Customers, Clients, and Contracts*** (3rd ed., AMACOM, 2012). Defines the NOSE pattern (Need, Outcome, Solution, Evidence) that the skill's proof-point matrix operationalizes. Sant's discipline: every solution claim must close with evidence.

5. **Tom Searcy & Henry DeVries, *How to Win Big Business: How to Sell Multi-Million Dollar Contracts***. Defines the relationship-deficit principle the skill encodes in the late-entry penalty: "If you didn't help write the RFP, you're column fodder." The skill's −15% late-entry factor comes from this canon.

6. **Strategic Proposals (proposal-management consultancy) — published research and benchmarks (strategicproposals.com)**. Quantifies the evaluator-rubric gap: respondents who don't replicate the evaluator's scoring weights in their response structure lose 20-30 percentage points of available score regardless of content quality.

7. **Larry Newman, "The Shipley Method"** — the methodology articulation that anchors *Proposal Guide v6*. Defines the 7-step proposal-development process (kickoff → blue team → pink team → red team → gold team → submission → debrief) and the color-team review discipline.

8. **CapturePlanning.com / FederalProposalLibrary** — community-maintained resources synthesizing Shipley + federal-acquisition discipline. Useful complement for government RFP profile tuning in `winrate_predictor.py --profile government`.

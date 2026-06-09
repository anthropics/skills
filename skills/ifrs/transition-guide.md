# GAAP-to-IFRS Transition Guide

This guide provides framework-agnostic guidance for entities transitioning from local GAAP to IFRS. It focuses on IFRS requirements and flags common difference areas rather than mapping from any specific national framework. For detailed IFRS 1 first-time adoption steps, see the IFRS 1 workflow in `workflows.md`. For the gap analysis template, see `compliance-templates.md`.

---

## 1. Overview

### What Is an IFRS Transition?

An IFRS transition is the process of converting an entity's financial reporting from a local (national) GAAP to International Financial Reporting Standards. The governing standard is **IFRS 1 — First-time Adoption of International Financial Reporting Standards**, which:

- Requires full retrospective application of all IFRS standards effective at the first IFRS reporting date, subject to specific mandatory exceptions and optional exemptions.
- Mandates an opening IFRS balance sheet at the **date of transition** (the beginning of the earliest comparative period).
- Requires at least one year of comparative information prepared under IFRS.
- Provides a structured set of exemptions to reduce the cost of transition where full retrospective application would be impracticable or excessively burdensome.

> **Cross-reference:** For the complete step-by-step IFRS 1 adoption procedure, see the IFRS 1 First-Time Adoption workflow in `workflows.md`.

### Governing Principles

1. **Retrospective application** — Apply each IFRS standard as if it had always been applied, unless an exemption is elected.
2. **Consistency** — Use the same accounting policies throughout all periods presented in the first IFRS financial statements.
3. **Transparency** — Provide reconciliations from previous GAAP to IFRS so users can understand the impact of the transition.

---

## 2. Key Dates

### Date Framework

| Date | Definition | Example (FY2026 Adoption, 1-Year Comparatives) |
|---|---|---|
| **Date of transition** | Beginning of the earliest comparative period presented under IFRS | 1 January 2025 |
| **Comparative period end** | End of the comparative period | 31 December 2025 |
| **First IFRS reporting date** | End of the first annual reporting period under IFRS | 31 December 2026 |

### Timeline Illustration (FY2026 Adoption)

```
1 Jan 2025              31 Dec 2025             31 Dec 2026
    |                       |                       |
    |--- Comparative -------|--- First IFRS Year ---|
    |                       |                       |
 Opening IFRS          Comparative             First IFRS
 balance sheet         financial              financial
 (date of             statements              statements
  transition)          (restated)             (published)
```

### What Happens at Each Date

- **1 January 2025 (date of transition):** Prepare an opening IFRS balance sheet. Recognise all assets and liabilities required by IFRS, derecognise items not permitted, reclassify as needed, and measure everything under IFRS. Adjustments go to retained earnings (or another equity category if appropriate).
- **31 December 2025 (comparative period end):** Present a full set of IFRS-compliant comparative financial statements for this period.
- **31 December 2026 (first IFRS reporting date):** Publish the first complete set of IFRS financial statements, including the IFRS 1 reconciliations and disclosures.

---

## 3. Common Difference Areas

The following ten areas represent the most frequent sources of adjustment when transitioning from local GAAP to IFRS. Each entry describes the IFRS requirement and flags typical differences found under common national frameworks.

### 3.1 Revenue Recognition — IFRS 15

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Model** | Five-step model based on transfer of control | Risks-and-rewards model; revenue recognised at a single point (e.g., delivery) |
| **Multiple performance obligations** | Allocate transaction price to each distinct performance obligation using standalone selling prices | Bundled arrangements often recognised as a single unit |
| **Variable consideration** | Estimate and constrain variable consideration at contract inception | Variable amounts recognised only when finalised or when uncertainty resolved |
| **Contract costs** | Capitalise incremental costs of obtaining a contract (IFRS 15.91-94) | Sales commissions and bid costs typically expensed as incurred |
| **Timing** | Recognise over time if criteria in IFRS 15.35 are met; otherwise at a point in time | Percentage-of-completion may apply under different criteria or not at all |

**Transition action:** Restate open contracts at the date of transition. Consider the IFRS 1 optional exemption for completed contracts.

### 3.2 Leases — IFRS 16

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Lessee model** | Single on-balance-sheet model: recognise right-of-use asset and lease liability for virtually all leases | Operating leases kept off balance sheet; only finance/capital leases on balance sheet |
| **Measurement** | Initial measurement at present value of lease payments; subsequent depreciation of ROU asset and interest on liability | Operating lease expense recognised on straight-line basis with no balance sheet impact |
| **Short-term / low-value** | Optional exemptions for leases under 12 months or of low-value underlying assets | No equivalent distinction needed when operating leases are off balance sheet |
| **Sale and leaseback** | Apply IFRS 15 to determine whether transfer is a sale; if so, measure ROU asset proportionally | May recognise full gain on sale; leaseback treated as new operating lease |

**Transition action:** Inventory all lease contracts. Quantify the balance sheet gross-up. IFRS 1 permits measuring the lease liability at transition date (rather than at lease inception) as a practical expedient.

### 3.3 Financial Instruments — IFRS 9

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Classification** | Three categories based on business model and contractual cash flow characteristics: amortised cost, FVOCI, FVTPL | Four or more categories (held-to-maturity, available-for-sale, loans and receivables, FVTPL) |
| **Impairment** | Expected credit loss (ECL) model — forward-looking, three-stage approach | Incurred loss model — impairment recognised only after a loss event occurs |
| **Hedge accounting** | Simplified qualifying criteria; more hedging strategies eligible; risk components of non-financial items hedgeable | More restrictive bright-line effectiveness tests (e.g., 80-125% corridor) |
| **Equity investments** | Irrevocable FVOCI election (no recycling to P&L); otherwise FVTPL | May permit cost method for unquoted equities or recycling of AFS gains |

**Transition action:** Reclassify financial assets based on IFRS 9 criteria. Calculate ECL allowances at the date of transition. Review hedge documentation for IFRS 9 compliance.

### 3.4 Employee Benefits — IAS 19

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Defined benefit measurement** | Project unit credit method; remeasurements (actuarial gains/losses) in OCI with no recycling | Corridor approach permitted (defer and amortise actuarial gains/losses); or immediate P&L recognition |
| **Discount rate** | High-quality corporate bonds (or government bonds where no deep market exists) | May use different benchmark rates |
| **Past service cost** | Recognise immediately in P&L when plan amendment occurs | Amortise over remaining service period |
| **Multi-employer plans** | Account as defined contribution unless sufficient information for defined benefit accounting | Treatment varies; some frameworks allow defined contribution accounting in all cases |

**Transition action:** Obtain actuarial valuations at the date of transition. Recognise the full net defined benefit liability/asset. IFRS 1 permits cumulative actuarial gains and losses to be reset to zero at the date of transition.

### 3.5 Impairment of Non-Financial Assets — IAS 36

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Trigger** | Impairment test when indicators exist; annual for goodwill and indefinite-life intangibles | Some frameworks require annual testing for all long-lived assets or have different trigger indicators |
| **Recoverable amount** | Higher of fair value less costs of disposal and value in use (discounted cash flows) | Undiscounted cash flow test as a first screen; impairment measured differently |
| **Cash-generating units** | Test at CGU level (smallest group generating independent cash inflows) | May test at a different level of aggregation (e.g., reporting unit, asset group) |
| **Reversal** | Reversal required when conditions change (except for goodwill impairment — never reversed) | Some frameworks prohibit reversal of any impairment |

**Transition action:** Identify CGUs. Test goodwill and indefinite-life intangibles at the date of transition. Consider the IFRS 1 deemed cost exemption for assets where historical IFRS cost would be difficult to reconstruct.

### 3.6 Property, Plant and Equipment — IAS 16

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Component depreciation** | Each significant component of an asset depreciated separately | Single useful life for the whole asset; no component accounting |
| **Revaluation model** | Permitted as an accounting policy (class-by-class election) | Revaluation prohibited in some frameworks; or permitted but with different mechanics |
| **Residual value** | Review at least annually; based on current prices | Set at acquisition and rarely updated |
| **Borrowing costs** | IAS 23 requires capitalisation for qualifying assets | May be expensed or capitalised at entity's option |
| **Decommissioning** | Include in cost with corresponding provision (IAS 37 / IFRIC 1) | Often not recognised until expenditure incurred |

**Transition action:** Componentise major assets. Reassess useful lives and residual values. Elect fair value or previous-GAAP revaluation as deemed cost under IFRS 1 if full retrospective cost data is unavailable.

### 3.7 Intangible Assets — IAS 38

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Development costs** | Capitalise when all six IAS 38.57 criteria are met | Expense all R&D as incurred; or capitalise under different criteria |
| **Useful life** | Indefinite life permitted (no amortisation; annual impairment test instead) | All intangibles amortised over a maximum period (e.g., 10 or 20 years) |
| **Internally generated** | Internally generated brands, mastheads, customer lists — not recognised | Some frameworks permit recognition of certain internally generated intangibles |
| **Revaluation** | Permitted only if active market exists (rare in practice) | Revaluation typically prohibited |

**Transition action:** Review capitalised development costs against IAS 38.57 criteria. Derecognise any internally generated intangibles not meeting IFRS recognition criteria. Assess useful lives (finite vs indefinite).

### 3.8 Provisions and Contingencies — IAS 37

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Recognition threshold** | "Probable" means more likely than not (>50%) | "Probable" may mean a higher threshold (e.g., ~75% in some frameworks) |
| **Measurement** | Best estimate; discount to present value if time value of money is material | Undiscounted amounts; or range-based measurement (e.g., low end of range) |
| **Restructuring** | Recognise only when detailed formal plan exists and valid expectation raised | Earlier recognition permitted based on board approval alone |
| **Contingent liabilities** | Disclose but do not recognise (unless acquired in a business combination) | Treatment varies; some frameworks require accrual at lower probability thresholds |

**Transition action:** Reassess all existing provisions against IAS 37 criteria. Discount long-term provisions. Review contingent liabilities for disclosure adequacy.

### 3.9 Consolidation and Group Accounting — IFRS 10

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Control model** | Consolidate when investor has power, exposure to variable returns, and ability to use power to affect returns | Voting-interest model (majority of voting rights triggers consolidation); or risks-and-rewards model |
| **Structured entities** | Assessed under same control model; consolidate if controlled | Separate evaluation framework (e.g., variable interest entity model) with different criteria |
| **Investment entities** | Exception from consolidation; measure subsidiaries at FVTPL (IFRS 10.31-33) | No equivalent exception; all subsidiaries consolidated |
| **Non-controlling interests** | Measured at fair value or proportionate share of net assets (election per combination) | Typically measured at book value of proportionate net assets |

**Transition action:** Reassess control conclusions for all investees. Identify structured entities. Consider the IFRS 1 exemption for business combinations that occurred before the date of transition.

### 3.10 Presentation and Disclosure — IAS 1

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Complete set of statements** | Statement of financial position, profit or loss and OCI, changes in equity, cash flows, and notes | Some frameworks do not require a statement of changes in equity or OCI as a separate statement |
| **OCI classification** | Items that will and will not be reclassified to P&L must be presented separately | OCI may not be required or may have different classification rules |
| **Current/non-current distinction** | Required unless a liquidity-based presentation is more relevant | Some frameworks mandate a different ordering or do not require the distinction |
| **Significant judgements and estimates** | Disclose key sources of estimation uncertainty and critical judgements (IAS 1.122-133) | Disclosure requirements may be less specific |
| **Comparative information** | Minimum one year of comparative information; three balance sheets if retrospective restatement | One year typical but specific requirements vary |

**Transition action:** Redesign the chart of accounts and financial statement templates. Map local GAAP line items to IAS 1 presentation requirements. Prepare IFRS-compliant note disclosures.

---

## 4. Deferred Tax Implications on Transition (IAS 12)

### General Principle

IAS 12 — Income Taxes must be applied to all IFRS-adjusted carrying amounts at the date of transition. IFRS 1 does not provide an exemption from IAS 12 — entities must recognise deferred tax assets and liabilities for all temporary differences that exist between IFRS carrying amounts and their tax bases at the date of transition.

Tax-basis amounts typically remain unchanged on transition because tax follows local rules, not IFRS. However, because IFRS carrying amounts often differ significantly from previous GAAP carrying amounts, new temporary differences arise that did not exist (or existed in different amounts) under the previous framework.

The deferred tax impact often materially affects the opening retained earnings figure and is one of the most frequently underestimated areas of transition complexity.

### Common Sources of New Temporary Differences on Transition

| Source | Nature of Temporary Difference |
|---|---|
| **IFRS 16 ROU assets and lease liabilities** | IFRS recognises a right-of-use asset and lease liability that typically have different carrying amounts from their tax base (which may be nil if the jurisdiction treats the lease as an operating lease for tax). The ROU asset and liability often differ from each other, creating a net temporary difference. |
| **IFRS 9 ECL provisions** | Expected credit loss provisions are typically larger than incurred-loss provisions under previous GAAP. Tax deductions for credit losses usually follow local tax rules (often requiring write-off or specific evidence of impairment), creating a deductible temporary difference. |
| **IAS 19 remeasured employee benefit obligations** | Full recognition of the net defined benefit liability under IAS 19 (using the projected unit credit method) often results in a larger liability than under previous GAAP, particularly where corridor approaches were used. Tax deductions typically follow cash contributions. |
| **IAS 36 impairment adjustments** | Impairment losses recognised on transition (or reversals of previous impairment) change carrying amounts of non-financial assets without affecting tax bases, creating temporary differences. |
| **IFRS 15 contract assets and liabilities** | Revenue timing differences under the IFRS 15 five-step model may create contract assets or liabilities that have no tax base (tax follows invoicing or cash receipts in many jurisdictions). |
| **IAS 38 capitalised development costs** | Development costs capitalised under IAS 38 that were expensed under previous GAAP (or vice versa) create temporary differences where tax deductions follow the previous GAAP treatment. |

### Deferred Tax Asset Recoverability

Entities must reassess deferred tax asset (DTA) recoverability under IFRS carrying amounts. The assessment is based on:

- Projected future taxable profits using IFRS-based forecasts
- Reversing taxable temporary differences against which deductible temporary differences can be utilised
- Tax planning opportunities available to the entity

Where IFRS adjustments significantly change the balance sheet (e.g., large new deductible temporary differences from ECL provisions or lease liabilities), the DTA recoverability assessment may yield a different conclusion from the one reached under previous GAAP.

---

## 5. IT and System Changes

System and technology changes are a critical workstream in any IFRS transition. These should begin during Phase 1 (Assessment), not deferred to Phase 2, because system procurement and implementation timelines are often the longest lead-time items.

### Typical System Workstreams

| Workstream | Description |
|---|---|
| **Lease accounting software (IFRS 16)** | For entities with significant lease portfolios, dedicated lease accounting software is essentially mandatory. The calculations (present value of lease payments, ROU asset depreciation, interest expense, remeasurement on modification) are too complex and voluminous for spreadsheets at scale. Evaluate build vs buy: most entities should buy a commercial solution unless their IT capability and lease complexity justify a bespoke build. |
| **ECL model infrastructure (IFRS 9)** | Expected credit loss modelling requires credit risk models, forward-looking macroeconomic scenarios, probability of default and loss-given-default estimates, and staging logic. Financial institutions typically need dedicated ECL platforms; corporates with simpler portfolios may manage with structured spreadsheets or lightweight tools. |
| **Chart of accounts redesign (IAS 1)** | IAS 1 presentation requirements often differ from local GAAP. The chart of accounts may need new accounts for OCI components, ROU assets, contract assets/liabilities, ECL allowances, and other IFRS-specific items. This redesign affects the general ledger, reporting tools, and consolidation systems. |
| **Dual-reporting capability** | During the parallel run period, systems must produce both local GAAP and IFRS outputs. This may require parallel ledgers, mapping tables, or adjustment journals layered on top of the existing ledger. Plan the technical approach early. |
| **Data migration and validation** | Transition adjustments must flow into production systems cleanly. Establish data validation procedures to ensure opening IFRS balances reconcile to the adjustment workpapers, and that ongoing IFRS processing produces correct results from day one. |

### Decision Framework: Spreadsheets vs Dedicated Software

| Factor | Spreadsheets May Suffice | Dedicated Software Recommended |
|---|---|---|
| **Volume** | Small number of items (e.g., <50 leases, simple loan book) | Large portfolios (hundreds of leases, complex financial instruments) |
| **Complexity** | Straightforward calculations, few modifications expected | Variable payments, frequent modifications, complex staging logic |
| **Audit trail** | Entity has strong spreadsheet controls and version management | Audit trail, access controls, and change logs needed |
| **Ongoing maintenance** | One-time transition calculation with simple ongoing needs | Ongoing monthly/quarterly recalculation and reporting |
| **Resource availability** | Skilled spreadsheet modellers available in-house | Prefer vendor-supported, maintainable solution |

### Timeline

System changes should begin in Phase 1 (Assessment), not Phase 2. Key milestones:

1. **Phase 1:** Identify system requirements, evaluate vendor solutions, begin procurement and implementation planning.
2. **Phase 2:** Complete system implementation, configure for IFRS policies, load opening balances, begin parallel processing.
3. **Phase 3:** Systems in production for IFRS reporting; resolve any issues surfaced during parallel runs.

---

## 6. Transition Project Planning

### Phase 1: Assessment (3-6 Months Before Date of Transition)

**Objective:** Understand the scope of change and build the business case.

1. **Perform a diagnostic gap analysis** — Compare current accounting policies with IFRS requirements across all material areas. Use the gap analysis template in `compliance-templates.md`.
2. **Quantify the expected impact** — Estimate the effect on key financial metrics (equity, net income, leverage ratios, debt covenants).
3. **Identify data and system requirements** — Determine what additional data capture, system modifications, or new subledgers are needed (e.g., lease system for IFRS 16, ECL model for IFRS 9).
4. **Assess IFRS 1 exemption elections** — Perform a preliminary assessment of which optional exemptions to elect (see Section 7 below).
5. **Establish governance** — Appoint a transition project team, define roles (finance, IT, external advisors, auditors), and set up a steering committee.
6. **Develop project timeline and budget** — Map all workstreams, milestones, and resource requirements against the key dates in Section 2.

### Phase 2: Preparation (Date of Transition to End of Comparative Period)

**Objective:** Build IFRS-ready processes and prepare the opening balance sheet.

1. **Draft IFRS accounting policy manual** — Document the entity's IFRS accounting policies, including elections and exemptions.
2. **Prepare the opening IFRS balance sheet** — Recognise, derecognise, reclassify, and remeasure all items as required by IFRS. Record adjustments to retained earnings (or other equity).
3. **Implement dual reporting** — Run parallel local GAAP and IFRS reporting during the comparative period to build confidence and test processes.
4. **Configure systems and controls** — Implement system changes, new chart of accounts, IFRS-compliant subledgers, and internal controls over IFRS reporting.
5. **Train finance staff** — Conduct IFRS technical training tailored to the entity's specific difference areas and new processes.
6. **Engage auditors early** — Discuss the opening balance sheet, policy elections, and transition adjustments with external auditors to avoid surprises.

### Phase 3: Execution (Comparative Period to First IFRS Reporting Date)

**Objective:** Produce the first complete set of IFRS financial statements.

1. **Prepare comparative IFRS financial statements** — Compile the full-year comparative period financial statements under IFRS.
2. **Prepare IFRS 1 reconciliations** — Build the required reconciliations (see Section 8 below) from previous GAAP equity and profit or loss to IFRS.
3. **Draft first IFRS financial statements** — Prepare the complete financial statements for the first IFRS reporting period, including all required notes and IFRS 1 disclosures.
4. **Obtain audit sign-off** — Work with external auditors to complete the audit of the first IFRS financial statements, including the opening balance sheet and comparative period.
5. **Communicate to stakeholders** — Brief investors, analysts, lenders, regulators, and board members on the impact of the transition and key changes from prior reporting.

### Stakeholder Communication Plan

Stakeholder communication should be planned and executed across all three phases:

**Phase 1 — Assessment:**
- **Board and audit committee awareness** — Present the transition business case, expected timeline, and preliminary impact assessment to the board and audit committee so they can provide governance oversight from the outset.
- **Lender notification** — Notify lenders about the upcoming transition and discuss potential covenant implications. IFRS adjustments (e.g., IFRS 16 lease capitalisation increasing debt) may trigger covenant breaches; proactive renegotiation may be needed.
- **Auditor engagement** — Engage external auditors early to agree on the transition approach, IFRS 1 exemption elections, and key accounting policy choices before work begins.

**Phase 2 — Preparation:**
- **Internal communication to business units** — Business units will need to provide data that may not have been collected under previous GAAP (e.g., lease contract details, credit risk data for ECL models). Communicate requirements early and clearly.
- **Training sessions** — Run targeted training for finance staff and operational staff who provide underlying data (e.g., procurement teams for lease data, sales teams for IFRS 15 contract terms).
- **Progress updates to board** — Provide regular progress updates to the board and audit committee, including key decisions made, issues encountered, and quantitative impact updates.

**Phase 3 — Execution:**
- **Analyst and investor briefings** — Before publishing the first IFRS financial statements, brief analysts and investors on the expected impact. Explain key differences from previous GAAP results and provide pro-forma reconciliations where helpful.
- **Regulatory notifications** — If required by the relevant securities regulator or stock exchange, submit formal notification of the change in reporting framework and any required filings.
- **Press release considerations** — Consider whether a press release is appropriate to explain the transition impact, particularly if IFRS results differ materially from previous GAAP (e.g., significant changes to reported equity or profit).

### Dual Reporting Considerations

Parallel (dual) reporting — running both local GAAP and IFRS reporting simultaneously — is a critical component of the transition:

- **Duration:** The dual reporting period should typically last at least one full financial year (the comparative period). Some entities extend it to include one or two quarters before the comparative period begins, to test processes early.
- **Interim IFRS reports:** Consider preparing interim IFRS reports (quarterly or half-yearly) during the parallel run period even if not required for publication. This builds confidence in the IFRS reporting process and surfaces issues well before the annual deadline.
- **Handling differences during parallel runs:** Establish a formal process for investigating and documenting differences that surface during parallel reporting. Each difference should be traced to a specific IFRS adjustment, a policy difference, or a data error. Unresolved differences must be escalated to the transition steering committee.
- **Resource implications:** Dual reporting approximately doubles the reporting workload during the parallel period. Plan for additional temporary staff, extended close timelines, or reduced non-essential reporting to accommodate the additional burden. This resource strain is temporary but must be budgeted and managed.

---

## 7. IFRS 1 Exemption Decision Framework

IFRS 1 provides optional exemptions from full retrospective application for specific areas. The decision to elect or not should be deliberate and documented.

### Decision Factors

| Factor | Elect Exemption | Do Not Elect Exemption |
|---|---|---|
| **Cost of retrospective application** | High — historical data is unavailable or would require excessive effort to reconstruct | Low — historical records are complete and accessible |
| **Data availability** | Source data for retrospective application does not exist or is unreliable | Reliable data exists for the entire retrospective period |
| **Comparability** | Exemption provides a reasonable starting point; limited impact on trend analysis | Full retrospective application provides more meaningful comparatives |
| **Subsequent measurement complexity** | Exemption simplifies ongoing measurement (e.g., deemed cost avoids tracking historical IFRS depreciation) | Full retrospective values align better with ongoing IFRS measurement |
| **Stakeholder expectations** | Users of financial statements accept the exemption approach | Investors or regulators prefer full retrospective figures |

### Mandatory Exceptions (IFRS 1.14-17)

These are NOT optional — entities MUST apply them:

- **Estimates** (IFRS 1.14-15): Use estimates consistent with previous GAAP at the date of transition. Cannot use hindsight to change estimates, even if IFRS would have required different estimates.
- **Derecognition of financial assets/liabilities** (IFRS 1.B2-B3): Apply IFRS 9 derecognition rules prospectively from date of transition (or earlier chosen date).
- **Hedge accounting** (IFRS 1.B4-B6): Apply IFRS 9 hedge accounting from transition date; cannot retrospectively designate hedges.
- **Non-controlling interests** (IFRS 1.B7): Apply IFRS 10 requirements prospectively.
- **Classification and measurement of financial assets** (IFRS 1.B8-B8C): Assess based on facts at date of transition.
- **Embedded derivatives** (IFRS 1.B9): Assess based on conditions at date of transition or when terms last modified.
- **Government loans** (IFRS 1.B10-B12): Apply IFRS 9 and IAS 20 prospectively.

The estimates exception is particularly important: entities cannot use information that became available after the date of transition to improve estimates.

### Key Optional Exemptions

| Exemption Area | What It Permits | When to Consider Electing |
|---|---|---|
| **Business combinations (IFRS 1.C1-C5)** | Do not restate business combinations before the date of transition | Acquisitions occurred many years ago; purchase price allocation data unavailable |
| **Deemed cost for PP&E/intangibles (IFRS 1.D5-D8)** | Use fair value or previous GAAP revaluation as deemed cost at the date of transition | Historical IFRS cost cannot be reliably determined; assets have been in use for many years |
| **Cumulative translation differences (IFRS 1.D12-D13)** | Reset cumulative translation differences to zero at the date of transition | Reconstructing historical translation adjustments is impracticable |
| **Employee benefits (IFRS 1.D10-D11)** | Reset cumulative actuarial gains and losses to zero at the date of transition | Actuarial records for prior periods are incomplete |
| **Leases (IFRS 1.D9B)** | Measure lease liability at the date of transition rather than at lease inception | Large volume of leases; inception-date data unavailable |
| **Share-based payment (IFRS 1.D2-D3)** | Do not apply IFRS 2 to awards vested before the date of transition | Share-based payment data for historical grants is incomplete |
| **Borrowing costs (IFRS 1.D23)** | Apply IAS 23 prospectively from the date of transition | Historical capitalisation records under IFRS criteria do not exist |

### Documentation Requirement

For every exemption elected or not elected, document:

- The exemption reference (IFRS 1 paragraph)
- The rationale for electing or not electing
- The quantitative impact (or the reason full quantification was impracticable)
- Approval by the transition steering committee

This documentation supports audit evidence and regulatory review.

---

## 8. Reconciliation Checklist

IFRS 1.24-28 requires specific reconciliations in the first IFRS financial statements. Use this checklist to ensure completeness.

### Required Reconciliations

- [ ] **Equity reconciliation at the date of transition** — Reconcile previous GAAP equity to IFRS equity at the opening balance sheet date (e.g., 1 January 2025)
- [ ] **Equity reconciliation at the end of the latest previous GAAP period** — Reconcile previous GAAP equity to IFRS equity at the comparative period end (e.g., 31 December 2025)
- [ ] **Profit or loss reconciliation for the latest previous GAAP period** — Reconcile previous GAAP profit or loss to IFRS for the comparative year (e.g., FY2025)
- [ ] **Total comprehensive income reconciliation** — If the entity presented a statement of comprehensive income under previous GAAP, reconcile total comprehensive income

### Reconciliation Content

For each reconciliation, ensure the following:

- [ ] **Starting balance clearly stated** — Previous GAAP amount with reference to the audited local GAAP financial statements
- [ ] **Individual adjustments separately identified** — Each IFRS adjustment shown as a separate line item with a description (e.g., "Capitalisation of operating leases under IFRS 16", "ECL adjustment under IFRS 9")
- [ ] **Tax effects of adjustments** — Deferred tax impact of each transition adjustment shown (IAS 12 applied to IFRS carrying amounts)
- [ ] **Non-controlling interest impact** — Adjustments allocated between owners of the parent and NCI where applicable
- [ ] **Narrative explanation of material adjustments** — Sufficient detail for users to understand the nature and drivers of each significant adjustment
- [ ] **Cross-reference to accounting policies** — Each adjustment linked to the relevant IFRS accounting policy in the notes
- [ ] **Impairment losses recognised or reversed** — Any impairment recognised (or previous impairment reversed) on transition separately disclosed (IFRS 1.24(c))
- [ ] **Fair value as deemed cost** — Where fair value or revaluation was used as deemed cost, disclose the aggregate amount and adjustments (IFRS 1.30)
- [ ] **Reclassification adjustments** — Items that changed classification without changing measurement (e.g., from one financial instrument category to another) separately identified
- [ ] **Consistency verified** — Reconciliations are internally consistent (opening equity + P&L adjustments + OCI adjustments = closing equity)

> **Cross-reference:** Use the IFRS 1 disclosure checklist in `compliance-templates.md` to ensure all first-time adoption disclosures are complete.

---

## 9. Common Pitfalls and Lessons Learned

The following issues recur frequently in IFRS transition projects. Awareness of these pitfalls can help entities avoid delays, cost overruns, and audit complications.

1. **Underestimating lease data collection effort (IFRS 16)** — Gathering complete, accurate lease data (commencement dates, payment schedules, renewal options, discount rates) across all business units and jurisdictions is consistently the most time-consuming data collection exercise. Entities with hundreds or thousands of leases should begin data collection at the very start of Phase 1.

2. **Failing to engage auditors early on the opening balance sheet** — The opening IFRS balance sheet is audited as part of the first IFRS financial statements. Disagreements with auditors on accounting policy choices, exemption elections, or significant estimates discovered late in the process can force rework and delay publication. Engage auditors during Phase 1 and seek their input on key judgements before finalising the opening balance sheet.

3. **Not documenting IFRS 1 exemption elections and rationale** — Every exemption election (and decision not to elect) should be formally documented with the rationale, quantitative impact, and steering committee approval. Incomplete documentation creates audit issues and regulatory risk.

4. **Insufficient parallel reporting period** — Entities that skip or shorten the parallel (dual) reporting period frequently discover errors and process gaps too late to correct them without significant effort. A full year of parallel reporting is strongly recommended.

5. **Underestimating the deferred tax complexity** — The deferred tax impact of IFRS transition adjustments is often material and complex (see Section 4). Entities that treat deferred tax as a "clean-up" exercise at the end of the transition frequently find it is one of the largest single adjustments to opening retained earnings.

6. **Not training operational staff who provide underlying data** — Finance teams receive IFRS training, but operational staff (procurement, sales, HR, treasury) who provide the underlying data often do not. This leads to incomplete or incorrect data inputs, particularly for IFRS 16 lease data, IFRS 15 contract terms, and IFRS 9 credit risk information.

7. **Leaving disclosure preparation to the last minute** — IFRS disclosure requirements are significantly more extensive than many local GAAP frameworks. First-time adoption disclosures (IFRS 1 reconciliations, explanations of material adjustments, exemption elections) add further volume. Disclosure drafting should begin during Phase 2, not left to Phase 3.

---

## Quick Reference: Related Skill Files

| File | Use For |
|---|---|
| `workflows.md` | IFRS 1 first-time adoption step-by-step workflow |
| `compliance-templates.md` | Gap analysis template, disclosure checklists |
| `standards-reference.md` | Detailed standard-by-standard guidance (IFRS 9, 15, 16, IAS 19, 36, 37, 38, etc.) |

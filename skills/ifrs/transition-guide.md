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

- **1 January 2025 (date of transition):** Prepare an opening IFRS balance sheet. Recognise all assets and liabilities required by IFRS, derecognise items not permitted, reclassify as needed, and measure everything under IFRS. Adjustments go to retained earnings (or another equity category if appropriate). This opening statement of financial position is **presented** in the first IFRS financial statements as the third statement of financial position: IFRS 1 paragraph **21** requires at least three statements of financial position, two statements of profit or loss and other comprehensive income, two separate statements of profit or loss if presented, two statements of cash flows and two statements of changes in equity, together with related notes and comparative information for all statements presented.
- **31 December 2025 (comparative period end):** Present a full set of IFRS-compliant comparative financial statements for this period.
- **31 December 2026 (first IFRS reporting date):** Publish the first complete set of IFRS financial statements, including the IFRS 1 reconciliations and disclosures.

---

## 2A. Comparative Period Mechanics

### What must be presented (IFRS 1.21)

The first IFRS financial statements shall include **at least**:

- **three** statements of financial position;
- **two** statements of profit or loss and other comprehensive income;
- **two** separate statements of profit or loss, if presented;
- **two** statements of cash flows;
- **two** statements of changes in equity;

**and related notes, including comparative information for all statements presented.**

The third statement of financial position is the **opening IFRS statement of financial position at the date of transition**. This is why the date of transition is defined as the **beginning** of the earliest comparative period and not its end.

### Presenting more than one comparative year

The date of transition moves with the number of comparative periods presented. Where a securities regulator requires two comparative years — the SEC's three-year income statement requirement for domestic registrants is the common case — the date of transition moves **back a further year**, and so does every exemption measured "at the date of transition": deemed cost, the lease liability under D9B, the CTD reset, and the FVTPL/FVOCI designations under D19–D19C.

**Decide the number of comparative periods before electing any exemption.** Changing it afterwards invalidates every transition-date measurement.

### Non-IFRS comparatives and historical summaries (IFRS 1.22)

Historical summaries of selected data for periods **before** the earliest full IFRS comparative period **need not** comply with IFRS recognition and measurement. Previous-GAAP comparative information may also be presented alongside the IFRS comparatives. In either case the entity **shall**:

- (a) **label the previous GAAP information prominently** as not prepared in accordance with IFRS; and
- (b) **disclose the nature of the main adjustments** that would make it comply. **Quantification is not required.**

This is the mechanism for the five-year summary in an annual report or a listing document, and it is materially cheaper than restating those years.

### Interaction with IAS 34 in the year of adoption (IFRS 1.32–33)

Where the entity presents an IAS 34 interim financial report for **part of the period covered by its first IFRS financial statements**, IFRS 1 applies to that interim report as well (para 2(b)), and the entity must satisfy IAS 34 **plus** the following:

| Requirement | Ref | Detail |
|---|---|---|
| **IFRS 18 headings and subtotals in condensed interims** | 32(za) | The entity shall present **each heading it expects to use in applying IFRS 18** and the subtotals required by **IFRS 18.69–74**, **notwithstanding IAS 34.10**. The normal IAS 34.10 condensed-presentation relief applies **only after** the first IFRS annual financial statements prepared under IFRS 18 have been issued. |
| **Interim equity reconciliation** | 32(a)(i) | Where an interim report was presented for the **comparable interim period of the immediately preceding year**, reconcile previous-GAAP equity at the end of that comparable interim period to IFRS equity at that date. |
| **Interim total comprehensive income reconciliation** | 32(a)(ii) | Reconcile to IFRS total comprehensive income for that comparable interim period, **both current-period and year-to-date**. The starting point is previous-GAAP total comprehensive income for the same period, or previous-GAAP profit or loss if no such total was reported. |
| **Annual reconciliations in the first interim report** | 32(b) | The **first** IAS 34 interim report within the first IFRS reporting period must **also** include the full IFRS 1.24(a) and (b) reconciliations, supplemented per paragraphs 25 and 26 — **or a cross-reference to another published document containing them**. |
| **Changes to policies or exemption use** | 32(c), 27A | If the entity changes its accounting policies or its use of the IFRS 1 exemptions during the first IFRS reporting period, it shall explain the change in **each** such interim report and **update** the reconciliations. Paragraph 27A requires the same explanation between the first IFRS interim report and the first IFRS annual financial statements. |
| **Information material to the interim period** | 33 | IAS 34's minimum disclosures assume users have the most recent **annual** financial statements. Where the entity's most recent previous-GAAP annual financial statements did **not** disclose information material to understanding the current interim period, the interim report must disclose it or cross-refer to a document that does. |

**Practical consequences.** Three points follow that reshape the transition timetable:

1. The **first interim report is the first public IFRS deliverable**, not the annual financial statements. The equity and TCI reconciliations, the exemption schedule and the IFRS 18 heading structure must all be finished by the first interim reporting date — typically **six months earlier** than most project plans assume.
2. Interim results **re-phase** on transition even where the annual result does not, because IAS 34 takes the **discrete** view of an interim period while several national frameworks (and US GAAP) take the **integral** view — see §3A row 74. Model the quarterly or half-yearly phasing and brief analysts **before** publication.
3. Comparative interim reconciliations are only required where a comparable interim report was actually presented in the prior year. An entity that did not report interim results under previous GAAP has a lighter obligation — but paragraph 32(b) still applies.

### Where the comparative period may be shorter than 12 months

One case only: **severe hyperinflation**. Under paragraph **D30**, where the functional currency normalisation date falls within a 12-month comparative period, the comparative period **may be shorter than 12 months**, provided a complete set of financial statements as required by **IFRS 18.10** is presented for that shorter period.

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

**Transition action:** Restate open contracts at the date of transition. Consider the IFRS 1 optional exemption for completed contracts (D35 — contracts completed before the earliest period presented need not be restated).

### 3.2 Leases — IFRS 16

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Lessee model** | Single on-balance-sheet model: recognise right-of-use asset and lease liability for virtually all leases | Operating leases kept off balance sheet; only finance/capital leases on balance sheet |
| **Measurement** | Initial measurement at present value of lease payments; subsequent depreciation of ROU asset and interest on liability | Operating lease expense recognised on straight-line basis with no balance sheet impact |
| **Short-term / low-value** | Optional exemptions for leases under 12 months or of low-value underlying assets | No equivalent distinction needed when operating leases are off balance sheet |
| **Sale and leaseback** | Apply IFRS 15 to determine whether transfer is a sale; if so, measure ROU asset proportionally | May recognise full gain on sale; leaseback treated as new operating lease |

**Transition action:** Inventory all lease contracts. Quantify the balance sheet gross-up. IFRS 1 permits measuring the lease liability at transition date (rather than at lease inception) as a practical expedient (D9B), together with the five D9D expedients — see §7.

### 3.3 Financial Instruments — IFRS 9

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Classification** | Three categories based on business model and contractual cash flow characteristics: amortised cost, FVOCI, FVTPL | Four or more categories (held-to-maturity, available-for-sale, loans and receivables, FVTPL) |
| **Impairment** | Expected credit loss (ECL) model — forward-looking, three-stage approach | Incurred loss model — impairment recognised only after a loss event occurs |
| **Hedge accounting** | Simplified qualifying criteria; more hedging strategies eligible; risk components of non-financial items hedgeable | More restrictive bright-line effectiveness tests (e.g., 80-125% corridor) |
| **Equity investments** | Irrevocable FVOCI election (no recycling to P&L); otherwise FVTPL | May permit cost method for unquoted equities or recycling of AFS gains |

**Transition action:** Reclassify financial assets based on IFRS 9 criteria. Calculate ECL allowances at the date of transition. Review hedge documentation for IFRS 9 compliance — **hedge relationships must be designated and documented on or before the date of transition**; mandatory exception B4–B6 prohibits retrospective designation and there is no cure.

### 3.4 Employee Benefits — IAS 19

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Defined benefit measurement** | Project unit credit method; remeasurements (actuarial gains/losses) in OCI with no recycling | Corridor approach permitted (defer and amortise actuarial gains/losses); or immediate P&L recognition |
| **Discount rate** | High-quality corporate bonds (or government bonds where no deep market exists) | May use different benchmark rates |
| **Past service cost** | Recognise immediately in P&L when plan amendment occurs | Amortise over remaining service period |
| **Multi-employer plans** | Account as defined contribution unless sufficient information for defined benefit accounting | Treatment varies; some frameworks allow defined contribution accounting in all cases |

**Transition action:** Obtain actuarial valuations at the date of transition. Recognise the full net defined benefit liability or asset measured under the projected unit credit method. **There is no IFRS 1 exemption** — paragraphs D10–D11 were deleted, so any previous-GAAP corridor or deferred actuarial balance is recognised in full against opening retained earnings. Obtain the valuation early: it is a long-lead-time deliverable and one of the largest single transition adjustments for a mature defined benefit sponsor. See "Exemptions that no longer exist" in §7.

### 3.5 Impairment of Non-Financial Assets — IAS 36

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Trigger** | Impairment test when indicators exist; annual for goodwill and indefinite-life intangibles | Some frameworks require annual testing for all long-lived assets or have different trigger indicators |
| **Recoverable amount** | Higher of fair value less costs of disposal and value in use (discounted cash flows) | Undiscounted cash flow test as a first screen; impairment measured differently |
| **Cash-generating units** | Test at CGU level (smallest group generating independent cash inflows) | May test at a different level of aggregation (e.g., reporting unit, asset group) |
| **Reversal** | Reversal required when conditions change (except for goodwill impairment — never reversed) | Some frameworks prohibit reversal of any impairment |

**Transition action:** Identify CGUs. Test goodwill and indefinite-life intangibles at the date of transition. Consider the IFRS 1 deemed cost exemption for assets where historical IFRS cost would be difficult to reconstruct. Note that several exemption elections trigger a **mandatory** transition-date IAS 36 test regardless of indicators — see §5A step 10.

### 3.6 Property, Plant and Equipment — IAS 16

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Component depreciation** | Each significant component of an asset depreciated separately | Single useful life for the whole asset; no component accounting |
| **Revaluation model** | Permitted as an accounting policy (class-by-class election) | Revaluation prohibited in some frameworks; or permitted but with different mechanics |
| **Residual value** | Review at least annually; based on current prices | Set at acquisition and rarely updated |
| **Borrowing costs** | IAS 23 requires capitalisation for qualifying assets | May be expensed or capitalised at entity's option |
| **Decommissioning** | Include in cost with corresponding provision (IAS 37 / IFRIC 1) | Often not recognised until expenditure incurred |

**Transition action:** Componentise major assets. Reassess useful lives and residual values. Elect fair value or previous-GAAP revaluation as deemed cost under IFRS 1 (D5–D8B) if full retrospective cost data is unavailable.

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
| **Recognition threshold** | "Probable" means more likely than not (>50%) | "Probable" may mean a materially higher threshold |
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

**Transition action:** Reassess control conclusions for all investees. Identify structured entities. Consider the IFRS 1 exemption for business combinations that occurred before the date of transition (C1–C5), remembering the C1 ratchet described in §7.

### 3.10 Presentation and Disclosure — IAS 1 / IFRS 18

> **Which standard applies:** **IFRS 18** supersedes IAS 1 for annual reporting periods beginning on or after **1 January 2027** (IFRS 18.C1, C8); earlier application is permitted. Because IFRS 1 paragraph 8 requires the IFRSs effective at the **end of the first IFRS reporting period** to be applied to the opening statement of financial position and all periods presented, an entity whose first IFRS reporting date is **31 December 2027 or later must build to IFRS 18 from the outset**. IFRS 1 has already been conformed — paragraph 32(za) requires IFRS 18 headings and subtotals in condensed interim reports, and paragraphs 21, 22, 24(a)(ii), 33 and D30 cross-refer to IFRS 18. See §10. The IAS 1 content below remains correct for first IFRS reporting dates before 1 January 2027.

| Aspect | IFRS Requirement | Common Local GAAP Difference |
|---|---|---|
| **Complete set of statements** | Statement of financial position, profit or loss and OCI, changes in equity, cash flows, and notes | Some frameworks do not require a statement of changes in equity or OCI as a separate statement |
| **OCI classification** | Items that will and will not be reclassified to P&L must be presented separately | OCI may not be required or may have different classification rules |
| **Current/non-current distinction** | Required unless a liquidity-based presentation is more relevant | Some frameworks mandate a different ordering or do not require the distinction |
| **Significant judgements and estimates** | Disclose critical judgements and key sources of estimation uncertainty — IAS 1.122 and IAS 1.125–133 for periods before 1 January 2027; **IAS 8.27G and IAS 8.31A–31I** from 1 January 2027, when IFRS 18 supersedes IAS 1 and this content moves to IAS 8. A first-time adopter whose date of transition falls on or after that date applies the IAS 8 requirements and never applies IAS 1. | Disclosure requirements may be less specific |
| **Comparative information** | Minimum one year of comparative information; three balance sheets if retrospective restatement | One year typical but specific requirements vary |

**Transition action:** Redesign the chart of accounts and financial statement templates. Map local GAAP line items to IAS 1 presentation requirements — or, where the first IFRS reporting date is 31 December 2027 or later, directly to IFRS 18, avoiding two redesigns. Prepare IFRS-compliant note disclosures.

---

## 3A. US GAAP → IFRS Difference Matrix

Applies where previous GAAP is **US GAAP** — most commonly a US-domiciled group listing or being acquired abroad, a foreign private issuer moving off a US GAAP reporting package, or a US subsidiary preparing an IFRS group reporting pack. US GAAP and IFRS are **converged in more areas than not** — business combinations, revenue, fair value measurement, segment reporting and share-based payment are all substantially aligned — so the matrix below is deliberately restricted to differences that **change a number**.

> **Source and verification status of the US GAAP column — read before relying on any ASC reference.** The US GAAP column follows **EY, *US GAAP versus IFRS Accounting Standards — The basics*, January 2026** (analysis reflecting guidance finalised as at 30 June 2025), except the government-grants row, which follows **FASB ASU 2025-10** directly. The FASB Codification itself (`asc.fasb.org`) is registration-gated and could not be opened, so every **ASC reference in this matrix is source-verified through EY, not primary-verified against the Codification**. Treat ASC references as pointers to be confirmed against the Codification before they are relied on in a filing or a memo. The IFRS column carries its own citations, verified against the standards' own text.

> **Researched but not merged — deliberate gaps in this matrix.** Four points were researched and could not be verified to this file's evidence standard. They are flagged inline rather than stated, because an absent row is less useful to a preparer than a note saying where the gap is:
> - **US federal tax consequences of abandoning LIFO** (row 1) — a US tax-law question (LIFO conformity and any resulting change-of-method catch-up), not an accounting one. Not stated here; obtain a US tax specialist's opinion. This is the most consequential omission in the matrix.
> - **The ASC topic governing agriculture / biological assets** (row 13) — the substance (US GAAP has no fair-value model equivalent to IAS 41) follows from the EY comparison's silence; the topic number could not be verified and is not given.
> - **The ASC topic governing rate-regulated operations** (row 78) — same position; the IFRS side of that row is fully verified.
> - **The numeric probability convention behind US GAAP's "probable"** (row 30) — the *definition* and the fact that it is a higher threshold than IFRS are sourced; the percentage ranges quoted in US practice are convention, not standard text, and are not stated.

### Assets

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 1 | **Inventory — cost formula** | LIFO is permitted (ASC 330). A consistent formula across inventories similar in nature or use is not explicitly required. | **LIFO is prohibited.** FIFO or weighted average only, and the **same** formula must be used for all inventories of similar nature and use (**IAS 2.25**). | For a LIFO entity this is the single largest first-day adjustment. Releasing the LIFO reserve increases inventory and opening retained earnings. **The US federal tax consequences of abandoning LIFO for book purposes are a tax-law question and are deliberately not stated in this guide** (see the gap note above) — they can exceed the accounting benefit, so obtain a US tax specialist's assessment **before** committing to a transition date. |
| 2 | **Inventory — measurement** | Inventory other than LIFO/RIM at **lower of cost and NRV**. LIFO and RIM at **lower of cost or market**, where market is current replacement cost, capped at NRV and floored at NRV less a normal profit margin. | **Lower of cost and NRV under all permitted methods.** NRV = estimated selling price less estimated costs of completion and costs to make the sale (IAS 2 [para-unconfirmed]). | Eliminates the replacement-cost ceiling/floor mechanic. Recompute every LIFO/RIM pool on an NRV basis at the date of transition. |
| 3 | **Inventory — reversal of write-downs** | Write-downs create a **new cost basis** and cannot be reversed, except a recovery within the **same fiscal year**. | Reversal is **required**, limited to the original write-down, when the reasons for it no longer exist (**IAS 2.34**), with disclosure of the amount and the circumstances. | Pre-transition write-downs whose cause has reversed must be **reversed in the opening balance sheet**. Requires the write-down history and the current NRV — data many entities do not retain. |
| 4 | **Inventory — RIM permanent markdowns** | Permanent markdowns do **not** affect the gross margin used in RIM; they reduce carrying cost to NRV less a normal profit margin, which may be below both cost and NRV. | Permanent markdowns **do** affect the average gross margin used in RIM; carrying amount is reduced to the lower of cost and NRV. | Retailers only, but material for them. Rebuild the RIM calculation. |
| 5 | **Development costs** | **Expensed as incurred** unless another Topic applies. External-use software capitalised from technological feasibility (ASC 985-20); internal-use software capitalised in the application development stage (ASC 350-40). | **Capitalisation is mandatory** once the IAS 38 criteria are met (technical feasibility, intent and ability to complete and use or sell, probable future benefits, adequate resources, reliable measurement of cost). **No separate software guidance.** | Two-way. R&D-intensive entities must build a **project-level cost capture** capability retrospectively, then defend the date each project crossed the criteria. Conversely, US software capitalisation thresholds do not map cleanly onto IAS 38 and some capitalised balances will fail. |
| 6 | **Cloud computing implementation costs** | A customer in a hosting arrangement that is a service contract applies **ASC 350-40** to decide whether to capitalise implementation costs. | **IFRS does not address** customer accounting for cloud arrangements or their implementation costs; judgement, applying several standards. | Expect a **write-off** of US-capitalised SaaS implementation costs. Sizeable for entities mid-ERP programme. See also the IFRIC agenda decisions in this area. |
| 7 | **Advertising costs** | Expensed as incurred **or** when the advertising first takes place — a **policy choice** — with limited exceptions. | **Expensed as incurred.** A prepayment is an asset only where payment precedes access to the goods or receipt of the services. | Small, but it removes an accounting policy and affects interim phasing. |
| 8 | **Revaluation of PP&E** | **Not permitted.** | **Permitted** as a policy election for an **entire class**, requiring regular revaluation to fair value (IAS 16 [para-unconfirmed]). | Not a required change — but the **IFRS 1 D5/D6 deemed cost election** is the practical equivalent for a US GAAP adopter and is normally where the value is. See §7. |
| 9 | **Component depreciation** | **Permitted but uncommon.** | **Required** where components of an asset have differing patterns of benefit (IAS 16 [para-unconfirmed]). | A genuine fixed-asset-register rebuild. Componentise before the date of transition; retrofitting it later means restating the comparative depreciation charge. Pairs badly with a large historic asset base — consider deemed cost. |
| 10 | **Major overhauls and inspections** | No general guidance outside **ASC 908** (airlines); repair and maintenance costs generally **expensed as incurred**. | Costs replacing a previously identified component, or a **major inspection**, are **capitalised** where use over more than one period is expected, benefits are probable and cost is reliably measurable; the carrying amount of the replaced part or prior inspection is **written off**. | Heavy for shipping, aviation, rail, energy and process manufacturing. Requires a component register that isolates inspection/overhaul cost — data rarely captured under US GAAP. |
| 11 | **Borrowing costs — measurement** | Eligible costs **exclude exchange rate differences**. For asset-specific borrowings, capitalise **average accumulated expenditures × borrowing rate**; interest earned on borrowed funds generally **cannot** offset interest cost. | Eligible costs **include** FX differences from foreign currency borrowings to the extent they are an adjustment to interest cost. For asset-specific borrowings, capitalise **actual** borrowing costs **less investment income earned on those borrowings** (**IAS 23.8**). | Recompute capitalised interest on every open qualifying asset. The investment-income offset reduces the capitalised amount for entities that draw down debt ahead of spend — common in project finance. The **IFRS 1 D23** exemption removes the historical recomputation but **not** the requirement to apply IAS 23 to assets already under construction. |
| 12 | **Investment property** | **Not separately defined**; accounted for as held-and-used or held-for-sale like other PP&E. | **IAS 40** defines it as property held to earn rent or for capital appreciation, and may include a lessee's ROU assets. Policy election of **cost or fair value model**, applied to all investment property (**IAS 40.30**). Under the fair value model there is **no depreciation** and fair value changes go to **profit or loss**. IFRS 16 requires a lessee to apply the IAS 40 fair value model to a leased property meeting the definition where that model is elected. | A structural decision, not a mechanical one. The fair value model puts property valuation movements **through P&L**, which changes earnings volatility and covenant behaviour. Decide the policy before the date of transition; the IFRS 1 D7(a) deemed cost extension is available **only if the cost model is chosen**. |
| 13 | **Biological assets** | No general model; agricultural assets generally at **cost** subject to industry guidance `[ASC-para-unconfirmed]` (the governing ASC topic could not be verified — see the gap note above). | **IAS 41**: biological assets at **fair value less costs to sell**, with gains and losses on initial recognition and on remeasurement in **profit or loss** (**IAS 41.26**). Agricultural produce at fair value less costs to sell **at the point of harvest**, which becomes its IAS 2 cost (**IAS 41.13**). Rebuttable presumption that fair value is reliably measurable, rebuttable **only on initial recognition** (**IAS 41.30**). Bearer plants are within IAS 16, not IAS 41. | Agriculture, forestry, aquaculture and plantation entities only, but transformative for them: a recurring, unrealised, non-cash fair value movement in operating results, plus an annual valuation obligation. |

### Impairment

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 14 | **Impairment of long-lived assets — method** | **Two-step.** A recoverability test first: carrying amount compared with the sum of **undiscounted** future cash flows using entity-specific assumptions. Only if it fails is a loss computed. | **One-step.** Where an indicator exists, compute the impairment directly (IAS 36 [para-unconfirmed]). | The undiscounted screen is a substantial cushion. Removing it means assets that never failed the US test may be impaired at the date of transition. **Model this early** — it is the difference most likely to produce an unexpected opening equity hit. |
| 15 | **Impairment of long-lived assets — measurement** | Loss = carrying amount less **fair value** using market-participant assumptions (ASC 820). | Loss = carrying amount less **recoverable amount**, being the **higher of** fair value less costs of disposal and **value in use** (entity-specific discounted cash flows) (IAS 36 [para-unconfirmed]). | IFRS gives the entity a **second chance** through value in use. Requires a VIU model, a pre-tax discount rate and a documented cash flow projection — new infrastructure for most US GAAP preparers. |
| 16 | **Goodwill — unit of account** | Assigned to a **reporting unit**: an operating segment (ASC 280) **or one level below** (a component). | Allocated to a **CGU or group of CGUs** at the **lowest level at which goodwill is monitored internally**, and **no larger than an operating segment before aggregation** (IFRS 8). | The IFRS ceiling and the US floor are different constraints. Re-map goodwill at the date of transition; a finer allocation removes the cross-subsidy that shielded weak units under US GAAP. |
| 17 | **Goodwill — test method** | **Qualitative ("Step 0") assessment permitted.** Quantitative test compares the reporting unit's **carrying amount with its fair value**; loss capped at goodwill allocated. | **Qualitative assessment is not permitted.** Annual quantitative one-step test comparing the CGU's carrying amount **including goodwill** with its **recoverable amount**; loss allocated first to goodwill, then **pro rata** to other assets of the CGU subject to limits. | An annual quantitative impairment model becomes **mandatory**, every year, for every CGU carrying goodwill. Budget the valuation effort as a permanent run cost, not a transition cost. Note the pro rata write-down of other CGU assets has no US GAAP analogue. |
| 18 | **Indefinite-lived intangibles — test** | Qualitative assessment permitted; quantitative test compares **fair value** with carrying amount; assets tested individually unless essentially inseparable, and **may not** be combined with finite-lived intangibles or goodwill. | Qualitative assessment **not permitted**. Tested individually **or as part of the CGU** where the asset does not generate largely independent cash inflows. | The CGU-level fallback pulls indefinite-lived intangibles into the goodwill test population. Re-scope the impairment model. |
| 19 | **Reversal of impairment** | **Prohibited** (except assets held for sale). | **Prohibited for goodwill.** For other assets, reversal indicators must be **reviewed at each reporting date** and the loss reversed up to the newly estimated recoverable amount, capped at the carrying amount that would have existed net of depreciation had no impairment been recognised. | A **new recurring control**. Every pre-transition impairment (other than goodwill) must be revisited at the date of transition and at every reporting date thereafter. Retain the original impairment models — you now need them permanently. |

### Financial instruments

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 20 | **Classification — debt instruments** | Driven largely by **legal form** (security vs loan) and **management intent**: HTM at amortised cost; Trading at FV-NI; AFS at FV-OCI. Loans and receivables held-for-investment at amortised cost or, if held for sale, at lower of amortised cost or fair value. | Legal form is irrelevant. Classification is driven by the **business model** and the **SPPI** contractual cash flow characteristics test: amortised cost, FVOCI, or FVTPL. Assets failing SPPI go to **FVTPL** regardless of intent (IFRS 9 [para-unconfirmed]). | Full reclassification exercise. The **AFS category disappears**. SPPI failures — contractually linked instruments, non-recourse features, leverage, non-genuine terms, and now ESG-linked features under the 2024 amendments — force FVTPL and introduce P&L volatility that did not exist. Mandatory exception **B8** fixes the assessment date at the date of transition. |
| 21 | **Classification — equity investments** | **FV-NI**, with a **measurement alternative** (cost less impairment, adjusted for observable price changes) for investments without readily determinable fair values. | **FVTPL** by default. An **irrevocable FVOCI election** is available for non-derivative equity instruments not held for trading; gains and losses in OCI are **never recycled** to P&L, though the cumulative amount may be transferred within equity. **No measurement alternative.** | Every cost-basis holding must be **fair valued** at the date of transition — often requiring valuations of private holdings that have never been valued. The **D19B** exemption gives a one-time window to make the FVOCI election on transition-date facts; miss it and the election is unavailable for existing holdings. |
| 22 | **Impairment of financial assets — model** | **CECL** (ASC 326): a **lifetime** expected credit loss recognised on **initial recognition** for assets in scope. Pool-based; a zero-loss estimate is appropriate only in limited circumstances. Write-offs when all or part is deemed **uncollectible**; the allowance **incorporates expected recoveries**. | **Three-stage ECL**. Stage 1: **12-month** ECL, applying while there has been no significant increase in credit risk. Stages 2 and 3: **lifetime** ECL. In Stage 2 interest income is on the **gross** carrying amount; in Stage 3, after a credit event, on the **amortised cost** (net of allowance). Write-offs when there is **no reasonable expectation of recovery**; IFRS gives **no guidance on subsequent recoveries**. | This is a **model rebuild, not a remeasurement**. CECL has no staging concept and no 12-month bucket; IFRS 9 has no expected-recovery component and shifts interest recognition in Stage 3. Neither model's output can be mapped to the other. Requires SICR criteria, stage-transfer logic, a Stage 3 interest engine, and forward-looking scenario weights. Mandatory exception **B8D–B8G** applies, including the **penalty default at B8G**: where determining SICR at the date of transition would require undue cost or effort, **lifetime ECL applies for the life of the instrument**. |
| 23 | **Impairment — FVOCI debt instruments** | Credit-related impairment recognised as an **allowance** capped at the excess of amortised cost over fair value; non-credit impairment stays in OCI. Intent-to-sell triggers full write-down to fair value through earnings. | Single ECL model. ECLs **do not reduce the carrying amount** — which remains fair value — but are recognised as an **accumulated impairment amount within OCI** with a corresponding **charge to profit or loss**. Cumulative OCI is **recycled** to P&L on derecognition. | Changes both the P&L charge and the OCI mechanics. Note the asymmetry with equity FVOCI (row 21), where nothing recycles. |
| 24 | **Impairment — equity instruments** | Generally not tested (measured at FV-NI); the measurement alternative is **qualitatively assessed** each period and written down to fair value if impaired. | **No impairment model for equity instruments at all** — they are at FVTPL or FVOCI. | Removes an assessment. Any US impairment loss on a cost-basis holding is subsumed into the transition-date fair value. |
| 25 | **Compound (hybrid) instruments** | Convertible debt is generally **not split** into debt and equity unless specific requirements are met; may be bifurcated into debt and derivative components. | **Split accounting is required**: liability and equity components, or a derivative component measured at fair value (IAS 32 [para-unconfirmed]). | Convertible bond issuers must **re-split every instrument at inception** and rebuild the effective interest amortisation. The **IFRS 1 D18** exemption applies **only** where the liability component is no longer outstanding at the date of transition — for live convertibles there is **no relief**. |
| 26 | **Derecognition of financial assets** | Control-based: **legal isolation**, transferee's right to pledge or exchange, and no effective control retained. Partial derecognition only for a **participating interest**. | **Mixed model**: risks and rewards first; control assessed **only if** that test is inconclusive. Control is surrendered if the transferee has the **practical ability to unilaterally sell** without restriction. **No legal isolation test.** Partial derecognition permitted for specifically identified or pro rata cash flows. | Securitisations, factoring and receivables-purchase programmes can flip on or off balance sheet. Mandatory exception **B2** makes this **prospective** — pre-transition derecognitions stand — which is a substantial relief. The **B3** retrospective option requires contemporaneous data and is rarely available. |
| 27 | **Hedge effectiveness** | Relationship must be **"highly effective"**; prospective **and retrospective** assessments at least quarterly. No requirement to separately measure and recognise ineffectiveness for highly effective cash flow and net investment hedges. **Shortcut method permitted** for interest rate swaps hedging recognised debt. | Requires an **economic relationship**, that value changes are **not dominated by credit risk**, and a **hedge ratio** consistent with actual risk management. **Prospective assessment only**, at each annual/interim reporting date or on a significant change. **Ineffectiveness is measured and recognised in P&L each period** (for cash flow and net investment hedges, limited to overhedges). **No shortcut method.** | The shortcut method's removal forces full measurement and P&L recognition of ineffectiveness on swap portfolios that previously reported none. Mandatory exception **B4–B6**: **no retrospective designation**. Every hedge relationship must be **documented afresh on or before the date of transition** — this is a hard deadline with no cure, and it is the single most common transition failure in treasury. |
| 28 | **Hedging risk components** | Permitted for financial and non-financial items, but hedgeable interest components are confined to **defined benchmark rates** (fixed-rate) and **contractually specified rates** (variable-rate). For forecast purchases/sales of a non-financial asset: FX risk, the entire price, or a **contractually specified** component. | Permitted for financial and non-financial items where the component is **separately identifiable and reliably measurable** — a broader test that does **not** require contractual specification. | IFRS **widens** eligibility. Commodity and energy hedgers can designate market-observable components (e.g. a benchmark crude leg within a refined product price) that ASC 815 would not accept. A rare case where transition improves the accounting — but only if designated in time. |
| 29 | **Excluded hedge components** | Initial value of an excluded component recognised in earnings on a **systematic and rational** basis; differences deferred in AOCI. **Policy election** to recognise fair value changes immediately in earnings. | Fair value changes of excluded components are **deferred in OCI** and reclassified based on the nature of the hedged item (transaction-related or time-period-related). **No immediate-earnings election.** | Removes a policy choice and changes the phasing of option time value and FX basis spread. |

### Liabilities, provisions and income taxes

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 30 | **Provisions — recognition threshold** | A loss must be **"probable"**, defined as *"the future event or events are **likely** to occur"* — in practice a threshold materially higher than more-likely-than-not. (The percentage conventions quoted in US practice are not standard text and are not stated here.) | **"Probable"** for IAS 37 purposes means **"more likely than not"** — i.e. **>50%**. Explicitly **a lower threshold than US GAAP**. | Systematically **more provisions** under IFRS. Re-run the entire litigation, warranty, environmental and regulatory contingency population against the 50% threshold at the date of transition. Frequently produces a material opening equity charge and requires fresh legal confirmations. |
| 31 | **Provisions — discounting** | Discounting permitted only where amount and timing are **fixed or reliably determinable** (e.g. ASC 410-30 environmental) or the obligation is measured at fair value (e.g. ASC 410-20 AROs). | Provisions are recorded at the amount to settle or transfer, **taking account of the time value of money if material**, using a **pre-tax rate reflecting current market assessments** and risks specific to the liability not already in the cash flows. Unwinding is **interest expense**. | Long-dated decommissioning, restoration, environmental and self-insurance provisions must be **discounted**, reducing the liability at transition but creating a **recurring finance charge** that shifts cost below the operating line. |
| 32 | **Provisions — range of outcomes** | Where no amount in a range is a better estimate, accrue the **minimum**. | **Best estimate.** For a large population (e.g. warranties), typically the **expected value**; the **midpoint** where any point in a continuous range is equally likely; for a single obligation, often the most likely outcome, but other outcomes must still be considered. | Systematically **higher** provisions where US practice defaulted to the low end of a range. |
| 33 | **Onerous contracts** | Losses on executory contracts generally **not permitted** except in a restructuring/exit activity, a business combination, or other specified transactions. | **IAS 37 requires** a provision when a contract is onerous — unavoidable costs exceed expected economic benefits — measured at the **least net cost of exiting**: the lower of the cost of fulfilling and any penalty for failure to fulfil. | A **new liability class** with no US GAAP equivalent. Sweep the contract population — long-term supply, take-or-pay, outsourcing, IT, property (outside IFRS 16) — at the date of transition. Watch the November 2024 IASB ED *Provisions — Targeted Improvements* for change. |
| 34 | **Exit or disposal cost obligations** | Under **ASC 420**, each cost type is assessed separately. One-time involuntary termination benefits recognised **over the future service period** (or immediately if no service is required after communication). Contract termination costs at **fair value** when incurred. | Once there is a legal or **constructive** obligation for a detailed exit plan, the general IAS 37 requirements apply. Costs are typically recognised **earlier** because IAS 37 focuses on the **plan as a whole** rather than its component costs. | Restructurings recognised earlier and in larger single amounts. Restructurings announced but not fully accrued before the date of transition need reassessment. |
| 35 | **Income taxes — DTA recognition** | DTAs recognised **in full**, then reduced by a separately recognised **valuation allowance** to the amount more likely than not to be realised. | DTAs recognised **only to the extent recovery is probable** (more likely than not). **No separate valuation allowance** is presented (**IAS 12.24**). | Same economic threshold, different presentation and disclosure. Gross DTA and valuation allowance disclosures disappear; the tax note is rebuilt. Note also the **B14** override forcing deferred tax on ROU assets, lease liabilities and decommissioning items. |
| 36 | **Income taxes — measurement rate** | **Enacted** rates at the balance sheet date only. | Enacted **or "substantively enacted"** rates at the balance sheet date (**IAS 12.46** for current tax, **IAS 12.47** for deferred tax). | Timing difference for jurisdictions where legislation is passed but not formally enacted at year end — notably the UK. Can move a rate change one reporting period earlier. |
| 37 | **Income taxes — intra-entity transfers of assets** | Tax paid on intercompany **inventory** profits is **deferred in consolidation** (a prepaid asset), and recognising deferred tax on the resulting step-up in tax basis is **prohibited**; the effect is recognised on sale outside the group. For assets **other than inventory**, both current and deferred effects are recognised **in the period of transfer** (ASC 740). | **IAS 12 requires** tax paid on intercompany profits to be recognised as **tax expense as incurred**, and requires **deferred tax on temporary differences between the tax bases of assets transferred** between entities or tax jurisdictions that remain within the group. | A real difference for groups with active IP or inventory migration. IFRS recognises deferred tax on the **buyer's** stepped-up basis, which US GAAP forbids for inventory. Requires transfer-level data by legal entity and jurisdiction — often not held centrally. |
| 38 | **Income taxes — uncertain tax positions** | **ASC 740-10-25** two-step: recognise when **more likely than not** to be sustained on technical merits, then measure at the **largest amount >50% likely** of being realised on settlement. Unit of account based on how the return position is prepared and supported. Detection risk **not** considered. | **IFRIC 23**: if it is **probable** the authority will accept the treatment, follow the treatment used or planned in the filing. If not probable, reflect the uncertainty using **either the expected value or the most likely amount**, whichever better predicts resolution. Treatments may be assessed separately or together on the same "better predicts" basis. Detection risk **not** considered. | Same recognition threshold, **different measurement**. The US "largest amount >50% likely" is a cumulative-probability construct with no IFRIC 23 equivalent; the expected-value option can produce a materially different liability. Rebuild the UTP inventory position by position. |
| 39 | **Income taxes — initial recognition exemption** | Generally **no** initial recognition exemption. Deferred tax is recognised on temporary differences arising on initial recognition of an acquired asset or liability; where consideration differs from tax basis outside a business combination, a **simultaneous equation** allocates between asset and deferred tax. | **Initial recognition exemption**: no deferred tax where (1) the item did not arise from a business combination, (2) at the time of the transaction it affects **neither accounting nor taxable profit**, and (3) it does not give rise to **equal** taxable and deductible temporary differences. | IFRS **removes** deferred tax the US model records — but note the (3) condition and the **B14** carve-out mean the exemption does **not** shelter leases or decommissioning. Do not assume the exemption applies broadly. |
| 40 | **Income taxes — outside basis differences** | No recognition for an investment in a **foreign** subsidiary or foreign corporate joint venture that is **essentially permanent in duration**, unless reversal becomes apparent. A DTL **is** recognised for a **domestic** subsidiary unless recovery can be tax-free and that means is expected. | No recognition where the reporting entity **controls the timing** of reversal **and** it is **probable** the difference will **not** reverse in the foreseeable future — with **no domestic/foreign distinction**. | The IFRS test is control-plus-intention rather than permanence-plus-domicile. Groups relying on the US domestic/foreign split must re-evidence control over distribution timing, subsidiary by subsidiary, including through shareholder agreements and local law constraints. |
| 41 | **Government grants** | Historically **no guidance** for business entities; entities analogised to **IAS 20**, ASC 450 or ASC 958-605. **ASU 2025-10, *Government Grants (Topic 832)*** (December 2025) creates guidance **based on IAS 20** with targeted improvements — effective for PBEs for annual periods beginning after **15 December 2028** (others: after 15 December 2029), early adoption permitted. | **IAS 20**: no recognition until there is **reasonable assurance** that conditions will be complied with and the grant will be received (**IAS 20.7**); recognition in profit or loss **on a systematic basis over the periods in which the related costs are expensed** (**IAS 20.12**); asset-related grants presented **either as deferred income or as a deduction from the asset's carrying amount** (**IAS 20.24**). | Until Topic 832 is adopted, US practice is **diverse** — establish what the entity actually did before mapping. Where it already analogised to IAS 20, the difference is presentational. Note the two IAS 20 presentation options materially change gross PP&E and the depreciation line. |
| 42 | **Hyperinflation** | **ASC 830**: local functional currency financial statements are **remeasured as if the functional currency were the reporting currency** (the US dollar for a US parent), with exchange differences **in income**. | **IAS 29**: the functional currency is **maintained**; amounts not already at the current period-end rate (**current and prior period**) are **indexed using a general price index**, with the resulting effect in income, and are then translated at the **closing rate**. | Fundamentally different mechanics for the same economics. Requires a general price index series for the whole comparative period and a restatement engine. Also note **Amendments to IAS 21: Translation to a Hyperinflationary Presentation Currency** — issued 13 November 2025, effective 1 January 2027, **not yet EU- or UK-adopted at 28 August 2026** — which sits alongside this. |

### Group accounting and business combinations

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 43 | **Consolidation model** | **Two models.** All entities are first tested as potential **VIEs** (power and benefits); if not a VIE, the **Voting Model** applies. Potential voting rights generally **not** included in either. **De facto control is not considered.** | **A single control model** for all entities including structured entities: power, exposure to variable returns, and the ability to use power to affect returns. **Potential voting rights are considered.** **De facto control is considered.** | Two-way, and the highest-risk judgement area. **De facto control** can pull in investees held below 50% where remaining holdings are dispersed — a concept with **no US GAAP analogue**. Conversely, VIEs consolidated on a benefits analysis may fall out. Re-perform the control assessment for **every** investee, not just the marginal ones. |
| 44 | **Uniform accounting policies** | **Not required** between parent and subsidiaries; not required between equity-method investor and investee provided the investee reports under US GAAP. | **Required** both for consolidated subsidiaries and for equity-method investees. | A group-wide policy alignment project, not an accounting entry. Affects every subsidiary ledger and every equity-accounted investee — and you can rarely compel an associate to change its policies, so an **adjustment layer** is needed. |
| 45 | **Reporting date alignment** | Differences of **up to three months** permitted; significant intervening events disclosed. | Same date **required**. Where impracticable, the subsidiary prepares **additional financial information** at the parent's date; if that is impracticable and the gap is **three months or less**, the subsidiary's statements are **adjusted** for significant transactions and events. | Subsidiaries on off-cycle year ends need either a close-date change or an adjustment process. A systems and calendar issue, not a measurement one. |
| 46 | **Investment company / investment entity parent** | A **non-investment-company parent retains** the investment company subsidiary's fair value accounting in the consolidated financial statements. | A parent of an investment entity **consolidates all entities it controls**, including those controlled through an investment entity subsidiary — it does **not** retain fair value accounting — unless the parent is itself an investment entity. | Directly opposite outcomes. Asset managers and holding structures with regulated fund subsidiaries face a **full consolidation build** where US GAAP required none. |
| 47 | **Joint arrangements** | Joint ventures generally equity-accounted, with a **fair value election** available. **Proportionate consolidation permitted** for unincorporated entities in certain construction and extractive industries and certain undivided interests. **ASC 805-60** requires newly formed joint ventures to apply a **new basis of accounting** at formation (fair value). | **Proportionate consolidation is prohibited, regardless of industry.** Joint arrangements are classified as **joint operations** (recognise the entity's share of assets, liabilities, revenues and expenses) or **joint ventures** (equity method). **IFRS does not address a joint venture's accounting on formation.** | Construction, oil and gas and mining entities using proportionate consolidation face a **material gross-up reversal** of revenue, assets and liabilities. Note the **IFRS 1 D31(b)** rider: moving from proportionate consolidation to the equity method requires a **mandatory IAS 36 impairment test** at the date of transition **regardless of indicators**, with any loss to retained earnings. |
| 48 | **Business combinations — NCI measurement** | NCI measured at **fair value**. | For NCI components that are present ownership interests entitling the holder to a proportionate share of net assets on liquidation: **fair value or the proportionate share of the acquiree's identifiable net assets**, elected **transaction by transaction**. All other components at fair value. | Only relevant to combinations the entity elects to restate under **IFRS 1 C1**. Where restating, the proportionate-share option avoids valuing NCI goodwill — usually the pragmatic choice. |
| 49 | **Business combinations — definition of a business** | The concentration **threshold test is mandatory**. | The concentration threshold test is **optional**, elected transaction by transaction. | Substantively converged; the IFRS option is a modest simplification. Affects whether a transaction is an asset acquisition or a business combination. |
| 50 | **Business combinations — measurement period adjustments** | Recognised **in the period determined**, including the earnings effect of amounts that would have been recorded in prior periods. | Recognised **retrospectively**; comparatives are revised, including prior-period income statement effects. | Affects any acquisition whose measurement period straddles the date of transition or the comparative period. IFRS requires the comparative to be **restated**, not caught up. |
| 51 | **Common control combinations** | Receiving entity records net assets at the transferor's **carrying amounts** (historical cost). | **Outside the scope of IFRS 3.** In practice a **policy election** between a US-GAAP-like predecessor/historical cost approach and the acquisition method (fair value) where the transaction has substance. | IFRS creates a policy choice where US GAAP prescribes an answer. Choose and document it **before** the date of transition; group reorganisations executed during the transition period are otherwise accounted for twice. |
| 52 | **Pushdown accounting** | An acquired entity **may elect** pushdown accounting in its separate financial statements; the election is **irrevocable**. | Not addressed. The general view is that the **IAS 8 hierarchy may not be used** to import it, because pushdown would recognise internally generated goodwill and intangibles at subsidiary level, conflicting with IAS 38. | Where US subsidiaries pushed down acquisition accounting, those separate financial statements must be **unwound** to pre-pushdown carrying amounts on transition. |

### Employee benefits and share-based payment

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 53 | **Defined benefit — actuarial method** | **Projected unit credit or traditional unit credit**, depending on the plan's benefit formula. | **Projected unit credit in all cases.** | New actuarial valuations at the date of transition for any plan on the traditional unit credit method. |
| 54 | **Defined benefit — return on plan assets** | **Expected long-term rate of return** applied to the **market-related value** of assets, which may smooth fair value changes over up to five years at the employer's election. | **The expected return concept does not exist.** A **net interest** expense or income on the net defined benefit liability/asset is recognised using the **discount rate used to measure the obligation**. | Removes the smoothing and the expected-return credit. For plans with a large equity allocation and a high assumed return, the P&L pension credit **falls materially** — a permanent earnings effect, not a one-off. |
| 55 | **Defined benefit — actuarial gains and losses** | **Employer's election**: recognise immediately in net income, or defer in AOCI and amortise into net income through a **corridor**. | **Immediately in OCI**, and **never subsequently recognised in net income**. | Any deferred corridor balance is **recognised in full** at the date of transition, straight to opening retained earnings. This is commonly among the two or three largest transition adjustments for a mature DB sponsor. **There is no IFRS 1 relief** — the former D10–D11 exemption was **deleted** (IFRS 1 paragraph 39L). See §7. |
| 56 | **Defined benefit — past service cost** | Prior service cost or credit initially **deferred in AOCI**, then generally recognised in net income prospectively over the average remaining service period. | **Recognised immediately in net income.** | Unamortised prior service cost in AOCI is written off to opening retained earnings, and future plan amendments hit P&L in full in the year of amendment. Increases earnings volatility around benefit redesigns. |
| 57 | **Defined benefit — settlements and curtailments** | Settlement gain or loss in net income when settlement occurs. **Curtailment loss** recognised when **probable and estimable**; curtailment **gain** when it occurs. | Settlement gain or loss when settlement occurs, but **fewer events qualify as settlements** than under US GAAP. Curtailment effect recognised at the **earlier of** the curtailment occurring and the recognition of related restructuring costs or termination benefits. | Changes the timing of restructuring-related pension effects — usually **earlier** under IFRS, aligning them with the restructuring provision. |
| 58 | **Multi-employer plans** | Accounted for **like a defined contribution plan**. | Classified as **defined contribution or defined benefit based on the terms**, contractual and constructive. Where defined benefit, the entity accounts for its **proportionate share** unless sufficient information is unavailable. | Potential recognition of a **share of a multi-employer deficit** on balance sheet where the plan terms make it defined benefit — a significant risk for construction, transport and unionised sectors. Obtain plan-level actuarial data early; trustees are often slow. |
| 59 | **Share-based payment — forfeitures** | **Accounting policy election**: recognise forfeitures **as they occur**, or estimate expected forfeitures and true up. | **No policy election.** The initial accrual must be based on the **estimated number of instruments expected to vest**, revised as information changes. | Entities on the "as they occur" election must build a **forfeiture estimation model** and restate the comparative charge. Small in amount, but it changes the expense profile every period and requires historical turnover data. |
| 60 | **Share-based payment — graded vesting** | Policy election between the **accelerated** (tranche-by-tranche) method and **straight-line** over the whole award, for service-only awards. Total fair value may be determined for the award as a single grant using an average expected life. | **Accelerated method is mandatory** and **each tranche must be measured separately**. | Entities using straight-line must **re-measure and re-phase** every graded-vesting grant. Front-loads the expense. |
| 61 | **Share-based payment — deferred tax** | DTA based on **cumulative book expense recognised**. All excess tax benefits and deficiencies go to **income tax expense or benefit in the income statement**. | DTA based on the **estimated tax deduction at each reporting date** (e.g. intrinsic value). Where the deduction **exceeds** cumulative compensation cost, the excess deferred tax effect is credited to **equity**; where it is less than or equal, it goes to **income**. | The IFRS DTA moves with the **share price**, not with the expense. Introduces tax-line volatility tracking the equity market and a partial equity credit that US GAAP eliminated in 2016. Requires period-end share prices per grant. |
| 62 | **Share-based payment — non-employees** | Employee defined largely by the **common law** definition. Non-employee awards measured on the fair value of the **equity instruments**; measurement date for equity-classified awards is generally the **grant date**. | Broader definition of employee, covering individuals providing similar services. Fair value based on the **goods or services received**, falling back to the equity instruments only where that cannot be reliably estimated. Measurement date is when the goods are obtained or the services rendered. | Contractor and consultant awards may be **remeasured at a different date and on a different basis**. Relevant where a material part of the workforce is engaged off payroll. |

### Presentation, EPS, segments and interim

| # | Topic | US GAAP treatment | IFRS treatment | Transition impact |
|---|---|---|---|---|
| 63 | **Third balance sheet** | **Not required.** | Required at the **beginning of the earliest comparative period** where a retrospective application, restatement or reclassification has a material effect on it (related notes are **not** required) — and **always required in the year an entity first applies IFRS**. | A presentation requirement that is easy to miss. IFRS 1 paragraph **21** sets the full requirement: **three** statements of financial position, **two** of everything else, plus related notes and comparative information for all statements presented. |
| 64 | **Discontinued operations — threshold** | Components held for sale or disposed of that represent a **strategic shift** with a major effect on operations and results. An acquired business or non-profit activity classified as held for sale on acquisition or on joint venture formation also qualifies. | A component disposed of or held for sale that (1) represents a **separate major line of business or geographical area of operations**, (2) is part of a **single co-ordinated plan** to dispose of one, or (3) is a **subsidiary acquired exclusively with a view to resale** (**IFRS 5.32**). | Different populations. The US "strategic shift" test can capture disposals that fall short of a separate major line of business, and vice versa. Re-assess any disposal in the comparative period — reclassification between continuing and discontinued changes **every** comparative income statement line. |
| 65 | **Balance sheet — refinanced short-term loans** | Classified **non-current** if the entity intends to refinance long-term and can demonstrate the ability to do so **before issuing** the financial statements. | Short-term loans refinanced **after** the balance sheet date **cannot** be reclassified as non-current. Non-current only where the entity has the **right to refinance for at least 12 months** under an **existing facility** at the balance sheet date. | Debt migrates from non-current to current. **Check covenants before the date of transition** — current ratio and working capital covenants are the ones that break. |
| 66 | **Balance sheet — covenant breaches** | Debt with a covenant violation may be **non-current** if a waiver is obtained before the statements are issued, or if it is probable the breach will be cured within a grace period. | Debt associated with a covenant violation **must be presented as current** unless the lender agreement was reached **before the balance sheet date**. | Same direction as row 65 and compounding with it. A breach cured in January reclassifies the entire facility to current at 31 December. |
| 67 | **Income statement — expense classification** | No general requirement to classify by function or nature; SEC registrants present function-based line items. | Presentation by **function or nature**; where function is used, **disclosure about the nature of expenses** is required in the notes. **Superseded from 1 January 2027 by IFRS 18**, which imposes required categories, totals and subtotals — see §10. | Do not build the IFRS chart of accounts to IAS 1 if the first IFRS reporting date is 2027 or later. Build it to **IFRS 18** and avoid two redesigns. |
| 68 | **EPS — contracts settleable in shares or cash at the issuer's option** | Share settlement is generally presumed, and that presumption **may not be overcome** by past practice or stated policy (except liability-classified share-based payment awards). | Such contracts are **always assumed to be settled in shares**; the presumption **may not be overcome** at all. | Narrow. Affects convertible instruments with issuer settlement choice. |
| 69 | **EPS — year-to-date diluted computation** | Under the treasury stock method, the incremental shares in the year-to-date denominator are the **weighted average of the quarterly incremental shares**. Contingently issuable shares included on a weighted-average basis. | **All** dilutive potential ordinary shares, including contingently issuable shares, are determined **independently for each period presented**, including year-to-date periods — **not** a weighted average of the interim computations. | Diluted EPS for the comparative year must be **recomputed from scratch**, not aggregated from published quarters. Affects the restated comparative EPS disclosed in the first IFRS financial statements. |
| 70 | **EPS — contingently convertible instruments** | Shares from an instrument with a **market price trigger** are included using the if-converted method **from the issuance date**, whether or not the trigger is met at period end. | No specific guidance; the contingently-issuable-share rules apply — included **only if the contingencies are satisfied at the end of the reporting period**. | IFRS is **less dilutive** here. Recompute diluted EPS for any contingent convertible. |
| 71 | **Segments — segment liabilities** | Not required to be disclosed, **even if** reported to the CODM. | **Required** if regularly reported to the CODM. | A disclosure build. Requires the segment balance sheet data to be extractable — often it is not. |
| 72 | **Segments — matrix organisations** | ASC 280 **requires** that components based on **products and services** be the operating segments. | All entities determine segments on the **management approach**, regardless of organisational form. | Segment structures can legitimately differ. For groups managed geographically as well as by product, IFRS may permit — or require — a **different reportable segment set**, which cascades into **goodwill CGU allocation** (row 16). |
| 73 | **Segments — long-lived asset disclosure** | For entity-wide geographic disclosures, "long-lived assets" implies **hard assets**, excluding intangibles including goodwill. | Geographic disclosure of **non-current assets**, which **often includes intangibles**. | Broader disclosure population; usually a data-sourcing exercise rather than a judgement. |
| 74 | **Interim reporting — view** | Each interim period is an **integral part** of the annual period. Costs benefiting more than one interim period **may be allocated**, deferred or accrued. | Each interim period is a **discrete** reporting period. A cost that does not meet the definition of an asset at the interim date is **not deferred**, and an interim liability must be a **present obligation**. Measurements are made **year-to-date** and the frequency of reporting must not affect annual results (**IAS 34.28**). | Interim results **re-phase**, sometimes materially: advertising, major repairs, volume rebates, annual bonuses and seasonal costs move between quarters even though the full-year figure is unchanged. Income taxes remain on an estimated annual effective rate under both, which is the main exception. **Brief the market on quarterly phasing before publishing the first IFRS interim report.** |
| 75 | **Subsequent events — cut-off** | Evaluated through the date the statements are **issued** (SEC registrants and conduit bond obligors) or **available to be issued** (others). | Evaluated through the date the statements are **authorised for issue**, which depends on the entity's governance and statutory approval procedures. Disclosure of that date, who authorised it, and whether owners can amend afterwards, is required. | Usually a short difference, but it moves the cut-off and requires a documented board authorisation date. Note IFRS **does not address reissuance** and recognises only one cut-off date. |
| 76 | **Fair value — NAV practical expedient** | Practical expedient to estimate the fair value of certain alternative investments (e.g. limited partner interests in private equity funds) using **NAV or its equivalent**. | **No NAV practical expedient.** | Funds-of-funds, insurers and pension-adjacent balance sheets must value alternative investment holdings **directly**. A real valuation cost, and a disclosure change (no NAV-based level exemption). |
| 77 | **Fair value — Day 1 gains and losses** | Recognised where transaction price differs from fair value, **including where the measurement uses significant unobservable (Level 3) inputs**, provided evidence substantiates the difference. | Recognised for financial instruments **only** where fair value is evidenced by a **Level 1 quoted price** or by a valuation technique using **only observable market data**. | IFRS is **more restrictive**: Day 1 gains on Level 3 structured trades are **deferred**. Structured products desks must build a deferral and release mechanism. |
| 78 | **Rate-regulated activities** | Regulatory assets and liabilities are recognised under specific US GAAP guidance for regulated operations `[ASC-para-unconfirmed]` (the governing ASC topic could not be verified — see the gap note above). | **IFRS 14** permits a first-time adopter to continue its previous-GAAP regulatory deferral accounting; **IFRS 20 *Regulatory Assets and Regulatory Liabilities*** was issued **27 May 2026**, effective **1 January 2029**, and is not yet EU-endorsed. | A rare structural advantage for first-time adopters: **IFRS 14 is available only to first-time adopters**, so a US regulated utility can carry its regulatory balances across — **but IFRS 14 was never EU-endorsed**, so this route is closed to an entity reporting under *IFRS as adopted by the EU*, for which IFRS 20 in 2029 will be a first-time recognition event rather than a change of model. **IFRS 1 D8B** separately allows previous-GAAP carrying amounts as deemed cost for rate-regulated PP&E, ROU and intangible assets, subject to a mandatory IAS 36 test. Plan for IFRS 20 replacing IFRS 14. |

---

## 3B. Local GAAP → IFRS: Differences That Recur Across Jurisdictions

Where previous GAAP is a national framework other than US GAAP, the specific differences vary — but the **pattern** does not. National GAAPs are generally shorter, more prescriptive, more closely coupled to tax and company law, and less oriented to fair value. The differences below recur in the great majority of transitions regardless of jurisdiction, and are the right starting population for a **diagnostic gap analysis** before jurisdiction-specific work begins.

`[unsourced — practice]` throughout the "typical local GAAP" column: it is a synthesis of recurring practice patterns, not a claim about any identified framework, and is offered as a diagnostic starting point only. The IFRS column carries the verified citations.

| # | Theme | Typical local GAAP position | IFRS position | Why it recurs |
|---|---|---|---|---|
| 1 | **Tax-driven measurement** | Depreciation rates, provisions and inventory valuation follow the tax code so that book equals taxable profit. | Measurement is driven by economics; tax is a **separate** IAS 12 computation on temporary differences. | Wherever a jurisdiction requires or strongly incentivises book–tax conformity. Produces adjustments across **PP&E lives, provisions and inventory simultaneously**, and creates large new deferred tax balances. |
| 2 | **Legal form over substance** | Legal ownership and contractual title determine recognition. | **Control** and **transfer of risks and rewards / obligations** determine recognition. | The root cause behind lease capitalisation, consolidation of structured entities, factoring derecognition, sale and leaseback, and consignment inventory — all at once. |
| 3 | **Off-balance-sheet leases** | Operating leases expensed straight line; only finance leases capitalised, often on bright-line tests. | **IFRS 16** single lessee model: ROU asset and lease liability for substantially all leases (IFRS 16 [para-unconfirmed]). | Near-universal, and normally the **largest gross-up** on transition. Also the largest data collection exercise — see §9 pitfall 1. |
| 4 | **Incurred-loss impairment** | Impairment on receivables and loans only after a loss event, often on formulaic or tax-driven percentages. | **Forward-looking ECL** (IFRS 9 [para-unconfirmed]). | Universal for financial institutions and material for any entity with a large trade receivables book. Even the IFRS 9 simplified approach requires a **provision matrix with forward-looking overlays**. |
| 5 | **No discounting** | Long-term provisions, deferred consideration and non-current receivables carried at **undiscounted** nominal amounts. | Discounting required where the time value of money is material; unwinding is a **finance cost**. | Recurs because discounting requires a rate policy most national frameworks never demanded. Moves cost from operating to financing — check EBITDA-based covenants. |
| 6 | **Higher recognition thresholds** | "Probable" set high; provisions recognised late; general or "smoothing" reserves permitted. | "Probable" means **more likely than not** for IAS 37; **general provisions are prohibited** — there must be a present obligation from a past event. | Two opposite adjustments in the same entity: **more** specific provisions recognised, and **general/regulatory reserves written back to equity**. |
| 7 | **No component depreciation** | A single life for a whole asset, frequently a statutory rate. | Significant components depreciated separately (IAS 16 [para-unconfirmed]). | Requires a fixed asset register that does not exist. The **IFRS 1 D5/D6 deemed cost election** is the standard mitigation. |
| 8 | **Amortisation of all intangibles, including goodwill** | Goodwill and all intangibles amortised over a statutory maximum (10, 20 or 40 years is typical). | Goodwill is **not amortised**; it is tested annually. Indefinite-lived intangibles are not amortised. Finite-lived intangibles are amortised over their useful lives. | Universal outside the US. Reverses accumulated goodwill amortisation into equity (or restates the acquisition where IFRS 3 is applied retrospectively), and replaces a predictable charge with an **annual impairment test**. |
| 9 | **Internally generated intangibles recognised** | Formation costs, start-up costs, internally generated brands, customer lists and mastheads capitalised. | **Prohibited** for internally generated brands, mastheads, publishing titles, customer lists and similar items; start-up costs expensed (IAS 38 [para-unconfirmed]). | Recurs in civil law jurisdictions where such capitalisation supports distributable reserves. **Straight write-off to opening retained earnings** — and check the **distributable profits** consequence with local counsel. |
| 10 | **R&D fully expensed** | All research and development expensed as incurred. | Development costs **capitalised** once the IAS 38 criteria are met. | The mirror image of row 9 and often in the same entity. |
| 11 | **Corridor or deferred actuarial gains** | Actuarial gains and losses deferred, amortised, or pension obligations measured on a statutory/funding basis rather than an accounting one. | **Projected unit credit**, full net defined benefit liability on balance sheet, remeasurements in **OCI with no recycling**. | Recognising the full deficit is frequently the second-largest equity adjustment. **No IFRS 1 relief exists** — the D10–D11 exemption was deleted. |
| 12 | **Revenue on delivery / risks and rewards** | Revenue on transfer of risks and rewards, invoice, or delivery; bundled arrangements as one unit; completed-contract or percentage-of-completion on local criteria. | **IFRS 15** five-step model on **transfer of control**, with distinct performance obligations, standalone selling price allocation, constrained variable consideration and capitalised incremental costs of obtaining a contract. | Universal. The **D35** exemption removes contracts completed before the earliest period presented; open multi-element and long-term contracts must be restated. |
| 13 | **Financial instruments at cost** | Unquoted equities at cost less impairment; derivatives off balance sheet or at cost; no hedge accounting framework, or one based on bright-line effectiveness bands. | Derivatives at **fair value** on balance sheet; equities at FVTPL or FVOCI by election; hedge accounting requires an **economic relationship** and full documentation. | Recurs everywhere outside the largest capital markets. The critical item is **hedge documentation on or before the date of transition** — mandatory exception **B4–B6** forbids retrospective designation, and there is no cure. |
| 14 | **Statutory formats** | A prescribed balance sheet and income statement layout, often set in company law, with fixed line items and captions. | A minimum line item list, presentation by function or nature, and required current/non-current classification unless liquidity presentation is more relevant. **IFRS 18 from 1 January 2027** imposes categories, totals and subtotals. | Requires a **chart of accounts redesign** and often creates a dual-reporting obligation because the statutory filing must still use the local format. Build to **IFRS 18**, not IAS 1. |
| 15 | **No OCI, no statement of changes in equity** | OCI is not a concept; equity movements shown in a note. | Statement of changes in equity is a **primary statement**; OCI items split between those that **will** and **will not** be reclassified to profit or loss. | Purely presentational, but it requires new ledger accounts for each OCI reserve and its recycling attribute — a system change, not a disclosure. |
| 16 | **Revaluation reserves and legal reserves** | Statutory revaluation reserves, legal reserves and non-distributable reserves prescribed by company law. | Recognised only where an IFRS supports them (e.g. the IAS 16 revaluation surplus). Others are reclassified within equity. | Total equity is usually unaffected, but the **distributable/non-distributable split changes** — which can affect dividend capacity. Involve local counsel early. |
| 17 | **Consolidation on legal ownership** | Consolidation where a majority of voting rights is held; special purpose entities and structured entities outside the group. | Single **control** model including de facto control and potential voting rights; structured entities assessed identically. | Brings SPEs, securitisation vehicles, employee benefit trusts and some franchise or agency arrangements on balance sheet. |
| 18 | **Proportionate consolidation of joint ventures** | Proportionate consolidation permitted or required. | **Prohibited.** Equity method for joint ventures; joint operations recognise the entity's share of assets, liabilities, revenues and expenses. | Large revenue and asset reversal for construction, extractive and infrastructure groups. Note the **D31(b)** mandatory impairment test. |
| 19 | **Related party and segment disclosure gaps** | Limited related party disclosure; no segment reporting or a statutory analysis only. | **IAS 24** related party disclosure including key management personnel compensation; **IFRS 8** management-approach segments for listed entities. | A disclosure and data-collection workstream that consistently starts too late. Key management personnel compensation in particular requires HR data and board sign-off. |
| 20 | **Disclosure volume** | A short, prescribed note set. | Extensive disclosure across every standard, plus IFRS 7, IFRS 13, IAS 24, IFRS 12 and the IFRS 1 first-time adoption disclosures. | The most consistently underestimated workstream. Note **IFRS 19** *Subsidiaries without Public Accountability: Disclosures* (issued 9 May 2024) may substantially reduce this for eligible subsidiaries — assess eligibility during Phase 1. IFRS 19.A1 is permissive, not mandatory: an entity **may elect** to apply it for reporting periods beginning on or after 1 January 2027. It is **not yet EU-endorsed** (endorsement expected Q3/Q4 2026); the UK adopted it, with the August 2025 amendments, on 8 May 2026. |

---

## 4. Deferred Tax Implications on Transition (IAS 12)

### General Principle

IAS 12 — Income Taxes must be applied to all IFRS-adjusted carrying amounts at the date of transition. IFRS 1 does not provide an exemption from IAS 12 — entities must recognise deferred tax assets and liabilities for all temporary differences that exist between IFRS carrying amounts and their tax bases at the date of transition.

Tax-basis amounts typically remain unchanged on transition because tax follows local rules, not IFRS. However, because IFRS carrying amounts often differ significantly from previous GAAP carrying amounts, new temporary differences arise that did not exist (or existed in different amounts) under the previous framework.

The deferred tax impact often materially affects the opening retained earnings figure and is one of the most frequently underestimated areas of transition complexity.

### The IFRS 1 B14 override — deferred tax on leases and decommissioning

**Mandatory exception B14** is the item most commonly missed on transition. **Despite** the IAS 12 initial recognition exemption (IAS 12.15 and 12.24), a first-time adopter **shall** recognise, at the date of transition, deferred tax on **all** deductible and taxable temporary differences associated with:

- (a) **right-of-use assets and lease liabilities**; and
- (b) **decommissioning, restoration and similar liabilities** and the corresponding amounts capitalised in the cost of the related asset.

Deferred tax assets are recognised only to the extent that recovery is probable. This is an exception, not an election — an entity that applies the IAS 12 initial recognition exemption to its newly recognised ROU assets and lease liabilities has misapplied IFRS 1.

### Common Sources of New Temporary Differences on Transition

| Source | Nature of Temporary Difference |
|---|---|
| **IFRS 16 ROU assets and lease liabilities** | IFRS recognises a right-of-use asset and lease liability that typically have different carrying amounts from their tax base (which may be nil if the jurisdiction treats the lease as an operating lease for tax). The ROU asset and liability often differ from each other, creating a net temporary difference. **Deferred tax is mandatory here under IFRS 1 B14** regardless of the IAS 12 initial recognition exemption. |
| **IFRS 9 ECL provisions** | Expected credit loss provisions are typically larger than incurred-loss provisions under previous GAAP. Tax deductions for credit losses usually follow local tax rules (often requiring write-off or specific evidence of impairment), creating a deductible temporary difference. |
| **IAS 19 remeasured employee benefit obligations** | Full recognition of the net defined benefit liability under IAS 19 (using the projected unit credit method) often results in a larger liability than under previous GAAP, particularly where corridor approaches were used. Tax deductions typically follow cash contributions. |
| **IAS 36 impairment adjustments** | Impairment losses recognised on transition (or reversals of previous impairment) change carrying amounts of non-financial assets without affecting tax bases, creating temporary differences. |
| **IFRS 15 contract assets and liabilities** | Revenue timing differences under the IFRS 15 five-step model may create contract assets or liabilities that have no tax base (tax follows invoicing or cash receipts in many jurisdictions). |
| **IAS 38 capitalised development costs** | Development costs capitalised under IAS 38 that were expensed under previous GAAP (or vice versa) create temporary differences where tax deductions follow the previous GAAP treatment. |
| **IAS 37 decommissioning and restoration provisions** | The provision and the capitalised asset component are both newly recognised or remeasured, and **IFRS 1 B14** requires deferred tax on the associated temporary differences notwithstanding the IAS 12 initial recognition exemption. |

### Deferred Tax Asset Recoverability

Entities must reassess deferred tax asset (DTA) recoverability under IFRS carrying amounts. The assessment is based on:

- Projected future taxable profits using IFRS-based forecasts
- Reversing taxable temporary differences against which deductible temporary differences can be utilised
- Tax planning opportunities available to the entity

Where IFRS adjustments significantly change the balance sheet (e.g., large new deductible temporary differences from ECL provisions or lease liabilities), the DTA recoverability assessment may yield a different conclusion from the one reached under previous GAAP.

Deferred tax is recognised at rates **enacted or substantively enacted** at the reporting date (**IAS 12.46** for current tax, **IAS 12.47** for deferred tax), and DTAs are recognised **only to the extent recovery is probable** with no separate valuation allowance presented (**IAS 12.24**).

---

## 5. IT and System Changes

System and technology changes are a critical workstream in any IFRS transition. These should begin during Phase 1 (Assessment), not deferred to Phase 2, because system procurement and implementation timelines are often the longest lead-time items.

### Typical System Workstreams

| Workstream | Description |
|---|---|
| **Lease accounting software (IFRS 16)** | For entities with significant lease portfolios, dedicated lease accounting software is essentially mandatory. The calculations (present value of lease payments, ROU asset depreciation, interest expense, remeasurement on modification) are too complex and voluminous for spreadsheets at scale. Evaluate build vs buy: most entities should buy a commercial solution unless their IT capability and lease complexity justify a bespoke build. |
| **ECL model infrastructure (IFRS 9)** | Expected credit loss modelling requires credit risk models, forward-looking macroeconomic scenarios, probability of default and loss-given-default estimates, and staging logic. Financial institutions typically need dedicated ECL platforms; corporates with simpler portfolios may manage with structured spreadsheets or lightweight tools. |
| **Chart of accounts redesign (IAS 1 / IFRS 18)** | Presentation requirements often differ from local GAAP. The chart of accounts may need new accounts for OCI components, ROU assets, contract assets/liabilities, ECL allowances, and other IFRS-specific items. This redesign affects the general ledger, reporting tools, and consolidation systems. Where the first IFRS reporting date is **31 December 2027 or later**, design to **IFRS 18** categories and subtotals from the outset — see §10. |
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

## 5A. Building the Opening IFRS Statement of Financial Position

IFRS 1 paragraph **6** requires an opening IFRS statement of financial position at the date of transition; it is *"the starting point for its accounting in accordance with IFRSs"*. Paragraph **10** sets out the four mechanical operations, and paragraph **11** determines where the adjustments go.

**The four operations (IFRS 1.10):** at the date of transition an entity shall (a) **recognise** all assets and liabilities whose recognition IFRS requires; (b) **not recognise** items as assets or liabilities where IFRS does not permit it; (c) **reclassify** items recognised under previous GAAP as one type of asset, liability or equity component that are a different type under IFRS; and (d) **measure** all recognised assets and liabilities in accordance with IFRS.

**Where the adjustments go (IFRS 1.11):** the resulting adjustments arise from events and transactions **before** the date of transition, and are therefore recognised **directly in retained earnings** (or another category of equity where appropriate) at the date of transition — **not** in profit or loss of any period presented.

**Which version of IFRS (IFRS 1.7–8):** the same accounting policies must be used in the opening statement of financial position **and throughout all periods presented** (para 7). Those policies must comply with the IFRSs effective **at the end of the first IFRS reporting period** — earlier versions may not be applied (para 8). A standard that is not yet mandatory but permits early application **may** be adopted. This is the point that catches most projects: an entity with a 31 December 2027 first IFRS reporting date must apply **IFRS 18** in its 1 January 2026 opening balance sheet, even though IFRS 18 was not effective on that date.

### Build sequence

Run these in order. Steps 1–4 are gating: an error in them invalidates everything downstream.

| Step | Action | Reference | Why it is at this position |
|---|---|---|---|
| **1** | **Fix the two dates and the IFRS version.** Confirm the first IFRS reporting date, derive the date of transition as the beginning of the earliest comparative period presented, and pin the IFRS suite effective at the **first IFRS reporting date**. | paras 7–8, 21 | Everything else is measured on these three parameters. Getting the IFRS version wrong means remeasuring the whole balance sheet. |
| **2** | **Determine the scope of the reporting entity.** Re-perform the IFRS 10 control assessment for **every** investee, and the IFRS 11 classification for every joint arrangement, on the facts at the date of transition. Identify investment entities. | IFRS 10, IFRS 11 | Consolidation scope determines *which* balance sheet you are building. Doing it after measurement means redoing measurement. |
| **3** | **Decide the Appendix C business combination date.** Elect whether to restate past business combinations, and if so from which date — remembering the C1 ratchet (all later combinations, plus IFRS 10 from that date) and the C5 extension to associates, joint ventures and joint operations. | paras C1–C5 | This fixes goodwill, the identifiable intangibles population and the NCI basis. Every subsequent measurement step depends on it. |
| **4** | **Complete and approve the full exemption and exception schedule.** Document every Appendix C and D election taken and **not** taken, with rationale, quantified impact, and steering committee approval; confirm the Appendix B exceptions and their consequences. | paras 12, 18, B1, C1, D1 | Elections are effectively irrevocable in practice once the opening balance sheet is audited. Late changes force reworking the reconciliations and, if made after an interim report, the paragraph **27A** explanation. |
| **5** | **Complete the mandatory hedge documentation.** Designate and document every continuing hedge relationship under IFRS 9 **on or before the date of transition**. | paras B4–B6 | **A hard deadline with no remedy.** Retrospective designation is prohibited. This is the only step in the sequence that cannot be fixed later at any cost. |
| **6** | **Recognise** all assets and liabilities IFRS requires that previous GAAP omitted. Typically: ROU assets and lease liabilities; derivatives at fair value; net defined benefit liabilities; decommissioning and restoration provisions with the corresponding asset component; onerous contract provisions; contingent liabilities assumed in a restated business combination; deferred tax on newly recognised items. | para 10(a) | Recognition before measurement — you cannot measure what is not yet on the balance sheet. |
| **7** | **Derecognise** items IFRS does not permit. Typically: internally generated brands, mastheads, customer lists and start-up/formation costs; general, smoothing or statutory-purpose reserves that are not present obligations; deferred charges that fail the asset definition; pushdown-accounting goodwill in separate financial statements; previous-GAAP lease incentive and straight-lining accruals replaced by IFRS 16. | para 10(b) | Do this before measurement so that measurement effort is not spent on items about to be removed. |
| **8** | **Reclassify** items whose classification changes without changing measurement. Typically: financial assets into the IFRS 9 categories; debt current/non-current under the refinancing and covenant rules; assets and disposal groups held for sale; investment property out of PP&E; equity components of compound instruments; statutory reserves within equity. | para 10(c) | Reclassification is cheap and clarifies the measurement population for step 9. |
| **9** | **Measure** everything under IFRS, applying the elected exemptions. Deemed cost for PP&E, investment property (cost model), ROU assets and qualifying intangibles; lease liabilities under D9B; ECL allowances under B8D–B8G; impairment testing at CGU level under IAS 36; provisions discounted under IAS 37; equity instruments at fair value with the D19B election where wanted. | para 10(d), Appendix D | The bulk of the work, and the point at which valuation and actuarial deliverables must already be in hand. |
| **10** | **Run the mandatory transition-date impairment tests.** IAS 36 on goodwill and indefinite-lived intangibles; IAS 36 on ROU assets (**D9B(c)**); IAS 36 on the investment where moving from proportionate consolidation to the equity method, **regardless of indicators** (**D31(b)**); IAS 36 or IFRS 6 on assets measured under the D8A oil and gas exemption; IAS 36 on each item using the D8B rate-regulated deemed cost. | paras D8A, D8B, D9B, D31 | These are triggered **by** the exemption elections, so they can only be run after step 9. Four of the five are mandatory and unindicated — they are easy to miss because nothing prompts them. |
| **11** | **Apply IAS 12 to every adjusted carrying amount.** Recompute temporary differences against **unchanged tax bases**, apply the **B14** override for ROU assets, lease liabilities and decommissioning items despite the IAS 12 initial recognition exemption, and reassess deferred tax asset recoverability on IFRS-based forecasts. | para B14, IAS 12.24, 12.46–47 | **Last, and never a clean-up exercise.** It must follow every other measurement change because it is computed on the final IFRS carrying amounts. See §4. |
| **12** | **Post the adjustments to retained earnings** (or another equity category where appropriate) and reset cumulative translation differences to zero if the D13 election is taken. | paras 11, D13 | The CTD reset is an intra-equity reclassification and must not be netted into the retained earnings adjustment total, or the reconciliation will not be explicable. |
| **13** | **Build the reconciliation as you post, not afterwards.** Tag every journal with the adjustment category that will appear in the IFRS 1.24 reconciliations, and split each between its pre-tax amount and its deferred tax effect. | paras 24–25 | Reconstructing the reconciliation from a posted ledger months later is the most common cause of a delayed first IFRS filing. The reconciliation is a **deliverable**, and it is cheapest to build at source. |
| **14** | **Prove the balance sheet.** Confirm it balances; confirm every adjustment traces to a workpaper and an exemption/exception reference; confirm the closing equity per the reconciliation equals the equity in the statement of financial position; confirm the four IFRS 1.10 operations were each considered for every material caption. | paras 10, 24 | The opening statement of financial position is **audited** as part of the first IFRS financial statements. Treat it as an auditable deliverable from day one. |

> **Cross-reference:** the exemption and exception schedule produced at step 4 is the input to the IFRS 1 disclosure checklist in `compliance-templates.md`, and its documentation requirements are set out in §7 below.

---

## 6. Transition Project Planning

### Phase 1: Assessment (3-6 Months Before Date of Transition)

**Objective:** Understand the scope of change and build the business case.

1. **Perform a diagnostic gap analysis** — Compare current accounting policies with IFRS requirements across all material areas. Use the gap analysis template in `compliance-templates.md`, and the matrices in §3A (US GAAP) or §3B (other national frameworks) as the starting population.
2. **Quantify the expected impact** — Estimate the effect on key financial metrics (equity, net income, leverage ratios, debt covenants).
3. **Identify data and system requirements** — Determine what additional data capture, system modifications, or new subledgers are needed (e.g., lease system for IFRS 16, ECL model for IFRS 9).
4. **Assess IFRS 1 exemption elections** — Perform a preliminary assessment of which optional exemptions to elect (see Section 7 below).
5. **Establish governance** — Appoint a transition project team, define roles (finance, IT, external advisors, auditors), and set up a steering committee.
6. **Develop project timeline and budget** — Map all workstreams, milestones, and resource requirements against the key dates in Section 2.

### Phase 2: Preparation (Date of Transition to End of Comparative Period)

**Objective:** Build IFRS-ready processes and prepare the opening balance sheet.

1. **Draft IFRS accounting policy manual** — Document the entity's IFRS accounting policies, including elections and exemptions.
2. **Prepare the opening IFRS balance sheet** — Recognise, derecognise, reclassify, and remeasure all items as required by IFRS. Record adjustments to retained earnings (or other equity). Follow the build sequence in §5A.
3. **Implement dual reporting** — Run parallel local GAAP and IFRS reporting during the comparative period to build confidence and test processes.
4. **Configure systems and controls** — Implement system changes, new chart of accounts, IFRS-compliant subledgers, and internal controls over IFRS reporting.
5. **Train finance staff** — Conduct IFRS technical training tailored to the entity's specific difference areas and new processes.
6. **Engage auditors early** — Discuss the opening balance sheet, policy elections, and transition adjustments with external auditors to avoid surprises.

### Phase 3: Execution (Comparative Period to First IFRS Reporting Date)

**Objective:** Produce the first complete set of IFRS financial statements.

1. **Prepare comparative IFRS financial statements** — Compile the full-year comparative period financial statements under IFRS.
2. **Prepare IFRS 1 reconciliations** — Build the required reconciliations (see Section 8 below) from previous GAAP equity and total comprehensive income to IFRS.
3. **Draft first IFRS financial statements** — Prepare the complete financial statements for the first IFRS reporting period, including all required notes and IFRS 1 disclosures.
4. **Obtain audit sign-off** — Work with external auditors to complete the audit of the first IFRS financial statements, including the opening balance sheet and comparative period.
5. **Communicate to stakeholders** — Brief investors, analysts, lenders, regulators, and board members on the impact of the transition and key changes from prior reporting.

> **Note the interim deliverable.** Where the entity publishes an IAS 34 interim report within the first IFRS reporting period, that report — not the annual financial statements — is the first public IFRS deliverable, and it carries the IFRS 1.32 reconciliations and the IFRS 18 heading structure. See §2A.

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
- **Analyst and investor briefings** — Before publishing the first IFRS financial statements, brief analysts and investors on the expected impact. Explain key differences from previous GAAP results and provide pro-forma reconciliations where helpful. Include the **interim phasing** effect: interim results re-phase on transition even where the annual result does not.
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

IFRS 1 provides optional exemptions from full retrospective application for specific areas, and mandatory exceptions that prohibit it. The decision to elect or not should be deliberate and documented.

### Decision Factors

| Factor | Elect Exemption | Do Not Elect Exemption |
|---|---|---|
| **Cost of retrospective application** | High — historical data is unavailable or would require excessive effort to reconstruct | Low — historical records are complete and accessible |
| **Data availability** | Source data for retrospective application does not exist or is unreliable | Reliable data exists for the entire retrospective period |
| **Comparability** | Exemption provides a reasonable starting point; limited impact on trend analysis | Full retrospective application provides more meaningful comparatives |
| **Subsequent measurement complexity** | Exemption simplifies ongoing measurement (e.g., deemed cost avoids tracking historical IFRS depreciation) | Full retrospective values align better with ongoing IFRS measurement |
| **Stakeholder expectations** | Users of financial statements accept the exemption approach | Investors or regulators prefer full retrospective figures |

### The two categories, and why preparers confuse them

IFRS 1 paragraph 12 establishes **two categories** of departure from full retrospective application, and they are not symmetrical:

| | **Mandatory exceptions** | **Optional exemptions** |
|---|---|---|
| **Where** | IFRS 1 paragraphs 14–17 and **Appendix B** | IFRS 1 Appendices **C, D and E** |
| **Nature** | IFRS 1 **prohibits** retrospective application (para 12(a)) | IFRS 1 **grants relief from** a requirement (para 12(b)) |
| **Choice** | **None.** "An entity **shall** apply the following exceptions" (para B1) | "An entity **may elect** to use one or more of the following exemptions" (para D1) |
| **Analogy** | n/a | **Prohibited** — "An entity shall not apply these exemptions by analogy to other items" (paras 18 and D1) |
| **Failure mode** | Applying hindsight where it is banned — an audit finding, potentially an error under IAS 8 | Failing to document a valid election — a documentation finding, not a misstatement |

The practical test: if you are asking *"should we?"* it is an exemption; if you are asking *"can we?"* it is an exception and the answer is no.

### Mandatory Exceptions (IFRS 1.13–17 and Appendix B)

These are NOT optional — entities MUST apply them. Paragraph **13** introduces them; paragraph **12(a)** identifies them as paragraphs 14–17 **and Appendix B**, where seven of the ten live. Paragraph **B1** lists them.

| # | Exception | Reference | What is prohibited / required |
|---|---|---|---|
| 1 | **Estimates** | paras 14–17 | Estimates at the date of transition **must be consistent with** those made under previous GAAP for the same date, after adjusting only for accounting-policy differences — unless there is **objective evidence those estimates were in error** (para 14). Information received after the date of transition about a previous-GAAP estimate is treated as a **non-adjusting event** under IAS 10 and taken to P&L (or OCI) of the later period (para 15). Where IFRS requires an estimate that previous GAAP did not, it must reflect **conditions at the date of transition** — market prices, interest rates and FX rates at that date (para 16). Paragraphs 14–16 apply equally to the **comparative period end** (para 17). |
| 2 | **Derecognition of financial assets and financial liabilities** | paras B2–B3 | IFRS 9 derecognition applies **prospectively** to transactions occurring on or after the date of transition. Items derecognised under previous GAAP before that date stay derecognised (para B2). *Limited relief:* an entity **may** apply IFRS 9 derecognition retrospectively from a date of its choosing, but **only if** the information needed was obtained **at the time of the original transaction** (para B3) — a genuine constraint, not a free election. |
| 3 | **Hedge accounting** | paras B4–B6 | At the date of transition: measure **all** derivatives at fair value and **eliminate** deferred derivative gains/losses carried as previous-GAAP assets or liabilities (para B4). A hedging relationship that does not qualify under IFRS 9 **cannot** be reflected in the opening statement of financial position (para B5). Transactions entered into before the date of transition **shall not be retrospectively designated as hedges** (para B6). |
| 4 | **Non-controlling interests** | para B7 | Apply **prospectively** from the date of transition: attribution of total comprehensive income to NCI even where this creates a deficit NCI balance (IFRS 10.B94); changes in ownership without loss of control (IFRS 10.23 and B96); loss of control (IFRS 10.B97–B99 and IFRS 5.8A). **Interaction:** if the entity elects to restate past business combinations under IFRS 3, it must apply IFRS 10 from the same date (para C1). |
| 5 | **Classification and measurement of financial assets** | paras B8–B8C | The SPPI test (IFRS 9.4.1.2 / 4.1.2A) is assessed on the **facts and circumstances existing at the date of transition** (para B8). Where a modified time-value-of-money element (para B8A) or the insignificance of a prepayment feature (para B8B) is impracticable to assess at that date, assess the contractual cash flows **without** that requirement and give the IFRS 7.42R / 42S disclosures. Where retrospective application of the **effective interest method** is impracticable, fair value at the date of transition becomes the new gross carrying amount / amortised cost (para B8C). |
| 6 | **Impairment of financial assets** | paras B8D–B8G | IFRS 9 Section 5.5 applies **retrospectively**, subject to four reliefs. Use reasonable and supportable information available **without undue cost or effort** to establish credit risk at initial recognition and compare it to credit risk at the date of transition (para B8E). The low-credit-risk simplification and the 30-days-past-due rebuttable presumption are available (para B8F). Where establishing whether credit risk has increased significantly would require **undue cost or effort**, the entity **must** recognise a **lifetime ECL at every reporting date** until derecognition — a penalty default, not a convenience (para B8G). |
| 7 | **Embedded derivatives** | para B9 | Assess separation on the conditions at the **later of** (a) the date the entity first became a party to the contract and (b) the date a reassessment is required by IFRS 9.B4.3.11. |
| 8 | **Government loans** | paras B10–B12 | Classify all government loans as liability or equity under IAS 32. Apply IFRS 9 and IAS 20 **prospectively**: the below-market interest benefit on a pre-transition loan is **not** recognised as a government grant, and the **previous-GAAP carrying amount** at the date of transition becomes the opening IFRS carrying amount (para B10). *Limited relief:* retrospective application is permitted only where the information was obtained at the time of initially accounting for the loan (para B11). The exception does not block the D19–D19C FVTPL designation exemptions (para B12). |
| 9 | **Insurance contracts** | para B13 | Apply the IFRS 17 transition provisions in **IFRS 17 Appendix C paragraphs C1–C24 and C28**, reading "transition date" in those paragraphs as **the date of transition to IFRSs**. |
| 10 | **Deferred tax on leases and decommissioning liabilities** | para B14 | **Despite** the IAS 12 initial recognition exemption (IAS 12.15 and 12.24), a first-time adopter **shall** recognise, at the date of transition, deferred tax on **all** deductible and taxable temporary differences associated with (a) right-of-use assets and lease liabilities and (b) decommissioning/restoration liabilities and the corresponding amounts capitalised in the related asset. Deferred tax assets only to the extent recovery is probable. The single most commonly missed item on transition — see §4. |

> **The estimates exception in one line:** you may not use what you learned after the date of transition to make the opening balance sheet look more accurate. The only permitted correction is for an estimate that was **wrong on the information available at the time**.

### The complete set of optional exemptions

#### Appendix C — business combinations (paragraphs C1–C5)

| Exemption | Reference | Decision rule |
|---|---|---|
| **Do not restate past business combinations** | C1 | **Take it** unless the acquisitions are recent, few, and you hold complete purchase-price-allocation working papers. **Note the ratchet:** restating *any* business combination obliges you to restate **all later** combinations **and** to apply IFRS 10 from that same date. Choosing a restatement date is therefore choosing a cut-off for the whole group history, not a per-deal election. |
| **Do not apply IAS 21 retrospectively to fair value adjustments and goodwill** | C2–C3 | **Take it** where acquired foreign operations are numerous or historical rates are unreconstructable. Consequence: those goodwill and fair value adjustments become **assets and liabilities of the acquirer**, not the acquiree — so they are either already in the functional currency or are non-monetary items carried at the previous-GAAP rate, and they will **not** retranslate going forward. Do **not** take it if you want goodwill to move with the subsidiary's currency. |
| **Extension to associates, joint ventures and joint operations that are businesses** | C5 | Automatic — the C1 exemption and **the same elected date** apply to past acquisitions of investments in associates, interests in joint ventures, and interests in joint operations whose activity constitutes a business as defined in IFRS 3. You cannot pick one date for subsidiaries and another for associates. |

#### Appendix D — exemptions from other IFRSs (paragraph D1 list, in order)

Paragraph **D1** enumerates the electable exemptions as (a) to (v), with (b), (e) and (o) now `[deleted]`. All twenty live items:

| D1 ref | Exemption | Paras | One-line decision rule |
|---|---|---|---|
| (a) | **Share-based payment transactions** | D2–D3 | **Take it** for equity instruments granted on or before 7 Nov 2002, and for those granted later but **vested before the later of the date of transition and 1 Jan 2005**; also for liabilities settled before the date of transition. Note IFRS 1 says a first-time adopter is *"encouraged, but not required"* to apply IFRS 2 to those awards — and if you *do* elect to apply IFRS 2 to them, you may only do so if the measurement-date fair value was **publicly disclosed**. IFRS 2.44–45 disclosures are still required for grants to which IFRS 2 is not applied (IFRS 19.31 for IFRS 19 reporters). **Do not take it** where the awards are large, still outstanding, and modelled data exists — comparability of the share-based payment charge matters to analysts. |
| (c) | **Deemed cost — PP&E, investment property (cost model), ROU assets, intangibles** | D5–D8B | Five distinct sub-elections; see the deemed-cost table below. |
| (d) | **Leases** | D9, D9B–D9E | See the leases table below. |
| (f) | **Cumulative translation differences** | D12–D13A | **Take it** almost always: reset CTD for **all** foreign operations to zero at the date of transition (D13(a)). Reconstructing decades of translation reserve movements has essentially no user value, and the reset is an intra-equity reclassification with **no effect on total equity**. Consequence: gain or loss on a later disposal of a foreign operation **excludes** pre-transition translation differences (D13(b)) — it is a permanent change to future disposal gains, not a timing difference. **Do not take it** where a disposal is imminent and the historic CTD is a large credit you would rather recycle. A subsidiary using the D16(a) election may instead push down the parent's CTD carrying amount (D13A). |
| (g) | **Investments in subsidiaries, joint ventures and associates (separate financial statements)** | D14–D15A | Where the separate financial statements carry such investments **at cost** under IAS 27, **take it** and use as deemed cost either (i) **fair value at the entity's date of transition** or (ii) the **previous-GAAP carrying amount** at that date (D15). Elect **investment by investment** — you are not locked into one basis for all. Where the equity method is used in separate financial statements, the Appendix C past-business-combination exemption applies to the acquisition (D15A(a)). |
| (h) | **Assets and liabilities of subsidiaries, associates and joint ventures** | D16–D17 | **Subsidiary adopting later than its parent (D16):** elect either (a) the carrying amounts in the **parent's** consolidated financial statements based on the **parent's** date of transition, before consolidation adjustments and business-combination effects, or (b) amounts based on the **subsidiary's own** date of transition. Take (a) to keep group and statutory numbers aligned and avoid a second measurement exercise; take (b) where the subsidiary's own accounting policies genuinely differ (e.g. cost model locally, revaluation model in the group). **Not available** to a subsidiary of an investment entity that must be measured at FVTPL. **Parent adopting later than its subsidiary (D17):** this is **not an election** — the parent **shall** use the subsidiary's carrying amounts, adjusted for consolidation, equity accounting and the business combination. |
| (i) | **Compound financial instruments** | D18 | **Take it** whenever the liability component of a compound instrument is **no longer outstanding** at the date of transition. It removes a pointless split of one equity balance into "original equity component" and "cumulative interest accreted in retained earnings", with **zero** effect on total equity. There is no reason not to take it. |
| (j) | **Designation of previously recognised financial instruments** | D19–D19C | Four fresh-start designations, all made on the **facts and circumstances existing at the date of transition** rather than at original recognition: **D19** — designate any financial liability as at FVTPL if it meets IFRS 9.4.2.2 at that date; **D19A** — designate a financial asset as at FVTPL under IFRS 9.4.1.5; **D19B** — make the irrevocable **FVOCI election for an equity instrument** under IFRS 9.5.7.5; **D19C** — assess whether own-credit presentation (IFRS 9.5.7.7) would create an accounting mismatch. **Take D19B** wherever previous GAAP held unquoted equities at cost and the FVOCI presentation is wanted — this is a **one-time-only** window; after the date of transition the election is only available at initial recognition of a new instrument. Disclosure of fair value at designation date and previous classification/carrying amount is required (paras 29 and 29A). |
| (k) | **Fair value measurement of financial assets or financial liabilities at initial recognition** | D20 | **Take it** if day-one gain/loss data (IFRS 9.B5.1.2A(b)) for pre-transition trades is unavailable — apply that requirement **prospectively** to transactions on or after the date of transition. Relevant almost exclusively to entities with Level 3 derivative or structured-product books. |
| (l) | **Decommissioning liabilities included in the cost of PP&E** | D21, D21A | **Take it** for asset-heavy extractive, utility and industrial entities. IFRIC 1 otherwise requires you to unwind every historical change in the liability through the asset's cost. Instead: (a) measure the liability at the date of transition under IAS 37; (b) discount it back to the date it first arose using your **best estimate of the historical risk-adjusted rate**; (c) run accumulated depreciation forward on that amount using the **current** estimate of useful life. **D21A variant:** an entity using the D8A oil-and-gas full-cost exemption applies D21A instead of D21 — measure the liability under IAS 37 and put the **entire difference straight to retained earnings**, with no asset-cost reconstruction at all. |
| (m) | **Financial or intangible assets under IFRIC 12 service concessions** | D22 | **Take it** where legacy concessions predate IFRIC 12 adoption; apply the IFRIC 12 transitional provisions. Relevant to infrastructure, PPP and regulated-utility operators. |
| (n) | **Borrowing costs** | D23 | **Take it** where you cannot reconstruct which historical borrowing costs met the IAS 23 criteria. Apply IAS 23 from the date of transition (or an earlier date permitted by IAS 23.28). Consequences are explicit: (a) do **not** restate the borrowing cost component already capitalised under previous GAAP and sitting in asset carrying amounts, and (b) **do** capitalise IAS 23-eligible costs from that date onward **including on qualifying assets already under construction** — the second half is routinely missed and creates a systems requirement mid-project. |
| (p) | **Extinguishing financial liabilities with equity instruments** | D25 | **Take it** where debt-for-equity swaps occurred pre-transition; apply the IFRIC 19 transitional provisions. Otherwise irrelevant. |
| (q) | **Severe hyperinflation** | D26–D30 | Applies where the functional currency **was or is** subject to *severe* hyperinflation — defined (D27) as both (a) no reliable general price index available to all entities and (b) the currency is not exchangeable into a relatively stable foreign currency (exchangeability assessed under IAS 21). If the date of transition is **on or after the functional currency normalisation date** (D28), elect to measure **all** assets and liabilities held before that date at **fair value**, and use that as deemed cost (D29). Note **D30**: where the normalisation date falls inside a 12-month comparative period, the **comparative period may be shorter than 12 months**, provided a complete set of financial statements per IFRS 18.10 is given for it. Disclosure of how and why the currency became, and ceased to be, severely hyperinflationary is required (para 31C). |
| (r) | **Joint arrangements** | D31 | **Take it** where previous GAAP used proportionate consolidation. Apply the IFRS 11 Appendix C transition provisions **at the date of transition** (D31(a)). Mandatory rider: on moving from proportionate consolidation to the equity method you **must** test the resulting investment for impairment under IAS 36 at that date **whether or not there is any indicator**, with any impairment charged to retained earnings (D31(b)). Budget for a valuation. |
| (s) | **Stripping costs in the production phase of a surface mine** | D32 | **Take it** for surface miners; apply IFRIC 20.A1–A4, reading "effective date" as the later of 1 Jan 2013 and the beginning of the first IFRS reporting period. |
| (t) | **Designation of contracts to buy or sell a non-financial item** | D33 | **Take it** to designate existing own-use commodity contracts as at FVTPL under IFRS 9.2.5 on the facts at the date of transition — but **only if** the entity designates **all similar contracts**. No cherry-picking the loss-making ones. Relevant to energy, mining and commodity traders. |
| (u) | **Revenue** | D34–D35 | Two separate reliefs. **D34** — apply the IFRS 15.C5 practical expedients, reading "date of initial application" as the **beginning of the first IFRS reporting period** (and then also apply IFRS 15.C6). **D35** — do **not** restate contracts **completed before the earliest period presented**, where "completed" means all goods or services identified under **previous GAAP** have been transferred. **Take D35 almost always**; it removes the long tail of legacy contracts at negligible cost to comparability. |
| (v) | **Foreign currency transactions and advance consideration** | D36 | **Take it** where volumes of prepayments/deposits are high: IFRIC 22 need not be applied to assets, expenses and income initially recognised **before** the date of transition. Removes a re-dating exercise across every historic customer deposit and supplier prepayment. |

#### The deemed cost family in detail (D5–D8B) — the highest-impact election in most transitions

| Sub-election | Ref | Decision rule |
|---|---|---|
| **Fair value as deemed cost at the date of transition** | D5 | Item-by-item election for PP&E. **Take it** where historical IFRS cost cannot be reliably reconstructed, or where previous-GAAP carrying amounts are materially below current value and the entity wants the step-up. Cost: a valuation. Benefit: a clean depreciation base and no historical cost archaeology. **Do not take it** where the step-up creates a deferred tax liability the entity cannot fund, or where it inflates the depreciation charge in a covenant-sensitive EBIT. |
| **Previous-GAAP revaluation as deemed cost** | D6 | Uses a revaluation performed **at or before** the date of transition, as deemed cost **at the date of that revaluation** — so subsequent IFRS depreciation runs from the revaluation date forward. Available only where the revaluation was, at that date, broadly comparable to (a) fair value or (b) IFRS cost / depreciated cost adjusted for a general or specific price index. **Take it** where a jurisdictional revaluation regime already produced a defensible number — it is free. |
| **Extension to investment property, ROU assets and intangibles** | D7 | D5 and D6 also apply to (a) **investment property, only if the entity elects the IAS 40 cost model**; (aa) **right-of-use assets**; and (b) **intangible assets** that meet both the IAS 38 recognition criteria (including reliable measurement of original cost) **and** the IAS 38 revaluation criteria (**an active market must exist**). The active-market condition makes (b) rare in practice. Explicitly **not available for other assets or for any liabilities**. |
| **Event-driven fair value** | D8 | Where previous GAAP established a deemed cost by fair-valuing assets at a **privatisation or IPO**. If the measurement date is **at or before** the date of transition, use it as deemed cost at that date. If it falls **after** the date of transition but **within** the first IFRS reporting period, use it as deemed cost **when the event occurs**, taking the adjustment **directly to retained earnings** at that date — and separately establish a D5–D7 deemed cost, or full IFRS measurement, at the date of transition. **Take it** — it costs nothing and the valuation already exists. |
| **Oil and gas full-cost pools** | D8A | For entities that accounted for exploration and development costs in large-geographic-area cost centres. Measure exploration and evaluation assets at previous-GAAP amounts; measure development/production assets at the previous-GAAP **cost-centre** amount and **allocate pro rata using reserve volumes or reserve values**. Mandatory rider: impairment-test the E&E assets under IFRS 6 and the development/production assets under IAS 36 **at the date of transition**, and write down if necessary. Pairs with D21A. |
| **Rate-regulated operations** | D8B | Where PP&E, ROU assets or intangibles used in **rate-regulated** operations carry previous-GAAP amounts that would not qualify for capitalisation under IFRS, elect the **previous-GAAP carrying amount as deemed cost**. Item-by-item — it need not be applied to all items. Mandatory IAS 36 impairment test at the date of transition for each item so measured. Disclosure of the fact and the previous-GAAP basis is required (para 31B). **Take it** where rate-base assets would otherwise be written off. |

#### The leases family in detail (D9, D9B–D9E)

| Sub-election | Ref | Decision rule |
|---|---|---|
| **Assess whether a contract contains a lease using facts at the date of transition** | D9 | Apply IFRS 16.9–11 on the **facts and circumstances existing at that date** rather than at inception. **Take it** always for a large or heterogeneous contract population. |
| **Modified retrospective lessee measurement** | D9B | Measure the **lease liability** at the present value of remaining lease payments, discounted at the **incremental borrowing rate at the date of transition**. Measure the **ROU asset**, choosing **lease by lease**, at either (i) the amount as if IFRS 16 had always applied, but discounted at the transition-date IBR, or (ii) **an amount equal to the lease liability**, adjusted for prepaid or accrued lease payments recognised immediately before transition. Then apply **IAS 36** to the ROU assets. **Take (ii) as the default**: it produces a **nil equity impact** on the lease itself (before reversing previous-GAAP lease accruals) and requires no inception-date data. Take (i) only where preserving the ROU/liability spread matters, e.g. for a sub-lease or a fair-value-model investment property. |
| **Investment property leases** | D9C | **Not an election.** Where a leased property meets the IAS 40 definition of investment property **and** the entity uses the IAS 40 fair value model, the ROU asset **shall** be measured at **fair value** at the date of transition. |
| **Five practical expedients, lease by lease** | D9D | (a) a **single discount rate** for a portfolio of leases with reasonably similar characteristics; (b) exclude leases whose term **ends within 12 months** of the date of transition and account for them as short-term leases under IFRS 16.6; (c) exclude **low-value** leases (IFRS 16.B3–B8) and account for them under IFRS 16.6; (d) exclude **initial direct costs** from the ROU asset at the date of transition; (e) use **hindsight**, e.g. in determining the lease term where extension or termination options exist. **Take (a), (b), (c) and (d) as standard.** (e) is the one to think about — hindsight on lease term is helpful where renewals have already been exercised, but it is applied lease by lease and must be documented consistently. |

#### Appendix E — short-term exemptions (E1–E2, E8)

**Both are now dead letters and should not appear in a current transition plan.** State this explicitly, because legacy checklists still carry them:

| Exemption | Ref | Status |
|---|---|---|
| **Relief from restating comparatives for IFRS 9 / IFRS 7** | E1–E2 | Available only where the **first IFRS reporting period begins before 1 January 2019**. Time-expired. |
| **Relief from reflecting IFRIC 23 in comparatives** | E8 | Available only where the **date of transition is before 1 July 2017**. Time-expired. |
| **E3–E7** | E3–E7 | `[Deleted]`. |

### Exemptions that no longer exist

Three items that appear in older transition literature and in many firm checklists have been **removed from IFRS 1** and must not be relied on:

| Withdrawn item | Former ref | What happened |
|---|---|---|
| **Employee benefits — reset cumulative actuarial gains and losses to zero** | D10–D11 | **Deleted** by *IAS 19 Employee Benefits (as amended in June 2011)*, which also amended D1 (IFRS 1 paragraph **39L**). The corridor approach was removed from IAS 19, so there is no deferred actuarial gain or loss to reset. A first-time adopter recognises the **full net defined benefit liability or asset** at the date of transition, with all remeasurements thereafter in OCI. There is **no relief**. |
| **Insurance contracts (as an Appendix D exemption)** | D1(b) | `[deleted]` from the D1 list. Insurance contracts are now a **mandatory exception** at paragraph **B13**, applying the IFRS 17 Appendix C transition provisions. It moved from the optional column to the compulsory one. |
| **Leases — IFRIC 4 determination** | D9A | `[Deleted]`. Superseded by the IFRS 16 regime in D9 and D9B–D9E. |

D1(e) and D1(o) are likewise shown as `[deleted]` in the current standard, and D4 and D24 are `[Deleted]`.

### Documentation Requirement

For every exemption elected or not elected, document:

- The exemption reference (IFRS 1 paragraph)
- The rationale for electing or not electing
- The quantitative impact (or the reason full quantification was impracticable)
- Approval by the transition steering committee

This documentation supports audit evidence and regulatory review. Document the mandatory exceptions too — not as elections, but as confirmation that each was identified and applied, and that its consequences (particularly the B4–B6 hedge documentation deadline and the B14 deferred tax override) were addressed.

---

## 8. Reconciliations Required by IFRS 1

### What paragraph 24 actually requires

Paragraph **23** sets the principle: the entity shall explain how the transition from previous GAAP to IFRS affected its **reported financial position, financial performance and cash flows**. Paragraph **24** gives the three specific deliverables:

| Ref | Deliverable | Precise requirement |
|---|---|---|
| **24(a)(i)** | **Equity reconciliation at the date of transition** | Previous-GAAP equity reconciled to IFRS equity at the date of transition. |
| **24(a)(ii)** | **Equity reconciliation at the end of the latest previous-GAAP period** | Previous-GAAP equity reconciled to IFRS equity at **the end of the latest period presented in the entity's most recent annual financial statements prepared under previous GAAP**. |
| **24(b)** | **Total comprehensive income reconciliation** | A reconciliation **to total comprehensive income under IFRS** for the latest period in the entity's most recent annual previous-GAAP financial statements. The **starting point** is previous-GAAP **total comprehensive income** for the same period — or, **if the entity did not report such a total, previous-GAAP profit or loss**. |
| **24(c)** | **Impairment disclosures** | Where impairment losses were **recognised or reversed for the first time** in preparing the opening IFRS statement of financial position, give the disclosures IAS 36 would have required had those losses or reversals been recognised in the period beginning at the date of transition. |

Three points that are routinely got wrong:

- **24(b) is a total comprehensive income reconciliation, not a profit or loss reconciliation.** Profit or loss is only the *starting point*, and only where previous GAAP did not report a total comprehensive income figure. Presenting a P&L reconciliation alone does not satisfy paragraph 24(b).
- **Sufficient detail (para 25).** The reconciliations must give enough detail for users to understand the **material adjustments** to the statement of financial position and to the statement of comprehensive income. If a statement of cash flows was presented under previous GAAP, the entity must **also explain the material adjustments to the statement of cash flows** — a narrative requirement, not a further reconciliation, and the most commonly omitted element of paragraph 25.
- **Errors are separated from policy changes (para 26).** Where the entity becomes aware of **errors** made under previous GAAP, the paragraph 24(a) and (b) reconciliations must **distinguish the correction of those errors from changes in accounting policies**. IAS 8 does not otherwise apply to the policy changes made on adopting IFRS (para 27).

Related disclosures: fair value used as deemed cost (para **30**) — the aggregate of those fair values and the aggregate adjustment to previous-GAAP carrying amounts, **for each line item** in the opening statement of financial position; deemed cost for rate-regulated items (para **31B**); deemed cost after severe hyperinflation (para **31C**); designation of financial assets and liabilities at FVTPL (paras **29** and **29A**); and, where no financial statements were presented for previous periods, disclosure of that fact (para **28**).

### Required Reconciliations

- [ ] **Equity reconciliation at the date of transition** — Reconcile previous GAAP equity to IFRS equity at the opening balance sheet date (e.g., 1 January 2025)
- [ ] **Equity reconciliation at the end of the latest previous GAAP period** — Reconcile previous GAAP equity to IFRS equity at the comparative period end (e.g., 31 December 2025)
- [ ] **Total comprehensive income reconciliation for the latest previous-GAAP period (IFRS 1.24(b))** — Reconcile **to total comprehensive income under IFRS** for the latest period in the entity's most recent annual previous-GAAP financial statements. The **starting point** is previous-GAAP total comprehensive income for the same period; use previous-GAAP profit or loss as the starting point **only if the entity did not report a total comprehensive income figure**.
- [ ] **Material adjustments to the statement of cash flows explained (IFRS 1.25)** — Where a statement of cash flows was presented under previous GAAP, explain the material adjustments to it. A narrative explanation is required; a formal reconciliation is not.
- [ ] **Errors distinguished from policy changes (IFRS 1.26)** — Where errors under previous GAAP are identified, the paragraph 24(a) and (b) reconciliations must separate the correction of those errors from changes in accounting policies.

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

## 8A. Worked Reconciliation — Meridian Industrial Holdings plc

A complete, arithmetically verified illustration of the paragraph 24(a) and 24(b) reconciliations. **All figures in £000.**

**Facts.** First IFRS reporting date **31 December 2026**; one comparative year presented; date of transition **1 January 2025**; comparative period **FY2025**. Previous GAAP is a national framework with off-balance-sheet operating leases, incurred-loss receivable impairment, an actuarial corridor, and no discounting of long-term provisions. Enacted and substantively enacted tax rate **25%** throughout. During FY2025 the entity paid dividends of **9,000** and issued shares for **5,000**; neither is affected by any IFRS adjustment.

**Elections and exceptions applied.** IFRS 1 **D5** (fair value as deemed cost for land and buildings); **D9B(b)(ii)** with the **D9D** expedients (leases); **D13** (CTD reset to zero); **D35** (completed contracts not restated); mandatory exceptions **B4–B6** (hedges designated at the date of transition), **B8D–B8G** (ECL) and **B14** (deferred tax on ROU assets, lease liabilities and decommissioning items). **No employee benefits exemption is available** — D10–D11 were deleted, so the full net defined benefit liability is recognised.

### Reconciliation of equity — IFRS 1.24(a)

| Ref | | **1 Jan 2025**<br>*(date of transition)* | **31 Dec 2025**<br>*(comparative period end)* |
|---|---|---:|---:|
| | **Equity under previous GAAP** | **210,000** | **232,400** |
| a | IFRS 16 — recognise ROU assets and lease liabilities, reverse previous-GAAP lease accruals and incentives | (2,700) | (3,450) |
| b | IFRS 9 — ECL allowance in excess of previous-GAAP incurred-loss provision | (4,200) | (4,850) |
| c | IFRS 15 — defer revenue on unsatisfied performance obligations, net of capitalised costs of obtaining contracts | (1,900) | (1,250) |
| d | IAS 19 — recognise full net defined benefit liability (previous-GAAP corridor eliminated) | (6,300) | (5,100) |
| e | IAS 38 — derecognise internally generated brand | (2,400) | (2,400) |
| f | IAS 38 — capitalise development costs meeting the recognition criteria | 3,100 | 4,000 |
| g | IAS 16 — fair value as deemed cost, land and buildings (IFRS 1 D5) | 18,000 | 17,550 |
| h | IAS 37 — recognise and discount decommissioning provision and related asset component | 900 | 760 |
| i | IAS 21 — reset cumulative translation differences to zero (IFRS 1 D13) | — | — |
| | **Total adjustments before tax** | **4,500** | **5,260** |
| j | Deferred tax on the above at 25% (IAS 12; includes IFRS 1 B14 items) | (1,125) | (1,315) |
| | **Total adjustments to equity** | **3,375** | **3,945** |
| | **Equity under IFRS** | **213,375** | **236,345** |

*Adjustment (i) is a reclassification **within** equity — the cumulative translation reserve is transferred to retained earnings — with no effect on total equity. It is presented as a line because IFRS 1 paragraph 25 requires sufficient detail for users to understand the material adjustments, and a reader tracing the translation reserve between the two frameworks will otherwise not find it.*

### Reconciliation of total comprehensive income for FY2025 — IFRS 1.24(b)

| Ref | | **Profit or loss** | **OCI** | **Total comprehensive income** |
|---|---|---:|---:|---:|
| | **Under previous GAAP** | **24,900** | **1,500** | **26,400** |
| a | IFRS 16 — depreciation and interest replacing straight-line operating lease expense | (750) | — | (750) |
| b | IFRS 9 — movement in ECL allowance | (650) | — | (650) |
| c | IFRS 15 — revenue recognised in the period on obligations deferred at transition, net of contract cost amortisation | 650 | — | 650 |
| d | IAS 19 — net interest and past service cost | 200 | — | 200 |
| d | IAS 19 — remeasurement of the net defined benefit liability | — | 1,000 | 1,000 |
| e | IAS 38 — internally generated brand (no amortisation in either framework) | — | — | — |
| f | IAS 38 — development costs capitalised in the period, net of amortisation | 900 | — | 900 |
| g | IAS 16 — additional depreciation on the deemed cost step-up | (450) | — | (450) |
| h | IAS 37 — unwinding of the discount on the decommissioning provision | (140) | — | (140) |
| | **Total adjustments before tax** | **(240)** | **1,000** | **760** |
| j | Deferred tax at 25% | 60 | (250) | (190) |
| | **Total adjustments** | **(180)** | **750** | **570** |
| | **Under IFRS** | **24,720** | **2,250** | **26,970** |

*Previous GAAP reported a total comprehensive income figure of 26,400, so that is the starting point required by paragraph 24(b). Had it not, the starting point would have been previous-GAAP profit or loss of 24,900.*

### Internal consistency proof

The two reconciliations must tie to each other. Rolling opening IFRS equity forward:

```
Equity under IFRS at  1 Jan 2025                    213,375
  Profit or loss under IFRS, FY2025                  24,720
  Other comprehensive income under IFRS, FY2025       2,250
  Dividends paid                                     (9,000)
  Shares issued                                       5,000
                                                    -------
Equity under IFRS at 31 Dec 2025                    236,345   ✓
```

Equivalently, each FY2025 reconciling item equals the **movement** in the corresponding equity adjustment between the two dates: adjustment (a) moves from (2,700) to (3,450), a charge of 750; (d) moves from (6,300) to (5,100), a credit of 1,200 split 200 to profit or loss and 1,000 to OCI; and so on. **Build the two reconciliations from a single adjustment schedule with opening and closing columns** — this identity is then structural rather than something to be reconciled at the end.

### Arithmetic verification

All figures above were computed and cross-checked with `python3`. The script and its output:

```python
TAX = 0.25
adj = {   # (pre-tax equity effect at 1 Jan 2025, at 31 Dec 2025)
 "a IFRS 16 leases":                 (-2700, -3450),
 "b IFRS 9 ECL":                     (-4200, -4850),
 "c IFRS 15 revenue":                (-1900, -1250),
 "d IAS 19 net DB liability":        (-6300, -5100),
 "e IAS 38 brand derecognised":      (-2400, -2400),
 "f IAS 38 development costs":       ( 3100,  4000),
 "g IAS 16 deemed cost":             (18000, 17550),
 "h IAS 37 decommissioning":         (  900,   760),
 "i IAS 21 CTD reset":               (    0,     0),
}
op, cl = sum(v[0] for v in adj.values()), sum(v[1] for v in adj.values())
dt_op, dt_cl = -TAX*op, -TAX*cl
pg_eq_op, pg_eq_cl = 210000, 232400
ifrs_eq_op, ifrs_eq_cl = pg_eq_op+op+dt_op, pg_eq_cl+cl+dt_cl
DIV, ISSUE = 9000, 5000
pg_tci   = (pg_eq_cl-pg_eq_op)     + DIV - ISSUE
ifrs_tci = (ifrs_eq_cl-ifrs_eq_op) + DIV - ISSUE
mv_pre = sum(v[1]-v[0] for v in adj.values())
OCI_PRE = 1000                       # IAS 19 remeasurement
pl_pre  = mv_pre - OCI_PRE
pl_net, oci_net = pl_pre-TAX*pl_pre, OCI_PRE-TAX*OCI_PRE
pg_pl, pg_oci = 24900, 1500
assert pg_pl + pg_oci == pg_tci
assert pl_net + oci_net == ifrs_tci - pg_tci
assert ifrs_eq_op + (pg_pl+pl_net) + (pg_oci+oci_net) - DIV + ISSUE == ifrs_eq_cl
```

```
pre-tax adj  1 Jan 2025 : 4500   deferred tax: -1125.0   net: 3375.0
pre-tax adj 31 Dec 2025 : 5260   deferred tax: -1315.0   net: 3945.0
IFRS equity  1 Jan 2025 : 213375.0
IFRS equity 31 Dec 2025 : 236345.0
prev-GAAP TCI FY2025    : 26400
IFRS TCI FY2025         : 26970.0    difference: 570.0
FY2025 pre-tax movement : 760    tax: -190.0   net: 570.0
P&L effect  net of tax  : -180.0
OCI effect  net of tax  : 750.0
sum == TCI difference   : True
prev-GAAP  PL/OCI/TCI   : 24900  1500  26400
IFRS       PL/OCI/TCI   : 24720.0  2250.0  26970.0
roll-forward check      : 236345.0 == closing IFRS equity  True
```

**All three assertions pass. The reconciliations reconcile.**

---

## 9. Common Pitfalls and Lessons Learned

The following issues recur frequently in IFRS transition projects. Awareness of these pitfalls can help entities avoid delays, cost overruns, and audit complications.

1. **Underestimating lease data collection effort (IFRS 16)** — Gathering complete, accurate lease data (commencement dates, payment schedules, renewal options, discount rates) across all business units and jurisdictions is consistently the most time-consuming data collection exercise. Entities with hundreds or thousands of leases should begin data collection at the very start of Phase 1.

2. **Failing to engage auditors early on the opening balance sheet** — The opening IFRS balance sheet is audited as part of the first IFRS financial statements. Disagreements with auditors on accounting policy choices, exemption elections, or significant estimates discovered late in the process can force rework and delay publication. Engage auditors during Phase 1 and seek their input on key judgements before finalising the opening balance sheet.

3. **Not documenting IFRS 1 exemption elections and rationale** — Every exemption election (and decision not to elect) should be formally documented with the rationale, quantitative impact, and steering committee approval. Incomplete documentation creates audit issues and regulatory risk.

4. **Insufficient parallel reporting period** — Entities that skip or shorten the parallel (dual) reporting period frequently discover errors and process gaps too late to correct them without significant effort. A full year of parallel reporting is strongly recommended.

5. **Underestimating the deferred tax complexity** — The deferred tax impact of IFRS transition adjustments is often material and complex (see Section 4). Entities that treat deferred tax as a "clean-up" exercise at the end of the transition frequently find it is one of the largest single adjustments to opening retained earnings. The **B14** override on leases and decommissioning is the item most often missed.

6. **Not training operational staff who provide underlying data** — Finance teams receive IFRS training, but operational staff (procurement, sales, HR, treasury) who provide the underlying data often do not. This leads to incomplete or incorrect data inputs, particularly for IFRS 16 lease data, IFRS 15 contract terms, and IFRS 9 credit risk information.

7. **Leaving disclosure preparation to the last minute** — IFRS disclosure requirements are significantly more extensive than many local GAAP frameworks. First-time adoption disclosures (IFRS 1 reconciliations, explanations of material adjustments, exemption elections) add further volume. Disclosure drafting should begin during Phase 2, not left to Phase 3.

8. **Missing the hedge documentation deadline (B4–B6)** — Hedge relationships cannot be designated retrospectively. Every continuing hedge must be designated and documented under IFRS 9 **on or before the date of transition**. This is the only transition step with no remedy at any cost, and it is the most common failure in treasury.

9. **Relying on an employee benefits exemption that no longer exists** — D10–D11 were deleted in 2011. Any project plan or checklist that assumes cumulative actuarial gains and losses can be reset to zero is planning for relief that is not available, and will discover a material unrelieved adjustment late.

---

## 10. Transitioning to IFRS 18 (Distinct from First-Time Adoption)

**IFRS 18 *Presentation and Disclosure in Financial Statements*** — issued **9 April 2024**; effective for annual reporting periods beginning on or after **1 January 2027**; **earlier application permitted** with disclosure of that fact (**IFRS 18.C1**). EU-endorsed **13 February 2026**, published in the Official Journal **16 February 2026**; UK-adopted 10 December 2025. It **supersedes IAS 1** (**IFRS 18.C8**).

This is **not** first-time adoption. IFRS 1 does not apply to an entity that already reports under IFRS (paragraph 5) — a change in a presentation standard is a **change in accounting policy under IAS 8**. For most existing IFRS preparers this is the transition actually in front of them right now, and its mechanics are entirely different from those in the rest of this guide.

> **First-time adopters take note:** an entity whose **first IFRS reporting date is 31 December 2027 or later** must apply IFRS 18 in its opening IFRS statement of financial position and throughout all periods presented (IFRS 1 paragraphs 7 and 8), even though the date of transition falls before 1 January 2027. Build the chart of accounts and financial statement templates to **IFRS 18**, not IAS 1. IFRS 1 has already been conformed: paragraph **32(za)** requires the IFRS 18 headings and subtotals in condensed interims, and paragraphs 21, 22, 24(a)(ii), 33 and D30 now cross-refer to IFRS 18.

### The transition requirements (IFRS 18 Appendix C)

| Ref | Requirement |
|---|---|
| **C2** | Apply IFRS 18 **retrospectively** in accordance with IAS 8. **Relief:** the entity is **not required to present the quantitative information specified in IAS 8.28(f)** — the standard third-party quantitative disclosure of the effect of a new standard on each line item for the current and prior periods. Entities applying **IFRS 19** are not required to present the equivalent information under IFRS 19.178(f). |
| **C3** | In the **annual** financial statements, for the **comparative period immediately preceding** the period of first application, disclose a reconciliation **for each line item in the statement of profit or loss** between (a) the restated amounts under IFRS 18 and (b) the amounts previously presented under IAS 1. |
| **C4** | Where IAS 34 condensed interim financial statements are prepared in the **first year of application**, present **each heading the entity expects to use** and the **subtotals required by IFRS 18.69–74**, **despite IAS 34.10**. The IAS 34.10 relief for headings and subtotals in condensed interims is **not available until the first annual IFRS 18 financial statements have been issued**. |
| **C5** | Where IAS 34 interim financial statements are prepared in the first year of application, disclose — as part of the information required by **IAS 34.16A(a)** — reconciliations **for each line item presented in the statement of profit or loss** for the comparative periods immediately preceding **both the current interim period and the cumulative year-to-date period**, between the restated amounts under IFRS 18 and the amounts previously presented under IAS 1. IFRS 19 reporters disclose the equivalent under IFRS 19.246(a). |
| **C6** | Disclosure of the C3 and C5 reconciliations for the **current period or earlier comparative periods** is **permitted but not required**. |
| **C7** | At the date of initial application, an entity eligible to apply **IAS 28.18** is permitted to **change its election** for measuring an investment in an associate or joint venture **from the equity method to fair value through profit or loss** under IFRS 9. Any such change is applied **retrospectively** under IAS 8, and an entity applying **IAS 27.11** must make the same change in its separate financial statements. |

### What this means in practice

1. **Comparatives are restated in full.** There is no modified retrospective or cumulative-catch-up option. The comparative statement of profit or loss must be rebuilt under IFRS 18's categories and subtotals. For a calendar-year entity adopting on 1 January 2027, that means **FY2026 must be captured in IFRS 18 form as it happens** — the practical deadline is the start of the 2026 comparative year, not 2027.

2. **The relief granted is narrow and the relief demanded is not.** The only real relief is C2's waiver of the IAS 8.28(f) quantitative disclosure. In its place, C3 requires a **line-by-line reconciliation of the entire comparative statement of profit or loss**, and C5 requires the same at every interim date in the first year, for both the current interim and the year-to-date comparative. Net, the disclosure burden is **higher** than a standard IAS 8 change, not lower.

3. **The interim requirement bites first.** C4 and C5 apply to interim reports in the first year of application. A calendar-year entity's first IFRS 18 deliverable is its **H1 2027 (or Q1 2027) interim report**, and it must already carry the full IFRS 18 heading and subtotal structure plus the line-by-line comparative reconciliation. This is typically **nine to twelve months** before the first annual IFRS 18 financial statements.

4. **C7 is a one-time strategic window that is easy to miss.** The date of initial application of IFRS 18 is the **only** opportunity to switch an eligible associate or joint venture from the equity method to FVTPL without a further IAS 8 justification. Entities holding venture capital, mutual fund or unit trust structures should evaluate this deliberately rather than discovering it afterwards. Note the related **Amendments to the Fair Value Option in IAS 28** — issued **26 June 2026**, which the IASB states **take effect when a company first applies IFRS 18** (1 January 2027 on the mandatory date; earlier where IFRS 18 is adopted early). They are **not yet EU-endorsed**, so an entity reporting under *IFRS as adopted by the EU* may face the first mandatory IFRS 18 year without the clarification. Assess them alongside C7.

5. **Management-defined performance measures move inside the audited financial statements.** IFRS 18 requires disclosure of MPMs in the notes, with a reconciliation to the most directly comparable IFRS subtotal. Non-GAAP measures previously living only in the front half of the annual report and in investor presentations become **audited note disclosure**. Inventory the entity's existing alternative performance measures during planning, decide which meet the MPM definition, and confirm each one can be reconciled and audited **before** the comparative year begins.

6. **The consequential amendments matter.** IFRS 18's Appendix D amends other standards, applicable for annual periods beginning on or after 1 January 2027 (or earlier if IFRS 18 is applied early). The material ones for a transition project are **IAS 7** (the operating profit starting point for the indirect method), **IAS 33**, **IAS 34**, and the renaming of **IAS 8** to *Basis of Preparation of Financial Statements*.

### Sequencing against a first-time adoption project

| Entity | Position | Action |
|---|---|---|
| First IFRS reporting date **31 December 2026** | IFRS 18 not yet effective at that date; IAS 1 applies unless IFRS 18 is early adopted | Consider **early adopting IFRS 18** (permitted, C1) to avoid two presentation changes in consecutive years. If not, plan an IAS 8 change of policy for FY2027 with C3/C5 reconciliations against the newly published IFRS comparatives. |
| First IFRS reporting date **31 December 2027 or later** | IFRS 18 is effective at the first IFRS reporting date | **IFRS 18 applies to the opening IFRS statement of financial position and all periods presented** (IFRS 1.7–8). IFRS 18 Appendix C is **not** applied — the entity is a first-time adopter, so IFRS 1 governs, and the C3/C5 IAS 1 comparative reconciliations are irrelevant because there are no IAS 1 IFRS comparatives. Build once, to IFRS 18. |
| Existing IFRS preparer | IFRS 18 is an IAS 8 change of policy | Apply IFRS 18 Appendix C in full. Capture the comparative year in IFRS 18 form as it happens. |

---

## Quick Reference: Related Skill Files

| File | Use For |
|---|---|
| `workflows.md` | IFRS 1 first-time adoption step-by-step workflow |
| `compliance-templates.md` | Gap analysis template, disclosure checklists |
| `standards-reference.md` | Detailed standard-by-standard guidance (IFRS 9, 15, 16, IAS 19, 36, 37, 38, etc.) |

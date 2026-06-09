# IFRS Standards Reference

## How to Use This File

Search for the specific standard number (e.g., "IFRS 15" or "IAS 36") rather than reading the entire file. Each standard follows a consistent format: scope, core principle, key rules, disclosure requirements, common pitfalls, and related standards.

---

---
## IFRS 1 — First-time Adoption of International Financial Reporting Standards

**Scope:** Applies to an entity preparing its first IFRS financial statements — i.e., the first annual financial statements in which the entity explicitly and unreservedly states compliance with IFRS. Also applies to interim financial reports presented under IAS 34 that cover part of the period covered by those first IFRS financial statements. Does not apply to entities that previously applied IFRS, discontinued, and are resuming (unless the gap was less than one full annual period).

**Core principle:** A first-time adopter must prepare an opening IFRS statement of financial position at the date of transition (the beginning of the earliest comparative period presented) and, in general, apply all IFRS effective at the end of its first IFRS reporting period retrospectively to that opening balance sheet.

**Key rules:**
- **Date of transition:** The beginning of the earliest comparative period presented in the first IFRS financial statements. For example, if the first IFRS financial statements cover the year ended 31 December 2025 with one comparative year, the transition date is 1 January 2024.
- **Mandatory exceptions (retrospective application is prohibited):**
  - Estimates — IFRS estimates at transition date must be consistent with estimates made under previous GAAP at that date (unless there is objective evidence of error)
  - Derecognition of financial assets and liabilities — assets/liabilities derecognised under previous GAAP before the transition date are generally not reinstated
  - Hedge accounting — hedge relationships that did not qualify under IFRS 9 cannot be retrospectively designated
  - Non-controlling interests — specific requirements under IFRS 10
  - Classification and measurement of financial instruments — assessed based on facts and circumstances at transition date
- **Optional exemptions (elections available to ease transition):**
  - Business combinations — can elect not to restate combinations before the transition date (IFRS 3 exemption)
  - Deemed cost — can use fair value, a revaluation, or a previous GAAP carrying amount as deemed cost for PP&E, investment property (if using cost model), or intangible assets at transition date
  - Leases — can apply IFRS 16 at transition date without restating comparatives (modified retrospective approach)
  - Employee benefits — can recognise all cumulative actuarial gains/losses at transition date (corridor method elimination)
  - Cumulative translation differences — can reset cumulative FX differences to zero at transition date
  - Share-based payments — need not apply IFRS 2 to equity instruments granted before 7 November 2002, or vested before transition date
  - Insurance contracts — limited exemption; largely replaced by IFRS 17 transition provisions
  - Fair value measurement of financial instruments — can designate financial assets/liabilities at FVTPL at transition date
- **Reconciliations required:**
  - Equity at transition date and at the end of the last period under previous GAAP
  - Total comprehensive income for the last period under previous GAAP
  - Cash flows if material differences exist
- **Impairment:** Must apply IAS 36 impairment indicators at the transition date; any resulting impairment is recognised in retained earnings or OCI as appropriate.

**Disclosure requirements:**
- Explanation of how the transition affected financial position, financial performance, and cash flows
- Reconciliation of equity (transition date and end of last previous GAAP period)
- Reconciliation of total comprehensive income for the last period
- Explanation of material adjustments to the cash flow statement
- If the entity recognised or reversed impairment losses for the first time, the disclosures required by IAS 36
- For deemed cost elections: aggregate of fair values used and aggregate adjustment to carrying amounts
- Description of each voluntary exemption applied and the basis

**Common pitfalls:**
- Failing to identify the correct transition date, particularly where comparative periods extend further back than expected
- Applying estimates with hindsight — IFRS 1 prohibits using information available after the transition date to revise estimates
- Overlooking mandatory exceptions while focusing on elective exemptions
- Inconsistent application of opening balance sheet adjustments between equity reconciliation and the actual opening balance sheet
- Not restating deferred tax for all temporary differences arising on transition
- Misclassifying financial instruments by applying IFRS 9 criteria based on current facts rather than facts at transition date

**Related standards:** IFRS 3 (business combinations exemption), IFRS 9 (financial instruments classification at transition), IFRS 16 (lease transition), IFRS 17 (insurance contracts transition), IAS 12 (deferred tax on transition adjustments), IAS 19 (employee benefits exemption), IAS 21 (FX translation differences exemption), IAS 36 (impairment at transition), IAS 38 (intangibles deemed cost), IAS 39 (superseded; relevant for historical comparison)

---

## IFRS 2 — Share-based Payment

**Scope:** Applies to all share-based payment transactions in which an entity receives goods or services, including:
- Equity-settled share-based payments
- Cash-settled share-based payments
- Transactions with a choice of settlement (equity or cash)
Excludes: business combinations (IFRS 3), interests in subsidiaries/joint ventures/associates acquired in share-based transactions. Also excludes transactions within the scope of IAS 32/IFRS 9 where the entity acquires financial instruments (rather than goods or services).

**Core principle:** An entity must recognise the goods or services received in a share-based payment transaction when the goods are obtained or as the services are received, with a corresponding increase in equity (equity-settled) or a liability (cash-settled), measured at the fair value of those goods or services, or, if that fair value cannot be reliably estimated, at the fair value of the equity instruments granted.

**Key rules:**
- **Equity-settled transactions:**
  - Measured at the **grant date fair value** of the equity instruments granted; this amount is never subsequently remeasured
  - Fair value determined using an option pricing model (Black-Scholes, binomial/lattice model) considering: exercise price, expected life, current share price, expected volatility, expected dividends, and risk-free interest rate
  - If goods/services received from non-employees: measured at fair value of goods/services unless that cannot be reliably estimated, in which case use equity instrument fair value at the date of receipt
  - Recognised over the **vesting period** (from grant date to vesting date); expensed on a straight-line basis unless a different attribution is more appropriate
  - **Vesting conditions:**
    - *Service conditions*: reflected in the number of equity instruments expected to vest; estimate revised each period
    - *Performance conditions (market-based)*: e.g., TSR — incorporated into grant date fair value; not revised for actual outcome
    - *Performance conditions (non-market)*: e.g., EPS targets — reflected in the number expected to vest; revised each period
    - *Non-vesting conditions*: incorporated into grant date fair value measurement; not revised
  - On vesting: no adjustment if actual instruments differ from those expected (except for service and non-market performance conditions)
  - **Modifications:** If the modification increases the fair value or number of instruments, recognise the incremental fair value over the remaining vesting period. Never reduce the minimum cumulative expense to below the original grant date fair value.
  - **Cancellations and settlements:** Treat as vesting — accelerate recognition of remaining expense. Any payment to employee on cancellation up to the fair value of the instruments is a deduction from equity; excess is an expense.
- **Cash-settled transactions:**
  - Recognise a liability measured at the **fair value of the liability** at each reporting date and at settlement date
  - Remeasure at each reporting date; changes in fair value recognised in profit or loss
  - Common example: share appreciation rights (SARs), phantom shares
- **Transactions with choice of settlement:**
  - If the *counterparty* has the choice: contains a debt component (present value of cash alternative) and an equity component (residual)
  - If the *entity* has the choice: account as cash-settled unless the entity has a past practice or stated policy of settling in equity, or the cash alternative has no commercial substance
- **Group share-based payment arrangements:**
  - The entity receiving goods or services accounts for the arrangement based on whether its own obligation is equity-settled or cash-settled
  - The entity settling the award accounts for it accordingly (may differ from the receiving entity's classification)

**Disclosure requirements:**
- Nature and extent: description of each type of arrangement, number and weighted-average exercise prices of options (granted, exercised, forfeited, expired, outstanding, exercisable)
- Fair value information: method, weighted-average assumptions used in the valuation model
- Effect on profit or loss and financial position: total expense recognised, liabilities at period-end and intrinsic value of vested liabilities
- For equity-settled: total carrying amount in equity
- IFRIC 11 (Group and Treasury Share Transactions) — superseded but embedded in IFRS 2 amendments (2009)

**Common pitfalls:**
- Remeasuring equity-settled awards after grant date (prohibited — only the number is revised, not fair value)
- Incorrectly classifying cash-settled versus equity-settled in group arrangements
- Failing to recognise an expense when vesting conditions are not met due to market conditions (market-based conditions are embedded in fair value — expense is recognised regardless of whether target is met)
- Underestimating the complexity of modifications — incremental value must be measured on the modification date
- Ignoring non-vesting conditions in the fair value model
- Using intrinsic value instead of fair value when a valuation model is practicable

**Related standards:** IFRS 3 (business combinations exclusion), IFRS 9 / IAS 32 (financial instruments exclusion), IAS 12 (deferred tax on share-based payments — temporary difference arises when tax deduction differs from cumulative IFRS 2 expense), IFRIC 11 (incorporated into IFRS 2 for group arrangements)

---

## IFRS 3 — Business Combinations

**Scope:** Applies to transactions that meet the definition of a business combination — transactions in which an acquirer obtains control of one or more businesses. A **business** is an integrated set of activities and assets capable of being conducted and managed to provide a return to investors or other owners, members, or participants. Excludes: formation of joint arrangements (IFRS 11), combinations of entities under common control (no current IFRS; typically policy applied by analogy), acquisition of an asset or group of assets that does not constitute a business.

**Core principle:** All business combinations are accounted for using the **acquisition method**. On the acquisition date, the acquirer recognises and measures the identifiable assets acquired, liabilities assumed, and any non-controlling interest (NCI) in the acquiree, and recognises goodwill or a gain from a bargain purchase.

**Key rules:**
- **Identifying the acquirer:** The entity that obtains control (IFRS 10 definition of control); the acquirer is usually the entity that transfers cash/other assets, issues equity, or is larger. In reverse acquisitions, the legal subsidiary may be the accounting acquirer.
- **Acquisition date:** The date on which the acquirer obtains control.
- **Recognition and measurement of identifiable assets and liabilities:**
  - Measured at **fair value** at the acquisition date
  - Identifiable intangibles must be recognised separately from goodwill if they arise from contractual/legal rights or are separable — even if not previously recognised by the acquiree (e.g., customer relationships, trade names, in-process R&D)
  - Contingent liabilities assumed: recognised at fair value if a present obligation exists, regardless of probability — unlike IAS 37
  - Operating leases: acquiree's favourable/unfavourable contracts recognised as intangible assets/liabilities; acquirer's own right-of-use assets and lease liabilities recognised under IFRS 16
  - Deferred tax: recognised per IAS 12 on temporary differences arising from fair value adjustments
- **Non-controlling interests (NCI):**
  - Option 1 (full goodwill / fair value method): NCI measured at fair value — results in full goodwill including the NCI's share
  - Option 2 (partial goodwill / proportionate share method): NCI measured at proportionate share of identifiable net assets — results in goodwill attributable to the acquirer only
  - Election is available on a transaction-by-transaction basis
- **Goodwill:**
  - Goodwill = Consideration transferred + NCI + FV of previously held interest − FV of identifiable net assets
  - Not amortised; subject to annual impairment testing under IAS 36 (cash-generating unit level)
  - Negative goodwill (bargain purchase): reassess identification and measurement, then recognise the gain immediately in profit or loss
- **Consideration transferred:**
  - Measured at fair value at acquisition date
  - Includes cash, other assets, equity instruments issued, contingent consideration
  - **Contingent consideration:** Recognised at fair value at acquisition date; subsequent changes in liability (financial liability) recognised in P&L; equity-classified contingent consideration is not remeasured
- **Previously held interest (step acquisitions):**
  - Remeasured to fair value at the acquisition date; gain or loss recognised in P&L
- **Transaction costs:** Expensed as incurred (not added to goodwill)
- **Measurement period:** Up to 12 months from acquisition date to finalise provisional fair values; adjustments made retrospectively to acquisition date amounts, with corresponding goodwill adjustment
- **Post-acquisition accounting for contingent liabilities:** Measured at the higher of IAS 37 amount and initial recognised amount (less cumulative amortisation per IFRS 15)
- **Common control transactions:** Not in scope; entities typically apply predecessor value method or a pooling-of-interests approach by analogy

**Disclosure requirements:**
- Name and description of acquiree, acquisition date, percentage of voting equity acquired
- Primary reasons for the combination and description of how control was obtained
- Fair values of consideration transferred (each class), NCI, previously held equity interests
- Amounts recognised for each major class of assets and liabilities at acquisition date
- Contingent consideration: description, basis for measurement, range of outcomes
- Goodwill amount and reasons why the acquisition resulted in goodwill (or bargain purchase explanation)
- Revenue and profit/loss of the combined entity for the current period as if acquisition date had been the beginning of the annual reporting period (pro-forma information)
- Subsequent adjustments to provisional amounts during the measurement period

**Common pitfalls:**
- Failing to identify and separately value intangible assets (particularly customer relationships and technology)
- Expensing acquisition-related costs but then capitalising post-acquisition integration costs that should also be expensed
- Incorrect treatment of contingent consideration — reclassification between liability and equity after initial recognition is not permitted
- Using the wrong NCI measurement method inconsistently (note: choice is per transaction)
- Misidentifying whether a transaction is a business combination or an asset acquisition (significant impact: no goodwill, no deferred tax gross-up in asset acquisitions)
- Overlooking the 12-month measurement period discipline — adjustments after the period close are taken to P&L
- Step acquisitions: forgetting to remeasure previously held interests to fair value

**Related standards:** IFRS 10 (control definition), IFRS 11 (joint arrangements — excluded), IFRS 13 (fair value measurement), IFRS 16 (lease accounting in acquisitions), IAS 12 (deferred tax on acquisition), IAS 36 (goodwill impairment), IAS 37 (contingent liabilities — modified criteria under IFRS 3), IAS 38 (intangible assets recognition in acquisitions)

---

## IFRS 5 — Non-current Assets Held for Sale and Discontinued Operations

**Scope:** Applies to accounting for non-current assets (or disposal groups) held for sale and to the presentation and disclosure of discontinued operations. A **disposal group** is a group of assets to be disposed of together (and directly associated liabilities). Excludes from the measurement requirements (but not presentation): deferred tax assets (IAS 12), employee benefit assets (IAS 19), financial assets within scope of IFRS 9, investment property measured at fair value (IAS 40), biological assets at fair value less costs to sell (IAS 41), and contractual rights under insurance contracts (IFRS 17).

**Core principle:** Non-current assets (or disposal groups) that are classified as held for sale are measured at the **lower of carrying amount and fair value less costs to sell**, and are no longer depreciated. They are presented separately in the statement of financial position. Results of discontinued operations are presented separately in the income statement.

**Key rules:**
- **Classification as held for sale — ALL of the following criteria must be met:**
  1. The asset must be available for immediate sale in its present condition (subject only to terms that are usual and customary for sales of such assets)
  2. The sale must be highly probable:
     - Management (appropriate level) is committed to a plan to sell
     - Active programme to locate a buyer has been initiated
     - Asset is actively marketed at a price reasonable in relation to its current fair value
     - Sale expected to be completed within **12 months** from classification date
     - It is unlikely that the plan will be significantly changed or withdrawn
  - Extension beyond 12 months is permitted only in limited circumstances beyond the entity's control (e.g., buyer requires regulatory approval, unusual market conditions), provided the entity remains committed
- **Measurement:**
  - Reclassify to held for sale at lower of: (a) carrying amount immediately before reclassification (apply applicable IFRS up to that point) and (b) fair value less costs to sell (FVLCTS)
  - Any write-down to FVLCTS is an impairment loss recognised in P&L
  - Subsequent increases in FVLCTS are recognised as gains (not exceeding cumulative impairment losses)
  - **No depreciation or amortisation** from the date of held-for-sale classification
  - Deferred tax and pension liabilities in a disposal group are measured per their own standards; the shortfall (if FVLCTS < net assets excluding scoped-out items) is allocated against the carrying amounts of non-current assets in scope, in the order: goodwill first, then pro-rata to remaining non-current assets
- **Discontinued operation:** A component of an entity that:
  - Has been disposed of or classified as held for sale, AND
  - Represents either a separate major line of business or geographical area, is part of a single co-ordinated plan to dispose of such a line/area, OR is a subsidiary acquired exclusively with a view to resale
  - A component is operations and cash flows that can be clearly distinguished, operationally and for financial reporting purposes, from the rest of the entity
- **Presentation:**
  - Non-current assets held for sale: presented separately in current assets (not reclassified in comparatives unless required by IAS 1)
  - Liabilities of disposal group: presented separately in current liabilities
  - Discontinued operations: single line in P&L for post-tax profit/loss from discontinued operations + post-tax gain/loss on measurement or disposal (detailed breakdown in notes or on the face)
  - Cash flows from discontinued operations: disclosed separately (either on face or in notes)
  - Comparatives for income statement and cash flows are restated to show discontinued operations separately
- **Assets no longer classified as held for sale:** Remeasured at lower of (a) carrying amount before classification (adjusted for depreciation that would have been recognised) and (b) recoverable amount; any adjustment recognised in P&L from continuing operations

**Disclosure requirements:**
- Description of the non-current asset or disposal group
- Description of the facts and circumstances of the sale (or expected sale) and the expected manner and timing of disposal
- Gain or loss recognised and the line item in P&L where it is included (if not separately presented)
- Segment in which the asset/disposal group is reported (IFRS 8)
- For discontinued operations: revenue, expenses, pre-tax profit/loss, income tax, gain/loss on disposal, related tax — either on face or in notes
- Cash flow information for discontinued operations
- If classification criteria are no longer met: description of facts and circumstances leading to the decision and the effect on results

**Common pitfalls:**
- Premature classification — the 12-month criterion and commitment criteria must all be met simultaneously; intent alone is insufficient
- Continuing to depreciate assets after held-for-sale classification
- Misidentifying a discontinued operation — cessation of a product line that is not a separate major line of business does not qualify
- Failing to restate comparative income statement and cash flow information for discontinued operations
- Incorrectly applying the measurement hierarchy when scoped-out items (e.g., deferred tax) cause the disposal group to appear loss-making
- Not recognising impairment when FVLCTS falls below carrying amount

**Related standards:** IFRS 3 (disposal in step-down transactions), IFRS 8 (segment reporting of disposal groups), IFRS 13 (fair value measurement), IAS 12 (deferred tax in disposal groups), IAS 16 (PP&E — depreciation ceases), IAS 36 (impairment testing before reclassification), IAS 37 (provisions on disposal)

---

## IFRS 6 — Exploration for and Evaluation of Mineral Resources

**Scope:** Applies to exploration and evaluation (E&E) expenditures — those incurred after an entity has obtained legal rights to explore in a specific area but before the technical feasibility and commercial viability of extracting a mineral resource is demonstrable. Does not apply to: expenditures incurred before obtaining legal rights (pre-licence costs — expensed under IAS 38/Conceptual Framework), expenditures after technical feasibility and commercial viability are demonstrable (development phase — IAS 16/IAS 38 apply). Note: IFRS 6 is an interim standard — the IASB acknowledges it defers a comprehensive treatment of extractive industries.

**Core principle:** An entity may develop an accounting policy for E&E expenditures that results in information that is relevant and reliable; the standard provides a temporary exemption from fully applying the Conceptual Framework's recognition criteria, allowing entities to continue using policies that were acceptable under previous GAAP.

**Key rules:**
- **Recognition:** An entity must determine its own accounting policy for which E&E expenditures are capitalised as E&E assets. The policy must be consistent; once expenditures are capitalised, the entity cannot expense them in a later period without evidence of impairment.
  - Costs that may be included: acquisition of rights to explore, topographical/geological/geochemical surveys, exploratory drilling, trenching, sampling, activities related to evaluating technical feasibility and commercial viability
  - Costs that cannot be included: administrative and general overhead not directly attributable to E&E activity
- **Classification:** E&E assets are classified as tangible (e.g., drilling rigs, vehicles) or intangible (e.g., drilling rights, licences). Classification is applied consistently.
- **Measurement after recognition:**
  - Cost model: cost less accumulated amortisation and impairment
  - Revaluation model: permitted if the applicable IAS (IAS 16 for tangible, IAS 38 for intangible) permits it for that asset class
- **Reclassification:** When technical feasibility and commercial viability are demonstrable, E&E assets are reclassified out of IFRS 6 and into development assets (IAS 16 / IAS 38). Test for impairment immediately before reclassification.
- **Impairment:** IFRS 6 provides a modified impairment test:
  - Indicators (not exhaustive): the licence period is expiring and renewal is not expected; no substantive further E&E planned for the area; the decision to discontinue E&E and the asset does not meet the held-for-sale criteria; evidence that carrying amount will not be recovered from successful development or sale
  - Level of aggregation: E&E assets may be grouped for impairment testing into cash-generating units no larger than an operating segment
  - Once an impairment indicator exists, the entity must determine recoverable amount per IAS 36 and recognise any impairment loss; the modified IAS 36 approach does not alter the measurement of impairment

**Disclosure requirements:**
- Accounting policies for E&E expenditures, including the basis on which assets are recognised
- Amounts of E&E assets capitalised and treated as expense during the period
- Amounts arising from exploration and evaluation: in the income statement, and in the statement of financial position (with E&E assets identified separately from other assets)
- Information that identifies and explains amounts in the financial statements arising from E&E
- The level at which impairment is assessed

**Common pitfalls:**
- Capitalising pre-licence costs that must be expensed under the Conceptual Framework
- Continuing to carry E&E assets after technical feasibility is demonstrated without reclassifying under IAS 16 or IAS 38
- Applying an inconsistent capitalisation threshold across licences or regions
- Failing to perform the impairment trigger assessment when licences approach expiry or exploration plans are abandoned
- Using a CGU group larger than an operating segment for impairment testing (the IFRS 6 ceiling)
- Not disclosing the accounting policy for capitalisation clearly — regulators frequently challenge vague policies

**Related standards:** IAS 16 (PP&E — tangible E&E assets and development assets), IAS 36 (impairment — modified application under IFRS 6), IAS 37 (decommissioning obligations on E&E assets), IAS 38 (intangibles — applies post-reclassification), IFRS 5 (if E&E assets are classified as held for sale), IFRS 8 (operating segments — relevant for impairment CGU ceiling)

---

## IFRS 7 — Financial Instruments: Disclosures

**Scope:** Applies to all entities for all types of financial instruments, except: interests in subsidiaries, associates, and joint ventures accounted for under IFRS 10, 11, or IAS 28 (unless those standards require IFRS 7 disclosures or the interest is a financial instrument under IFRS 9); employers' rights and obligations from employee benefit plans (IAS 19); insurance contracts (IFRS 17) except financial guarantee contracts and investment components; financial instruments designated as hedging instruments and accounted for under IFRS 9; financial instruments that are equity instruments of the reporting entity.

**Core principle:** Entities must disclose information that enables users of financial statements to evaluate: (1) the significance of financial instruments for the entity's financial position and performance; and (2) the nature and extent of risks arising from financial instruments, and how the entity manages those risks.

**Key rules:**
- **Classes of financial instruments:** Disclosures are made by class — a grouping appropriate to the nature of the information and characteristics of the instruments. Entities must reconcile classes to line items in the statement of financial position.
- **Significance disclosures (Part A):**
  - **Statement of financial position:** carrying amounts by IFRS 9 category (amortised cost, FVOCI — debt, FVOCI — equity, FVTPL); net gains/losses by category
  - **Fair value:** For instruments not measured at fair value, disclose fair value if practicable; for all instruments measured at fair value, apply the three-level hierarchy (IFRS 13)
  - **Fair value hierarchy (IFRS 13 cross-reference):**
    - Level 1: Quoted prices in active markets for identical assets/liabilities
    - Level 2: Inputs other than Level 1 that are observable (directly or indirectly)
    - Level 3: Unobservable inputs — entity's own assumptions
    - Disclose transfers between Level 1 and Level 2; explain Level 3 movements with reconciliation
  - **Income statement and equity:** Interest income/expense; fee income/expense; impairment losses; gains/losses on derecognition
  - **Hedge accounting disclosures:**
    - Risk management strategy and how it relates to the hedging instrument
    - Hedging instruments: amounts, carrying values, line items in balance sheet, change in fair value
    - Hedged items: carrying amounts, accumulated OCI (cost of hedging reserve), change in value used for hedge effectiveness
    - Hedge effectiveness: sources of ineffectiveness, amounts of ineffectiveness in P&L, hedge ratio
    - Reconciliation of hedging reserve movements
  - **Credit risk:**
    - Maximum exposure, collateral and credit enhancements held
    - For financial assets at amortised cost and FVOCI (debt): gross carrying amount, loss allowance, credit quality analysis using credit risk grades
    - **ECL staging disclosures:**
      - Stage 1 (12-month ECL): amounts at each balance sheet date
      - Stage 2 (lifetime ECL — not credit-impaired): amounts
      - Stage 3 (lifetime ECL — credit-impaired): amounts, interest revenue using the net carrying amount
      - POCI (purchased or originated credit-impaired): separate disclosure
    - Reconciliation of gross carrying amounts and loss allowances (opening to closing)
    - Write-off policy, collateral and other credit enhancements obtained during the period
    - Modifications: how modified assets were assessed, carrying amount of assets modified while in Stage 2/3
    - Assumptions and inputs used in ECL models (including forward-looking information used)
  - **Liquidity risk:**
    - Maturity analysis of financial liabilities (including derivatives) showing contractual undiscounted cash flows
    - Description of how liquidity risk is managed
  - **Market risk:**
    - Sensitivity analysis for each type of market risk (interest rate, currency, equity price, commodity price): showing the effect on P&L and equity of a reasonably possible change
    - Alternatively: Value-at-Risk (VaR) analysis with specific disclosures about methodology and parameters
    - Concentrations of risk
  - **Capital disclosures (IAS 1 requirement cross-referenced):** Objectives, policies, and processes for managing capital

**Disclosure requirements:**
- Quantitative and qualitative disclosures for credit risk, liquidity risk, and market risk
- Fair value disclosures including the level hierarchy and any transfers between levels
- Collateral information — pledged as security and held as collateral
- Compound financial instruments with multiple embedded derivatives
- Defaults and breaches of loan agreements
- Financial assets transferred but not derecognised (e.g., securitisations, repo agreements): nature of continuing involvement, carrying amounts, associated liabilities
- Netting arrangements: gross amounts, amounts offset, net amounts

**Common pitfalls:**
- Inadequate description of ECL methodology — disclosures must explain forward-looking macroeconomic factors, not just state that they are used
- Omitting the reconciliation of loss allowances (movement table from opening to closing)
- Insufficient granularity in the maturity analysis for liquidity risk — using contractual maturities only, without also providing behavioural maturities where relevant
- Failing to disclose Level 3 sensitivity analysis or the valuation techniques for Level 3 instruments
- Boilerplate sensitivity analyses that do not reflect actual risk exposure
- Not disclosing concentrations of credit risk by geography, industry, or counterparty where material
- Overlooking disclosures for transferred financial assets (repos, securities lending, factoring with retained risk)

**Related standards:** IFRS 9 (measurement and recognition — IFRS 7 disclosures must mirror IFRS 9 categories), IFRS 13 (fair value measurement and hierarchy), IAS 1 (capital disclosures; presentation), IAS 32 (financial instrument definitions; offset criteria), IFRIC 16 (hedges of net investments — relevant for hedge disclosures)

---

## IFRS 8 — Operating Segments

**Scope:** Applies to the separate or consolidated financial statements of an entity whose debt or equity instruments are traded in a public market, or that files (or is in the process of filing) its financial statements with a securities commission or other regulatory organisation for the purpose of issuing any class of instrument in a public market. Parent entities that present consolidated financial statements apply IFRS 8 only at the consolidated level (not required for the separate financial statements). Entities that are not publicly accountable are encouraged but not required to apply IFRS 8.

**Core principle:** An entity must report financial and descriptive information about its reportable operating segments, based on internal information used by the chief operating decision maker (CODM) to allocate resources and assess performance — the **management approach**.

**Key rules:**
- **Operating segment definition:** A component of an entity that:
  1. Engages in business activities from which it may earn revenues and incur expenses
  2. Whose operating results are regularly reviewed by the CODM
  3. For which discrete financial information is available
  - A segment may be a single product/service line or encompass multiple products/services; start-up activities that have not yet earned revenues are still operating segments
- **CODM:** The function (not necessarily a single individual) that allocates resources and assesses segment performance — could be the CEO, executive committee, or board
- **Aggregation criteria:** Two or more operating segments may be aggregated into a single reportable segment if they have similar economic characteristics AND are similar in each of: nature of products/services, nature of production processes, type/class of customer, distribution methods, and regulatory environment
- **Quantitative thresholds:** A segment is reportable if ANY of the following applies:
  - Revenue (including intersegment): ≥ 10% of combined revenue of all operating segments
  - Reported profit or loss: absolute amount ≥ 10% of the greater of (a) combined profits of all profitable segments or (b) combined losses of all loss-making segments
  - Assets: ≥ 10% of combined assets of all operating segments
- **75% test:** The total external revenue attributable to reportable segments must be at least 75% of total external revenue. If not met, additional segments must be identified as reportable (even if below the 10% thresholds) until the 75% threshold is reached.
- **All other segments:** Remaining segments are combined and disclosed as "all other segments" — not a single reportable segment; revenue sources must be described
- **Practical maximum:** No specific maximum number of segments, but IFRS 8 notes that above approximately 10 segments, disclosures may become overly detailed
- **Measurement:** Segment information is reported on the basis used internally by the CODM — this may not conform to IFRS. Differences between segment totals and IFRS-compliant totals must be reconciled.
- **Restatement:** When the composition of segments changes, prior period comparatives must be restated unless the information is not available and cannot be reasonably determined; if not restated, disclose both old and new segment information in the year of change

**Disclosure requirements:**
- General information: factors used to identify operating segments, types of products/services in each segment
- Segment profit/loss, segment assets, segment liabilities (if regularly provided to CODM)
- Specific items if included in segment profit/loss or reviewed by CODM: revenue (external and intersegment), depreciation/amortisation, material items of income and expense (IAS 1.97), interest income and expense (separately, unless the CODM reviews net interest), income tax expense, significant non-cash items other than depreciation
- Basis of measurement for each reported segment measure
- **Reconciliations** (mandatory):
  - Total segment revenues to entity revenue
  - Total segment profit/loss to entity profit/loss before tax (and discontinued operations)
  - Total segment assets to entity assets
  - Total segment liabilities to entity liabilities (if segment liabilities reported)
  - Any other material segment items to corresponding entity amounts
- **Entity-wide disclosures** (required even for a single-segment entity):
  - Revenues from external customers: by product/service line
  - Revenues from external customers: by geographic area (country of domicile; any individual foreign country that is material)
  - Non-current assets: by geographic area (country of domicile; any individual material foreign country) — excludes financial instruments, deferred tax, post-employment benefit assets, and rights arising under insurance contracts
  - Information about major customers: if any single external customer accounts for ≥ 10% of revenue, disclose that fact, the revenue, and the segment reporting that revenue (not the customer identity)

**Common pitfalls:**
- Misidentifying the CODM — leads to incorrect segment identification; the CODM function is key, not the individual's title
- Aggregating segments that have different economic characteristics without sufficient justification
- Reporting segment information in a way that does not match what the CODM actually reviews — the management approach should be applied faithfully, not rationalised after the fact
- Failing to provide the 75% reconciliation test check before finalising the number of reportable segments
- Omitting entity-wide disclosures for a single-reportable-segment entity
- Not restating prior period comparatives when the segment structure changes
- Disclosing segment liabilities inconsistently — if regularly reviewed by CODM, they must be disclosed

**Related standards:** IAS 1 (material items of income and expense; capital management), IAS 36 (goodwill allocation to segments for impairment testing), IFRS 3 (business combinations may create new segments), IFRS 5 (discontinued operations and their interaction with segment disclosures)

---

## IFRS 9 — Financial Instruments

**Scope:** Applies to all financial instruments except: interests in subsidiaries, associates, and joint ventures (IFRS 10, 11, IAS 27, IAS 28 — unless designated at FVTPL for venture capital/similar entities); rights and obligations in leases (IFRS 16 — except for impairment of lease receivables and derecognition of lease liabilities); employee benefit plan rights and obligations (IAS 19); equity instruments issued by the entity (IAS 32); insurance contracts (IFRS 17 — except for certain financial guarantee contracts meeting the IFRS 9 definition, at issuer's election); certain loan commitments (not measured at FVTPL); financial instruments, contracts, and obligations under share-based payment transactions (IFRS 2). Applies to financial guarantee contracts and commitments to provide a loan at below-market interest rate.

**Core principle:** Financial instruments must be classified and measured on the basis of the entity's business model for managing financial assets and the cash flow characteristics of the financial asset. Impairment is based on expected (not incurred) credit losses. Hedge accounting may be applied when hedging relationships meet specified criteria and reflect the entity's risk management activities.

---

### Part A: Classification and Measurement

#### Financial Assets — Classification Decision Tree

**Step 1 — SPPI Test (Solely Payments of Principal and Interest):**

Assess whether the contractual cash flows are solely payments of principal and interest on the principal amount outstanding.
- **Principal:** fair value of the financial asset at initial recognition
- **Interest:** consideration for the time value of money, credit risk, other basic lending risks (e.g., liquidity risk), and a profit margin
- **Fails SPPI if:**
  - Cash flows are linked to an equity index or commodity price
  - Leverage in cash flows (e.g., inverse floater, leveraged interest rate)
  - Non-recourse features that significantly limit cash flows (depends on instrument; some non-recourse pass the SPPI test)
  - Prepayment or extension terms that are not symmetric and not solely compensation for early termination (unless the *de minimis* or *solely compensation* exception applies)
  - Contractually linked instruments (CLOs, CDOs) unless assessed using a look-through to the underlying pool and the pool itself passes SPPI
- **Modified time value of money:** If interest is reset periodically but the reset frequency does not match the tenor, assess whether the difference is *de minimis* or whether the instrument behaves like a basic lending arrangement (benchmark comparison)

**Step 2 — Business Model Test:**

Determine the business model in which the financial asset is held:

| Business Model | Description | Classification |
|---|---|---|
| Hold to collect | Objective is to collect contractual cash flows; sales are incidental | Amortised cost (if SPPI passes) |
| Hold to collect and sell | Objective is both collecting cash flows and selling assets | FVOCI — debt instrument (if SPPI passes) |
| Other / trading / residual | Objective is primarily to realise fair value gains; any other model | FVTPL (regardless of SPPI) |

- Business model is assessed at a portfolio/group level, not instrument-by-instrument
- Frequency, volume, and timing of past sales are considered; a single sale does not change the business model; a change of business model is rare and requires significant changes in operations
- **FVTPL designation (OCI election):** Even if SPPI passes and business model is hold-to-collect, an entity may designate a financial asset at FVTPL if doing so eliminates or significantly reduces an accounting mismatch — irrevocable at initial recognition
- **Equity instruments:** Cannot pass SPPI; always FVTPL unless irrevocably elected at initial recognition to measure at FVOCI (only for equity instruments that are not held for trading); FVOCI equity gains/losses are never recycled to P&L — only dividend income is recognised in P&L

#### Financial Assets — Measurement Summary

| Category | Initial measurement | Subsequent measurement | Impairment |
|---|---|---|---|
| Amortised cost | Fair value + directly attributable transaction costs | EIR method; foreign exchange gains/losses in P&L | ECL (3-stage model) |
| FVOCI — debt | Fair value + transaction costs | Fair value; changes in OCI; EIR, FX, and impairment in P&L | ECL in P&L; OCI balance is cumulative FV change less P&L items |
| FVTPL | Fair value (transaction costs expensed) | Fair value; all changes in P&L | No separate impairment |
| FVOCI — equity (irrevocable election) | Fair value + transaction costs | Fair value; changes in OCI (never recycled); dividends in P&L | No separate impairment |

#### Financial Liabilities — Classification

- **Default:** Amortised cost using EIR method
- **FVTPL (mandatory):** Held for trading (including derivatives that are liabilities); contingent consideration in a business combination (IFRS 3)
- **FVTPL (designated — Fair Value Option):** Permitted if: eliminates or significantly reduces accounting mismatch; financial liability is part of a group managed on a FV basis with a documented strategy; hybrid instrument with embedded derivative
  - **Own credit risk:** For FVO liabilities, changes in fair value attributable to the entity's own credit risk are presented in OCI (not P&L), unless this creates or enlarges an accounting mismatch — then all changes remain in P&L
- **Financial guarantee contracts:** Measured at higher of: (a) ECL amount under IAS 37 principles and (b) amount initially recognised less cumulative amortisation
- **Embedded derivatives:** Only separate from a host financial liability that is not measured at FVTPL if: (a) economic characteristics not closely related to host; (b) a separate instrument with the same terms would be a derivative; (c) host is not measured at FVTPL. For financial asset hosts — the whole instrument is assessed for SPPI; if fails SPPI it is FVTPL in its entirety.

---

### Part B: Impairment — Expected Credit Loss (ECL) Model

**Scope of ECL:** Applies to financial assets at amortised cost, financial assets at FVOCI (debt), lease receivables (IFRS 16), contract assets (IFRS 15), loan commitments not at FVTPL, and financial guarantee contracts.

#### The 3-Stage ECL Model

**Stage 1 — Performing (12-month ECL):**
- Apply to financial instruments where credit risk has **not significantly increased** since initial recognition (or where credit risk is low at reporting date)
- Recognise a loss allowance equal to **12-month ECL** — the portion of lifetime ECL from default events expected within 12 months of the reporting date
- Interest revenue: calculated on **gross carrying amount** (i.e., before deducting the loss allowance) using the EIR

**Stage 2 — Underperforming (Lifetime ECL — not credit-impaired):**
- Apply when credit risk has **significantly increased** since initial recognition but the asset is **not yet credit-impaired**
- Recognise **lifetime ECL** — expected credit losses from all possible default events over the expected life of the instrument
- Interest revenue: still calculated on **gross carrying amount**
- **Significant increase in credit risk (SICR):** Assessed based on change in risk of default (not change in loss given default or exposure):
  - Quantitative: change in PD (probability of default) — compare current lifetime PD to lifetime PD at origination
  - Qualitative indicators: significant deterioration in external credit ratings, past-due status (30 days past due = rebuttable presumption of SICR), watchlist, covenant breach, forbearance
  - Forward-looking information must be incorporated
  - **Low credit risk simplification:** If credit risk is low at the reporting date (e.g., investment-grade equivalent), entity may assume no SICR — remains in Stage 1

**Stage 3 — Credit-impaired (Lifetime ECL — credit-impaired):**
- Apply when the financial asset is **credit-impaired** — one or more events have had a detrimental impact on estimated future cash flows
- **Credit impairment indicators (objective evidence of impairment):**
  - Significant financial difficulty of issuer or borrower
  - Breach of contract (default or delinquency in interest/principal payments)
  - Lender granting a concession that would not otherwise be considered (forbearance/restructuring)
  - Probability that borrower will enter bankruptcy or financial reorganisation
  - Disappearance of an active market for the financial asset
  - Purchase or origination at a deep discount that reflects incurred credit losses (POCI)
- Recognise **lifetime ECL**
- Interest revenue: calculated on **net carrying amount** (gross carrying amount less loss allowance) using the EIR — net interest approach

**POCI (Purchased or Originated Credit-Impaired) Assets:**
- Credit-impaired at initial recognition
- Interest revenue calculated using a credit-adjusted EIR applied to the amortised cost (net of allowance)
- Only cumulative changes in lifetime ECL since initial recognition are recognised as a loss allowance (changes can be positive — loss allowance gain)
- Never migrates to Stage 1 or 2

#### ECL Measurement — Key Inputs

- **PD (Probability of Default):** Probability of default over the measurement horizon
- **LGD (Loss Given Default):** 1 minus the recovery rate; reflects collateral, security, and seniority
- **EAD (Exposure at Default):** Contractual cash flows outstanding at the time of default, including expected drawdowns on undrawn commitments
- **ECL = PD × LGD × EAD** (simplified; discounted at the original EIR or credit-adjusted EIR for POCI)
- **Forward-looking information:** ECL must reflect unbiased, probability-weighted information about past events, current conditions, and forecasts of future economic conditions. Entities must consider multiple economic scenarios; point-in-time PDs (not through-the-cycle)
- **Write-offs:** When there is no reasonable expectation of recovery; reduce gross carrying amount; may still pursue enforcement activity
- **Simplified approach (trade receivables, contract assets, lease receivables):**
  - Trade receivables and contract assets without a significant financing component: must use lifetime ECL from day 1 (no staging); typically implemented using a provision matrix
  - Trade receivables with a significant financing component, contract assets, and lease receivables: entity may elect to apply lifetime ECL from day 1 (optional simplification)

#### Interaction with Modification / Restructuring

- A modification that does not result in derecognition: recalculate gross carrying amount using modified cash flows discounted at original EIR; recognise modification gain/loss in P&L; reassess staging based on modified terms (30-day past due clock may reset; delinquency history used for SICR assessment continues)
- A modification resulting in derecognition: new financial asset recognised; if credit-impaired at origination, POCI treatment applies

---

### Part C: Hedge Accounting

**Overview:** Hedge accounting is a voluntary election that aligns the timing of gain/loss recognition in P&L for a hedging instrument with the hedged item. IFRS 9 hedge accounting more closely reflects risk management activities than IAS 39. Entities may also irrevocably elect to continue using IAS 39 hedge accounting (subject to removal on adoption of the IASB's macro hedge accounting project, when completed).

#### Qualifying Criteria (all must be met)

1. The hedging relationship consists only of eligible hedging instruments and eligible hedged items
2. Formal designation and documentation of the hedging relationship at inception: entity's risk management objective and strategy, type of hedge, identification of hedging instrument and hedged item, the hedged risk, and how effectiveness will be assessed
3. The hedging relationship meets all of the following effectiveness requirements:
   - Economic relationship exists between the hedging instrument and hedged item (both respond to the same risk)
   - Credit risk does not dominate the value changes from the economic relationship
   - The hedge ratio reflects the actual quantities used for risk management (not set to achieve an accounting outcome)

#### Eligible Hedging Instruments

- Derivatives measured at FVTPL (the most common)
- Non-derivative financial assets or liabilities at FVTPL, but only for currency risk hedges
- A proportion (not a time component alone) of a derivative may be designated
- Options: can designate intrinsic value only (time value excluded from designation and deferred in OCI as "cost of hedging") — avoids P&L volatility from time value decay; similarly, forward element of forward contracts and currency basis spread may be excluded

#### Eligible Hedged Items

- A recognised asset or liability
- An unrecognised firm commitment (except for foreign currency risk)
- A highly probable forecast transaction
- A net investment in a foreign operation (IAS 21)
- An aggregated exposure (a hedged item combined with a derivative)
- A group of items (if individually eligible); a net position may be designated only for foreign currency risk (with certain conditions)
- Portions: a risk component (if separately identifiable and reliably measurable), a nominal portion, a layer component of a hedged item

#### Types of Hedge Relationships

**Fair Value Hedge:**
- Hedges exposure to changes in fair value of a recognised asset/liability or firm commitment attributable to a particular risk
- **Accounting:** Changes in fair value of the hedging instrument are recognised in P&L; the carrying amount of the hedged item is adjusted for the gain/loss attributable to the hedged risk (fair value hedge adjustment) and that adjustment also recognised in P&L
- When the hedge is discontinued, any remaining fair value hedge adjustment on the hedged item (if it is a financial instrument at amortised cost) is amortised to P&L over the remaining life using the EIR

**Cash Flow Hedge:**
- Hedges exposure to variability in cash flows attributable to a particular risk associated with a recognised asset/liability or highly probable forecast transaction
- **Accounting:**
  - The effective portion of the gain/loss on the hedging instrument is recognised in OCI (the cash flow hedge reserve — CFHR)
  - The ineffective portion is recognised immediately in P&L
  - When the hedged forecast transaction occurs and affects P&L: reclassify the CFHR to P&L (recycling)
  - If the hedged item results in the recognition of a non-financial asset or liability: either reclassify when the asset/liability affects P&L, or include in the initial cost of the non-financial asset/liability (basis adjustment — applicable only for non-financial items; irrevocable election at inception)
  - If the forecast transaction is no longer expected to occur: reclassify CFHR to P&L immediately

**Net Investment Hedge:**
- Hedges the currency risk on a net investment in a foreign operation
- **Accounting:** Effective portion of the hedging instrument's gain/loss recognised in OCI (translation reserve); reclassified to P&L only on disposal or partial disposal of the foreign operation
- Can use monetary items (e.g., intercompany loans) or derivatives as hedging instruments; borrowing in the functional currency of the foreign operation also qualifies

#### Hedge Effectiveness Assessment

- Prospective: assess whether an economic relationship exists; done at inception and on an ongoing basis (at a minimum at each reporting date)
- Hedge ratio: must be the same as used for risk management; rebalancing required if the ratio changes
- Rebalancing: adjust quantities of hedging instrument or hedged item to restore required ratio; prior hedging relationship continues
- Discontinuation: mandatory only when the qualifying criteria are no longer met (in whole or in part); voluntary discontinuation is prohibited under IFRS 9 (unlike IAS 39)

#### IFRIC Interpretations Relevant to IFRS 9

- **IFRIC 16 — Hedges of a Net Investment in a Foreign Operation:** Clarifies (1) the nature of hedged risk (functional currency of subsidiary vs. presentation currency of parent); (2) which entity in a group can hold the hedging instrument; (3) how to determine amounts reclassified to P&L on disposal
- **IFRIC 19 — Extinguishing Financial Liabilities with Equity Instruments:** When equity instruments are issued to a creditor to extinguish a financial liability, the difference between carrying amount of liability extinguished and fair value of equity issued is recognised in P&L
- **IFRIC 10 — Interim Financial Reporting and Impairment:** Prohibits reversal of impairment losses on goodwill (and certain investments) recognised in an interim period; less relevant post-IFRS 9 ECL model but noted for completeness

---

**Disclosure requirements:**
- See IFRS 7 above — IFRS 7 contains all disclosure requirements for IFRS 9 instruments
- Specifically for IFRS 9 impairment: ECL methodology, assumptions, and inputs; staging movement tables; write-off and recovery policies; forward-looking information used
- Specifically for hedge accounting: see IFRS 7 hedge accounting disclosure requirements above

**Common pitfalls:**
- **Classification:** Applying SPPI at entity level rather than instrument level; failing to assess modified time value of money features; incorrectly treating equity investments as debt (e.g., preference shares with mandatory redemption)
- **Business model:** Using the wrong level of aggregation; changing classification based on a single sale rather than a genuine business model change; confusing intent (SPPI concern) with business model
- **ECL — SICR:** Using only backward-looking or lagging indicators; failing to incorporate macroeconomic forecasts; mechanically applying the 30-day presumption without considering lead indicators
- **ECL — forward-looking:** Single-scenario ECL that ignores non-linearity; using through-the-cycle PDs rather than point-in-time
- **ECL — staging:** Moving assets back to Stage 1 too quickly after cure; insufficient cure period evidence
- **ECL — provision matrix:** Using industry-average loss rates without adjustment for entity-specific and forward-looking factors
- **Hedge accounting — designation:** Hedging the benchmark rate component without meeting the separately identifiable and reliably measurable criteria; designating a net position for non-FX risks
- **Hedge accounting — discontinuation:** Voluntarily discontinuing to manage volatility (prohibited under IFRS 9)
- **Own credit risk on FVO liabilities:** Forgetting to present the own credit adjustment in OCI rather than P&L
- **Derecognition:** Failing to properly analyse pass-through arrangements and retained risks/rewards; partial derecognition errors in transfers

**Related standards:** IFRS 7 (all disclosures for financial instruments), IFRS 13 (fair value measurement), IFRS 15 (contract assets within ECL scope), IFRS 16 (lease receivables within ECL scope), IFRS 17 (insurance contracts — interaction with financial guarantee contracts), IAS 12 (deferred tax on fair value movements in OCI for FVOCI instruments), IAS 21 (foreign currency — interaction with hedge accounting and FVOCI), IAS 28 (equity method investments — SPPI not applicable), IAS 32 (classification of instruments as equity or liability — prerequisite for IFRS 9), IAS 39 (predecessor standard; still applicable for macro hedging under the IAS 39 election), IFRIC 16 (net investment hedge), IFRIC 19 (extinguishing liabilities with equity)

---

*End of IFRS 1–9 Reference. Last updated: March 2026.*
## IFRS 10 — Consolidated Financial Statements

**Scope:** Applies to all entities that control one or more other entities (subsidiaries). Excludes investment entities (which measure subsidiaries at fair value through profit or loss under IFRS 9), post-employment benefit plans, and entities within the scope of IFRS 17.

**Core principle:** A parent must present consolidated financial statements that combine its financials with those of its subsidiaries, reflecting the group as a single economic entity. Control is the sole basis for consolidation.

**Key rules:**
- **Control model (three elements — all must be present):**
  - Power over the investee (existing rights that give the ability to direct relevant activities)
  - Exposure, or rights, to variable returns from involvement with the investee
  - Ability to use power to affect the amount of those returns
- **Relevant activities:** Activities that significantly affect the investee's returns (e.g., operating and capital decisions, appointment of key management)
- **Potential voting rights:** Must be considered if they are substantive (currently exercisable)
- **De facto control:** Control can exist with less than a majority of voting rights if the investor holds the largest block and other shareholders are dispersed
- **Structured entities:** Assessed on substance; contractual and non-contractual involvement both considered
- **Investment entities exception:**
  - Must meet all three criteria: obtains funds from investors to provide investment management services; business purpose is investing for capital appreciation/investment income; measures and evaluates investments on a fair value basis
  - Investment entity consolidates only subsidiaries that provide investment-related services
- **Consolidation procedures:**
  - Combine like items of assets, liabilities, equity, income, and expenses
  - Eliminate intragroup balances, transactions, income, expenses, and unrealised profits/losses
  - Non-controlling interests (NCI) presented within equity, separately from the parent's equity
  - Uniform accounting policies and consistent reporting dates (difference must not exceed 3 months)
- **Changes in ownership interests:** Accounted for as equity transactions if control is retained; gain/loss recognised in P&L only on loss of control

**Disclosure requirements:**
- Significant judgements and assumptions used in determining whether control exists
- Information about subsidiaries with material NCI: name, place of incorporation, proportion of ownership and voting rights held by NCI, summarised financial information
- Nature and extent of significant restrictions on access to group assets or settlement of group liabilities
- Consequences of changes in the parent's ownership interest that did not result in loss of control
- Nature of risks associated with interests in consolidated structured entities

**Common pitfalls:**
- Failing to consolidate entities where control exists without a majority of voting rights (de facto control)
- Overlooking substantive removal rights held by other parties (which could negate power)
- Incorrect assessment of relevant activities in structured entities — focusing on legal form rather than economic substance
- Not reassessing control when facts and circumstances change
- Treating NCI as a liability rather than as equity
- Omitting elimination of upstream and downstream intragroup transactions (including unrealised profit in inventory)
- Misapplying the investment entity exception — all three criteria must be satisfied simultaneously

**Related standards:** IAS 27 (Separate Financial Statements), IAS 28 (Associates and Joint Ventures), IFRS 11 (Joint Arrangements), IFRS 12 (Disclosure), IFRS 3 (Business Combinations), IFRS 9 (Financial Instruments — for investment entities)

---

## IFRS 11 — Joint Arrangements

**Scope:** Applies to entities that have rights and obligations in joint arrangements — arrangements over which two or more parties have joint control. Does not apply to arrangements where joint control does not exist (those are assessed under IFRS 10 or IAS 28).

**Core principle:** An entity must classify its joint arrangements as either a joint operation or a joint venture based on the rights and obligations of the parties, and account for each type using the appropriate method.

**Key rules:**
- **Joint control:** Contractually agreed sharing of control; exists only when decisions about relevant activities require unanimous consent of the parties sharing control
- **Two types of joint arrangements:**
  - **Joint operation:**
    - Parties (joint operators) have rights to the assets and obligations for the liabilities of the arrangement
    - Structured through contractual arrangement or via a separate vehicle where legal form does not confer separation, or contractual terms override legal form, or relevant activities are dependent on the joint operators
    - Accounting: recognise own assets/liabilities (including share of jointly held assets/liabilities), own revenues/expenses, and share of revenues/expenses earned/incurred jointly — line-by-line
  - **Joint venture:**
    - Parties (joint venturers) have rights to the net assets of the arrangement
    - Structured via a separate vehicle where legal form does confer separation, contractual terms do not override, and relevant activities are not solely dependent on joint venturers
    - Accounting: equity method (same as associates under IAS 28)
- **Classification indicators (separate vehicle analysis):**
  - Legal form of the separate vehicle (limited liability company vs. partnership/unincorporated)
  - Terms of the contractual arrangement (whether parties have rights to assets and obligations for liabilities)
  - Other facts and circumstances (e.g., joint operators provide virtually all output; arrangement designed to provide output at cost)
- **Proportionate consolidation is prohibited** for joint ventures
- **Transactions between the entity and a joint arrangement:** Gains and losses recognised only to the extent of third-party interests; unrealised profits eliminated

**Disclosure requirements:**
- Nature, extent, and financial effects of interests in joint arrangements (name, place of business, ownership interest, nature of relationship)
- Summarised financial information for material joint ventures (balance sheet, income statement, including fair value if quoted)
- Risks associated with interests in joint ventures (commitments, contingent liabilities)
- For joint operations: the nature of the arrangement and the entity's share

**Common pitfalls:**
- Applying equity method to joint operations (must use line-by-line recognition)
- Classifying a joint venture as a joint operation based solely on legal form without considering contractual terms and other facts
- Assuming that a separate vehicle automatically creates a joint venture — substance over form analysis is required
- Failing to reassess classification when facts change
- Incorrectly computing the share of profits where output arrangements exist
- Not eliminating unrealised gains on transactions with joint arrangements

**Related standards:** IAS 28 (Equity Method), IFRS 10 (Consolidated Financial Statements), IFRS 12 (Disclosure), IFRS 3 (Business Combinations — for acquisitions of interests in joint operations)

---

## IFRS 12 — Disclosure of Interests in Other Entities

**Scope:** Applies to entities that have interests in subsidiaries, joint arrangements, associates, and unconsolidated structured entities. Disclosure requirements supplement (do not replace) those in IFRS 10, IFRS 11, and IAS 28.

**Core principle:** An entity must disclose information that enables users of financial statements to evaluate the nature of, and risks associated with, its interests in other entities, and the effects of those interests on its financial position, performance, and cash flows.

**Key rules:**
- **Significant judgements and assumptions** must be disclosed wherever they affect classification or consolidation conclusions:
  - Whether control or joint control exists with less than a majority of voting rights
  - Why an entity is or is not an investment entity
  - Nature of protective versus substantive rights
- **Subsidiaries:**
  - Composition of the group; restrictions on access to assets; NCI information
  - Changes in ownership interests not resulting in loss of control
  - Consequences of losing control
- **Unconsolidated subsidiaries (investment entity exception):** Summarised financial information and restrictions
- **Joint ventures (material):** Summarised balance sheet and P&L, reconciliation to carrying amount, fair value if quoted
- **Associates (material):** Same requirements as joint ventures
- **Non-material interests:** Aggregate disclosure by category (joint ventures/associates)
- **Unconsolidated structured entities (sponsored but not consolidated):** Nature, purpose, size, activities, financing; maximum exposure to loss
- **Quantitative and qualitative risk information** for all interests

**Disclosure requirements:**
- Objectives, policies, and processes for managing risks from interests in other entities
- For NCI: name, principal place of business, proportion held, summarised financial information, dividends paid to NCI
- For unconsolidated structured entities: how the entity determined it does not control the entity; contractual obligations to provide financial support; financial or other support provided during the period

**Common pitfalls:**
- Treating IFRS 12 as a standalone standard — it requires cross-referencing with IFRS 10, 11, and IAS 28
- Providing boilerplate disclosures rather than entity-specific judgements and risks
- Omitting disclosures for non-material interests in aggregate
- Failing to disclose for sponsored structured entities even when they are not consolidated
- Inadequate disclosure of restrictions on the parent's ability to access subsidiary assets

**Related standards:** IFRS 10 (Consolidated Financial Statements), IFRS 11 (Joint Arrangements), IAS 28 (Investments in Associates and Joint Ventures), IFRS 9 (Financial Instruments)

---

## IFRS 13 — Fair Value Measurement

**Scope:** Applies when another IFRS requires or permits fair value measurement or disclosure. Does not apply to: share-based payment transactions (IFRS 2); leasing transactions (IFRS 16); measurements that are similar to but not identical to fair value (e.g., net realisable value in IAS 2, value in use in IAS 36).

**Core principle:** Fair value is the price that would be received to sell an asset or paid to transfer a liability in an orderly transaction between market participants at the measurement date (an exit price).

**Key rules:**
- **Unit of account:** The level at which the asset or liability is aggregated for measurement; determined by the IFRS that requires the measurement
- **Market participants:** Knowledgeable, willing parties acting in their economic best interest; entity's own intentions are irrelevant
- **Principal market:** The market with the greatest volume and level of activity; if no principal market, the most advantageous market
- **Highest and best use:** For non-financial assets — the use that maximises value, physically possible, legally permissible, and financially feasible; in-use vs. in-exchange premise
- **Fair value hierarchy:**
  - **Level 1:** Quoted prices (unadjusted) in active markets for identical assets or liabilities (most reliable)
  - **Level 2:** Inputs other than quoted prices that are observable, either directly or indirectly (comparable assets, yield curves, credit spreads)
  - **Level 3:** Unobservable inputs — entity's own assumptions about market participant assumptions; requires maximum use of observable inputs
- **Valuation techniques:**
  - Market approach: uses prices from market transactions for identical or comparable assets
  - Income approach: discounts future amounts (cash flows, income) to a present value
  - Cost approach: reflects the amount required to replace the service capacity (current replacement cost)
- **Liabilities and own credit risk:** Assumes liability is transferred, not settled; own credit risk (non-performance risk) must be included
- **Day 1 gains/losses:** If transaction price differs from fair value on initial recognition, recognise difference only if fair value is evidenced by a quoted price in an active market (Level 1) or a valuation technique using only observable inputs; otherwise, defer
- **Bid-ask spread:** Use the price within the bid-ask spread most representative of fair value
- **Blockage factors:** Not allowed as an adjustment to Level 1 inputs even for large holdings

**Disclosure requirements:**
- Fair value hierarchy level for each class of assets/liabilities
- For Level 3: opening/closing reconciliation, unrealised gains/losses in P&L, transfers into/out of Level 3, valuation techniques and inputs used, sensitivity analysis (quantitative for recurring Level 3)
- Description of valuation processes used
- Highest and best use (if differs from current use for non-financial assets)
- For non-recurring fair values: reason for measurement

**Common pitfalls:**
- Confusing fair value (exit price) with transaction price or entry price
- Using entity-specific inputs rather than market participant assumptions
- Applying blockage discounts to Level 1 inputs
- Failing to assess whether the market is active before using quoted prices
- Inadequate Level 3 sensitivity disclosures
- Not considering transfer restrictions that market participants would price in
- Incorrectly including entity-specific synergies in valuations

**Related standards:** IAS 36 (Impairment — uses value in use, not fair value), IAS 40 (Investment Property — fair value model), IFRS 9 (Financial Instruments), IFRS 3 (Business Combinations), IFRS 16 (Leases), IFRS 17 (Insurance Contracts)

---

## IFRS 14 — Regulatory Deferral Accounts

**Scope:** Applies only to first-time adopters of IFRS that conduct rate-regulated activities (i.e., supply of goods or services at prices determined by a regulator). Entities already reporting under IFRS cannot apply IFRS 14. It is an interim standard — the IASB has a broader rate regulation project ongoing (IFRS 17 does not replace it).

**Core principle:** A first-time adopter engaged in rate-regulated activities may continue to recognise regulatory deferral account balances in accordance with its previous GAAP, allowing comparability while the IASB completes its comprehensive project on regulatory assets and liabilities.

**Key rules:**
- **Permitted (not required):** The entity may elect to continue its previous GAAP accounting policy for recognising, measuring, impairing, and derecognising regulatory deferral account balances
- **Regulatory deferral account balances:** Amounts of expense/income that would not be recognised under other IFRS but are deferred because rate regulation allows recovery or requires return of amounts to customers in future periods
- **Separate presentation:** Regulatory deferral account debit balances (assets) and credit balances (liabilities) must be presented separately from all other items on the balance sheet; not classified as financial instruments
- **Separate line items:** Movements in regulatory deferral account balances presented as separate line items in the statement of profit or loss and OCI
- **Impairment:** Debit balances must be assessed for recoverability; impaired if the regulatory body will not allow recovery
- **Discontinued election:** If an entity ceases to apply the standard, it must derecognise all balances and cannot re-apply

**Disclosure requirements:**
- Nature of rate regulation and classes of regulatory deferral account balances
- Risks associated with the rate-regulated activities and regulatory balances
- Effects of rate regulation on financial statements (amounts recognised, movements)
- Judgements made in determining whether amounts qualify as regulatory deferral balances
- Rate-regulated activities and the regulatory framework governing them

**Common pitfalls:**
- Misapplying the standard to entities already reporting under IFRS (it is exclusively for first-time adopters)
- Treating regulatory deferral accounts as financial instruments
- Presenting regulatory deferral balances within other asset/liability line items rather than separately
- Not assessing impairment/recoverability of debit balances
- Failing to disclose the regulatory framework and risks adequately

**Related standards:** IFRS 1 (First-time Adoption of IFRS), IAS 8 (Accounting Policies), IAS 36 (Impairment of Assets)

---

## IFRS 15 — Revenue from Contracts with Customers

**Scope:** Applies to all contracts with customers except: leases (IFRS 16), financial instruments and similar items (IFRS 9, 10, 11, IAS 27, 28), insurance contracts (IFRS 17), and non-monetary exchanges between entities in the same line of business. A customer is a party that has contracted to obtain goods or services that are the output of the entity's ordinary activities in exchange for consideration.

**Core principle:** Recognise revenue in a manner that depicts the transfer of promised goods or services to customers in an amount that reflects the consideration to which the entity expects to be entitled in exchange for those goods or services.

**Key rules:**
- **The 5-Step Model:**

  - **Step 1 — Identify the contract(s) with a customer:**
    - Contract must be approved, each party's rights identified, payment terms identifiable, commercial substance, and collection probable
    - Contract modifications: treat as a new contract (if distinct goods/services at standalone selling price) or a modification of the existing contract (cumulative catch-up or prospective adjustment)
    - Combining contracts: treat as one contract if negotiated as a package, consideration in one affects the other, or goods/services are a single performance obligation

  - **Step 2 — Identify the performance obligations:**
    - A performance obligation is a promise to transfer a distinct good or service (or a series of distinct goods/services that are substantially the same with the same transfer pattern)
    - **Distinct:** Capable of being distinct (customer can benefit from it on its own or with readily available resources) AND distinct within the context of the contract (separately identifiable — not highly interrelated/integrated, not modification/customisation, not highly interdependent)
    - Series provision: treat as a single performance obligation if each distinct increment is the same and transferred over time with the same measure of progress

  - **Step 3 — Determine the transaction price:**
    - **Variable consideration:** Estimate using expected value method (probability-weighted) or most likely amount (binary outcomes); include only to the extent it is highly probable a significant reversal will not occur (constraint)
    - **Significant financing component:** Adjust if payment timing provides a significant financing benefit; practical expedient if contract period is one year or less
    - **Non-cash consideration:** Measure at fair value; if fair value cannot be estimated, use standalone selling price
    - **Consideration payable to customer:** Reduces transaction price unless it is for a distinct good/service
    - **Sales-based and usage-based royalties on licences:** Recognised only when the subsequent sale or usage occurs (exception to the general variable consideration constraint)

  - **Step 4 — Allocate the transaction price:**
    - Allocate based on relative standalone selling prices (SSP) of each performance obligation
    - SSP estimation methods: adjusted market assessment, expected cost plus margin, residual (only if SSP highly variable or uncertain)
    - Discounts allocated to all performance obligations unless evidence that discount relates to only some
    - Variable consideration may be allocated entirely to one performance obligation if: the variable consideration relates specifically to that obligation AND allocation is consistent with the allocation objective

  - **Step 5 — Recognise revenue when (or as) performance obligations are satisfied:**
    - **Over time** if any one of three criteria is met:
      - Customer simultaneously receives and consumes benefits as the entity performs
      - Entity's performance creates or enhances an asset the customer controls as it is created
      - Entity's performance does not create an asset with an alternative use AND entity has an enforceable right to payment for performance completed to date
    - **At a point in time** if none of the over-time criteria are met; consider: right to payment, legal title, physical possession, risks and rewards, customer acceptance
    - **Measure of progress (over time):** Output methods (milestones, units delivered) or input methods (costs incurred, labour hours); must be consistent and applied to performance obligations of similar nature

- **Contract costs:**
  - **Costs to obtain a contract:** Capitalise incremental costs expected to be recovered (e.g., sales commissions); practical expedient to expense if amortisation period would be one year or less
  - **Costs to fulfil a contract:** Capitalise if directly related to a specific contract (or anticipated contract), generate or enhance resources used to satisfy future obligations, and are expected to be recovered
  - **Amortisation:** On a basis consistent with the transfer of goods/services to the customer
  - **Impairment:** Carrying amount exceeds remaining consideration less costs directly to satisfy remaining performance obligations

- **Licensing guidance:**
  - **Right to access** the intellectual property (IP) as it exists throughout the licence period: revenue recognised over time (IP is a right of access, not a right of use)
  - **Right to use** IP as it exists at the point in time the licence is granted: revenue recognised at a point in time
  - **Indicators of right to access:** Entity must continue to undertake activities that significantly affect the IP; customer is exposed to positive or negative effects of those activities; activities do not transfer a good or service to the customer
  - **Sales-based and usage-based royalties:** Exception — recognise only when subsequent sale/usage occurs regardless of whether the licence is right-of-use or right-of-access
  - **Distinct licence:** Assess separately; if not distinct, combine with other goods/services

- **Principal vs. agent:**
  - Principal: controls the good or service before it is transferred to the customer; recognises gross revenue
  - Agent: arranges for another party to provide the good or service; recognises only the fee/commission (net)
  - Indicators of principal: primary responsibility for fulfilment, inventory risk before and after delivery, discretion in setting price

- **Bill-and-hold arrangements:** Revenue recognised when customer has the good (control transferred), it was requested by the customer, it is identified as belonging to the customer, and it is ready for physical transfer

- **Repurchase agreements:** Call option — no revenue if entity can compel repurchase; put option — if customer has significant economic incentive to exercise, treat as a financing arrangement (loan) not a sale

**Disclosure requirements:**
- Disaggregation of revenue into categories that depict the nature, amount, timing, and uncertainty of revenue and cash flows
- Contract balances (contract assets, contract liabilities, receivables) — opening/closing balances, significant movements, revenue recognised from contract liabilities
- Remaining performance obligations (transaction price allocated to unsatisfied or partially satisfied obligations), with quantitative disclosures
- Significant judgements: timing of satisfaction of performance obligations, determining transaction price (variable consideration constraint, significant financing component), allocating transaction price
- Assets recognised from costs to obtain/fulfil contracts: amount, amortisation, impairment losses

**Common pitfalls:**
- Bundling distinct goods/services into a single performance obligation
- Failing to apply the variable consideration constraint, leading to premature revenue recognition
- Incorrectly assessing over-time vs. point-in-time criteria — especially the alternative use and enforceable right to payment test
- Misclassifying licensing as right-of-use vs. right-of-access
- Principal/agent misclassification, especially in digital platform or intermediary businesses
- Omitting the significant financing component adjustment
- Not assessing whether contract modifications create a new contract or modify the existing one
- Inadequate disaggregation of revenue disclosures

**Related standards:** IFRS 9 (Financial Instruments — contract assets), IFRS 16 (Leases), IFRS 17 (Insurance Contracts), IAS 37 (Provisions — onerous contracts), IAS 8 (Accounting Policies — judgements), IFRS 3 (Business Combinations — contract assets/liabilities acquired), IFRIC 12 (Service Concession Arrangements — construction and operation services revenue)

Note: IFRIC 15 (Agreements for the Construction of Real Estate) was superseded by IFRS 15.

---

## IFRS 16 — Leases

**Scope:** Applies to all leases, including leases of right-of-use assets in subleases. Excludes: leases to explore for or use minerals and similar resources (IFRS 6); leases of biological assets (IAS 41); service concession arrangements (IFRIC 12); licences of intellectual property granted by a lessor (IFRS 15); and rights held by lessees under licensing agreements for intangibles (IAS 38). Practical expedients: short-term leases (12 months or less) and leases for which the underlying asset is of low value may be excluded from lessee balance sheet recognition.

**Core principle:** A lessee must recognise a right-of-use (ROU) asset and a lease liability for all leases (subject to exemptions). A lessor classifies leases as either finance leases or operating leases.

**Key rules:**
- **Identifying a lease:**
  - A contract contains a lease if it conveys the right to control the use of an identified asset for a period of time in exchange for consideration
  - **Identified asset:** Specified explicitly or implicitly; substantive substitution rights by supplier preclude identification
  - **Right to obtain substantially all economic benefits** from use of the asset throughout the period of use
  - **Right to direct the use** of the asset: how and for what purpose the asset is used; or relevant decisions are predetermined and customer operates the asset (or designed it to dictate how it is used)

- **Lessee accounting:**
  - **Initial recognition:**
    - **Lease liability:** Present value of lease payments not paid at commencement, discounted at the rate implicit in the lease (or incremental borrowing rate if implicit rate cannot be readily determined)
    - **Lease payments included:** Fixed payments (including in-substance fixed), variable payments based on an index or rate (using rate at commencement), exercise price of purchase option if reasonably certain, payments for penalties for terminating if the lease term reflects exercise
    - **ROU asset:** Initial measurement of lease liability + lease payments made at or before commencement + initial direct costs + estimated dismantlement/restoration costs (per IAS 37)
  - **Subsequent measurement:**
    - **Lease liability:** Amortised cost — increased by interest (unwinding of discount at effective interest rate), decreased by lease payments; remeasured on reassessment
    - **ROU asset:** Cost model (less accumulated depreciation and impairment) unless:
      - Investment property (IAS 40 fair value model if adopted)
      - Underlying asset is of a class to which entity applies revaluation model (IAS 16)
    - Depreciation: over shorter of useful life and lease term (unless lease transfers ownership or exercise of purchase option is reasonably certain — then over useful life)
  - **Reassessment of lease liability:** Required when there is a change in lease term (reassess whether extension/termination option is reasonably certain), change in assessment of purchase option, change in amounts expected to be paid under residual value guarantee, change in index or rate (when lease payment changes)
  - **Lease modifications:**
    - Separate lease (if adds right-of-use of additional asset at standalone price): new lease
    - Not a separate lease: either remeasure liability with revised discount rate (if scope change) or remeasure liability using original discount rate

- **Lessor accounting:**
  - **Finance lease** (transfers substantially all risks and rewards of ownership):
    - Derecognise the underlying asset
    - Recognise net investment in lease (PV of lease payments + unguaranteed residual value, discounted at rate implicit in lease)
    - Recognise finance income over lease term using effective interest method
    - Indicators: ownership transfers; purchase option reasonably certain; lease term is major part of economic life; PV of lease payments substantially equals fair value; specialised nature such that only lessee can use without major modification
    - Manufacturer/dealer lessors: recognise selling profit/loss (same as outright sale) and finance income
  - **Operating lease** (does not transfer substantially all risks and rewards):
    - Continue to recognise underlying asset
    - Recognise lease income on straight-line basis (or another systematic basis if more representative)
    - Initial direct costs added to carrying amount of underlying asset and expensed over lease term
  - **Subleases:** Intermediate lessor classifies based on ROU asset (not underlying asset); if head lease is short-term exemption, sublease is an operating lease

- **Sale and leaseback:**
  - If the transfer qualifies as a sale (per IFRS 15): seller-lessee recognises ROU asset and lease liability; only the gain/loss relating to the rights retained by the buyer-lessor is recognised
  - If the transfer does not qualify as a sale: treat as a financing transaction (recognise financial liability)
  - Off-market terms: adjust selling price to fair value; recognise prepayment or additional financing

**Disclosure requirements:**
- **Lessee:** ROU assets by class, depreciation charges, additions; lease liabilities (maturity analysis of undiscounted payments), interest expense on lease liabilities; short-term and low-value lease expenses; variable lease payments not in liability; subleases; sale and leaseback transactions; commitments for leases not yet commenced
- **Lessor:** Finance leases — net investment (maturity analysis, unearned finance income, unguaranteed residual values, allowance for credit losses); operating leases — maturity analysis of future lease payments, depreciation of underlying assets; significant assumptions and judgements

**Common pitfalls:**
- Incorrectly identifying whether a contract contains a lease — particularly in service agreements with dedicated assets and substitution clauses
- Using the incremental borrowing rate without rigorous estimation (especially for entities without direct borrowing)
- Forgetting to include extension option payments in the lease liability when reasonably certain to exercise
- Not reassessing the lease term when a significant event or change occurs
- Lessee applying operating lease accounting (income statement only) — not permitted under IFRS 16 except for short-term and low-value exemptions
- Lessors incorrectly classifying leases — applying operating lease treatment when risks and rewards have been substantially transferred
- Sale and leaseback: recognising the full gain on a sale and leaseback rather than only the portion relating to the buyer-lessor's retained interest
- Intermediate lessors classifying subleases based on the underlying asset rather than the ROU asset

**Related standards:** IAS 17 (superseded), IFRS 9 (Financial Instruments — lessor's net investment, impairment), IFRS 15 (Revenue — sale and leaseback transfer assessment), IAS 36 (Impairment of ROU assets), IAS 37 (Provisions — lease reinstatement costs), IFRS 13 (Fair Value — investment property ROU assets), IFRS 3 (Business Combinations — lease assets and liabilities acquired)

---

## IFRS 17 — Insurance Contracts

**Scope:** Applies to: insurance contracts (including reinsurance) issued; reinsurance contracts held; and investment contracts with discretionary participation features (DPF) issued by an entity that also issues insurance contracts. Excludes: warranties (IAS 37/IFRS 15); employers' assets/liabilities under employee benefit plans (IAS 19); financial guarantee contracts (unless explicitly designating them as insurance contracts); contingent consideration in IFRS 3; direct insurance contracts held (except reinsurance held).

**Core principle:** An entity must measure insurance contracts based on building blocks that reflect the time value of money, the risk inherent in the contracts, and the entity's expectation of profit (the CSM). Revenue is recognised as insurance services are provided.

**Key rules:**

- **Level of aggregation:**
  - Group contracts into portfolios (contracts subject to similar risks managed together)
  - Within each portfolio, separate into cohorts no wider than annual issue year, and into three profitability groups:
    - Onerous at inception
    - Profitable — no significant possibility of becoming onerous
    - Remaining profitable contracts
  - Cannot offset groups

- **General Measurement Model (GMM) / Building Block Approach (BBA) — default model:**
  - **Fulfilment cash flows (FCF):**
    - **Estimates of future cash flows:** Current, unbiased, probability-weighted estimates of all cash inflows (premiums) and outflows (claims, benefits, expenses) within the contract boundary
    - **Discount rate:** Reflects time value of money and characteristics of the cash flows; must reflect the liquidity characteristics of the insurance contracts (not the assets held); top-down (yield of reference portfolio less illiquidity premium) or bottom-up (risk-free rate plus illiquidity premium)
    - **Risk adjustment for non-financial risk (RA):** Compensation required for bearing uncertainty about the amount and timing of cash flows from non-financial risk; disclosed as equivalent confidence level
  - **Contractual Service Margin (CSM):**
    - Represents the unearned profit on a group of insurance contracts
    - At inception: If FCF at inception shows a net liability (loss), the CSM is zero and the loss is recognised immediately in P&L (onerous group). If FCF shows a net asset, the CSM equals that amount
    - Subsequent measurement: CSM is adjusted for changes in estimates of future cash flows relating to future coverage (for non-onerous groups), accretes interest at the locked-in rate, and is released to P&L as the entity provides coverage (based on coverage units)
  - **Liability for remaining coverage (LRC):** FCF + CSM (related to future coverage)
  - **Liability for incurred claims (LIC):** FCF related to past events (claims incurred but not settled)
  - **Changes in FCF:** Changes relating to future service adjust the CSM (unless the group is onerous); changes relating to past or current service (claims experience adjustments) go to P&L; changes in discount rate go to either P&L or OCI (accounting policy choice)
  - **Insurance revenue:** Comprises the expected claims and expenses for the period, release of RA for the period, and the CSM released

- **Premium Allocation Approach (PAA) — simplified model:**
  - **Eligibility:** Available if at the inception of the group: the coverage period of each contract in the group is one year or less; OR the entity reasonably expects the PAA would produce a measurement not materially different from the GMM
  - **LRC:** Measured as premiums received minus acquisition costs (unless expensed), adjusted for amortisation. No explicit CSM. No discounting of LRC unless significant financing component
  - **LIC:** Must be discounted if expected to be settled more than one year after the incurred claims; risk adjustment required
  - **Onerous contracts:** Loss component recognised if facts and circumstances indicate a group is onerous

- **Variable Fee Approach (VFA) — for direct participating contracts:**
  - **Eligibility:** Contracts where the entity has a substantive obligation to pay policyholders a significant share of returns on underlying items; policyholders hold a significant proportion of underlying items
  - **Key differences from GMM:**
    - CSM reflects entity's share of changes in fair value of underlying items
    - Changes in fulfilment cash flows that relate to future service (including changes from underlying items) adjust the CSM rather than going to P&L
    - CSM can be adjusted for changes in financial risk, providing a "natural hedge"
    - Risk of CSM becoming negative: limited offset available via the "risk mitigation" option

- **Reinsurance contracts held:**
  - Measured separately from the underlying insurance contracts issued
  - CSM represents the net cost (if any) of purchasing reinsurance
  - Loss recovery component recognised when underlying contracts are onerous
  - Cannot net reinsurance assets against insurance liabilities

- **Transition approaches (for contracts existing at transition):**
  - Full retrospective approach (preferred if practicable)
  - Modified retrospective approach (limited use of hindsight)
  - Fair value approach (use fair value of contract group as CSM proxy at transition date)

- **Contract boundary:** Defined by when the entity has the substantive right to reassess risk and reprice. Premiums beyond that point are not part of the contract.

**Disclosure requirements:**
- Reconciliation of opening to closing balances of insurance contract assets/liabilities (separately for LRC and LIC, FCF and CSM)
- Insurance revenue and insurance service expenses
- Insurance finance income/expense and OCI
- Significant judgements: discount rates, risk adjustment methodology (confidence level equivalent), methods for determining coverage units
- Sensitivity analysis for changes in assumptions that would affect insurance finance income/expense
- Nature and extent of risks arising from insurance contracts: concentration, credit risk (reinsurance), liquidity risk, market risk exposure
- Transition method applied and related adjustments

**Common pitfalls:**
- Incorrect determination of the contract boundary — including premiums for future periods where the entity can reprice
- Incorrect level of aggregation — grouping contracts with different risk profiles or across annual cohorts
- Misclassifying contracts as PAA-eligible without performing the eligibility test, especially for contracts longer than 12 months
- Not recognising losses immediately for onerous groups at inception
- Incorrectly adjusting the CSM for experience variances (which relate to past coverage and should go directly to P&L)
- Misapplying VFA — insufficient rigour in assessing whether the participation is substantive
- Using asset discount rates rather than insurance contract discount rates (top-down/bottom-up methodology must reflect contract characteristics)
- Reinsurance: netting against insurance contracts issued rather than presenting separately
- Inadequate disclosure of confidence level equivalent for the risk adjustment

**Related standards:** IFRS 9 (Financial Instruments — assets backing insurance), IFRS 13 (Fair Value — underlying items in VFA), IFRS 7 (Financial Instruments Disclosures — financial risk), IAS 37 (Provisions — excluded from IFRS 17 scope), IFRS 3 (Business Combinations — insurance contract assets/liabilities acquired), IFRS 4 (superseded)

## IAS 1 — Presentation of Financial Statements

**Scope:** Applies to all general purpose financial statements prepared in accordance with IFRS. Does not apply to condensed interim financial statements prepared under IAS 34, though IAS 34 builds upon its principles.

**Core principle:** Financial statements must present fairly the financial position, financial performance, and cash flows of an entity. Fair presentation requires faithful representation of the effects of transactions and events in accordance with the definitions and recognition criteria in the Conceptual Framework.

**Key rules:**
- **Complete set of financial statements** — must include:
  - Statement of financial position (balance sheet)
  - Statement of profit or loss and other comprehensive income (single or two-statement approach)
  - Statement of changes in equity
  - Statement of cash flows
  - Notes (including a summary of material accounting policies)
  - Comparative statement of financial position when an entity restates prior periods or reclassifies items
- **Going concern** — management must assess the entity's ability to continue as a going concern. If material uncertainties exist, they must be disclosed. If not a going concern, that basis must be used and disclosed.
- **Accrual basis** — all financial statements except the cash flow statement must be prepared on an accrual basis.
- **Materiality and aggregation** — each material class of similar items must be presented separately. Immaterial items may be aggregated.
- **Offsetting** — assets and liabilities, income and expenses, shall not be offset unless required or permitted by an IFRS.
- **Frequency of reporting** — at least annually. If the reporting period changes, disclose the reason and that comparatives are not fully comparable.
- **Comparative information** — minimum of one prior period comparative for all amounts in the current period financial statements.
- **Consistency of presentation** — presentation and classification of items shall be retained from one period to the next unless a change is justified.
- **Other comprehensive income (OCI)** — items must be classified by whether they will or will not be subsequently reclassified to profit or loss. Tax effects must be allocated to OCI items.
- **Current/non-current distinction** — entities present current and non-current assets/liabilities separately unless a liquidity presentation provides more reliable information.
  - An asset is current if expected to be realised within 12 months or the operating cycle, held for trading, or is cash/cash equivalent.
  - A liability is current if due within 12 months, there is no unconditional right to defer settlement, or it is held for trading.
  - Breach of loan covenants: if a breach occurs by period end and the lender has not agreed by period end to waive the right to demand repayment, the liability is current.

**Disclosure requirements:**
- Identification of the financial statements (entity name, whether consolidated/separate, reporting date, presentation currency, level of rounding)
- Accounting policies that are material to understanding the financial statements
- Judgements made in applying accounting policies that have the most significant effect on amounts recognised
- Key sources of estimation uncertainty — assumptions about the future that have a significant risk of causing a material adjustment within the next year
- Information about capital management (qualitative and quantitative)
- Dividends proposed or declared after the reporting period (and per share amount)
- Restatements: nature, amount of corrections, and effect on earnings per share

**Common pitfalls:**
- Failing to distinguish between material judgements (IAS 1 para 122) and estimation uncertainty (para 125) — they require separate disclosures
- Classifying a breach-of-covenant liability as non-current when the waiver was obtained after period end
- Presenting a single OCI line without splitting items that will vs. will not be reclassified
- Boilerplate accounting policy disclosures that do not reflect the entity's actual circumstances
- Omitting the third balance sheet when a restatement or reclassification has occurred

**Related standards:** IAS 7 (cash flows), IAS 8 (accounting policies, errors), IAS 10 (events after reporting period), IAS 34 (interim reporting), IFRS 7 (financial instrument disclosures), IFRS 13 (fair value hierarchy disclosures), IAS 33 (EPS)

---

## IAS 2 — Inventories

**Scope:** Applies to all inventories except: work in progress under construction contracts (IFRS 15), financial instruments (IFRS 9), biological assets and agricultural produce at point of harvest (IAS 41), and commodity broker-traders who measure inventories at fair value less costs to sell.

**Core principle:** Inventories shall be measured at the lower of cost and net realisable value (NRV). Cost comprises all costs of purchase, costs of conversion, and other costs incurred to bring the inventories to their present location and condition.

**Key rules:**
- **Cost of inventories:**
  - *Costs of purchase* — purchase price plus import duties, transport, handling, and other directly attributable costs, less trade discounts and rebates
  - *Costs of conversion* — direct labour and a systematic allocation of fixed and variable production overheads
  - *Fixed overhead allocation* — based on normal capacity (not actual production); abnormal idle capacity costs are expensed as incurred
  - *Excluded costs* — abnormal waste, storage costs (unless necessary before a further production stage), administrative overheads unrelated to production, selling costs, and borrowing costs (unless IAS 23 applies)
- **Cost formulas (methods):**
  - Specific identification — for items not ordinarily interchangeable and goods produced for specific projects
  - First-In First-Out (FIFO) — permitted
  - Weighted average cost (WAC) — permitted (can be periodic or moving average)
  - **LIFO is explicitly prohibited under IFRS**
  - The same cost formula must be used for all inventories of similar nature and use; different formulas may be used for different categories
- **Net realisable value (NRV):**
  - Estimated selling price in the ordinary course of business, less estimated costs of completion and estimated selling costs
  - NRV write-downs are assessed item-by-item (or by groups of similar items); not by broad category or total inventory
  - Written-down value is reassessed each subsequent period; reversals are permitted up to the original write-down amount
- **Recognition as expense:** The carrying amount of inventories sold is recognised as cost of goods sold in the period in which the related revenue is recognised.

**Disclosure requirements:**
- Accounting policies adopted for measuring inventories, including the cost formula used
- Total carrying amount of inventories and carrying amount by classification (raw materials, WIP, finished goods, etc.)
- Carrying amount of inventories carried at fair value less costs to sell
- Amount of inventories recognised as an expense during the period
- Amount of any write-down to NRV and circumstances/events leading to the write-down
- Amount of any reversal of a write-down and the circumstances causing the reversal
- Carrying amount of inventories pledged as security

**Common pitfalls:**
- Using LIFO (explicitly prohibited under IFRS; common US GAAP divergence)
- Allocating fixed overheads based on actual production rather than normal capacity, overstating inventory in low-production periods
- Including selling and distribution costs in inventory cost
- Performing NRV testing at a portfolio or total-inventory level rather than item-by-item or similar-group level
- Failing to reverse NRV write-downs when selling prices subsequently recover
- Omitting or incorrectly capitalising borrowing costs per IAS 23 for qualifying inventory

**Related standards:** IAS 23 (borrowing costs for qualifying inventory), IFRS 15 (contract costs and work in progress), IAS 41 (agricultural produce pre-harvest), IFRS 13 (fair value measurement for broker-trader exception)

---

## IAS 7 — Statement of Cash Flows

**Scope:** Applies to all entities that prepare financial statements in accordance with IFRS. Requires a statement of cash flows as an integral part of the financial statements for every period for which financial statements are presented.

**Core principle:** The statement of cash flows provides information about an entity's historical changes in cash and cash equivalents, classified by operating, investing, and financing activities. This enables users to assess the entity's ability to generate cash and its liquidity needs.

**Key rules:**
- **Cash and cash equivalents:**
  - Cash: cash on hand and demand deposits
  - Cash equivalents: short-term, highly liquid investments readily convertible to known amounts of cash, with an insignificant risk of changes in value (typically original maturity of three months or less)
  - Bank overdrafts repayable on demand that form an integral part of cash management are included as a component of cash and cash equivalents
- **Classification of activities:**
  - *Operating activities* — principal revenue-producing activities and other activities that are not investing or financing. Cash generated from operations adjusted for working capital movements; tax paid is generally classified as operating unless specifically identified with financing or investing
  - *Investing activities* — acquisition and disposal of long-term assets and other investments not included in cash equivalents (e.g., PPE purchases, business acquisitions/disposals, loans made and repaid, purchase/sale of investments)
  - *Financing activities* — activities that result in changes in the size and composition of equity and borrowings (e.g., proceeds from issuing shares, proceeds from borrowings, repayment of borrowings, payment of lease liabilities, dividends paid)
- **Reporting methods for operating cash flows:**
  - *Direct method* — discloses major classes of gross cash receipts and payments. Encouraged by IAS 7
  - *Indirect method* — reconciles profit or loss to net cash from operating activities by adjusting for non-cash items, changes in working capital, and items classified as investing/financing. Permitted and widely used in practice
- **Interest and dividends** — classification is an accounting policy choice that must be applied consistently:
  - Interest paid: operating or financing
  - Interest received: operating or investing
  - Dividends paid: financing or operating
  - Dividends received: investing or operating
- **Taxes on income** — generally classified as operating unless specifically identifiable with financing or investing
- **Foreign currency cash flows** — translated at the exchange rate at the date of the cash flow (or average rate as approximation). Effect of exchange rate changes on cash held in foreign currencies is presented separately as a reconciling item
- **Non-cash transactions** — excluded from the cash flow statement but disclosed elsewhere in the notes (e.g., acquiring an asset via finance lease, converting debt to equity, acquiring assets by assuming liabilities)
- **Gross vs. net presentation:**
  - Generally gross presentation required
  - Net presentation permitted for: cash receipts and payments on behalf of customers, and cash receipts and payments for items where turnover is quick, amounts are large, and maturities are short (e.g., credit card principal)
- **Reconciliation** — the closing balance of cash and cash equivalents in the statement of cash flows must reconcile to the balance sheet

**Disclosure requirements:**
- Components of cash and cash equivalents and a reconciliation to the balance sheet
- Accounting policies for determining cash and cash equivalents
- Significant non-cash transactions
- Separate disclosure of cash flows from acquisition and disposal of subsidiaries (investing section)
- Cash and cash equivalents not available for use by the group (e.g., restricted cash held by a subsidiary with exchange controls) and the amount and reasons
- Interest and dividends received/paid (with classification policy)
- Segment cash flow information (encouraged but not required)
- Undrawn borrowing facilities

**Common pitfalls:**
- Classifying bank overdrafts as financing rather than as a component of cash and cash equivalents (when part of cash management)
- Presenting investing/financing cash flows on a net basis when gross presentation is required
- Incorrect classification of interest and dividends (particularly when the entity has not established a clear accounting policy)
- Including non-cash transactions in the statement (e.g., right-of-use assets on initial recognition of a lease)
- Failing to disclose restricted cash separately and the resulting reconciliation break
- Treating proceeds from sale of financial assets (held for investment) as operating rather than investing

**Related standards:** IAS 1 (financial statement presentation), IAS 21 (foreign currency translation of cash flows), IFRS 16 (lease liability payments in financing activities), IFRS 3 (cash flows from business combinations)

---

## IAS 8 — Accounting Policies, Changes in Accounting Estimates and Errors

**Scope:** Applies to the selection and application of accounting policies and the accounting for changes in accounting policies, changes in accounting estimates, and corrections of prior period errors. Does not address accounting for income taxes arising from corrections of errors or changes in accounting policies (see IAS 12).

**Core principle:** Accounting policies shall be selected and applied consistently. Changes in accounting policy, changes in accounting estimates, and corrections of material prior period errors each have specific and distinct accounting treatments.

**Key rules:**
- **Selection of accounting policies:**
  - When an IFRS specifically applies, follow that standard
  - When no specific IFRS applies, management uses judgement to develop a policy that is relevant and reliable, considering in order: (1) requirements of IFRS dealing with similar/related issues, (2) the IASB Conceptual Framework
  - May also consider pronouncements of other standard-setting bodies that use a similar framework, other accounting literature, and accepted industry practices
- **Changes in accounting policy:**
  - Permitted only if required by an IFRS, or if the change results in the financial statements providing more reliable and relevant information
  - **Retrospective application** — restate all prior periods presented as if the new policy had always been applied; adjust the opening balance of equity of the earliest period presented
  - If retrospective application is impracticable for a specific prior period, apply the new policy from the beginning of the earliest period for which retrospective application is practicable
  - Changes resulting from initial application of a new IFRS are accounted for per the transitional provisions of that IFRS (which may specify prospective or modified retrospective)
- **Changes in accounting estimates:**
  - A change in estimate results from new information or new developments, not from correcting errors
  - **Prospective application** — recognise the effect in profit or loss in the current period and future periods affected
  - Examples: useful lives and residual values of assets, allowance for expected credit losses, warranty provisions, fair value measurements
  - If the distinction between a policy change and an estimate change is difficult, treat it as a change in estimate
- **Prior period errors:**
  - Omissions or misstatements arising from failure to use, or misuse of, reliable information
  - **Retrospective restatement** — correct by restating comparative amounts for prior periods presented, and restating the opening balance of assets, liabilities, and equity for the earliest prior period presented
  - If impracticable, restate from the earliest practicable period
  - Material errors must be corrected retrospectively; immaterial errors may be corrected prospectively
- **Impracticability** — applying a requirement is impracticable when the entity cannot apply it after making every reasonable effort to do so (e.g., data not available, significant estimation required that cannot be reliably made)

**Disclosure requirements:**
- **Change in accounting policy:**
  - Title of the standard, nature and reason for change
  - Amount of adjustment for current and each prior period presented (and beyond if practicable)
  - Amount of adjustment relating to periods before those presented
  - If retrospective application is impracticable, description of circumstances and how change was applied
- **Change in accounting estimate:**
  - Nature and amount of the change with effect on current period
  - If future periods are affected, the expected effect (or a statement that it is impracticable to estimate)
- **Prior period errors:**
  - Nature of the error
  - Amount of correction for each prior period presented (and beyond if practicable)
  - Correction to the opening balance of the earliest prior period presented
  - If restatement is impracticable, description of circumstances

**Common pitfalls:**
- Misclassifying a change in accounting estimate as a change in accounting policy (or vice versa), leading to incorrect retrospective vs. prospective treatment
- Applying new IFRS standards using full retrospective restatement when the transitional provisions specify modified retrospective (no restatement of comparatives)
- Correcting immaterial current-year errors through restatement when prospective correction is sufficient
- Failing to adjust the opening equity of the earliest comparative period when restating errors
- Voluntary changes in accounting policy without documenting that the change provides more reliable and relevant information
- Disclosing only current-year impact without providing the per-period impact table required by IAS 8

**Related standards:** IAS 1 (presentation), IAS 12 (tax effects of corrections and policy changes), IAS 16 (change in depreciation method treated as change in estimate), IAS 37 (revision of provisions treated as change in estimate), all IFRS transitional provisions

---

## IAS 10 — Events after the Reporting Period

**Scope:** Applies to the accounting for, and disclosure of, events — both favourable and unfavourable — that occur between the end of the reporting period and the date on which the financial statements are authorised for issue. Does not address events already reflected in the financial statements or addressed by other standards (e.g., discontinued operations under IFRS 5).

**Core principle:** Events after the reporting period are classified as either adjusting or non-adjusting. Adjusting events provide evidence of conditions existing at the end of the reporting period and require changes to the financial statements. Non-adjusting events are indicative of conditions that arose after the reporting period and are disclosed but do not change recognised amounts.

**Key rules:**
- **Adjusting events (adjust the financial statements):**
  - Settlement after the reporting period of a court case that confirms a liability existing at the end of the reporting period
  - Receipt of information after the reporting period indicating that an asset was impaired at period end (e.g., bankruptcy of a customer after period end confirming a loss already incurred; sale of inventory after period end at below carrying amount indicating NRV was below cost at period end)
  - Discovery of fraud or errors showing the financial statements were incorrect
  - Determination after period end of the purchase price or proceeds from sale of assets bought/sold before period end
- **Non-adjusting events (disclose only, do not adjust):**
  - Decline in market value of investments after period end (reflects conditions after period end)
  - Major business combination or disposal after period end
  - Announcement of a plan to discontinue an operation
  - Major purchases/disposals of assets or their expropriation
  - Destruction of a major production plant by fire after period end
  - Announcement or commencement of a major restructuring
  - Major ordinary share transactions and potential ordinary share transactions after period end
  - Abnormally large changes in asset prices or foreign exchange rates after period end
  - Changes in tax rates or tax laws enacted after period end
  - Entering into significant commitments or contingent liabilities
- **Dividends:**
  - Dividends declared after the reporting period but before the financial statements are authorised for issue are **non-adjusting** — no liability is recognised at period end. They are disclosed in the notes
- **Going concern:**
  - If management determines after the reporting period that it intends to liquidate the entity or cease trading, or has no realistic alternative but to do so, the going concern basis is inappropriate even if the event occurs after period end — the financial statements must be revised accordingly
- **Date of authorisation for issue:**
  - Must be disclosed; this is the date the financial statements are approved by the board (or equivalent)
  - If the entity's owners or others have the power to amend the financial statements after issue, that does not change the authorisation date

**Disclosure requirements:**
- The date when the financial statements were authorised for issue and who gave that authorisation
- For each material category of non-adjusting event:
  - Nature of the event
  - Estimate of its financial effect, or a statement that such an estimate cannot be made
- Update of disclosures relating to conditions at period end when new information is received after period end

**Common pitfalls:**
- Treating a post-balance sheet event as adjusting when it reflects new conditions rather than confirming conditions at period end (e.g., treating a decline in listed share price as adjusting)
- Recognising dividends declared after period end as a liability at period end
- Failing to identify or disclose the authorisation date
- Overlooking going concern events that arise between period end and authorisation
- Confusion between the "reporting period" (year-end) and the "authorisation date" — the window between these two dates is where IAS 10 applies

**Related standards:** IAS 1 (going concern, authorisation date for comparative third balance sheet), IAS 37 (provisions for conditions existing at period end), IAS 36 (impairment evidence arising after period end), IFRS 5 (discontinued operations)

---

## IAS 12 — Income Taxes

**Scope:** Applies to the accounting for income taxes, including all domestic and foreign taxes based on taxable profits, and withholding taxes payable by subsidiaries on distributions to the parent. Does not apply to government grants (IAS 20) or investment tax credits, except by analogy where appropriate. IFRIC 23 supplements IAS 12 for uncertain tax treatments.

**Core principle:** Current and deferred tax are recognised as income or expense in profit or loss, except to the extent that the tax arises from a transaction recognised in OCI or directly in equity, in which case the tax is also recognised in OCI or equity respectively. Deferred tax reflects the future tax consequences of recovering or settling the carrying amounts of assets and liabilities.

**Key rules:**
- **Current tax:**
  - The amount of income tax payable (recoverable) in respect of taxable profit (loss) for the current and prior periods
  - Measured using enacted or substantively enacted tax rates at the balance sheet date
  - Recognised as a liability (or asset if tax paid exceeds tax due)
- **Temporary differences:**
  - Differences between the carrying amount of an asset or liability in the balance sheet and its tax base
  - *Taxable temporary differences* — give rise to deferred tax liabilities (DTLs): taxable amounts in future periods
  - *Deductible temporary differences* — give rise to deferred tax assets (DTAs): deductible amounts in future periods
- **Deferred tax liabilities (DTLs):**
  - Recognised for all taxable temporary differences except:
    - Initial recognition of goodwill
    - Initial recognition of an asset or liability in a transaction that is not a business combination and, at the time of the transaction, affects neither accounting profit nor taxable profit (the "initial recognition exemption")
    - Taxable temporary differences arising on investments in subsidiaries, associates, and joint ventures where the parent/investor controls the timing of reversal and it is probable the difference will not reverse in the foreseeable future
- **Deferred tax assets (DTAs):**
  - Recognised for all deductible temporary differences to the extent that it is probable that taxable profit will be available against which the deductible temporary difference can be utilised
  - Also recognised for unused tax losses and tax credits carried forward, to the extent probable that future taxable profit will be available
  - The assessment of "probable" requires judgement and must be reviewed at each balance sheet date
  - Unrecognised DTAs reassessed at each period end
- **Measurement of deferred tax:**
  - Measured at the tax rates expected to apply in the period the asset is realised or the liability settled, based on enacted or substantively enacted rates at the balance sheet date
  - The rate used depends on the *expected manner of recovery/settlement* (e.g., use vs. sale of an asset may attract different rates)
  - Deferred tax is **not discounted**
- **Offsetting:**
  - Current tax assets and liabilities may be offset only when there is a legally enforceable right to offset and the entity intends to settle on a net basis or simultaneously
  - Deferred tax assets and liabilities may be offset only when: (a) there is a legally enforceable right to offset current tax assets against current tax liabilities, and (b) they relate to income taxes levied by the same taxing authority on the same taxable entity (or different entities that intend to settle/recover on a net basis)
- **Tax on OCI and equity items:**
  - Deferred and current tax arising from items recognised in OCI (e.g., revaluation of PPE, remeasurements of defined benefit plans) is recognised in OCI
  - Tax on equity transactions (e.g., equity-settled share-based payments) is recognised in equity
- **IFRIC 23 — Uncertainty over Income Tax Treatments:**
  - Applies when there is uncertainty about whether a tax treatment will be accepted by the tax authority
  - An uncertain tax position must be reflected in the measurement of current and deferred tax if it is not probable that the tax authority will accept the treatment
  - The entity assumes the tax authority will examine the positions and has full knowledge of all relevant information
  - Measurement: either the most likely amount or the expected value (probability-weighted), whichever better predicts the resolution
  - Reassess judgements whenever facts or circumstances change or new information becomes available

**Disclosure requirements:**
- Current and deferred tax recognised in profit or loss, OCI, and equity
- Tax relating to discontinued operations separately
- Numerical reconciliation between tax expense and the product of accounting profit multiplied by the applicable tax rate (either using the domestic rate or a weighted average)
- Explanation of changes in tax rates
- Amount of deductible temporary differences, unused tax losses, and unused tax credits for which no DTA is recognised, and expiry dates
- Amount of DTA recognised and evidence supporting recognition when utilisation depends on future taxable profits in excess of existing taxable temporary differences
- Nature and amount of each type of temporary difference and unused loss/credit (if DTL or DTA is significant)
- Deferred tax relating to investments in subsidiaries/associates/JVs where no DTL is recognised
- Tax consequences of dividends proposed or declared
- Uncertain tax positions recognised (per IFRIC 23): judgements made, key assumptions, potential changes

**Common pitfalls:**
- Recognising a DTA for tax losses without sufficient evidence of probable future taxable profits
- Applying the wrong tax rate (e.g., using the enacted rate rather than the substantively enacted rate, or failing to consider the expected manner of recovery/settlement)
- Incorrectly applying the initial recognition exemption to subsequent changes in temporary differences (it applies only at initial recognition)
- Recognising a DTL on goodwill (explicitly prohibited)
- Failing to recognise tax on OCI items separately from tax in profit or loss
- Omitting IFRIC 23 disclosures for uncertain positions
- Discounting deferred tax balances (prohibited under IAS 12)
- Not reassessing previously unrecognised DTAs when circumstances improve

**Related standards:** IAS 1 (presentation of tax on OCI), IAS 8 (tax effects of corrections and policy changes), IFRS 3 (deferred tax in business combinations), IAS 32/IFRS 9 (tax on equity components), IFRIC 23 (uncertain tax treatments)

---

## IAS 16 — Property, Plant and Equipment

**Scope:** Applies to all property, plant and equipment (PPE) unless another standard requires or permits a different treatment. Excludes: biological assets (IAS 41), mineral rights and reserves (IFRS 6), and investment property (IAS 40) — though IAS 16 applies to PPE used to develop or maintain assets in those categories. Also excludes assets classified as held for sale (IFRS 5).

**Core principle:** The cost of an item of PPE shall be recognised as an asset if, and only if, it is probable that future economic benefits will flow to the entity and the cost can be measured reliably. Subsequently, the entity may use either the cost model or the revaluation model as its accounting policy for each class of PPE.

**Key rules:**
- **Initial recognition and measurement at cost:**
  - Purchase price, including import duties and non-refundable taxes, less trade discounts
  - Directly attributable costs: site preparation, delivery, installation, professional fees, estimated costs of dismantling and restoration (IAS 37 provision)
  - Borrowing costs attributable to qualifying assets (IAS 23)
  - Excludes: administration and general overhead, costs of opening a facility, costs of introducing a new product, costs of conducting business in a new location, and training costs
  - If payment is deferred beyond normal credit terms, the cost is the cash price equivalent (difference is interest over the credit period)
  - If acquired in exchange for a non-monetary asset: measured at fair value unless (a) the exchange lacks commercial substance or (b) fair value cannot be reliably measured — in those cases, use the carrying amount of the asset given up
- **Component depreciation:**
  - Each significant component of an item of PPE with a different useful life must be depreciated separately
  - Example: an aircraft fuselage, engines, and interior fittings each have different useful lives and must be componentised
  - Cost of replacing a component is recognised as an asset and the carrying amount of the replaced component derecognised
- **Subsequent costs:**
  - Included in the asset's cost only if they meet the recognition criteria (probable future economic benefits, reliable measurement)
  - Day-to-day servicing costs ("repairs and maintenance") are expensed as incurred
  - Major inspections (e.g., overhauls required by regulation) are capitalised and depreciated over the period to the next inspection; prior inspection costs derecognised
- **Depreciation:**
  - Depreciable amount (cost or revalued amount less residual value) allocated on a systematic basis over the useful life
  - Begins when the asset is available for use; continues until derecognition or reclassification as held for sale (IFRS 5) — not when idle
  - Residual value and useful life reviewed at least at each year end; changes are changes in accounting estimates (IAS 8)
  - Depreciation method (straight-line, diminishing balance, units of production) shall reflect the pattern of consumption of economic benefits and be reviewed at least annually
  - Land is not depreciated (indefinite useful life), but buildings are depreciated separately
- **Cost model:** Carry at cost less accumulated depreciation and accumulated impairment losses
- **Revaluation model:**
  - An entire class of PPE must be revalued (cannot cherry-pick individual assets within a class)
  - Revaluations must be kept sufficiently up to date (frequency depends on volatility of fair values)
  - Revaluation surplus: increase credited to OCI and accumulated in equity (revaluation reserve)
  - Decrease: first offsets any existing revaluation surplus for that asset; any excess is charged to profit or loss
  - Revaluation increases that reverse prior decreases recognised in profit or loss are recognised in profit or loss up to the amount previously charged
  - Accumulated depreciation at date of revaluation: either restated proportionally or eliminated against gross carrying amount (asset restated to revalued amount)
  - Depreciation on a revalued asset: based on the revalued amount over the remaining useful life
  - Transfer from revaluation reserve to retained earnings: either as the asset is used (excess depreciation) or on derecognition — not through profit or loss
- **Derecognition:**
  - Carrying amount derecognised on disposal or when no future economic benefits expected
  - Gain or loss = net disposal proceeds minus carrying amount, recognised in profit or loss
  - Gains are not classified as revenue
- **Impairment:** Subject to IAS 36

**Disclosure requirements:**
- Measurement bases, depreciation methods, useful lives or depreciation rates
- Gross carrying amount and accumulated depreciation (including impairment) at start and end of period
- Reconciliation of carrying amounts (additions, disposals, depreciation, impairment, revaluations, transfers)
- For revalued assets: effective date of revaluation, whether an independent valuer was involved, methods and assumptions, carrying amount if cost model had been used, revaluation surplus and changes therein
- Contractual commitments for acquisition of PPE
- PPE restricted as security for liabilities
- Compensation received from third parties for impaired/lost assets

**Common pitfalls:**
- Failing to componentise significant parts with different useful lives
- Revaluing selected assets within a class rather than the entire class
- Not updating residual values and useful lives at least annually
- Continuing to depreciate an asset after it meets the IFRS 5 held-for-sale criteria
- Incorrectly capitalising costs that should be expensed (training, administrative overheads, launch costs)
- Failing to derecognise the carrying amount of replaced components on major overhaul
- Recognising gains on revaluation in profit or loss rather than OCI

**Related standards:** IAS 23 (borrowing costs), IAS 36 (impairment), IAS 37 (decommissioning provisions), IFRS 5 (held for sale), IAS 40 (investment property — entity may use cost or fair value model), IFRS 16 (right-of-use assets), IFRS 13 (fair value for revaluations)

---

## IAS 19 — Employee Benefits

**Scope:** Applies to all employee benefits except share-based payments (IFRS 2). Covers short-term employee benefits, post-employment benefits (defined contribution and defined benefit plans), other long-term employee benefits, and termination benefits.

**Core principle:** An entity shall recognise a liability when an employee has provided service in exchange for employee benefits to be paid in the future, and an expense when the entity consumes the economic benefit arising from service provided by an employee in exchange for employee benefits.

**Key rules:**
- **Short-term employee benefits** (expected to be settled wholly within 12 months after the end of the annual reporting period in which the employee renders the service):
  - Wages, salaries, social security contributions, paid annual leave, paid sick leave, profit-sharing and bonuses, non-monetary benefits
  - Recognised as a liability (accrued expense) as service is rendered; undiscounted
  - Accumulating paid absences (unused vacation carried forward): accrue as employees render service
  - Non-accumulating paid absences: recognise when absences occur
  - Profit-sharing/bonus: recognise only if there is a present legal or constructive obligation and the amount can be reliably estimated
- **Post-employment benefits — Defined Contribution (DC) plans:**
  - Entity's obligation is fixed: the contributions payable for the period
  - Recognise the contribution as an expense when the employee has rendered service
  - If contributions do not fall due within 12 months, they are discounted
- **Post-employment benefits — Defined Benefit (DB) plans:**
  - Entity's obligation is to provide the agreed benefits; the entity bears actuarial and investment risk
  - **Net defined benefit liability (asset):** present value of the defined benefit obligation (DBO) less the fair value of plan assets
  - *Defined benefit obligation (DBO):* present value of expected future payments attributed to employee service using the projected unit credit method; discounted using the yield on high quality corporate bonds (or government bonds where no deep market) with currency and term consistent with the obligation
  - *Current service cost:* increase in the DBO resulting from employee service in the current period — recognised in profit or loss
  - *Past service cost:* change in the DBO for employee service in prior periods resulting from a plan amendment or curtailment — recognised immediately in profit or loss (no longer deferred)
  - *Net interest cost (income):* applying the discount rate to the net defined benefit liability (asset) at the start of the period — recognised in profit or loss
  - **Remeasurements — recognised in OCI, never recycled to profit or loss:**
    - Actuarial gains and losses: changes in the DBO from experience adjustments and changes in actuarial assumptions
    - Return on plan assets excluding the amount included in net interest (actual return minus expected return at the discount rate)
    - Changes in the effect of the asset ceiling (excluding interest)
  - *Asset ceiling:* the net DB asset is limited to the present value of economic benefits available as refunds or reductions in future contributions; any excess is recognised as a reduction of the asset via OCI
  - Multi-employer plans: treated as DC if insufficient information to use DB accounting; as DB otherwise
- **Other long-term employee benefits** (e.g., long-service leave, jubilee awards, long-term disability):
  - Similar to DB accounting but all changes (including remeasurements) are recognised in profit or loss — no OCI
- **Termination benefits:**
  - Recognised at the earlier of: (a) when the entity can no longer withdraw the offer, or (b) when restructuring costs are recognised (IAS 37)
  - If expected to be settled more than 12 months after the reporting period, they are discounted

**Disclosure requirements:**
- Description of the plan, its risks, and entity's involvement in governance
- Explanation of amounts in the financial statements (reconciliation of opening to closing DBO, plan assets, and net liability/asset)
- The significant actuarial assumptions used (discount rate, salary growth, mortality, etc.) and sensitivity analysis showing how the DBO would change if each significant actuarial assumption changed by a reasonably possible amount
- Description of plan assets and their fair value by major category; amounts included in plan assets for the entity's own financial instruments or assets it uses
- Funding information: expected contributions to DB plans for the next annual period, weighted average duration of the DBO, maturity analysis of benefit payments
- Multi-employer plan disclosures if classified as DC due to insufficient information
- DC expense recognised in the period

**Common pitfalls:**
- Recognising actuarial gains and losses in profit or loss rather than OCI (the "corridor method" is no longer permitted under IAS 19 Revised 2011)
- Deferring past service cost amortisation (no longer permitted; past service cost is now immediate)
- Using an incorrect discount rate (e.g., using a government bond rate when a deep corporate bond market exists)
- Failing to apply the asset ceiling test when the DB plan is in surplus
- Confusing the "net interest" component (recognised in P&L) with the actual return on plan assets (split between net interest and remeasurement)
- Inadequate sensitivity analysis disclosures

**Related standards:** IAS 37 (termination benefits and restructuring), IFRS 2 (share-based payments), IAS 1 (presentation of OCI — remeasurements presented separately), IFRS 10/IAS 28 (group plan arrangements)

---

## IAS 20 — Accounting for Government Grants and Disclosure of Government Assistance

**Scope:** Applies to all government grants and to the disclosure of other forms of government assistance. Does not apply to: government participation in the ownership of the entity; government grants covered by IAS 41 (agriculture); government assistance provided in the form of tax benefits (investment tax credits, tax holidays — those fall under IAS 12); or special problems of government grants in hyperinflationary economies (IAS 29).

**Core principle:** Government grants shall not be recognised until there is reasonable assurance that the entity will comply with the conditions attached to the grant and that the grant will be received. Grants are recognised in income on a systematic basis over the periods in which the entity recognises as expenses the related costs for which the grants are intended to compensate.

**Key rules:**
- **Types of grants:**
  - *Grants related to assets:* government grants whose primary condition is that an entity qualifying for them should purchase, construct, or otherwise acquire long-term assets
  - *Grants related to income:* government grants other than those related to assets
- **Recognition:**
  - Reasonable assurance is required both that conditions will be complied with and that grants will be received. Cash receipt is not sufficient on its own; nor is a government announcement
  - Non-monetary grants (e.g., land or other resources) may be measured at fair value or at nominal value
  - Repayable grants: treated as a liability when repayment becomes probable
- **Presentation of grants related to assets — two acceptable methods:**
  1. **Deferred income method:** The grant is set up as deferred income and recognised in profit or loss systematically over the useful life of the asset (typically matching the depreciation charge)
  2. **Deduction from asset method:** The grant is deducted from the carrying amount of the asset, reducing depreciation charges over the asset's useful life
  - Both methods produce the same net effect on profit or loss over time
- **Presentation of grants related to income — two acceptable methods:**
  1. **Gross presentation:** Present the grant as "other income" or in a separate line item
  2. **Net presentation:** Deduct the grant from the related expense
  - Gross presentation is generally considered more informative
- **Conditions and contingencies:**
  - If conditions attached to a grant are not met, any amounts recognised must be repaid/reversed
  - When repayment of a grant related to income becomes probable, it is recognised as an expense; when repayment of a grant related to an asset becomes probable, the deferred income is increased (deduction from asset method: carrying amount of asset is increased) by the amount repayable
- **Government assistance** (benefits provided that cannot reasonably have a value placed on them, or transactions which cannot be distinguished from normal trading — e.g., government procurement policies, technical advice): disclosed but not recognised

**Disclosure requirements:**
- Accounting policy adopted for government grants, including presentation methods used
- Nature and extent of government grants recognised, and an indication of other forms of government assistance from which the entity has directly benefited
- Unfulfilled conditions and other contingencies attaching to recognised grants

**Common pitfalls:**
- Recognising a grant on receipt of cash rather than when reasonable assurance criteria are met
- Applying the deferred income method but failing to update the amortisation pattern when the asset's useful life changes
- Inconsistently applying the two presentation methods across similar grants
- Failing to assess and disclose unfulfilled conditions that could lead to repayment
- Not recognising a repayment liability promptly when repayment becomes probable
- Accounting for grants differently under deferred income vs. deduction from asset without considering user comparability

**Related standards:** IAS 16 (PPE — deduction from asset method), IAS 38 (grants related to intangible assets, same two-method presentation), IAS 12 (tax benefits not in scope of IAS 20), IAS 37 (contingent liabilities/repayment obligations), IAS 41 (agricultural grants)

---

## IAS 21 — The Effects of Changes in Foreign Exchange Rates

**Scope:** Applies to: (a) accounting for transactions and balances in foreign currencies; (b) translating results and financial position of foreign operations included in consolidated financial statements or equity-method financial statements; and (c) translating an entity's results and financial position into a presentation currency. Does not apply to: hedge accounting for foreign currency items (IFRS 9), presentation of cash flows from foreign currency transactions in the statement of cash flows (IAS 7), or restatement of financial statements from functional currency to another in hyperinflationary economies (IAS 29).

**Core principle:** An entity shall determine its functional currency — the currency of the primary economic environment in which it operates — and translate all foreign currency items into that functional currency using prescribed exchange rates. The results of foreign operations are then translated into any chosen presentation currency using specific translation procedures, with exchange differences arising on translation recognised in OCI.

**Key rules:**
- **Functional currency determination:**
  - Primary indicators (highest weight): currency that mainly influences sales prices for goods/services; currency of the country whose competitive forces and regulations mainly determine selling prices; currency that mainly influences labour, material, and other costs of providing goods/services
  - Secondary indicators: currency in which financing activities generate funds; currency in which receipts from operating activities are usually retained
  - Management uses judgement when indicators are mixed; once determined, functional currency is not changed unless there is a change in the underlying transactions, events, and conditions
- **Functional vs. presentation currency:**
  - *Functional currency*: determined by economic reality; not a free choice
  - *Presentation currency*: any currency the entity chooses for presenting its financial statements
- **Initial recognition of a foreign currency transaction:**
  - Recorded in the functional currency using the spot exchange rate at the date of the transaction (or an average rate for the period as an approximation if rates do not fluctuate significantly)
- **Translation of monetary vs. non-monetary items at subsequent reporting dates:**
  - *Monetary items* (cash, receivables, payables, loans): retranslated at the closing rate (spot rate at reporting date); exchange differences recognised in **profit or loss**
  - *Non-monetary items measured at historical cost* (PPE at cost, intangibles at cost, inventories): not retranslated; carried at the original transaction-date exchange rate
  - *Non-monetary items measured at fair value* (PPE under revaluation model, equity investments at FVOCI): retranslated at the rate on the date the fair value was determined; exchange differences included in the fair value movement (P&L or OCI depending on the host standard)
- **Exchange differences in P&L:**
  - Arising on settlement or retranslation of monetary items: recognised in profit or loss in the period they arise
  - Exception: exchange differences on intragroup monetary items that form part of the net investment in a foreign operation — recognised in the consolidated financial statements in OCI (accumulated in translation reserve)
  - Exception: exchange differences on foreign currency borrowings that are effective hedges of net investments — recognised in OCI under IFRS 9 hedge accounting
- **Translation of foreign operations into presentation currency:**
  - *Assets and liabilities:* translated at the closing rate at the balance sheet date (including goodwill and fair value adjustments arising on acquisition)
  - *Income and expenses:* translated at exchange rates at the dates of the transactions (or average rates as approximation)
  - *Equity items* (share capital, pre-acquisition reserves): translated at historical rates
  - *Exchange differences arising:* recognised in **OCI** and accumulated in the foreign currency translation reserve (FCTR) in equity
  - On disposal of a foreign operation: the cumulative FCTR relating to that operation is reclassified from OCI to profit or loss (recycled)
  - Partial disposal: proportionate amount of FCTR reclassified only on loss of control/significant influence/joint control; for other partial disposals (without loss of control) the FCTR is not recycled
- **Goodwill and fair value adjustments on acquisition:** Treated as assets/liabilities of the foreign operation and translated at the closing rate
- **Highly inflationary economies (IAS 29 interaction):** The financial statements of a foreign operation that reports in the currency of a hyperinflationary economy should be restated under IAS 29 before being translated at the closing rate

**Disclosure requirements:**
- The amount of exchange differences recognised in profit or loss (except for those arising on financial instruments measured at fair value through P&L)
- Net exchange differences recognised in OCI and classified in a separate component of equity, and a reconciliation of the opening and closing balance of that component
- When the presentation currency is different from the functional currency: that fact, the functional currency, and the reason for using a different presentation currency
- When there is a change in functional currency: that fact, the reason for the change, and the date of the change
- The entity's policy for translating goodwill and fair value adjustments
- When an entity disposes of a foreign operation: amount of exchange differences reclassified to P&L

**Common pitfalls:**
- Treating functional currency as a free choice (it is determined by economic facts, not management preference)
- Retranslating non-monetary items carried at historical cost at the closing rate
- Failing to retranslate monetary items at the closing rate and recognising the exchange difference
- Recognising the translation reserve recycling on partial disposals that do not result in loss of control
- Applying average rates to translate items where exchange rates fluctuated significantly (approximation is permitted only when rates do not fluctuate significantly)
- Not translating goodwill and fair value adjustments at the closing rate (treating them as parent-entity items)
- Forgetting to recycle the FCTR on full disposal of a foreign operation, or recycling on partial disposals that do not involve a loss of control/influence

**Key interpretations:**
- **IFRIC 22 (Foreign Currency Transactions and Advance Consideration):** When advance consideration is paid or received in a foreign currency, the date of the transaction for the resulting non-monetary prepayment asset or liability is the date of initial recognition of the prepayment — not the date the related asset, expense, or income is subsequently recognised.

**Related standards:** IFRS 9 (hedge accounting for foreign currency risk), IAS 7 (translation of cash flows), IAS 29 (hyperinflationary economies), IFRS 3 (business combinations — translation of goodwill and fair value adjustments), IFRS 10 (consolidation — translation of foreign subsidiaries), IAS 28 (equity method — translation of associates/JVs), IFRIC 22 (Foreign Currency Transactions and Advance Consideration)

---

## IAS 23 — Borrowing Costs

**Scope:** Applies to borrowing costs directly attributable to the acquisition, construction, or production of a qualifying asset. Excludes borrowing costs related to assets measured at fair value, inventories manufactured in large quantities on a repetitive basis, and biological assets within the scope of IAS 41.

**Core principle:** Borrowing costs that are directly attributable to the acquisition, construction, or production of a qualifying asset must be capitalized as part of the cost of that asset. All other borrowing costs are expensed in the period incurred.

**Key rules:**
- **Qualifying asset:** An asset that necessarily takes a substantial period of time to get ready for its intended use or sale (e.g., self-constructed buildings, power plants, large inventories, intangible assets under development)
  - No bright-line threshold for "substantial period" — judgment required; typically interpreted as at least 12 months
- **Directly attributable borrowing costs:**
  - Specific borrowings: actual borrowing costs incurred on that borrowing less any investment income on temporary investment of those funds
  - General borrowings: apply a capitalization rate (weighted average cost of general borrowings outstanding) to expenditure on the asset
- **Capitalization rate:** Weighted average of borrowing costs applicable to outstanding general borrowings; excludes borrowings taken out specifically for a qualifying asset
- **Commencement of capitalization:** All three conditions must be met simultaneously:
  - Expenditures on the asset are being incurred
  - Borrowing costs are being incurred
  - Activities necessary to prepare the asset for use or sale are in progress
- **Suspension:** Capitalization is suspended during extended periods of active development being interrupted (not during brief interruptions or necessary delays)
- **Cessation:** Capitalization stops when substantially all activities to prepare the asset for intended use or sale are complete; components of a multi-part asset cease capitalization when substantially complete
- **Excess over recoverable amount:** Capitalized amount reduced to the asset's recoverable amount under IAS 36

**Disclosure requirements:**
- Amount of borrowing costs capitalized during the period
- Capitalization rate used (when general borrowings are used)

**Common pitfalls:**
- Continuing to capitalize during genuine suspension of active development
- Incorrectly including investment income from temporary investment of specific borrowings as a reduction in eligible costs rather than netting it against capitalized costs
- Applying a capitalization rate to total asset expenditure rather than to the weighted average carrying amount of the qualifying asset during the period
- Failing to cease capitalization when the asset is ready for use even if not yet in use

**Related standards:** IAS 2 (inventories — qualifying assets), IAS 16 (PP&E — qualifying assets), IAS 36 (recoverable amount cap), IAS 38 (intangible assets under development), IAS 40 (investment property under construction)

---

## IAS 24 — Related Party Disclosures

**Scope:** Applies to all entities presenting IFRS financial statements. Requires identification and disclosure of related party relationships and transactions, including outstanding balances and commitments. The government-related entity partial exemption applies to entities controlled, jointly controlled, or significantly influenced by a government.

**Core principle:** Financial statements must disclose information about related party relationships, transactions, and outstanding balances — including commitments — that are necessary for users to understand the potential effect on the financial statements.

**Key rules:**
- **Related party definition — persons:** A person (or close family member) is related to the reporting entity if they:
  - Control or jointly control the entity
  - Have significant influence over the entity
  - Are a member of key management personnel (KMP) of the entity or its parent
- **Related party definition — entities:** An entity is related to the reporting entity if:
  - It is a parent, subsidiary, fellow subsidiary, or associate
  - It is a joint venture of the entity or of a group member
  - It is controlled or jointly controlled by a person identified above
  - A person with significant influence over the entity (or close family member) controls it
  - It has a post-employment benefit plan for employees of either entity
  - Note: Two associates of the same investor are NOT related to each other solely for that reason
- **Key management personnel (KMP):** Persons having authority and responsibility for planning, directing, and controlling the activities of the entity, including any director (executive or non-executive)
- **Government-related entity exemption:** An entity related to a government may apply a partial exemption, disclosing only the nature of its relationship, the fact transactions are government-related, and sufficient qualitative/quantitative information — rather than full detail of each transaction
- **Arm's length assertion:** Entities may NOT assert that related party transactions were on arm's length terms unless that claim can be substantiated

**Disclosure requirements:**
- Name of parent and ultimate controlling party (even if no transactions occurred)
- Compensation of KMP in total and split by category (short-term employee benefits, post-employment, other long-term, termination, share-based payment)
- For each category of related party: nature of the relationship, amounts of transactions, outstanding balances and their terms, provisions for doubtful debts, bad debt expense
- Guarantees given or received
- Commitments with related parties

**Common pitfalls:**
- Omitting transactions with entities under common control of KMP's family members
- Disclosing only net amounts rather than gross transaction amounts
- Asserting arm's length terms without substantiation
- Failing to identify post-employment benefit plans as related parties
- Missing the ultimate controlling party disclosure when it differs from the immediate parent

**Related standards:** IFRS 10 (consolidated financial statements — control definition), IFRS 11 (joint arrangements), IAS 27 (separate financial statements), IAS 28 (associates)

---

## IAS 26 — Accounting and Reporting by Retirement Benefit Plans

**Scope:** Applies to the financial statements of retirement benefit plans themselves (i.e., the plan as a reporting entity), not to the employer entity's financial statements. Covers both defined contribution and defined benefit plans. Does not apply to employee benefit costs as reported by employers (that is IAS 19).

**Core principle:** Financial statements of a retirement benefit plan must provide information about the plan's resources and activities that is useful to assess the plan's ability to meet its obligations to current and future beneficiaries.

**Key rules:**
- **Defined contribution plans:**
  - Report a statement of net assets available for benefits
  - Report a description of the funding policy
  - Investments reported at fair value (for marketable securities, fair value is market value)
- **Defined benefit plans:**
  - Report a statement of net assets available for benefits
  - Report a statement of changes in net assets available for benefits
  - Actuarial present value of promised retirement benefits (distinguishing between vested and non-vested) must be disclosed, either:
    - In the financial statements, or
    - In an accompanying actuarial report cross-referenced to the financial statements
  - If actuarial valuation not obtained at reporting date, must use most recent valuation as a basis and disclose the date
  - Investments: reported at fair value; for plan assets, market value is used; if fair value cannot be estimated, disclosure of reason and range in which fair value likely falls
- **Actuarial present value of promised benefits:** Based on benefits promised under the plan's terms using either:
  - Current salary levels, or
  - Projected salary levels — method chosen must be disclosed
- **Relationship between net assets and actuarial present value:** If actuarial present value exceeds net assets available, the plan is in deficit — this relationship must be transparent in the financial statements

**Disclosure requirements:**
- Statement of changes in net assets available for benefits (contributions, investment income, benefits paid, expenses, gains/losses on investments)
- Summary of significant accounting policies, particularly investment valuation basis
- Description of the plan and any changes during the period
- Description of any investment policies
- For defined benefit: actuarial assumptions, method used, date of most recent actuarial valuation

**Common pitfalls:**
- Confusing IAS 26 (plan's own financial statements) with IAS 19 (employer accounting)
- Using cost rather than fair value for plan investments
- Omitting the actuarial present value disclosure or failing to cross-reference an actuarial report
- Not disclosing whether projected or current salaries were used in actuarial valuations

**Related standards:** IAS 19 (employee benefits — employer perspective), IFRS 13 (fair value measurement of plan assets)

---

## IAS 27 — Separate Financial Statements

**Scope:** Applies when an entity elects to or is required by local regulation to present separate financial statements. Separate financial statements are those presented in addition to (or instead of, for certain investment entities) consolidated financial statements. Does not apply to consolidated financial statements (IFRS 10) or equity method accounting in consolidated statements (IAS 28).

**Core principle:** In separate financial statements, investments in subsidiaries, associates, and joint ventures must be accounted for either at cost, in accordance with IFRS 9 (fair value), or using the equity method — with the same method applied to each category of investment.

**Key rules:**
- **Three permitted measurement methods for investments:**
  - Cost method: dividends recognized as income when the right to receive is established; no adjustment for the investee's post-acquisition profits
  - IFRS 9 (fair value): changes in fair value through profit or loss or OCI (for equity instruments designated at FVOCI)
  - Equity method (per IAS 28): share of investee's profit/loss and OCI recognized; permitted but not required
- **Consistency requirement:** Once a method is chosen for a category (e.g., subsidiaries), it must be applied consistently to all investments within that category
- **Dividends:** Under cost method, dividends received are income; entity must assess whether the dividend indicates an impairment of the investment (i.e., dividend exceeds total comprehensive income of the subsidiary)
- **Investment entities:**
  - An investment entity (as defined in IFRS 10) measures subsidiaries at fair value through profit or loss in both consolidated and separate financial statements
  - Exception: subsidiaries that provide investment-related services are consolidated (not measured at FVTPL)
- **Reorganizations:** When parent inserts a new entity above an existing group structure under specific conditions (same ultimate shareholders, no change in rights), the new parent measures investments at the carrying amount of equity items of the original parent
- **Identification:** Separate financial statements must be clearly identified as such and distinguished from consolidated financial statements

**Disclosure requirements:**
- Fact that the financial statements are separate financial statements
- List of significant investments (subsidiaries, associates, joint ventures): name, registered office, country of incorporation, proportion of ownership and voting rights held
- Accounting method used for each category of investments
- If an entity is exempt from consolidation (IFRS 10), the name and principal place of business of the entity that produces consolidated financial statements
- For investment entities: description of nature of the entity, significant judgments in applying the investment entity definition

**Common pitfalls:**
- Using different measurement methods for different subsidiaries within the same category
- Recognizing dividends from subsidiaries as income under cost method without assessing whether they indicate impairment
- Confusing cost method with equity method treatment
- Failing to identify the financial statements clearly as "separate financial statements"

**Related standards:** IFRS 10 (consolidated financial statements), IFRS 11 (joint arrangements), IAS 28 (equity method), IFRS 9 (financial instruments — fair value option), IFRS 13 (fair value)

---

## IAS 28 — Investments in Associates and Joint Ventures

**Scope:** Applies to investments in associates and investments in joint ventures. Does not apply to investments held by venture capital organizations, mutual funds, unit trusts, and similar entities that are measured at FVTPL under IFRS 9 (these entities may elect exemption). Also applies to how the equity method is applied in both consolidated and separate financial statements.

**Core principle:** An investment in an associate or joint venture must be accounted for using the equity method, unless an exemption applies, because the investor has significant influence (or joint control) that creates a relationship closer than a simple financial asset.

**Key rules:**
- **Significant influence:** Presumed when holding 20%–50% of voting rights, unless clearly demonstrated otherwise; can exist below 20% with evidence (board representation, participation in policy-making, material transactions, interchange of managerial personnel, provision of essential technical information)
- **Equity method mechanics:**
  - Initial recognition at cost
  - Subsequently: carrying amount adjusted for the investor's share of profit or loss (recognized in P&L) and other comprehensive income (recognized in OCI)
  - Distributions received reduce the carrying amount
  - Upstream and downstream transactions: profits/losses eliminated to the extent of the investor's interest (unrealized profits on sales between investor and associate)
  - Excess losses: once carrying amount is reduced to zero, investor stops recognizing further losses unless it has incurred legal or constructive obligations or made payments on behalf of the associate
- **Goodwill:** Any goodwill relating to an associate or joint venture is included in the carrying amount and is not separately tested for impairment (but the entire carrying amount is tested under IAS 36)
- **Accounting policies:** If the associate uses different accounting policies, adjustments must be made unless impracticable
- **Reporting dates:** If the associate's financial statements are drawn up to a different date, the investor uses the most recent financial statements; the difference must be no more than three months; adjustments for significant transactions in the intervening period
- **Exemptions from equity method (use IFRS 9 instead):**
  - Investor is a parent exempt from preparing consolidated financial statements under IFRS 10
  - Investment is held for sale (IFRS 5)
  - The investor itself is a wholly-owned or partially-owned subsidiary and certain conditions are met
- **Impairment:** Apply IAS 36 to test the entire carrying amount of the investment as a single asset (not individual components); loss recognized in P&L, reversed if conditions change

**Disclosure requirements:**
- Fair value of investments in associates/joint ventures with quoted prices
- Summarized financial information for each material associate/joint venture (assets, liabilities, revenue, profit/loss, OCI, dividends received)
- Nature and extent of significant restrictions on ability to transfer funds
- Unrecognized losses for the period and cumulatively
- Share of contingent liabilities of associates
- Reasons if 20–50% holding does not give significant influence, or why <20% does

**Common pitfalls:**
- Continuing to recognize losses once the carrying amount reaches zero without legal/constructive obligations
- Failing to eliminate unrealized profits on intercompany transactions
- Using the associate's unadjusted financial statements when accounting policies differ
- Treating goodwill embedded in the equity-accounted carrying amount as separately testable
- Missing the impracticability threshold for aligning accounting policies

**Related standards:** IFRS 3 (business combinations — initial measurement concepts), IFRS 5 (assets held for sale), IFRS 9 (financial instruments — fair value alternative), IFRS 10 (consolidated financial statements), IFRS 11 (joint arrangements), IFRS 12 (disclosures), IAS 27 (separate financial statements), IAS 36 (impairment)

---

## IAS 29 — Financial Reporting in Hyperinflationary Economies

**Scope:** Applies when an entity's functional currency is the currency of a hyperinflationary economy. Applies to the financial statements (including consolidated financial statements) of any entity whose functional currency is hyperinflationary. There is no absolute rate of inflation that establishes hyperinflation; judgment is required based on qualitative and quantitative indicators.

**Core principle:** Financial statements of an entity that reports in the currency of a hyperinflationary economy must be stated in terms of the measuring unit current at the balance sheet date — i.e., all amounts restated to the current purchasing power unit — and the gain or loss on the net monetary position recognized in profit or loss.

**Key rules:**
- **Indicators of hyperinflation** (not exhaustive; judgment required):
  - The general population prefers to keep wealth in non-monetary assets or stable foreign currency
  - Prices are quoted in a stable foreign currency
  - Credit transactions use prices that compensate for expected purchasing power loss
  - Interest rates, wages, and prices are linked to a price index
  - Cumulative three-year inflation rate approaches or exceeds 100%
- **Restatement of historical cost financial statements:**
  - Non-monetary items (PP&E, inventories, equity items, revenue/expense at historical transaction dates): restated by applying a general price index from the date of acquisition/transaction to the balance sheet date
  - Monetary items (cash, receivables, payables): already expressed in current measuring unit; NOT restated but give rise to monetary gain or loss
  - Monetary gain or loss = the net effect of holding monetary assets and liabilities during a period of inflation; recognized in P&L (IAS 29 requires separate disclosure)
  - Opening equity restated from transaction dates using general price index
  - All items in the income statement and cash flow statement restated to current measuring unit using the price index at the transaction date (or average rate as an approximation if inflation was roughly even)
- **Restatement of current cost financial statements:** Non-monetary items already at current cost are not further restated; other procedures same as above
- **Consolidated financial statements:** Subsidiary in hyperinflationary economy: restate its financial statements before including in the consolidation (even if parent is not hyperinflationary); then translate using the closing exchange rate
- **Comparatives:** Prior period comparatives restated to the current period measuring unit (not presented in the original measuring unit)
- **When hyperinflation ceases:** Cease applying IAS 29; amounts expressed in current measuring unit at the date of cessation become the new historical cost basis

**Disclosure requirements:**
- Fact that financial statements and prior period comparatives have been restated for changes in purchasing power
- Whether the financial statements are based on historical cost or current cost approach
- Identity and level of the price index at the balance sheet date and the movement during the period
- Gain or loss on net monetary position (usually in P&L or as a separate line)

**Common pitfalls:**
- Failing to identify hyperinflation early — waiting for the 100% threshold rather than using qualitative indicators
- Restating monetary items (which are already in current units)
- Using an exchange rate instead of a domestic price index for restatement
- Presenting prior period comparatives in original nominal terms rather than restated current-period units
- After cessation, reverting to historical costs at the original amounts instead of using the restated carrying amounts as the new deemed cost

**Related standards:** IAS 21 (effects of changes in foreign exchange rates — translation of hyperinflationary subsidiaries), IFRS 13 (fair value), IAS 36 (impairment of restated assets)

---

## IAS 32 — Financial Instruments: Presentation

**Scope:** Applies to the classification of financial instruments as financial liabilities or equity, to the presentation of compound instruments, and to the offsetting of financial assets and liabilities. Does NOT address recognition, measurement, or hedge accounting (those are IFRS 9). Applies from the issuer's perspective.

**Core principle:** The classification of a financial instrument as a financial liability or equity must be based on the substance of the contractual arrangement and the economic reality, not legal form. A financial instrument is equity only if the issuer has no contractual obligation to deliver cash or another financial asset, and settlement in the issuer's own equity instruments meets specific criteria.

**Key rules:**
- **Liability vs. equity classification — the fundamental test:**
  - Financial liability: instrument gives rise to a contractual obligation to deliver cash or another financial asset, OR to exchange financial instruments under potentially unfavourable conditions
  - Equity: residual interest after deducting all liabilities; NO contractual obligation to deliver cash or other financial assets
  - Preference shares: classified as liabilities if they carry mandatory dividend payments or mandatory redemption (regardless of being called "shares")
  - Perpetual debt: may be equity if there is genuinely no obligation to repay
- **Puttable instruments:** Classified as equity only if they meet strict conditions under IAS 32.16A–16D (reclassification from liability to equity exception)
- **Contingent settlement provisions:** If settlement depends on uncertain future events beyond the control of both parties, the instrument is a liability (unless the contingency is extremely rare, highly abnormal, or remote)
- **Compound financial instruments (split accounting):**
  - Instruments with both liability and equity components (e.g., convertible bonds) must be split on initial recognition
  - Liability component = present value of contractual cash flows discounted at the market rate for a comparable non-convertible instrument
  - Equity component = residual (total proceeds minus liability component); no subsequent remeasurement of the equity component
  - Transaction costs allocated proportionately between liability and equity components
  - On conversion: derecognize the liability, reclassify equity component — no gain or loss
- **Treasury shares:** Own equity instruments reacquired must be deducted from equity; no gain or loss recognized on purchase, sale, issue, or cancellation of treasury shares; consideration paid/received is recognized directly in equity
- **Interest, dividends, gains and losses:**
  - Payments on instruments classified as financial liabilities: recognized in P&L (interest expense)
  - Payments on instruments classified as equity: distributions from equity, not expense
- **Offsetting financial assets and liabilities:**
  - Present net only when BOTH conditions are met:
    - Legally enforceable right to set off the amounts, AND
    - Intention to settle net OR realize the asset and settle the liability simultaneously
  - Master netting agreements alone do NOT meet the offsetting criteria unless both conditions are satisfied

**Disclosure requirements:**
- The nature and extent of risks arising from financial instruments (detailed disclosures required by IFRS 7, not IAS 32 itself)
- For compound instruments: the carrying amounts of the liability and equity components
- Terms and conditions of equity instruments

**Common pitfalls:**
- Classifying preference shares as equity merely because they are called "shares" — must assess contractual obligations
- Forgetting to split compound instruments at inception and not tracking the unamortized discount on the liability component
- Assuming a master netting agreement permits offsetting — it only does if real-time simultaneous settlement is intended or the legal right is currently enforceable in all circumstances
- Treating the equity component of a convertible bond as a liability when conversion is probable
- Recognizing gain or loss on repurchase of own equity instruments

**Related standards:** IFRS 7 (financial instruments disclosures), IFRS 9 (financial instruments — recognition and measurement), IFRS 2 (share-based payment — instruments to deliver own equity)

---

## IAS 33 — Earnings Per Share

**Scope:** Applies to entities whose ordinary shares (or potential ordinary shares) are publicly traded, and to entities that are in the process of issuing such instruments. Other entities that disclose EPS voluntarily must comply with IAS 33 in full. Applies to individual and consolidated financial statements; where consolidated are presented, EPS is based on consolidated data.

**Core principle:** EPS provides a measure of the return attributable to each ordinary share. Basic EPS reflects actual shares outstanding; diluted EPS reflects the maximum potential dilution from convertible instruments, options, and warrants, giving users a "worst-case" picture of per-share earnings.

**Key rules:**
- **Basic EPS:**
  - Numerator: profit or loss attributable to ordinary equity holders of the parent, after deducting preference dividends (including undeclared cumulative preference dividends) and other adjustments for non-ordinary instruments
  - Denominator: weighted average number of ordinary shares outstanding during the period
  - Bonus issues / stock splits: treated as if they occurred at the beginning of the earliest period presented (retrospective adjustment; no time-weighting)
  - Rights issues at below-market price: contains a bonus element; use a theoretical ex-rights price to restate prior periods
- **Diluted EPS:**
  - Numerator: adjusted for after-tax effect of dividends/interest on dilutive potential ordinary shares and other adjustments
  - Denominator: weighted average shares plus weighted average dilutive potential ordinary shares (options, warrants, convertibles, contingently issuable shares)
  - Options/warrants: treasury share method — only the incremental shares (proceeds assumed to buy back shares at average market price) are added; out-of-the-money options are anti-dilutive
  - Convertible instruments: "if converted" method — add back after-tax interest on convertibles; add all shares that would result from conversion from the beginning of the period (or issue date if later)
  - Anti-dilutive instruments: EXCLUDED from diluted EPS (must disclose their existence)
  - Order of dilution: instruments ranked from most dilutive to least dilutive (incremental EPS method); include in sequence until cumulative EPS is no longer declining
- **Contingently issuable shares:** Included in diluted EPS if conditions are currently satisfied; included in basic EPS only when all conditions are met and shares are actually issued
- **Restatement:** If share transactions occur after the reporting date but before financial statements are authorized, EPS is recalculated for all periods presented
- **Presentation:** Basic and diluted EPS for continuing operations and for total profit/loss (including discontinued) must be presented on the face of the income statement with equal prominence

**Disclosure requirements:**
- Basic and diluted EPS on the face of the statement of comprehensive income (or income statement)
- Numerators used (reconciled to profit/loss) and denominators (shares)
- Instruments that could potentially dilute basic EPS in the future but were anti-dilutive in the current period
- Description of transactions after the reporting date that would have changed EPS materially

**Common pitfalls:**
- Including anti-dilutive instruments in diluted EPS calculations (this increases EPS, which is not "dilution")
- Failing to adjust the prior period comparatives for bonus issues or share splits
- Incorrect treatment of the bonus element in a rights issue (using full proceeds rather than theoretical ex-rights price)
- Omitting the adjustment for cumulative preference dividends even when not declared
- Using end-of-period shares rather than the weighted average for basic EPS

**Related standards:** IFRS 5 (discontinued operations — EPS must show contribution), IAS 32 (classification of preference shares affects EPS numerator), IFRS 2 (share-based payment — dilution from options)

---

## IAS 34 — Interim Financial Reporting

**Scope:** Applies when an entity is required or elects to publish interim financial reports. Does not mandate which entities must present interim reports or how frequently — that is determined by securities regulators or other authorities. IAS 34 sets the minimum content and recognition/measurement principles for such reports.

**Core principle:** Interim financial reports must provide an update on the most recent annual financial statements, focusing on new activities, events, and circumstances. The same recognition and measurement principles applied in annual financial statements must be applied in interim periods.

**Key rules:**
- **Minimum content (condensed interim financial report):**
  - Condensed statement of financial position
  - Condensed statement of comprehensive income (or separate income statement)
  - Condensed statement of changes in equity
  - Condensed statement of cash flows
  - Selected explanatory notes
  - If a complete set is presented, it must conform to all IFRS requirements
- **Comparative periods:**
  - Balance sheet: current period-end vs. most recent annual year-end
  - Income statement: current interim period and YTD vs. comparable periods of preceding year
  - Cash flow: YTD vs. comparable YTD of preceding year
  - Changes in equity: YTD vs. comparable YTD of preceding year
- **Discrete vs. integral approach:**
  - IAS 34 requires the discrete approach: each interim period is treated as a discrete accounting period
  - Revenues are recognized when earned; costs are accrued when incurred — NOT deferred/anticipated solely because of the annual accounting period
- **Taxes:** Use the estimated annual effective tax rate to determine the tax expense for the interim period (exception to strict discrete approach — anticipation of full-year tax is required)
- **Year-end bonuses, seasonal revenues:** Recognized on the same basis as annual (do not smooth or defer)
- **Materiality:** Assessed in relation to interim period financial data, not the expected full-year data
- **Changes in accounting policy:** Applied retrospectively; restate all prior period interim data presented
- **Estimates:** If an estimate made in an interim period is revised in a subsequent interim period in the same year, recognize in the period of change; do NOT restate prior interim periods (prospective treatment within the year)
- **Fourth quarter:** No separate fourth-quarter report required, but significant events between the third quarter and year-end must be disclosed in the annual financial statements

**Disclosure requirements:**
- Significant events and transactions (including seasonality/cyclicality, unusual items, changes in estimates, dividends, segment information, acquisitions/disposals, changes in accounting policy)
- Statement that the same accounting policies as the most recent annual report have been applied (or description of any changes)
- Comparative figures as required
- Explanation of seasonality or cyclicality of operations

**Common pitfalls:**
- Deferring costs in early interim periods that are expected to benefit later periods (not permitted — costs expensed when incurred)
- Anticipating revenues not yet earned at interim date to smooth annual results
- Using year-to-date materiality rather than interim period materiality
- Restating prior interim periods for changes in estimates (should be prospective within the year)
- Omitting segment disclosures required by IFRS 8 in condensed interim reports

**Related standards:** IFRS 8 (operating segments — segment disclosures required), IAS 12 (income taxes — annual effective tax rate method), IAS 36 (impairment — cannot reverse impairment recognized at interim date in subsequent interim period of same year)

---

## IAS 36 — Impairment of Assets

**Scope:** Applies to impairment testing of most non-financial assets, including PP&E, right-of-use assets, investment property carried at cost, intangible assets, goodwill, investments in subsidiaries/associates/JVs, and assets under construction. Key exclusions: financial assets (IFRS 9), investment property at fair value (IAS 40), biological assets at fair value (IAS 41), deferred tax assets (IAS 12), employee benefit plan assets (IAS 19), and most non-current assets held for sale (IFRS 5).

**Core principle:** An asset must not be carried at more than its recoverable amount. If the carrying amount exceeds the recoverable amount, an impairment loss must be recognized immediately. Recoverable amount is the higher of fair value less costs of disposal (FVLCOD) and value in use (VIU).

**Key rules:**
- **Indications of impairment** (trigger review required at each reporting date):
  - External: significant decline in market value, adverse changes in technology/market/economy/law, increase in market interest rates, market capitalization below net assets
  - Internal: evidence of obsolescence, physical damage, significant changes in use or performance below expectation, worse-than-expected economic performance
  - Goodwill, indefinite-life intangibles, and intangibles not yet available for use: tested annually regardless of indicators
- **Recoverable amount:**
  - FVLCOD: price from an orderly transaction between market participants less incremental costs to sell (per IFRS 13 fair value hierarchy); excludes financing costs and tax
  - VIU: present value of future cash flows expected from the asset in its current condition and intended use
    - Cash flow projections: based on reasonable assumptions, maximum 5-year management budgets/forecasts (beyond 5 years, extrapolate using a steady or declining growth rate — growth rate must not exceed long-term average for country/industry)
    - Exclude financing cash flows and income taxes
    - Discount rate: pre-tax rate reflecting current market assessments of time value of money and asset-specific risks; may start from a WACC and adjust; must be consistent with how cash flows are estimated
    - Terminal value using a Gordon Growth Model or exit multiple is common but the growth rate cap applies
- **Cash-generating units (CGUs):**
  - Smallest identifiable group of assets generating cash inflows that are largely independent of other assets
  - Asset tested at CGU level if individual asset's recoverable amount cannot be determined
  - CGU boundaries must be consistent period to period
  - CGU must not be larger than an operating segment (before any aggregation) per IFRS 8
- **Goodwill allocation:**
  - Goodwill must be allocated to CGUs (or groups of CGUs) that are expected to benefit from the synergies of the combination
  - Each such CGU represents the lowest level at which goodwill is monitored internally and must not be larger than an operating segment
  - Tested annually (and whenever there is an indicator) by comparing the carrying amount of the CGU (including goodwill) with its recoverable amount
  - Impairment loss on a CGU: first reduces goodwill to zero, then allocated pro-rata to other assets (but not below the highest of FVLCOD, VIU, or zero)
- **Corporate assets:** Cannot generate cash flows independently; allocate to CGUs on a reasonable and consistent basis; if cannot be fully allocated, test the smallest group of CGUs that includes the corporate asset
- **Recognition of impairment loss:**
  - Single asset: recognized in P&L (or in OCI to the extent of a previous revaluation surplus for revalued assets under IAS 16/IAS 38)
  - CGU: reduce goodwill first, then other assets pro-rata
- **Reversal of impairment:**
  - Allowed for individual assets and CGUs (other assets within CGU) if there is an indication that the loss may have decreased
  - Reversal: increased carrying amount must not exceed what the depreciated/amortized carrying amount would have been without the impairment
  - Goodwill impairment: NEVER reversed

**Disclosure requirements:**
- For each class of assets: impairment losses and reversals recognized, their location in the income statement
- For material impairment/reversals: description of the asset/CGU, events leading to the impairment, amount, FVLCOD or VIU approach used
- For CGUs with significant goodwill or indefinite-life intangibles: carrying amount, description of key assumptions, approach to determining values (growth rates, discount rate), sensitivity analysis if reasonable change in assumption would cause further impairment

**Common pitfalls:**
- Using post-tax cash flows with a post-tax discount rate inconsistently (IAS 36 requires pre-tax; the pre-tax and post-tax approaches should give the same answer only if applied correctly)
- Using a growth rate in the terminal value that exceeds the long-term average
- Failing to test goodwill annually and only testing on indicators
- Reversing goodwill impairment losses (never permitted)
- Allocating impairment losses below an asset's FVLCOD or VIU
- Not splitting a CGU when operations or monitoring has changed

**Related standards:** IFRS 3 (goodwill recognition), IFRS 5 (held for sale — impairment rules differ), IFRS 8 (segment reporting — CGU size limit), IFRS 13 (fair value measurement for FVLCOD), IAS 16 (PP&E — revaluation surplus), IAS 38 (intangible assets)

---

## IAS 37 — Provisions, Contingent Liabilities and Contingent Assets

**Scope:** Applies to provisions (liabilities of uncertain timing or amount), contingent liabilities, and contingent assets. Key exclusions: financial instruments at fair value (IFRS 9), executory contracts (unless onerous), insurance contracts (IFRS 17), items covered by other standards (e.g., income taxes — IAS 12, leases — IFRS 16, employee benefits — IAS 19, construction contracts — IFRS 15).

**Core principle:** A provision must be recognized when, and only when: (1) an entity has a present obligation (legal or constructive) as a result of a past event; (2) it is probable (more likely than not) that an outflow of resources embodying economic benefits will be required; and (3) a reliable estimate can be made of the amount. Provisions are distinguished from other liabilities because there is uncertainty about timing or amount.

**Key rules:**
- **Three recognition criteria — all must be met:**
  - Present obligation (legal or constructive) arising from a past obligating event
  - Probable outflow (more likely than not > 50%)
  - Reliable estimate possible (only in extremely rare circumstances will this not be possible)
- **Legal vs. constructive obligation:**
  - Legal: arising from a contract, legislation, or other operation of law
  - Constructive: entity has created a valid expectation through established pattern of past practice, published policies, or specific statements
- **Measurement:**
  - Best estimate of expenditure required to settle the obligation at the reporting date
  - For a large population of items (e.g., warranty provisions): use expected value (probability-weighted average)
  - For a single obligation: use the most likely outcome, but consider other possible outcomes
  - Reflect risks and uncertainties; do not double-count
  - Discount to present value when the time value of money is material (use pre-tax risk-free rate; do not include risks already reflected in cash flows)
  - Future events (e.g., new legislation, technological changes): taken into account only when there is sufficient objective evidence they will occur
  - Expected disposal of assets: NOT included in measurement of a provision (even if tied to the obligating event) — account for separately under IFRS 5/IAS 16
- **Reimbursements:** A reimbursement (e.g., insurance proceeds) is recognized as a separate asset only when virtually certain to be received; offset against provision expense only in P&L presentation; the gross provision is not reduced
- **Onerous contracts:** When unavoidable costs of meeting contractual obligations exceed economic benefits — recognize a provision for the lower of the cost of fulfilling the contract and any compensation/penalties from failing to fulfill it; before recognizing, impair any dedicated assets (IAS 36)
- **Restructuring provisions:** Only when: (1) detailed formal plan exists identifying the business/locations, employees affected, expenditures, and implementation timeline; AND (2) the entity has raised a valid expectation in those affected (announcement or commencement). Future operating losses are NOT included in restructuring provisions.
- **Contingent liabilities:** Possible obligation (not probable) or present obligation not probable or cannot be reliably estimated — disclose in notes only; do NOT recognize on balance sheet
- **Contingent assets:** Possible assets from past events; disclose only when inflow is probable (more likely than not); do not recognize unless inflow is virtually certain (at which point it is no longer contingent)
- **Reviews:** Provisions must be reviewed at each reporting date and adjusted to reflect the current best estimate; if outflow is no longer probable, provision is reversed

**Disclosure requirements:**
- For each class of provision: carrying amount at start and end, additions, amounts used, reversals, discounting effect; description of nature, timing, amount uncertainty, and reimbursement rights
- For contingent liabilities: nature, estimate of financial effect, uncertainties, possibility of reimbursement
- For contingent assets: nature and estimate of financial effect (if probable)
- In extremely rare cases, information may be omitted if its disclosure would seriously prejudice the entity in a dispute — must disclose the general nature and reason for omission

**Common pitfalls:**
- Recognizing provisions for future operating losses (not permitted — no obligation until loss is incurred)
- Recognizing provisions based on management intent rather than past obligating events
- Netting reimbursements against provisions on the balance sheet
- Including future operating costs in restructuring provisions
- Failing to discount long-term provisions when the time value of money is material
- Recognizing contingent assets before inflow is virtually certain

**Key interpretations:**
- **IFRIC 21 (Levies):** The obligating event for a levy imposed by government is the activity that triggers payment as specified in legislation. If the obligating event occurs over a period, the liability is recognised progressively. If triggered by reaching a minimum threshold, no liability is recognised before that threshold is reached.

**Related standards:** IAS 10 (events after the reporting period — clarifying provisions), IAS 12 (income taxes — excluded), IAS 19 (employee benefits — excluded), IFRS 9 (financial guarantees — some may be provisions), IFRS 15 (revenue — onerous contracts overlap), IFRS 16 (leases — onerous lease contracts), IFRIC 21 (Levies)

---

## IAS 38 — Intangible Assets

**Scope:** Applies to intangible assets not covered by other standards. Key exclusions: financial assets (IFRS 9), exploration and evaluation assets (IFRS 6), mineral rights and reserves, intangible assets arising from insurance contracts (IFRS 17), deferred acquisition costs and intangible assets in the scope of IFRS 17. Goodwill from business combinations is within IFRS 3, not IAS 38.

**Core principle:** An intangible asset is recognized when, and only when, it is probable that expected future economic benefits attributable to the asset will flow to the entity, and the cost can be measured reliably. The intangible asset must also meet the definition: it must be identifiable, non-monetary, and without physical substance.

**Key rules:**
- **Definition criteria:**
  - Identifiable: separable (capable of being separated and sold, transferred, licensed) OR arising from contractual or other legal rights
  - Controlled by the entity (power to obtain benefits and restrict others)
  - Future economic benefits attributable to the asset
- **Separate acquisition:** Presumed that the probability criterion is always satisfied; recognized at cost
- **Business combination:** Recognized at fair value at acquisition date (IFRS 3); probability criterion deemed satisfied; recognized separately from goodwill if definition met
- **Internally generated intangibles — the 6 capitalization criteria (development phase):** ALL must be met to capitalize:
  1. Technical feasibility of completing the intangible asset
  2. Intention to complete and use/sell it
  3. Ability to use or sell it
  4. How the asset will generate probable future economic benefits (e.g., existence of a market)
  5. Availability of adequate technical, financial, and other resources to complete development
  6. Ability to reliably measure expenditure attributable to the asset during development
- **Research phase:** ALL research expenditure must be expensed as incurred; if the entity cannot distinguish research from development, treat the entire project as research
- **Internally generated brands, mastheads, publishing titles, customer lists, and similar items:** NEVER recognized as intangible assets (cannot be distinguished from the cost of developing the business as a whole)
- **Subsequent measurement:**
  - Cost model: cost less accumulated amortization less accumulated impairment losses
  - Revaluation model: permitted only if an active market exists for that type of intangible (rare in practice); revalued to fair value less subsequent amortization and impairment
- **Useful life:**
  - Finite useful life: amortize over useful life; method reflects pattern of consumption of economic benefits (straight-line is default if pattern cannot be reliably determined); residual value presumed zero unless commitment from a third party or active market
  - Indefinite useful life: NO amortization; test for impairment annually and whenever there is an indicator; reassess each year whether indefinite life assessment remains appropriate
- **De-recognition:** When disposed of or when no future economic benefits are expected from use or disposal; gain/loss in P&L (not revenue)
- **Advertising and training expenditure:** Always expensed as incurred (even if future benefit is expected — the entity does not control the asset)
- **Website development costs:**
  - Planning stage: expense
  - Application/infrastructure development, graphical design, content development (that generates economic benefits): capitalize if criteria met
  - Operating stage: expense

**Disclosure requirements:**
- For each class: gross carrying amount, accumulated amortization and impairment; useful life or amortization rate; method; reconciliation of carrying amount
- Significant individual intangible assets: description, carrying amount, remaining amortization period
- For intangibles with indefinite useful lives: carrying amount, reasons supporting the indefinite assessment
- R&D expenditure recognized as expense during the period
- For revaluation model: effective date of revaluation, carrying amount under cost model, revaluation surplus

**Common pitfalls:**
- Capitalizing research expenditure or failing to separate research from development phases
- Capitalizing internally generated brands or customer lists
- Applying the revaluation model without an active market for the asset
- Amortizing an asset with an indefinite useful life (should be tested for impairment instead)
- Failing to reassess whether indefinite useful life remains appropriate each period
- Capitalizing training costs or advertising expenditure

**Related standards:** IFRS 3 (intangibles in business combinations), IAS 16 (property, plant and equipment — similar model), IAS 36 (impairment, especially for indefinite-life intangibles and goodwill), IFRS 6 (exploration and evaluation assets — excluded), IFRIC 12 (Service Concession Arrangements — intangible asset model)

---

## IAS 40 — Investment Property

**Scope:** Applies to investment property: land or a building (or part of a building) held to earn rentals, for capital appreciation, or both, rather than for use in production/supply of goods/services or for sale in the ordinary course of business. Includes property held under an operating lease that meets the definition (entity may elect to classify on a property-by-property basis). Excludes owner-occupied property (IAS 16), property held for sale in the ordinary course (IAS 2/IFRS 15), biological assets on land (IAS 41), and mineral rights.

**Core principle:** An entity must choose either the fair value model or the cost model as its accounting policy for all investment property and apply it consistently. Under the fair value model, gains and losses from changes in fair value are recognized in profit or loss. Under the cost model, investment property is measured at depreciated cost less impairment, but fair value must still be disclosed.

**Key rules:**
- **Identification and classification:**
  - Judgment required for properties with dual use (partly owner-occupied, partly let) — classify separately if portions can be sold/leased independently; otherwise only classify as investment property if the owner-occupied portion is insignificant
  - Ancillary services: if services provided are a relatively insignificant component, property is investment property (e.g., building with security services); if services are significant (e.g., hotel), property is owner-occupied (IAS 16)
- **Initial recognition:** At cost, including transaction costs; no start-up costs or initial operating losses before the property achieves planned occupancy
- **Fair value model:**
  - Measured at fair value at each reporting date; changes in fair value recognized in P&L
  - If fair value cannot be reliably measured on a continuing basis (rare), use cost model for that property and disclose the situation; in practice, fair value is presumed determinable for completed investment property
  - Properties under construction that are investment property: measured at fair value if reliably measurable; otherwise at cost until construction complete or fair value becomes reliably measurable
  - NO depreciation under fair value model
- **Cost model:**
  - Depreciated cost (same as IAS 16 cost model) less any accumulated impairment losses
  - Must disclose fair value of the investment property
- **Transfers:**
  - Transfers to/from investment property only when there is a change in use evidenced by:
    - Owner-occupied → investment property: remeasure to fair value under IAS 16 (revaluation), then transfer; difference vs. carrying amount to OCI/P&L per IAS 16
    - Investment property → owner-occupied: deemed cost for subsequent IAS 16 accounting is the fair value at date of change
    - Investment property → inventories: deemed cost for IAS 2 is fair value at date of change
    - Inventories → investment property (e.g., developer keeps a property): difference between fair value and carrying amount recognized in P&L
  - Under cost model, transfers between categories at carrying amount with no P&L impact
- **Disposal:** Derecognize on disposal or when no future economic benefits are expected; gain/loss is the difference between net disposal proceeds and carrying amount; recognize in P&L (not revenue)

**Disclosure requirements:**
- Whether fair value or cost model is used
- Criteria to distinguish investment property from owner-occupied and inventory property
- Methods and assumptions in determining fair value (for both models)
- Fair value model: reconciliation of opening to closing carrying amounts; income/expenses from investment property; existence and amounts of restrictions; contractual obligations to purchase, construct, or develop
- Cost model: depreciation methods, useful lives, gross carrying amounts, accumulated depreciation and impairment, reconciliation; fair value of the investment property (or explanation if not determinable)

**Common pitfalls:**
- Classifying hotel properties or student accommodation as investment property (they are owner-occupied if the services provided are significant)
- Failing to recognize fair value changes in P&L under the fair value model (some entities incorrectly recognize in OCI)
- Incorrectly accounting for transfers — particularly the IAS 16 revaluation treatment required on transfer from owner-occupied to investment property
- Not depreciating under the cost model (many preparers omit depreciation on investment property)
- Using net rental yield to impute fair value rather than using IFRS 13 valuation techniques

**Related standards:** IAS 16 (owner-occupied property), IAS 2 (property held for sale — inventory), IFRS 13 (fair value measurement), IAS 36 (impairment under cost model), IFRS 16 (lease classification — right-of-use assets may be classified as investment property)

---

## IAS 41 — Agriculture

**Scope:** Applies to biological assets (living animals and plants) in the context of agricultural activity, agricultural produce at the point of harvest, and government grants related to biological assets measured at fair value less costs to sell. Does not apply to land related to agricultural activity (IAS 16/IAS 40), intangible assets related to agricultural activity (IAS 38), or bearer plants (which are within IAS 16 following 2014 amendments).

**Core principle:** A biological asset must be measured at fair value less costs to sell, both on initial recognition and at each subsequent reporting date, with changes recognized in profit or loss, unless fair value cannot be reliably measured. Agricultural produce harvested from biological assets is measured at fair value less costs to sell at the point of harvest; this becomes the cost basis for IAS 2 thereafter.

**Key rules:**
- **Definitions:**
  - Biological asset: a living animal or plant (e.g., livestock, dairy cattle, vines, fruit trees excluding bearer plants, fish stocks, poultry)
  - Agricultural produce: the harvested product from biological assets (e.g., milk, wool, picked grapes, harvested fish)
  - Agricultural activity: management of the biological transformation of biological assets for sale, as agricultural produce, or as additional biological assets
  - Harvest: detachment of produce from a biological asset or cessation of a biological asset's life processes
  - Bearer plant (post-2014): a living plant used in the production/supply of agricultural produce, expected to bear produce for more than one period, and for which there is a remote likelihood of being sold as agricultural produce — accounted for under IAS 16, not IAS 41 (only the produce growing on the bearer plant remains under IAS 41)
- **Measurement — fair value less costs to sell (FVLCTS):**
  - Apply fair value hierarchy (IFRS 13): quoted market prices in active markets are the best evidence; if no active market, use most recent market transaction price, market prices for similar assets, or sector benchmarks
  - Costs to sell: incremental costs directly attributable to disposal (commissions, levies, transfer taxes) — exclude transport costs if market price is for an asset at its current location
  - Grouped by age, quality, or other attributes for measurement if prices exist for such groups
- **Unreliable fair value exception:**
  - Only on initial recognition and only if quoted market prices are not available and alternative fair value estimates are clearly unreliable
  - Measure at cost less accumulated depreciation and impairment
  - Once fair value becomes reliably measurable, switch to FVLCTS (prospective); do not restate
  - This exception is expected to be rare
- **Government grants related to biological assets at FVLCTS:**
  - Unconditional: recognize when and only when the grant becomes receivable
  - Conditional: recognize when conditions are met
  - Contrast with IAS 20 treatment (which may permit deferral) — IAS 41's treatment takes precedence for biological assets in scope
- **Agricultural produce:**
  - Measured at FVLCTS at the point of harvest
  - After harvest: IAS 2 (inventories) or other applicable standards; the harvest value is the cost for IAS 2 purposes — no further fair value accounting under IAS 41
- **Gains and losses:**
  - Initial recognition of biological assets at fair value: gain or loss in P&L
  - Changes in fair value during the period: gain or loss in P&L
  - Physical changes (growth, degeneration, procreation) and price changes are both reflected in the gain/loss; entities are encouraged but not required to disclose the split between physical change and price change components

**Disclosure requirements:**
- Aggregate gain or loss from initial recognition of biological assets and agricultural produce and from changes in fair value
- Description of each group of biological assets
- Biological asset carrying amounts split by consumable and bearer (note: bearer plants now in IAS 16; remaining in IAS 41 are animals/produce-bearing plants)
- Methods and assumptions in determining fair value, including whether market prices are used or valuation techniques
- Fair value of agricultural produce harvested during the period
- Existence and carrying amounts of biological assets subject to restricted title or pledged as security
- Commitments for development/acquisition of biological assets
- Financial risk management strategies related to agricultural activity
- Reconciliation of opening and closing carrying amounts of biological assets (showing physical changes separately from price changes if disclosed)
- For government grants: nature and extent, conditions, significant decreases expected

**Common pitfalls:**
- Continuing to apply IAS 41 to bearer plants (post-2014 amendment these are within IAS 16)
- Applying IAS 41 to agricultural land (IAS 16 or IAS 40)
- Applying IAS 41 after harvest — post-harvest produce is within IAS 2
- Including transport costs in costs to sell when the market price already reflects transport to market
- Using cost as a proxy for fair value without properly establishing that fair value is unreliable
- Double-counting the FVLCTS adjustment on both biological assets and government grants

**Related standards:** IAS 2 (inventories — agricultural produce after harvest), IAS 16 (PP&E — bearer plants, agricultural land at cost), IAS 20 (government grants — general; IAS 41 overrides for in-scope biological assets), IAS 36 (impairment — applies to biological assets measured at cost under the unreliable fair value exception), IAS 40 (investment property — land used in agriculture), IFRS 13 (fair value measurement hierarchy)

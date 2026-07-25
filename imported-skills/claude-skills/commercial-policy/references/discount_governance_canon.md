# Discount Governance Canon

Authoritative sources on **how mature SaaS companies govern discounts off list price** — the rules of engagement that the commercial-policy skill operationalizes. Cite these in any policy doc this skill produces.

The unifying claim across every source below: **discount discipline correlates more strongly with retention and gross margin expansion than top-of-funnel velocity.** Bands aren't conservative for the sake of it — they protect the LTV math that funds the next year of GTM.

---

## 1. OpenView Partners — Annual SaaS Benchmarks (2018-2025)

OpenView's annual State of the SaaS Industry survey publishes discount distributions by ARR band and growth stage. Two consistent findings across 7 years:

- **Median enterprise discount = 18–22% off list.** Anything above 30% is the top decile and correlates with weaker NRR (typically 8–12 pts lower than disciplined peers).
- **The top quartile on net dollar retention discounts ~6 pts less than the bottom quartile.** Less discount, more retention — the leaky-bucket effect of "buying logos" with deep discounts shows up at renewal.

**Cite this for:** the empirical floor on what a "normal" discount band looks like across the SaaS industry. If your band exceeds 30% for non-strategic deals, you're outside the disciplined cohort.

URL: https://openviewpartners.com/blog/saas-benchmarks/

---

## 2. David Skok — For Entrepreneurs ("Discount Math")

Skok's canonical post on discount math shows that a percentage discount off list price erodes margin **more than proportionally**:

> A 30% discount on an 80% gross-margin product reduces margin by **37.5%**, not 30%. The discount is taken before the cost of goods sold is subtracted, so each percentage of discount removes a larger percentage of gross margin.

He further argues that the LTV impact compounds: discounted customers tend to expand less (lower NRR) and churn earlier (lower retention). The compound effect on LTV/CAC is often 2-3× the headline discount percentage.

**Cite this for:** the margin-floor calculation in `discount_matrix_builder.py`. The skill's per-cell `margin_floor_pct` enforces a hard floor below which no cell can publish a discount band.

URL: https://www.forentrepreneurs.com/

---

## 3. Tomasz Tunguz — Discount Distribution Studies (Redpoint)

Tunguz has published multiple analyses of discount distribution across enterprise SaaS deals (using anonymized Redpoint portfolio data). Three structural findings:

- **End-of-quarter discounts are 7-10 pts deeper than mid-quarter** across every ARR band. This is a forecast-pressure artifact, not a customer-value signal.
- **Deals closing in the last week of a quarter have NRR 4-6 pts lower at year 1** than deals closing in week 1-11.
- **Logo discounts that aren't accompanied by a written expansion commitment** show no NRR premium over standard discounts — the strategic value never materializes.

**Cite this for:** the "named expansion path in writing" compensating commitment in `exception_router.py`. Tunguz's data is the empirical reason verbal expansion promises aren't enough.

URL: https://tomtunguz.com/

---

## 4. Bessemer Venture Partners — State of the Cloud (annual)

BVP's State of the Cloud report (2020-2026) tracks discount and retention by cohort. Key claims this skill leans on:

- **Companies with formal discount matrices have NRR 8-15 pts higher** than peers with ad-hoc approval.
- **"Approver-of-record" governance** (every discount tied to a named human, not a role) reduces discount creep year-over-year by ~50%.
- The "Rule of 40" companies (growth + margin > 40%) consistently sit in the bottom quartile on discount depth.

**Cite this for:** the requirement that every cell in the matrix carry a named `approver_tier`, and that exceptions produce an `audit_trail` block with `requested_by` and `approver_chain` recorded.

URL: https://www.bvp.com/atlas/state-of-the-cloud-2025

---

## 5. KeyBanc Capital Markets — Annual SaaS Survey (formerly Pacific Crest)

KeyBanc's annual private-SaaS survey (~400 respondents) consistently publishes payment-terms and term-length data. Two findings the matrix encodes:

- **Every 15 days of payment terms adds ~2% to effective deal value.** NET-60 vs NET-30 is worth ~4% — so a customer asking for NET-60 plus 30% discount is asking for ~34% effective discount.
- **Multi-year prepay deals carry ~3-5 pts of NRR premium** over annual auto-renew, even at higher discount levels, because the cash and the commitment lock retention.

**Cite this for:** the `payment_penalty` and `term_bonus` parameters in `discount_matrix_builder.py`. NET-60 carries a penalty; multi-year prepay carries a bonus.

URL: https://key.com/businesses-institutions/industries-expertise/technology.jsp

---

## 6. Bridge Group — SaaS AE Compensation & Approval Research

Bridge Group's annual benchmark study of SaaS sales orgs publishes approver-chain practices. Two structural findings:

- **AEs allowed to self-approve discounts > 15% show 30%+ year-over-year discount creep.** Self-approval normalizes deeper discounts; AEs anchor on what they themselves approved last quarter.
- **Named-human approval reduces precedent drift by 50%+** vs. role-only approval. "VP Sales approves" is structurally weaker than "Maria Singh, VP Sales, approved on date X with these compensating commitments".

**Cite this for:** the audit-trail metadata block in `exception_router.py`, and the explicit `requested_by` field. The lint rule L09 (`cell_unreviewed`) is downstream of Bridge's finding that unobserved bands drift.

URL: https://bridgegroupinc.com/sales-research/

---

## 7. RevOps Co-op — Policy Design Playbooks

The RevOps Co-op community (Rosalyn Santa Elena, Jeff Ignacio, others) has published several playbooks on commercial-policy design. Three principles the skill enforces:

- **Discount bands must be backed by win-rate AND retention data**, not by sales leadership's negotiating room. If you can't show "at this band, we win X% and retain at NRR Y", the band is rhetoric.
- **Every exception must produce written compensating commitments** before the approver signs. "Strategic" isn't enough — what specifically does the customer commit to, in writing?
- **Quarterly policy review is non-optional.** Markets shift, competitors shift, customer mix shifts — a matrix unchanged for 12 months is almost certainly mispriced in some band.

**Cite this for:** the `data_backing` field per cell in `discount_matrix_builder.py` and the `required_compensating_commitments` block in `exception_router.py`. Lint rule L08 (thin data in critical cell) operationalizes RevOps Co-op's first principle.

URL: https://www.revopscoop.com/

---

## 8. Forrester — Deal Desk & Commercial Policy Research

Forrester's Deal Desk research (Mary Shea, Anthony McPartlin, Bob Apollo) consistently finds that companies with **formalized, data-backed commercial policy** outperform peers on three metrics:

- Cycle time (faster approvals when policy is clear)
- Win rate (AEs don't waste time on deals outside policy)
- Renewal margin (discounts at sign predict renewal economics)

The Forrester model treats commercial policy as a **product** that the RevOps team ships and maintains — not a memo that lives in the CFO's drawer.

**Cite this for:** the framing of commercial-policy as a designed artifact (with the lint pass), versus a precedent that accumulates through deal-by-deal exceptions.

URL: https://www.forrester.com/research/

---

## Synthesis: how the canon maps to this skill

| Canon source | Maps to |
|---|---|
| OpenView discount benchmarks | `base_max_pct` defaults in `PROFILES` |
| Skok discount math | `margin_floor_pct` enforcement per cell + lint L03 |
| Tunguz expansion-commitment data | `named_expansion_path` compensating commitment |
| BVP discount discipline | `approver_tier` per cell + audit trail |
| KeyBanc payment-terms data | `payment_penalty` and `term_bonus` parameters |
| Bridge Group AE-approval research | `requested_by` + audit trail metadata |
| RevOps Co-op playbooks | `data_backing` per cell + quarterly review hook |
| Forrester deal-desk research | The skill's existence — policy as designed artifact |

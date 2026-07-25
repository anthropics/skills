# Contract Landmines

The 10 founder/seller-killer patterns the `terms_redliner.py` tool detects, with example counter-language for each. This is a triage reference, **not** legal advice — every HIGH/CRITICAL finding must be reviewed by named counsel before signing.

For deep prose-level redline of an actual contract, use `c-level-advisor/skills/general-counsel-advisor/scripts/contract_risk_scanner.py`. The tool in this skill operates on a *structured terms JSON*, which is what the deal desk typically has from the intake template.

## The 10 patterns

### 1. UNCAPPED_INDEMNITY (CRITICAL)

**Trigger**: `indemnity_cap` is `null` or absent.

**Why it matters**: A single indemnity claim can be larger than the entire ARR of the deal — sometimes larger than the company's revenue. Uncapped indemnity is the most common contract risk that destroys early-stage companies.

**Counter-language**:

> "Each party's aggregate liability for indemnification obligations shall not exceed twelve (12) times the monthly subscription fees paid in the twelve (12) months preceding the claim, except for breaches of confidentiality, willful misconduct, or third-party intellectual-property infringement, for which a super-cap of three (3) times annual fees shall apply."

**Approver**: General Counsel + CFO.

### 2. MISSING_DPA_EU_DATA (CRITICAL)

**Trigger**: `eu_data_involved == True` and `dpa_present == False`.

**Why it matters**: GDPR Article 28 mandates a Data Processing Agreement when personal data of EU residents is processed by a service provider. Missing DPA = (a) regulatory exposure under GDPR, (b) immediate audit failure on any SOC 2 or ISO 27001 review, (c) customer escalation to their privacy officer.

**Counter-language**: Attach standard DPA (2021/914 Standard Contractual Clauses, or vendor's own template) as an exhibit. **Do not sign the master agreement until the DPA is countersigned.**

**Approver**: General Counsel + DPO.

### 3. MFN_PRICING (HIGH)

**Trigger**: `mfn_clause_present == True`.

**Why it matters**: Most-Favored-Nation clauses bind the seller to refund the customer (or extend matching terms) if any other customer gets a better price. This freezes pricing innovation: no bundles, no segment pricing, no competitive deals without triggering MFN obligations across the base.

**Counter-language**:

> "Strike Section [X] (Most-Favored-Nation Pricing) in its entirety. If retained, scope to: same SKU, same volume tier, same contract term, same geography, and same industry vertical; and time-bound to twelve (12) months from the Effective Date."

**Approver**: VP Sales + CFO.

### 4. AUTORENEW_LONG_NOTICE (HIGH)

**Trigger**: `auto_renew == True` and `auto_renew_notice_days > 30`.

**Why it matters**: Auto-renewal with a long notice window (60, 90, 120 days) is a classic vendor trap. Customers miss the window and get locked into another full term — but this also goes the other way: as a seller, accepting 60+ day notice on your own auto-renewals gives the buyer asymmetric exit.

**Counter-language**:

> "Either party may provide written notice of non-renewal not less than thirty (30) days prior to the end of the then-current term."

**Approver**: Deal Desk + General Counsel.

### 5. PERPETUAL_LICENSE_BACK (CRITICAL)

**Trigger**: `ip_assignment == "perpetual_license_back"`.

**Why it matters**: A perpetual license-back gives the customer the right to use the vendor's IP **forever**, often royalty-free and surviving termination. This kills the moat — the customer can stop paying and keep using.

**Counter-language**:

> "Customer's license to the Services and Vendor IP is co-terminus with the Subscription Term, field-of-use limited to internal business operations, non-transferable, non-sublicensable, and terminates upon any termination or expiration of this Agreement."

**Approver**: General Counsel + CEO.

### 6. AMBIGUOUS_IP (HIGH)

**Trigger**: `ip_assignment == "ambiguous"`.

**Why it matters**: Ambiguous IP ownership becomes a dispute at acquisition diligence. Buyers will hold back purchase price (or walk) until IP chain-of-title is clarified. Costs weeks of legal time and can break an M&A deal.

**Counter-language**:

> "Vendor retains all right, title, and interest in and to the Services, the Vendor IP, and any improvements, modifications, or derivatives thereof developed in connection with this Agreement. Customer retains all right, title, and interest in Customer Data and in any outputs derived solely from Customer Data."

**Approver**: General Counsel.

### 7. EXCLUSIVITY_UNCOMPENSATED (CRITICAL)

**Trigger**: `exclusivity_clause_present == True` and `exclusivity_compensated == False`.

**Why it matters**: Exclusivity removes the entire competitive segment of the addressable market for no economic benefit. Even *paid* exclusivity needs a kill switch on missed quarterly minimums — otherwise the buyer locks the seller into the segment without performance pressure.

**Counter-language**:

> "Strike exclusivity in its entirety. If retained, exclusivity is contingent on Minimum Guaranteed Spend of $[X] per quarter, payable in advance, and Vendor may terminate exclusivity (while preserving the underlying agreement) upon two consecutive quarters of MGS shortfall."

**Approver**: CRO + General Counsel.

### 8. LONG_PAYMENT_TERMS (HIGH)

**Trigger**: `payment_terms_days > 45`.

**Why it matters**: NET-60/75/90/120 inflates DSO and ties up working capital. A $200K deal on NET-90 is effectively $200K of zero-interest financing extended to the buyer. Material on any deal that's > 10% of cash balance.

**Counter-language**:

> "Payment terms shall be NET-30 from invoice date. Customer may elect NET-15 prepay terms in exchange for a 1.5% prepayment discount. Late payments accrue interest at 1.5% per month or the maximum permitted by law, whichever is lower."

**Approver**: CFO + Deal Desk.

### 9. LOW_LIABILITY_CAP (MEDIUM)

**Trigger**: `liability_cap < 1.0` (multiple of annual fees).

**Why it matters**: When the customer pushes for a sub-1x liability cap, they're usually expecting outsized claims. Don't accept without symmetric protection (mutual cap, both directions).

**Counter-language**:

> "Each party's aggregate liability shall not exceed one (1) times the fees paid by Customer in the twelve (12) months preceding the claim, except for breaches of confidentiality, IP infringement, or willful misconduct, for which a super-cap of three (3) times annual fees shall apply. This cap is mutual and applies to both parties."

**Approver**: General Counsel.

### 10. BROAD_NON_SOLICIT (MEDIUM)

**Trigger**: `non_solicit_years >= 2`.

**Why it matters**: Multi-year non-solicit clauses limit hiring and are increasingly unenforceable in many US jurisdictions (notably California, where they are void as a matter of public policy except in narrow circumstances). Negotiate down.

**Counter-language**:

> "Each party agrees not to solicit for employment any employee of the other party who was directly engaged on the project for a period of twelve (12) months following such employee's last day of engagement on the project. This restriction does not apply to general advertising, solicitation through public job boards, or responses to unsolicited inquiries."

**Approver**: General Counsel + CHRO.

## Sources

1. **Y Combinator — Startup Library** — Sam Altman's and the YC partners' canonical guidance on contracts founders sign. https://www.ycombinator.com/library
2. **Robert Klingberg — *Founder's Guide to SaaS Agreements*** — Practitioner reference on SaaS-specific contract patterns (MSA, DPA, BAA, MNDA).
3. **Bowman + Brooke — Contract Redline Guides** — Defense-side commercial litigation firm's published guides on enterprise contract risk.
4. **IACCM / WorldCC — World Commerce & Contracting Research** — The trade association for commercial contracting; annual surveys of *the most negotiated terms* and *the most disputed terms* in B2B contracts. https://www.worldcc.com/
5. **Practical Law (Thomson Reuters) — Contracts Library** — Standard clause library + redline best practices used by AmLaw 100 firms.
6. **Bradley Tusk — *The Fixer: My Adventures Saving Startups from Death by Politics*** — Practical advice on enterprise contracts, including the patterns that destroy young companies.
7. **GC100 — General Counsel Forum** — Senior in-house counsel from FTSE 100 companies; their guidance on commercial contract risk allocation. https://www.gc100.co.uk/
8. **American Bar Association — *Model Software License Provisions*** — Reference for industry-standard software licensing terms.

## How to use this reference

1. The deal-desk intake template asks the AE to capture the structured terms.
2. `terms_redliner.py --input deal_terms.json` produces a ranked list of detected landmines.
3. Each landmine is mapped to a section in this document with the counter-language and named approver.
4. The deal-desk packet attaches the counter-language so the AE can return to the customer with a defensible position.

Remember: **every CRITICAL or HIGH finding must reach the named approver before the deal closes.** This skill triages; it does not approve.

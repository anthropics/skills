# Contracts Playbook — Standard Startup Agreements

Reference for the 7 contracts every startup signs in its first 5 years and the clause traps to avoid in each. **Not legal advice.** Bring redlines to qualified counsel.

## 1. Master Service Agreement (MSA) — Vendor Side (you signing theirs)

**What it is:** The umbrella contract for an ongoing relationship with a vendor (cloud, tooling, services, agencies). Usually paired with one or more SOWs / Order Forms.

**Top 5 redlines to push:**

1. **Auto-renewal:** Cut notice period to 30 days max. Reject 60/90/180 day notice.
2. **Liability cap:** Insist on 12 months of fees. Reject "fees in the preceding 3 months" (too narrow).
3. **Mutual indemnification:** Reject one-sided. Mirror the scope on both sides.
4. **IP ownership of deliverables:** All work product belongs to you. Vendor retains rights to pre-existing tools / methodologies, granted back to you for use.
5. **Data: DPA + return-or-destroy on termination.** Specifically: vendor cannot use your data to train AI models.

**Bonus catch:** Watch for "Vendor may modify these terms upon notice" — this means the contract you signed isn't the contract you have.

## 2. Customer SaaS Agreement (your paper)

**Standard structure:**

1. License grant (subscription, scope, term)
2. Acceptable use policy (what customer can/can't do)
3. Fees & payment (annual prepay vs. monthly, late fee, currency)
4. Service Level Agreement (uptime %, credits, exclusions)
5. Confidentiality (mutual, residuals carve-out)
6. Data Protection (DPA exhibit, subprocessor list, security commitments)
7. Warranties (limited, disclaim implied)
8. Indemnification (mutual, IP-infringement focused)
9. Limitation of liability (12 months fees, carve-outs for IP/data breach/willful)
10. Term & termination (term, termination for cause, termination for convenience)

**Founder traps when accepting customer redlines:**

- "Most-favored-nation" pricing (means you can never give anyone else a better deal).
- Uncapped liability for data breach with no minimum threshold.
- Customer right to perpetual license-back of "improvements" to your product.
- Customer "ownership" of any custom configuration (often hiding IP creep).
- Source-code escrow with auto-release triggers tied to customer convenience.

## 3. Non-Disclosure Agreement (NDA)

**One-way (you receiving):** Acceptable to sign without redlines for short evaluations.

**Mutual NDA (both directions):** The default for ongoing discussions.

**Critical carve-outs (always include):**

- **Residuals:** Information retained in unaided memory after end of engagement is not confidential.
- **Independent development:** If you build something similar without using their info, it's yours.
- **Public domain:** Information already public is not confidential.
- **Rightfully received:** Information received from a third party without confidentiality obligation.
- **Required by law:** Information disclosed under subpoena (with notice).

**Founder trap:** NDAs that prevent you from "engaging in similar business" — that's a non-compete in disguise. Strip it out.

## 4. Data Processing Agreement (DPA)

**Required when:** Personal data of EU residents flows (GDPR Article 28), or California residents (CCPA / CPRA), or HIPAA-covered data, or biometrics in IL/TX/WA (BIPA).

**Standard structure (GDPR-aligned):**

- Scope of processing (what data, what purpose)
- Controller / Processor designation
- Subprocessor list + flow-down obligations
- Data subject rights (access, deletion, portability)
- Security measures (encryption, access controls, training)
- Breach notification timelines (within 72 hours for GDPR)
- Audit rights (annual, reasonable)
- International transfer mechanism (SCCs, adequacy decision, BCRs)
- Return-or-destroy on termination

**Templates:** Use IAPP, EU Commission SCCs, or vendor-friendly DPA (e.g., Vanta's, Stripe's).

**Founder trap:** Missing DPA when EU/CA data flows = contract may be unenforceable AND regulatory fine exposure.

## 5. Employment Agreement / Offer Letter

**Must-have provisions:**

- **At-will employment** (US most states; not enforceable in MT for example)
- **Compensation:** salary, bonus structure, equity (option grant separately documented)
- **Invention assignment:** all IP created during employment using company resources belongs to company
- **Confidentiality:** ongoing duty, surviving termination
- **Non-solicit:** 12 months post-termination, employees + customers (carve out general advertising)
- **Non-compete:** state-dependent (CA, ND, OK, DC: void; many other states: enforceable if reasonable)
- **Arbitration:** mutual, AAA or JAMS rules, employer pays fees

**Founder traps:**

- Forgetting to require employees to sign **before** starting work (otherwise IP assignment is weak).
- Not including a "previously created inventions" exhibit (lets founders document pre-existing IP brought into the company).
- Skipping background checks for senior hires.

## 6. Contractor / 1099 Agreement

**Critical differences from employment:**

- **IP assignment is NOT automatic.** Without a written clause, the contractor owns what they create (under US law, "work for hire" applies only to specific categories of work).
- **Misclassification risk:** If a contractor functions like an employee (controlled hours, exclusive engagement, supplied equipment), tax authorities can reclassify, triggering back taxes + penalties.
- **No benefits, no withholding, contractor handles their own taxes.**

**Must-have provisions:**

- **Explicit work-for-hire OR written IP assignment** ("Contractor hereby assigns all right, title, and interest...").
- **Independent contractor status:** contractor controls means and methods.
- **Termination:** 30-day notice, immediate for cause.
- **Indemnification:** contractor indemnifies you for misclassification claims if they misrepresent status.

**Tooling:** Use Deel, Remote, or Velocity Global for international contractors to handle classification correctly.

## 7. Equity Agreements (Option Grants, Advisor Grants)

**Employee option grant:**

- **Strike price:** must be ≥ fair market value (FMV) at grant date (409A valuation, refreshed annually).
- **Vesting:** standard 4 years, 1 year cliff, monthly thereafter.
- **Exercise window post-termination:** 90 days standard; 7-10 years is founder-friendly.
- **ISO vs NSO:** ISOs have tax advantages (long-term capital gains if held) but limits ($100K vest/year) and US-citizen-only.

**Advisor grant (FAST template by Founder Institute):**

- 0.1% - 1% equity vested over 1-2 years, depending on level and stage.
- 2-year vesting, no cliff (advisors are tested through engagement, not retention).
- Single trigger acceleration on change of control (rare; double trigger more common).

**Founder trap:**

- Issuing options before completing the 409A valuation — strike price might be challenged by IRS.
- Verbal promises about acceleration — must be in writing.
- Forgetting to issue option grants to early employees within 90 days of hire (loses ISO eligibility).

## Quick Triage Heuristics

When you have 5 minutes to look at a contract:

1. **Find the liability cap.** No cap or > 24 months of fees = red flag.
2. **Find the indemnity clauses.** One-sided = red flag.
3. **Find the IP clause.** Vague or "as agreed" = red flag.
4. **Find the term + termination.** Auto-renewal with > 30 day notice = red flag.
5. **Find the choice of law/venue.** Exclusive in counterparty home jurisdiction = red flag.

Run `scripts/contract_risk_scanner.py` for the automated version.

---

**Final reminder:** This is a triage playbook. Every contract over $100K or longer than 1 year deserves outside counsel review. Every contract that touches personal data deserves a privacy attorney. Every term sheet deserves a securities / venture attorney. Period.

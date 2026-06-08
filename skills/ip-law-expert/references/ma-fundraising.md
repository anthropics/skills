# IP in M&A and Fundraising

## IP Due Diligence Checklist

IP due diligence is conducted by investors in every funding round (Series A and beyond) and by acquirers in M&A. The scope intensifies with deal size.

### 1. Patent Portfolio Review
- [ ] List all issued patents, pending applications (published and unpublished), and abandoned applications
- [ ] Verify USPTO assignment records — confirm the company (not founders, employees, or prior employers) is the recorded assignee
- [ ] Review prosecution history for each patent (prior art cited, office action responses, claim amendments)
- [ ] Assess claim breadth and quality — broad claims vs. narrowly prosecuted fallback positions
- [ ] Check maintenance fee payment status (lapsed patents = lost rights)
- [ ] Review any licenses granted to or received from third parties (in-licenses, out-licenses)
- [ ] Assess freedom to operate (FTO) position relative to third-party patents (see FTO section below)
- [ ] Review any patent litigation history (as plaintiff or defendant)

### 2. Copyright Ownership
- [ ] Verify all material code was written by employees covered by PIIAs or contractors covered by IP assignment agreements
- [ ] Review PIIA/contractor agreement execution dates — pre-hire gaps can create chain of title issues
- [ ] Identify all open source software used and confirm license compliance
- [ ] Check for any GPL/AGPL code incorporated into proprietary software without proper compliance
- [ ] Review copyright registration status for key software products
- [ ] Verify no copyright infringement claims pending

### 3. Trade Secret Portfolio
- [ ] Identify key trade secrets (model weights, training data, algorithms, business methods)
- [ ] Review reasonable measures documentation (NDAs signed, access controls, training records)
- [ ] Confirm DTSA whistleblower notice in all employee/contractor agreements
- [ ] Review any history of trade secret misappropriation claims (as plaintiff or defendant)

### 4. Trademark and Brand
- [ ] List all registered trademarks, pending applications, and common law marks
- [ ] Verify proper maintenance and renewal (Section 8 and 15 affidavits for US marks)
- [ ] Review domain name registrations — confirm company owns all key domains
- [ ] Review any trademark oppositions, cancellation proceedings, or infringement claims
- [ ] Check for pending UDRP proceedings

### 5. Chain of Title and IP Ownership
- [ ] All founders signed IP assignment agreements at or before incorporation
- [ ] All early employees/contractors signed PIIAs before beginning work
- [ ] Pre-incorporation work explicitly assigned to the company at formation
- [ ] No IP created at prior employers incorporated into the company's IP
- [ ] University-sourced IP: Review tech transfer agreements if technology originated at a university
- [ ] Government-funded research: Check Bayh-Dole compliance if NIH, NSF, or DOE funding was received (government may have rights)

### 6. Third-Party IP Rights
- [ ] Review all software licenses for compliance (open source and commercial)
- [ ] Review data licenses — confirm rights to use training data for AI model development
- [ ] Review any joint development agreements — who owns jointly developed IP?
- [ ] Review customer contracts for any IP ownership provisions granting customers rights to company IP
- [ ] Review API terms of service for any IP grants or restrictions

## IP Representations and Warranties

In VC financings and M&A, the company makes representations and warranties about IP. Standard IP reps (based on NVCA model documents and market practice):

**Typical company IP reps include**:
1. **Ownership**: Company owns or has licenses to all IP used in its business; no IP claims outstanding
2. **No infringement**: Company does not infringe third-party IP; not aware of any pending claims
3. **No third-party rights in company IP**: Company IP is not subject to third-party claims; all employee and contractor IP has been assigned
4. **Trade secret protection**: Reasonable measures to protect trade secrets; no breach of confidentiality
5. **Open source compliance**: All open source software used in compliance with applicable licenses; no GPL/AGPL contamination of proprietary code
6. **IP agreements**: All material IP agreements listed on a schedule; no material breach
7. **No IP liens**: Company IP is not pledged as collateral (except to disclosed lenders)
8. **Chain of title**: All material IP properly documented and recorded

**What investors and acquirers look for**:
- Clean chain of title (every piece of IP assignment properly documented)
- No GPL contamination (GPL code incorporated into proprietary product = existential risk)
- No prior employer IP taint on founders/key engineers
- Strong trade secret protection measures
- No active IP litigation

**Reps & warranties insurance**: In larger M&A transactions, rep and warranty insurance covers breaches of IP reps for 1-3 years post-closing. Premium: ~3-5% of coverage. Insurer conducts independent IP diligence before coverage.

## Freedom to Operate (FTO) Analysis

An FTO analysis determines whether commercializing a product would infringe valid, enforceable patents held by third parties.

**When to conduct FTO**:
- Before product launch (especially in crowded IP spaces)
- Before Series A/B fundraising (investors require it or it becomes a diligence item)
- Before M&A (standard in any technology M&A)
- When entering a new technology area with significant patent activity
- Upon receiving a cease and desist letter from a patent holder

**FTO process**:
1. **Define the product/technology scope**: Identify the specific product features and technical implementation to be analyzed
2. **Prior art and patent search**: Search US Patent Database (USPTO), EPO, WIPO, and Google Patents for relevant patents and published applications
3. **Claim mapping**: Map the product's technical implementation against the claims of potentially relevant patents
4. **Validity analysis**: Assess whether potentially infringed patents are valid (prior art that wasn't before the examiner, Alice/101 issues, obviousness)
5. **Opinion letter**: Qualified attorney writes a written opinion (provides good faith defense against willful infringement)
6. **Risk assessment**: Categorize patents as high/medium/low risk; identify design-around options

**Cost of FTO analysis**:
- Preliminary/focused FTO (single product feature, narrow search): $5,000–$15,000
- Full FTO analysis (product launch): $15,000–$50,000+
- Comprehensive M&A FTO: $50,000–$200,000+

**FTO opinion letter (35 U.S.C. § 285 willfulness)**: A written FTO opinion from a qualified patent attorney provides a defense against a finding of "willful" infringement. Willful infringement can result in treble damages. This defense is critical — get it before launching in any patent-heavy space.

**FTO by company stage**:
- Seed/Pre-seed: Informal preliminary search; prioritize for core product differentiators
- Series A: Formal FTO for core technology; investors increasingly require this
- Series B+: Comprehensive FTO; actively monitor competitor patent filings
- M&A: Full FTO covering all products and markets is standard

## IP Valuation

IP valuation is required for M&A, licensing negotiations, bankruptcy proceedings, and financial reporting (ASC 805 in M&A).

**Three valuation approaches**:

1. **Cost approach**: What would it cost to recreate the IP? Useful for trade secrets and copyrights. Limitations: Doesn't capture commercial value exceeding cost.

2. **Market approach**: What have comparable IP assets sold for? Difficult for patents (transactions are often confidential); more useful for trademark portfolios and brand valuations.

3. **Income approach (most common)**: Present value of future cash flows attributable to the IP. Methods:
   - Relief from Royalty: Estimate what the company would pay to license the IP if it didn't own it
   - Multi-Period Excess Earnings Method (MPEEM): Attribute future earnings to a specific IP asset by deducting returns on all other contributing assets
   - With-or-without method: Compare DCF projections with and without the IP asset

**Practical factors driving AI/ML company IP value**:
- Defensibility of patent claims (post-Alice eligibility, claim breadth)
- Market exclusivity provided by patents
- Strength of trade secret protection (model weights, training data)
- Revenue attributable to patented features
- Licensing revenue history

**Patent assertion value vs. company value**: Many acquirers separately assess the defensive value of patents (blocking competitors) from their assertion value (ability to generate licensing revenue or damages from infringers). Defensive value is primary for operating companies; assertion value for patent holding companies.

## Key IP Issues by Fundraising Stage

**Pre-Seed / Seed**:
- File provisionals to establish priority dates for core innovations
- Execute PIIAs with all founders and early employees
- Choose your open source strategy and implement license compliance
- Register your brand trademark early (before publicity creates squatting risk)

**Series A**:
- Convert provisionals to non-provisionals before 12-month deadline
- Conduct FTO analysis on core product
- Complete comprehensive IP assignment audit (all employees, contractors, early contributors)
- Investors expect a patent pending or filed strategy; document your IP strategy in board materials

**Series B / Growth**:
- Build patent portfolio (3-10+ patents covering core differentiating technology)
- Conduct periodic FTO monitoring as you enter new markets
- Implement formal open source license compliance program
- Consider trade secret audit and protection enhancement

**Pre-M&A / IPO**:
- Full IP audit and clean-up (fix any chain of title issues)
- Comprehensive FTO opinion across all products
- IP litigation history review and resolution
- IP schedule preparation for the definitive agreement

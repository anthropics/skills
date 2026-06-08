# Industry Regulatory Compliance Reference

## Fintech Compliance

### Money Transmission Licensing

**The core problem**: there is no single US national money transmitter license. Each state has its own regime. 49 states + DC + territories require licenses (Montana is the only state without a requirement as of 2025).

**Who needs a license**: any business that receives money from one party to transmit to another — payment processors, P2P apps, digital wallets, crypto exchanges, remittance services, some B2B payment platforms.

**Money Transmission Modernization Act (MTMA)**:
CSBS-developed model law intended to standardize state requirements. 31 states had enacted MTMA in full or in part as of February 2026. Standardizes: net worth requirements, surety bond requirements, permissible investment rules.

**Key licensing requirements (typical across states):**
- Net worth / minimum capital: ranges from $25K (small states) to $500K+ (California, New York)
- Surety bond: typically $50K–$1M+
- FinCEN MSB registration: federal requirement for all Money Services Businesses (MSBs); file online; anti-money laundering (AML) program required
- AML/BSA compliance program: written policies, designated compliance officer, employee training, independent audit, suspicious activity reporting (SARs), currency transaction reports (CTRs for $10K+ cash)
- Background checks on principals, officers, directors
- Business plan, financial statements, ownership structure
- Permissible investments: liquid assets to cover customer liabilities

**Timelines**:
- Small states: 3–6 months
- California (DBO): 6–18 months
- New York (DFS): 6–18 months; also requires BitLicense for virtual currency businesses
- Multi-state: use NMLS (Nationwide Multistate Licensing System) for streamlined applications in participating states

**Cost**: attorney fees $50K–$250K+ for multi-state licensing; ongoing compliance $100K+/yr for larger programs

**New York BitLicense**: separate license from DFS for virtual currency activities; among most stringent crypto licenses globally; full compliance program, capital requirements, cybersecurity policy (23 NYCRR 500), quarterly financial reporting; application cost $5,000; processing time 12–24 months.

**Exemptions to research**: many states exempt (1) agents of a licensee, (2) payment processors with direct merchant relationships, (3) companies operating under banking charter, (4) certain government entities, (5) de minimis volume.

**Banking as a Service (BaaS)**: startups partner with chartered banks (sponsor banks) to avoid direct money transmission licensing; bank holds the license; fintech is the technology layer. Regulatory attention increasing — OCC and FDIC scrutinizing BaaS arrangements.

---

### PCI DSS (Payment Card Industry Data Security Standard)

**Nature**: not a law — contractually required by card networks (Visa, Mastercard, Amex, Discover) for any entity storing, processing, or transmitting cardholder data.

**Current version**: PCI DSS v4.0 (effective March 2024; transition period for some requirements through March 2025).

**12 Requirements:**
1. Install and maintain network security controls
2. Apply secure configurations to all system components
3. Protect stored account data
4. Protect cardholder data with strong cryptography during transmission over open, public networks
5. Protect all systems and networks from malicious software
6. Develop and maintain secure systems and software
7. Restrict access to system components and cardholder data by business need to know
8. Identify users and authenticate access to system components
9. Restrict physical access to cardholder data
10. Log and monitor all access to system components and cardholder data
11. Test security of systems and networks regularly
12. Support information security with organizational policies and programs

**Merchant Levels (by transaction volume/year):**
- Level 1: 6M+ Visa transactions; requires annual on-site audit by QSA (Qualified Security Assessor) + quarterly network scans by ASV
- Level 2: 1M–6M; annual SAQ (Self-Assessment Questionnaire) + quarterly scans
- Level 3: 20K–1M e-commerce; annual SAQ + quarterly scans
- Level 4: < 20K e-commerce, < 1M other; annual SAQ recommended

**SAQ Types**: different questionnaires for different business models (SAQ A for outsourced card processing, SAQ D for full assessment, etc.)

**Non-compliance consequences**: fine $5K–$100K/month from card networks; breach liability; loss of ability to accept cards

**Key for startups**: use a PCI-compliant payment processor (Stripe, Braintree, etc.) to reduce scope. If you never touch card data (payment processor tokenizes), you're in SAQ A scope — minimal requirements.

---

### SOC 2 (System and Organization Controls 2)

**Nature**: auditing standard by AICPA (American Institute of CPAs). Assesses service organization's controls over customer data. Highly valued by enterprise customers.

**5 Trust Service Criteria (TSC):**
1. Security (CC): mandatory for all SOC 2; protection against unauthorized access
2. Availability (A): system is available for operation as committed
3. Processing Integrity (PI): system processing is complete, valid, accurate, timely
4. Confidentiality (C): information designated as confidential is protected
5. Privacy (P): personal information collected, used, retained, disclosed per privacy notice

**SOC 2 Type I vs. Type II:**
- Type I: point-in-time assessment of whether controls are suitably designed (faster, 2–4 months; less valuable to customers)
- Type II: period-of-time assessment (minimum 6 months of operating effectiveness); considered gold standard; takes 6–12 months total to achieve

**Timeline and costs (2025):**
- Readiness assessment: $5,000–$25,000
- Implementation/remediation: $20,000–$100,000+ (engineering time + tools)
- Type II audit: $20,000–$75,000+ (auditor fees)
- Compliance tools (Vanta, Drata, SecureFrame): $10,000–$50,000/yr
- Total first-year investment: $50,000–$200,000+

**When to pursue**: before first enterprise deal (typical procurement requirement); before Series B (investors expect it). Many startups begin readiness at Series A.

---

## Healthtech Compliance

### HIPAA (see also `data-privacy.md` for full detail)

**Key additional detail for health tech products:**

**Is your product subject to HIPAA?** HIPAA applies only if you are a covered entity or business associate. If you sell a consumer wellness app that never receives data from a healthcare provider/plan, HIPAA may NOT apply. The FTC Health Breach Notification Rule (16 CFR Part 318) may apply instead for direct-to-consumer health apps.

**Business Associate determination**: does your software/service create, receive, maintain, or transmit PHI on behalf of a covered entity? If yes → Business Associate → need BAA + HIPAA compliance program.

**Technical safeguards required (HIPAA Security Rule)**:
- Unique user identification (no shared accounts)
- Emergency access procedure
- Automatic logoff
- Encryption and decryption of ePHI
- Audit controls / access logs
- Integrity controls
- Authentication
- Transmission security (encryption in transit)

**HIPAA compliance timeline**: 5–7 months for initial compliance; ongoing program management.

---

### FDA Software as Medical Device (SaMD)

**Legal basis**: Federal Food, Drug, and Cosmetic Act (FD&C Act); FDA guidance on Software as a Medical Device.

**Definition**: software intended to be used for a medical purpose that runs on a general-purpose computing platform (not embedded in a medical device).

**21st Century Cures Act (2016) exclusions** (NOT regulated as medical devices):
- Administrative support for healthcare facility
- Maintaining patient records
- Facilitating communication within healthcare team
- General wellness apps
- Electronic health records (with narrow exceptions)

**Regulated SaMD**: software that:
- Displays, analyzes, or prints medical images from imaging devices
- Analyzes information from in vitro diagnostic devices
- Analyzes patient-specific data for diagnostic or treatment decisions

**IMDRF Risk Classification Matrix** (FDA adopted):
- Axis 1: State of healthcare situation (critical, serious, non-serious)
- Axis 2: Significance of SaMD output (treat/diagnose, drive clinical management, inform clinical management)
- Risk level determines regulatory pathway (Class I/II/III)

**FDA Regulatory Pathways:**
- Class I (low risk): general controls; often 510(k) exempt
- Class II: 510(k) premarket notification required (prove substantial equivalence to predicate device); typical timeline: 6–12 months; fee $15,000+
- Class III (high risk): PMA (Premarket Approval) required; clinical studies often required; timeline 1–3+ years; fee $500,000+

**De Novo pathway**: for novel low-to-moderate risk devices without predicate; establishes new classification.

**FDA's Predetermined Change Control Plan (PCCP)**: for AI/ML-based SaMD; allows planned updates without requiring new submission for each algorithm change.

**Quality System Regulation** (21 CFR Part 820): design controls, risk management, software validation, post-market surveillance required for cleared/approved devices.

---

## Government Contracting — FedRAMP

**FedRAMP (Federal Risk and Authorization Management Program)**: government-wide security assessment, authorization, and monitoring program for cloud services used by federal agencies.

**Authority**: FedRAMP Authorization Act (part of NDAA FY2023) codified FedRAMP; mandatory for cloud services used by executive agencies.

**Impact Levels:**
- Low: publicly available information, no significant harm if compromised
- Moderate: most government data; roughly 80% of FedRAMP authorizations
- High: law enforcement, emergency services, financial systems, health data

**Authorization Paths:**
1. **Agency Authorization**: one federal agency sponsors and authorizes; most common
2. **Joint Authorization Board (JAB) Authorization**: provisional authority from DoD, DHS, GSA (hardest to get; best market signal)
3. **FedRAMP Ready**: designation that CSP has passed a readiness review; not full authorization

**Controls**: NIST SP 800-53 controls (325 for Moderate, 421 for High). Must implement all applicable controls and document in System Security Plan (SSP).

**Process timeline**: 12–24 months from start to authorization; requires 3PAO (Third-Party Assessment Organization) assessment.

**Cost**: $500,000–$2M+ for initial authorization (including 3PAO fees $50K–$300K, internal engineering, and consulting).

**Once authorized**: annual assessment, continuous monitoring, monthly reporting to FedRAMP PMO.

**Market value**: FedRAMP authorization is a significant competitive advantage for GovTech companies; often prerequisite for large federal contracts.

---

## Edtech Compliance

**FERPA (Family Educational Rights and Privacy Act)**: Protects student education records. Schools cannot disclose education records without consent. Edtech companies contracting with schools to perform services are "school officials" with legitimate educational interest — may access records without parental consent, but:
- Must be under direct control of school regarding use of records
- Can use data only for authorized purposes
- Cannot use student data for advertising or other commercial purposes

**COPPA**: applies to edtech apps directed to children under 13 or with actual knowledge of child users — parental consent required.

**Student Privacy Pledge**: industry self-certification (signatory schools and companies commit to not selling student data, using it only for education purposes, maintaining security).

**State student privacy laws**: many states (California SOPIPA, NY Ed Law 2-d, etc.) impose additional requirements beyond FERPA — varying requirements on data deletion, prohibitions on behavioral advertising, data governance agreements with vendors.

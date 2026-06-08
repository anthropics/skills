# IP Enforcement and Defense for Technology Companies

## Cease and Desist Letters

A cease and desist (C&D) letter is a formal demand that the recipient stop an activity alleged to infringe the sender's IP rights. A C&D letter is NOT a court order — it is not legally enforceable on its own and does not require compliance without further legal process.

### Receiving a C&D Letter

**Immediate steps**:
1. Do not ignore it (though you are not legally required to respond)
2. Do not respond without legal counsel — your response may be used against you in litigation
3. Preserve all relevant documents and communications (litigation hold)
4. Contact an IP attorney immediately — most have experience evaluating these

**Evaluation framework**:
- What right is asserted? (Patent, copyright, trademark, trade secret?)
- Is the asserted right valid? (Expired patents, weak trademark registrations, overbroad copyright claims)
- Is infringement likely? (Claim mapping for patents; compare marks for trademarks)
- Who is the sender? (Established company with a real dispute, or a patent troll/NPE?)
- What is the litigation risk vs. business risk of compliance?

**Response options**:
1. **Cease the activity**: If infringement is likely and the cost of redesign is lower than litigation risk
2. **Design around**: Modify the product to avoid the asserted claims while preserving functionality
3. **Negotiate a license**: If the IP is valid and licensing terms are reasonable
4. **Dispute the claim**: Send a detailed response explaining why there is no infringement (requires attorney analysis)
5. **Declaratory judgment action**: File in federal court seeking a declaration of non-infringement or invalidity — puts pressure on the patentee and gives you choice of forum
6. **Challenge validity**: File an IPR at the USPTO challenging the patent's validity (see IPR section below)

**Do NOT**:
- Admit infringement in writing
- Make oral admissions to the sender
- Continue the allegedly infringing activity without legal advice while ignoring the letter (risk of willful infringement finding)

## Patent Trolls (Non-Practicing Entities / NPEs)

**NPE statistics (2025)**:
- NPEs account for 55.4% of all US patent lawsuits
- In the high-tech sector, NPEs account for 90.3% of all patent litigation
- NPE district court filings increased 21.6% in 2025 vs. 2024
- AI-related NPE activity growing: 5G-related NPE cases grew ~34% year-over-year in 2024-2025
- USPTO received 70,000+ AI patent applications in 2024; many ultimately acquired by NPEs

**NPE business model**: Acquire patents (often broad, software-era patents predating Alice), send demand letters to many companies, collect nuisance settlement fees ($50K–$500K) from companies that calculate litigation defense costs exceed settlement, occasionally litigate against large companies.

**NPE defense strategy for tech startups**:

**1. Assess the threat before responding**:
- Research the NPE (patentdocs.org, IPWatchdog, Unified Patents database)
- Have an attorney analyze whether asserted claims read on your product
- Identify the NPE's litigation history — have they gone to trial? What settlements do they typically accept?
- Check if they have filed IPRs previously or if IPRs have been filed against their patents

**2. Challenge patent validity via Inter Partes Review (IPR)**:
- File an IPR petition at the USPTO PTAB challenging the patent's validity
- IPR is significantly cheaper than district court litigation ($100,000–$400,000 vs. $3M–$10M+)
- Institution rate was ~65% in 2024 (declined to ~37% by early 2026 due to Director policy changes — check current rates)
- If instituted, about 80% of IPRs result in at least some claims being cancelled
- **Warning**: A denied IPR petition does not help your case and may hurt estoppel positions

**3. Join Unified Patents**:
- Unified Patents is a member organization that files IPRs to defend sectors from NPEs
- Members pay annual dues (varies by sector and company size — typically $10,000–$100,000/year for startups)
- Unified Patents filed 16%+ of all ex parte reexamination requests in the first half of 2025
- Particularly effective for fighting AI, 5G, and standard-essential patent (SEP) trolls

**4. Alice/§ 101 motion to dismiss**:
- Many NPE patents on software and business methods are Alice-ineligible
- File a motion to dismiss or early motion for judgment on the pleadings under § 101
- If the asserted patent covers abstract ideas without a specific technical improvement, this can be a cost-effective defense
- Success rate varies but can result in early dismissal before expensive discovery

**5. Defensive patent portfolio**:
- Own patents that the NPE potentially infringes (for cross-licensing negotiations)
- Even for startups: 5–10 patents in your core technology area creates negotiating leverage
- Joining patent pools (Open Invention Network for Linux ecosystem; Unified Patents sector zones)

**6. NPE insurance**:
- Patent litigation insurance is available for companies at risk of NPE attacks
- Covers defense costs; premiums vary based on technology area and revenue
- Often cost-effective for companies with revenue >$10M in high-NPE sectors (software, mobile, e-commerce)

## Inter Partes Review (IPR)

**What it is**: A trial proceeding at the USPTO PTAB (Patent Trial and Appeal Board) to challenge the validity of an issued patent on the basis of prior art (printed publications and patents only — not public use or sale).

**Governed by**: 35 U.S.C. §§ 311–319

**Key parameters**:
- Must be filed within **1 year** of being served with a complaint for patent infringement (after 1 year, the IPR bar applies)
- Filing fee: $19,000–$30,000 in USPTO fees alone; attorney fees add $100,000–$300,000 for petition preparation
- Institution rate: ~65% historically; declined to ~37% by April 2026 due to USPTO Director policy changes (monitor current rates)
- **Timeline**: If instituted, trial concludes in approximately 12 months
- **Estoppel**: If IPR is instituted and reaches final written decision, the petitioner is estopped from later arguing in district court that the patent is invalid on any ground that was raised or reasonably could have been raised in the IPR

**When to use IPR**:
- Defendant in patent litigation facing a weak but asserted patent (particularly pre-Alice-era software patents)
- Proactive invalidity challenge against a competitor's key patent blocking market entry
- As leverage in licensing negotiations

**Post-Grant Review (PGR)**:
- Similar to IPR but allows broader challenges (any ground of invalidity, not just prior art)
- Must be filed within 9 months of patent grant
- Rarely used for software patents; more common for biotech/pharma

**Ex Parte Reexamination**:
- Lower cost alternative ($2,000–$5,000 USPTO fee + attorney fees)
- Anyone can request anonymously — useful to challenge competitor patents without revealing identity
- Only prior art (patents and publications); no opportunity to participate in examination once initiated
- Unified Patents uses this tool extensively

## Copyright Infringement Defense and DMCA

### Responding to DMCA Takedown Notices
If your content is removed via a DMCA takedown notice and you believe removal was in error:

**File a DMCA counter-notice** to the platform/OSP:
1. State your name, address, phone, and email
2. Identify the removed content and its location before removal
3. Statement under penalty of perjury that the material was removed by mistake or misidentification
4. Statement consenting to jurisdiction of federal court (district where you reside)
5. Statement that you will accept service of process from the person who sent the original takedown notice

**After proper counter-notice**: OSP must restore content within 10–14 business days unless the original claimant files a lawsuit seeking a court order to keep the content down.

**Misuse of DMCA**: Sending fraudulent DMCA takedowns (where you know you have no valid copyright claim) can result in liability for misrepresentation under 17 U.S.C. § 512(f).

### AI-Specific Copyright Defense
If accused of copyright infringement in your AI training data:
- Document all training data sources and any licensing terms reviewed
- Preserve evidence of the transformative purpose of training
- Assess which specific copyrighted works are alleged to have been copied
- Evaluate whether the AI outputs actually reproduce protectable expression
- Consider whether the training would qualify as fair use under the four-factor test
- Monitor the evolving litigation landscape (NYT v. OpenAI expected to produce fair use decisions in 2026-2027)

## Trademark Enforcement

### Policing Your Mark
Trademark rights can be lost through failure to police — if you knowingly allow widespread infringement without enforcement, your mark can become unenforceable or generic. Establish a trademark monitoring program:
- Monitor USPTO applications for confusingly similar marks (watch services: Thomson CompuMark, MarkMonitor)
- Monitor internet, social media, and app stores for unauthorized use
- Send cease and desist letters for clear infringement
- File oppositions against USPTO applications for confusingly similar marks within 30 days of publication

### Sending C&D for Trademark Infringement
A trademark C&D must include:
- Identification of your mark and registration number (if registered)
- Description of the infringing use
- Demand to cease and desist the infringing use
- Response deadline (typically 10–30 days)
- Reservation of all rights

### TTAB Opposition Proceedings
If a confusingly similar trademark application publishes for opposition:
- File an opposition within 30 days (extensions of 90 days available)
- TTAB proceedings conducted on paper (discovery, briefs, no jury)
- Timeline: 1–3 years to resolution
- Cost: $15,000–$100,000+ in attorney fees depending on complexity

## Emerging Enforcement Issues (2024-2026)

**Voice cloning and deepfake enforcement**:
- Tennessee ELVIS Act (2024) creates state causes of action for unauthorized voice cloning
- NO FAKES Act (pending federal legislation) would create federal right of publicity for digital replicas
- Platform-level enforcement through takedown procedures
- Right of publicity lawsuits increasing: Lehrman v. Lovo (SDNY 2024); NY voice cloning case (2025)

**EU AI Act enforcement**:
- European AI Office established to enforce AI Act compliance
- GPAI model providers face copyright compliance obligations as of August 2025
- National supervisory authorities enforce against prohibited AI practices
- Penalties up to €35M or 7% of global annual turnover

**AI-generated content and copyright enforcement**:
- Copyright Office's inability to register AI-generated works may limit enforcement options
- Trade secret protection for AI model weights as alternative to copyright
- Emerging market for provenance and content authentication (C2PA standard) to distinguish human vs. AI-generated content

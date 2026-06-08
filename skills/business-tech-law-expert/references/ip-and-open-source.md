# Intellectual Property & Open Source Reference

## IP Assignment in the Startup Context

### PIIA (Proprietary Information and Inventions Agreement)
See also `contracts.md` for full PIIA structure. Critical startup IP facts:

**Timing is everything**: IP created before PIIA signing may not be assigned. If founders built pre-incorporation, use a "prior inventions" assignment or at least list the prior inventions to ensure clarity.

**Scope of assignment**: should be written broadly — "any IP created during the term of employment that relates to the business of the company, could reasonably be expected to relate to the company's anticipated business, or is developed using company resources."

**California §2870 limitation**: CA employees cannot be required to assign:
- IP developed entirely on employee's own time
- Without using company equipment, supplies, facilities, or trade secrets
- AND that does not relate to the company's business or reasonably anticipated business
- AND that does not result from work performed for the company
All four conditions must be met for the exemption to apply — narrow.

**Contractor IP**: copyright work-for-hire requires written agreement AND work falls in one of 9 statutory categories (17 U.S.C. §101). Software is arguably a "contribution to a collective work" or "compilation" — some jurisdictions disagree. Patent assignment does NOT work via work-for-hire. Always use explicit assignment clause in every contractor agreement.

### IP Due Diligence Checklist (for funding rounds)
- All founders signed PIIA with complete/correct prior inventions schedule
- All full-time employees signed PIIA
- All contractors and advisors have IP assignment in their agreements
- No founder used another employer's resources to develop company IP
- Any pre-incorporation IP formally assigned to company
- No open source licenses that would trigger disclosure obligations
- No third-party IP incorporated without proper license
- Patent applications filed (where applicable)

---

## Patent Strategy for Tech Startups

**Patent eligibility** (35 U.S.C. §101): processes, machines, manufactures, compositions — excludes abstract ideas, laws of nature, natural phenomena (Alice/Mayo framework limits software patents).

**Software patent landscape**: Alice Corp. v. CLS Bank (2014) eliminated many software patents; patents require concrete technical implementation, not just abstract idea + computer. Work with patent attorney to draft claims with sufficient technical specificity.

**Types of applications:**
- Provisional: 12 months to file non-provisional; establishes priority date; $320 (large) / $160 (small) / $80 (micro entity) USPTO fees; no examination
- Non-provisional: full examination; 2–4 year prosecution; USPTO fees $1,640–$3,200+ entity; attorney fees $8,000–$20,000+
- PCT (International): 18-month window for national phase entries; file in 150+ countries from one application

**Patent licensing**: Exclusive vs. non-exclusive; field-of-use restrictions; territory limits; royalty structures (fixed, running, minimum); sublicense rights; IP ownership upon termination.

**Software escrow**: Licensee of critical software may require source code escrow with neutral escrow agent (Iron Mountain, NCC Group); release triggers: vendor bankruptcy, product discontinuation, failure to maintain. Relevant for enterprise SaaS where continuity risk matters.

---

## Open Source Licensing — Complete Guide

### License Categories

**Permissive Licenses** (commercial use-friendly):
- **MIT**: simplest; only requires preserving copyright notice and license text; no copyleft
- **Apache 2.0**: permissive + explicit patent grant from contributors; requires NOTICE file; preferred for corporate use
- **BSD 2-Clause / 3-Clause**: similar to MIT; 3-clause adds non-endorsement provision
- **ISC**: functionally equivalent to 2-Clause BSD; common in Node.js ecosystem

**Weak Copyleft Licenses** (library use):
- **LGPL (GNU Lesser GPL)**: allows linking to proprietary software without copyleft trigger; modifications to LGPL code itself must be released as LGPL
- **MPL 2.0 (Mozilla Public License)**: file-level copyleft; modifications to MPL files must be released; new files added to MPL project can be proprietary

**Strong Copyleft Licenses** (viral):
- **GPL v2/v3 (GNU General Public License)**: distribution of software containing GPL code (via static or dynamic linking in most interpretations) requires distributing ALL linked code under GPL; triggered by distribution, not internal use; does NOT trigger for SaaS (network use exception — the "SaaS loophole")
- **AGPL v3 (Affero GPL)**: GPL + **network use trigger** — if users interact with AGPL software over a network (SaaS), the source code of the entire application must be made available under AGPL. This closes the SaaS loophole.

### AGPL and SaaS — The Critical Risk

AGPL v3, Section 13: "If you modify the Program, your modified version must prominently offer all users interacting with it remotely through a computer network (if your version supports such interaction) an opportunity to receive the Corresponding Source..."

**Practical consequence**: Any SaaS product built using AGPL-licensed code (as a library, dependency, or modified fork) must:
1. Offer all users access to the complete source code of the modified AGPL software AND
2. In the FSF's interpretation, potentially the entire application (if AGPL code is "combined" with proprietary code)

**Due diligence implication**: Discovering an undisclosed AGPL dependency during M&A due diligence is a common deal-killer. Investors and acquirers treat AGPL violations as high-severity legal risk — forcing open-sourcing of the entire codebase or expensive license renegotiation (often $100K–$1M+ for commercial license).

**Common AGPL-licensed tools** that startups inadvertently use:
- RRDtool, Ghostscript (legacy), MongoDB (SSPL, similar), Neo4j (AGPL community edition), Mautic, Matomo, many ML/AI tools

**Note on SSPL (Server Side Public License)**: MongoDB's SSPL is similar to AGPL but even more expansive — requires open-sourcing all software used to provide the service (logging, monitoring, etc.) if you offer MongoDB as a service. Not OSI-approved. Treat like a restrictive commercial license.

### Dual Licensing Model
Some open source companies (MongoDB, Elasticsearch pre-relicense, Qt, MariaDB) offer:
- Open source version under AGPL/copyleft (free but requires open-sourcing derivatives)
- Commercial license for a fee (allows proprietary use)

This model requires:
- **CLA (Contributor License Agreement)**: contributors grant the company broad rights to relicense contributions under commercial terms; must be collected from all contributors before accepting PRs
- **Copyright assignment** from contributors (some companies require full copyright transfer; others take broad license grant)

### License Scanning Tools

**FOSSA**: industry standard; integrates with CI/CD; scans all direct and transitive dependencies; policy engine to block prohibited licenses; generates attribution notices; can automate SBOM generation. Enterprise pricing starts ~$30K/yr.

**Black Duck (Synopsys)**: deep binary scanning (catches obfuscated/copied code even if package not present); comprehensive license database; preferred for M&A diligence and enterprise compliance. Enterprise pricing $50K+/yr.

**Snyk Open Source**: developer-focused; license policy UI; integrated with popular dev tools (GitHub, Jira, Slack); free tier available; real-time alerts; good for smaller teams. Paid plans from ~$98/mo.

**FOSS License Scanner (OSS Review Toolkit, ORT)**: open source tool; supports SPDX; CI integration; free but requires setup.

**When to implement**: before first enterprise deal (customers will ask), before Series A diligence (VCs check), before M&A discussions (acquirers always check). Retrofitting compliance on a large codebase is expensive; building it in CI/CD from day 1 is cheap.

### Software Bill of Materials (SBOM)
**NTIA/CISA guidelines** and **Executive Order 14028** (May 2021, Biden): software sold to US government must include SBOM. SBOM = machine-readable inventory of software components and their licenses.
Standards: SPDX (ISO/IEC 5962:2021) and CycloneDX both accepted. Tools like Syft, FOSSA, Black Duck can generate.

### Contributor License Agreements (CLAs)
**Individual CLA (ICLA)**: contributor grants company copyright license + patent license for their contributions; allows company to relicense, sublicense, dual-license
**Corporate CLA (CCLA)**: company grants rights for all employees' contributions; commonly used when employees contribute to company's open source project at work
**Apache-style CLA**: contributor grants broad license but retains copyright; company gets rights to relicense
**Developer Certificate of Origin (DCO)**: lighter weight than CLA; contributor attests they have right to submit; used by Linux kernel, many projects; does NOT grant company right to relicense commercially

**Practical note**: GitHub makes CLA signing easy via CLA Assistant bot — integrate with PR workflow.

---

## Trademark Licensing and Policing

**Naked license doctrine**: if licensor fails to maintain quality control over licensee's use of the mark, the trademark may be abandoned. Every trademark license must include quality control provisions.

**License requirements**: licensee permitted fields of use; territorial scope; quality standards; inspection rights; licensor approval for materials; royalties or royalty-free; term and termination.

**Trademark policing obligation**: owners must monitor and enforce against infringement or risk losing distinctiveness (especially for marks that could become generic). Send cease-and-desist to infringers; maintain records of enforcement.

**Domain names**: UDRP (Uniform Domain-Name Dispute-Resolution Policy) allows expedited dispute resolution for domain names registered in bad faith by cybersquatters — faster and cheaper than litigation. ICANN-accredited providers: WIPO, NAF.

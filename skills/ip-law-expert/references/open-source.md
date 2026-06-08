# Open Source Strategy for Technology Companies

## License Categories and Key Properties

### Permissive Licenses (Maximize Adoption)

**MIT License**
- Allow anyone to use, copy, modify, merge, publish, distribute, sublicense, and sell
- Requires only: attribution (preserve copyright notice) and include the license text
- No copyleft — users can incorporate into proprietary products without open-sourcing their code
- Most popular license: ~45% of all open source projects
- Best for: Maximum adoption, libraries, tools where you want ubiquitous use, goodwill/community building

**Apache License 2.0**
- Like MIT but adds: explicit patent grant from contributors (protects users from patent claims by contributors), patent retaliation clause (lose your license if you sue for patent infringement)
- Requires: attribution, include license text, state changes made to the code
- Cannot combine Apache 2.0 with GPLv2 (patent grant language incompatible)
- Best for: Corporate adoption where patent protection is important; enterprise software; APIs

**BSD 2-Clause / 3-Clause**
- Functionally equivalent to MIT; 3-Clause adds non-endorsement clause
- BSD-2 = MIT essentially (shorter text); BSD-3 = MIT + "may not use the name of the project or its contributors to endorse or promote products"
- Less commonly used than MIT/Apache in new projects

### Weak Copyleft Licenses

**LGPL (GNU Lesser General Public License)**
- Copyleft that applies only to the LGPL library itself, not to applications linking to it
- End users can use the library in proprietary applications via dynamic linking without open-sourcing their application
- If you modify the LGPL library itself, modifications must be released under LGPL
- Best for: Libraries where you want copyleft protection on the library but broader adoption in proprietary software

**MPL 2.0 (Mozilla Public License)**
- "File-level" copyleft — only files that contain MPL code must remain MPL
- New files added to an MPL project can be proprietary
- Compatible with Apache 2.0 and GPL/LGPL
- Good middle ground between permissive and strong copyleft

### Strong Copyleft (Viral) Licenses

**GPL v3 (GNU General Public License)**
- Any software that incorporates GPL code must itself be released under GPL upon distribution
- "Distribution" triggers copyleft — traditionally, deploying software as a service (SaaS, running on a server) does NOT trigger GPL obligations (users don't receive a copy)
- Patent retaliation clause similar to Apache 2.0
- Incompatible with Apache 2.0 (cannot combine Apache and GPLv2)
- GPLv3 added anti-tivoization provision (hardware must allow software modification)
- Best for: Tools you want to remain permanently open; building a community where contributors must contribute back

**AGPL v3 (GNU Affero General Public License)**
- GPL + "network use as distribution" clause
- If you run AGPL software as a network service and make modifications, you must make those modifications available to users of the service
- **Closes the "SaaS loophole"** of GPL — running AGPL software as a service triggers open-source obligations even if you never "distribute" it
- Best for: SaaS-targeted protection; you want competitors running your code as a service to contribute back or pay for a commercial license
- Major adopters: MongoDB (former), Redis (former), Nextcloud, Mastodon

### Source-Available / Business Source Licenses

**Business Source License (BSL) 1.1**
- Code is available to view and use with restrictions for a set period (typically 4 years)
- After the "Change Date," automatically converts to a specified open source license (usually GPL or Apache)
- Allows internal use and development, but restricts production use without a commercial license
- Adopted by: MariaDB (original creator), CockroachDB, Couchbase

**Elastic License 2.0 (ELv2)**
- Free to use for most purposes, but prohibits: providing the software to third parties as a managed service/hosted offering; circumventing license key mechanisms; removing license notices
- Not OSI-approved "open source" but source is viewable and usable
- Adopted by: Elasticsearch, Kibana (replacing Apache 2.0 in 2021)

**SSPL (Server Side Public License)**
- MongoDB's license; very broad — if you offer SSPL software as a service, you must open-source your entire service stack (including all supporting infrastructure code)
- Extremely aggressive copyleft; most controversial source-available license
- Rejected by OSI as open source; not adopted widely outside MongoDB

**Fair Source (FSL-1.1)**
- Automatically converts to Apache 2.0 or MIT after 2 years (vs. BSL's 4 years)
- Prohibits competing managed services during the non-compete period
- Designed as a more community-friendly alternative to BSL

## Business Models and License Strategy

### Dual Licensing
Run two parallel licensing tracks:
1. **Open source license** (AGPL or GPL) — free for open source projects, individuals, and those who can comply with copyleft
2. **Commercial license** — for companies that cannot comply with copyleft (proprietary products) or want additional features, support, or indemnification

Revenue model: Sell commercial licenses to companies that cannot open-source their own products due to GPL/AGPL copyleft.

**Critical requirement for dual licensing**: You must own ALL the copyright in the code to dual-license. This requires either:
- Only your own employees wrote the code (work-for-hire), or
- All contributors signed a **Contributor License Agreement (CLA)** assigning or licensing their contributions to you

Example dual licensing companies: Qt (LGPL + commercial), MySQL/MariaDB (GPL + commercial), Redis (formerly AGPL), GitLab (MIT core + proprietary modules).

### Open Core
- Free, OSI-approved open source "core" (typically MIT or Apache)
- Proprietary "enterprise" features in separate, closed-source modules
- Community uses and contributes to the open core; enterprises pay for enterprise features
- Core must be genuinely useful standalone — if users feel the open core is a marketing demo, community trust erodes

Examples: GitLab (Community Edition vs. Enterprise Edition), Elasticsearch (pre-license change), HashiCorp (pre-BSL change).

**Legal architecture**: Keep open core and proprietary code as separate packages/modules. Document the boundary clearly. Ensure proprietary modules don't incorporate GPL/AGPL dependencies.

### Community Edition / Commercial Edition
Similar to open core but the entire product has two editions. May use the same or different licenses for each edition.

## Contributor License Agreements (CLAs)

A CLA is a legal agreement between a project and contributors defining the IP terms of contributions.

**Why CLAs matter**:
- Without a CLA, each contributor retains copyright in their contribution
- You cannot relicense without approval from all copyright holders
- Dual licensing is impossible without owning or having a broad license over all contributions
- Enforcing your project's license requires standing as a copyright holder

**Two types of CLAs**:

1. **Copyright Assignment CLA**: Contributor assigns copyright to the project. Project can relicense, sue for infringement, and dual-license without restriction. Risk: Contributors are permanently divesting their IP. Often rejected by contributors for this reason.

2. **Copyright License CLA** (more common): Contributor retains copyright but grants the project a perpetual, worldwide, non-exclusive, royalty-free license to reproduce, modify, distribute, sublicense, and commercialize the contribution. Core language: grants rights sufficient for relicensing and dual licensing. Less friction than full assignment.

**DCO (Developer Certificate of Origin)**: Lightweight alternative to CLA — contributors simply certify via `git commit -s` that they have the right to submit the code. Does NOT give the project any rights beyond the project's existing license. Insufficient for dual licensing or relicensing.

**CLA implementation tools**: CLA Assistant (free, GitHub integration), Linux Foundation's EasyCLA, GitHub CLA bot.

**2024 concern**: When projects with CLAs change licenses (Redis, HashiCorp, Elastic did in 2022-2024), forks (Valkey for Redis, OpenTofu for Terraform) arise using the last open source version. CLAs benefit the original maintainer but don't prevent forks at the last open source version.

## License Compatibility

Before combining code under different licenses, check compatibility:

| Your code | Library's license | Can combine? |
|---|---|---|
| Proprietary | MIT | Yes |
| Proprietary | Apache 2.0 | Yes |
| Proprietary | GPL v2 | No (copyleft infects your code) |
| Proprietary | LGPL | Yes (dynamic linking only) |
| Proprietary | AGPL | No |
| Apache 2.0 | GPL v2 | No (patent clause conflict) |
| Apache 2.0 | GPL v3 | Yes |
| MIT | Apache 2.0 | Yes |
| GPL v3 | AGPL v3 | Yes |
| GPL v2 | GPL v3 | No (v2 only, unless "or later") |

**Key rule**: GPL/AGPL is "viral" — if you statically link GPL code into your proprietary product and distribute it, your product must be released under GPL. Dynamic linking (shared libraries) and running GPL code as a separate service may avoid copyleft depending on jurisdiction and court interpretation.

## Practical Compliance Steps

1. **Maintain an SBOM (Software Bill of Materials)**: Track all third-party dependencies and their licenses. Use SPDX format. Tools: FOSSA, Black Duck, Dependabot with licensing.

2. **License headers**: Add SPDX license identifiers to all source files: `SPDX-License-Identifier: MIT` (or appropriate identifier). Follow the REUSE specification (reuse.software) for comprehensive compliance.

3. **NOTICE file**: Apache 2.0 requires a NOTICE file in distributions listing any copyright notices, patent notices, attributions from dependencies.

4. **Don't modify canonical license texts**: Never edit the canonical text of MIT, Apache, GPL, etc. Use sanctioned mechanisms (additional terms sections, NOTICE files, separate trademark policies) to add requirements.

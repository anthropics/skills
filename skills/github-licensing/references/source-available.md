# Source-Available & Commercial-Restriction Licenses: A Founder's Reference

**Goal this file serves:** You want to *publish your source code* but *prevent a cloud provider or competitor from reselling your work as a managed/SaaS service.* This is the single most common reason teams leave permissive/OSI licenses. The licenses below are the tools the industry actually uses, plus the current (2023–2025) relicensing history that shows how they play out.

> **The one thing to internalize first:** Almost every license in this file is **NOT OSI-approved** and therefore **you may not call it "open source"** (the term is defined by the [Open Source Definition](https://opensource.org/osd)). The honest umbrella terms are **"source-available"** or, for the eventually-converting ones, **"Fair Source"** ([fair.io](https://fair.io)). The only OSI-approved option here that still deters SaaS resale is **AGPL-3.0** — covered in the decision tree.

---

## Quick comparison table

| License | SPDX ID | OSI-approved? | Core mechanism | Converts to open later? |
|---|---|---|---|---|
| AGPL-3.0 | `AGPL-3.0-only` / `-or-later` | **Yes** (true open source) | Network copyleft: hosters must release *their modifications* | n/a (already open) |
| Business Source License 1.1 | `BUSL-1.1` | **No** | Time-bombed source-available; you define the carve-out | **Yes** — to your "Change License" on the "Change Date" (≤4 yrs) |
| Functional Source License 1.1 | `FSL-1.1-MIT`, `FSL-1.1-ALv2` (in SPDX list) | **No** | Anti-"competing use" only; everything else allowed | **Yes** — to MIT or Apache-2.0 after **2 years** |
| Elastic License 2.0 | `Elastic-2.0` | **No** | 3 bright-line bans (managed service, key circumvention, notices) | No (perpetual) |
| Server Side Public License 1.0 | `SSPL-1.0` | **No** (withdrawn from OSI) | §13: offer as a service → open-source your *entire* service stack | No (perpetual) |
| Commons Clause | (no SPDX ID) | **No** (it's a rider, not a license) | Removes the right to "Sell" from a base license | Depends on base license |
| PolyForm family | `PolyForm-Noncommercial-1.0.0`, etc. | **No** | Modular grants: noncommercial / internal / small-biz / anti-compete | No (perpetual) |

Sources for SPDX IDs and OSI status: [SPDX license list](https://spdx.org/licenses/), verified directly against the machine-readable [spdx/license-list-data](https://github.com/spdx/license-list-data) JSON (each of `BUSL-1.1`, `Elastic-2.0`, `SSPL-1.0`, `PolyForm-Noncommercial-1.0.0`, `PolyForm-Small-Business-1.0.0`, `FSL-1.1-MIT`, `FSL-1.1-ALv2` returns `"isOsiApproved": false`); [OSI license list](https://opensource.org/licenses). Note: **Commons Clause has no SPDX identifier** (it is a rider, not a standalone license); PolyForm Internal-Use / Perimeter / Shield / Free-Trial are published by the project but are not all in the SPDX short-id list.

---

## 1. Business Source License 1.1 (BSL / BUSL-1.1)

- **SPDX:** `BUSL-1.1` ([spdx.org/licenses/BUSL-1.1.html](https://spdx.org/licenses/BUSL-1.1.html)). **OSI status: NOT approved.** The license text itself states up front: *"The Business Source License ... is not an Open Source license."*
- **Origin/steward:** Created by MariaDB; canonical text at [mariadb.com/bsl11](https://mariadb.com/bsl11/).
- **Plain English:** Source-available with a licensor-defined commercial carve-out that **automatically converts to a real open-source license after a set date (max 4 years).**

### Why OSI/FSF object
It restricts fields of use and time-limits the grant — violating the Open Source Definition's "no discrimination against fields of endeavor" and "free redistribution" expectations. It is open *eventually*, not *now*.

### Restriction mechanism — the three parameters
BSL is a **template**: you (the Licensor) fill in three fields that define the deal.

1. **Additional Use Grant** — the production-use carve-out. This is where you encode "you can use it in production *unless* you compete with me." If you write `None`, *all* production use requires a commercial license until the Change Date.
2. **Change Date** — the date the restriction expires. Per the license terms, it must be **no more than four years** after the version's first public distribution (or the 4th anniversary auto-applies, whichever is first).
3. **Change License** — the license the work converts to on the Change Date. Must be **GPLv2-or-later or a GPL-compatible license** (e.g., MPL 2.0, Apache 2.0).

On the Change Date, every covered version retroactively becomes available under the Change License — a credible "we'll be open eventually" promise.

### Canonical BSL 1.1 parameter block (fill this in)
```
Business Source License 1.1

Parameters

Licensor:             [ Your legal entity, e.g. Acme, Inc. ]

Licensed Work:        [ Product Name ] Version [ X.Y.0 ] or later.
                      The Licensed Work is (c) [ year ] [ Your legal entity ]

Additional Use Grant: [ e.g. "You may make production use of the Licensed Work,
                      provided Your use does not include offering the Licensed
                      Work to third parties on a hosted or embedded basis which
                      is competitive with [Your Company]'s products." 
                      — or write "None" to require a commercial license for all
                      production use. ]

Change Date:          [ e.g. "Four years from the date the Licensed Work is
                      published." — must be <= 4 years ]

Change License:       [ GPLv2-or-later or a GPL-compatible license, e.g. MPL 2.0
                      or Apache 2.0 ]

For information about alternative licensing arrangements for the Licensed Work,
please visit: [ your-licensing-url ]
```
The mandatory **Notice** block must accompany distribution and begins: *"The Business Source License (this document...) is not an Open Source license. However, the Licensed Work will eventually be made available under an Open Source license, as stated in this License."* (Verbatim from the [SPDX BUSL-1.1 text](https://spdx.org/licenses/BUSL-1.1.html).)

**Hard rules from the BSL "Covenants of Licensor" (do not violate, or you may not use the "Business Source License" name/trademark):** (1) Change License must be **GPLv2-or-later or GPL-compatible**; (2) Additional Use Grant must either add rights without adding restrictions, **or** say "None"; (3) you must specify a Change Date; (4) **you may not modify the License text in any other way.** (Verbatim covenants confirmed in the [SPDX BUSL-1.1 JSON](https://github.com/spdx/license-list-data).)

### What's still allowed
Read source, self-host, modify, fork, contribute, and — depending on your Additional Use Grant — most production use. Non-competing commercial use is typically fine.

### Real-world adopters & events
- **HashiCorp → BSL 1.1 (Aug 2023):** Moved Terraform, Vault, Consul, Nomad, Boundary, Packer, Waypoint from MPL 2.0 to BSL. Change License: **MPL 2.0**; Change Date: **four years**. The *current live* Terraform `LICENSE` (post-IBM acquisition) names the Licensor as **"International Business Machines Corporation (IBM)"** for "Terraform Version 1.6.0 or later," and its Additional Use Grant reads (verbatim, abbreviated): *"You may make production use of the Licensed Work, provided Your use does not include offering the Licensed Work to third parties on a hosted or embedded basis in order to compete with IBM Corp.'s paid version(s) of the Licensed Work."* It then defines "competitive offering," "Product," and "Embedded," and clarifies that **internal use is never competitive** ([Terraform LICENSE](https://github.com/hashicorp/terraform/blob/main/LICENSE); [hashicorp.com/bsl](https://www.hashicorp.com/en/bsl); [license FAQ](https://www.hashicorp.com/license-faq)). This is the best real-world model to copy for a competitor-blocking Additional Use Grant.
- **OpenTofu fork:** The community responded with the OpenTF Manifesto (Aug 15 2023), forked Terraform (Aug 25 2023), and joined the Linux Foundation as **OpenTofu** (Sep 20 2023), staying on MPL 2.0; first stable release Jan 2024 ([opentofu.org](https://opentofu.org/blog/opentofu-announces-fork-of-terraform/)). IBM later acquired HashiCorp.
- **Others:** MariaDB MaxScale, **Couchbase** ([blog](https://www.couchbase.com/blog/couchbase-adopts-bsl-license/)), Sentry (before moving to FSL), CockroachDB, Akka.

### When to pick BSL
You want a **time-limited** moat with a credible open-source endgame, and you want **fine-grained control** over exactly which uses are carved out. Best when "eventually open" is part of your community pitch.

---

## 2. Functional Source License 1.1 (FSL-1.1)

- **SPDX:** none yet; canonical IDs are `FSL-1.1-MIT` and `FSL-1.1-Apache-2.0` (a.k.a. `FSL-1.1-ALv2`). Text at [fsl.software](https://fsl.software/), repo [getsentry/fsl.software](https://github.com/getsentry/fsl.software). **OSI status: NOT approved.**
- **Origin/steward:** Created by **Sentry** (Nov 2023) as a deliberately simpler successor to BSL.
- **Plain English:** *"You can do anything with FSL software except economically undermine its producer through harmful free-riding"* — and it **becomes Apache-2.0 or MIT after just two years.**

### Restriction mechanism
A single concept: **no "Competing Use."** A Competing Use means making the Software available in a commercial product/service that (1) substitutes for the Software, (2) substitutes for any other product/service you offer using the Software as of release date, or (3) offers the same or substantially similar functionality. Everything else — including **internal use, non-commercial education, non-commercial research, and professional services to licensees** — is explicitly permitted.

### Conversion
**Grant of Future License:** an irrevocable additional license under Apache-2.0 (or MIT) effective on the **second anniversary** of each version's release. This 2-year window is the headline difference vs. BSL's up-to-4-years.

### FSL-1.1 template (the ONLY fill-ins are `${year}` and `${licensor name}`)
The canonical files in the repo are `FSL-1.1-ALv2.template.md` (Apache future license) and `FSL-1.1-MIT.template.md`. Verbatim structure:
```
# Functional Source License, Version 1.1, ALv2 Future License

## Abbreviation
FSL-1.1-ALv2

## Notice
Copyright ${year} ${licensor name}

## Terms and Conditions
### Licensor ("We")  — the party offering the Software.
### The Software     — each version we make available under these Terms.
### License Grant    — use, copy, modify, create derivatives, perform, display,
                       redistribute, for any Permitted Purpose.
### Permitted Purpose — any purpose OTHER THAN a Competing Use.
   A "Competing Use" = making the Software available to others in a commercial
   product or service that: (1) substitutes for the Software; (2) substitutes
   for any other product/service we offer using the Software as of the release
   date; or (3) offers the same or substantially similar functionality.
   Permitted Purposes specifically INCLUDE: (1) your internal use and access;
   (2) non-commercial education; (3) non-commercial research; (4) professional
   services you provide to a licensee.
### Patents / ### Redistribution / ### Disclaimer / ### Trademarks  (boilerplate)

## Grant of Future License
We hereby irrevocably grant you an additional license to use the Software under
the Apache License, Version 2.0 that is effective on the second anniversary of
the date we make the Software available. ...
```
(Verbatim from [getsentry/fsl.software](https://github.com/getsentry/fsl.software/blob/main/FSL-1.1-ALv2.template.md), confirmed by direct fetch. The MIT variant is identical except the future license is MIT.)

### What's still allowed
Read, self-host, modify, fork, contribute, internal production use, consulting/professional services, research, education — anything that is not a Competing Use.

### When to pick FSL
You like BSL's idea but want **dramatically less complexity** (no parameters to mis-fill), a **shorter, fixed 2-year** path to true open source, and alignment with the **Fair Source** brand. This is arguably the best-fit license for the exact "stop a competitor from reselling my SaaS" goal for a small startup.

---

## Fair Source (the umbrella)

**Fair Source** ([fair.io](https://fair.io)) is a movement/definition (championed by Sentry's Chad Whitacre) for software that is **publicly readable, allows use/modification/redistribution, and is undermine-resistant (no harmful free-riding), with a delayed transition to true open source.** Recognized Fair Source licenses include **FSL**, **BSL**, and Keygen's **Fair Core License (FCL)** ([fcl.dev](https://fcl.dev/)). Marketing as "Fair Source" is honest where "open source" is not.

---

## 3. Elastic License 2.0 (ELv2)

- **SPDX:** `Elastic-2.0` ([spdx.org/licenses/Elastic-2.0.html](https://spdx.org/licenses/Elastic-2.0.html)). **OSI status: NOT approved.**
- **Origin/steward:** Elastic N.V. ([elastic.co/licensing/elastic-license](https://www.elastic.co/licensing/elastic-license)).
- **Plain English:** Very permissive *except* you can't run it as a managed service for others, can't defeat its license keys, and can't strip its notices.

### Restriction mechanism — three bright-line limitations
1. **No managed/hosted service:** *"You may not provide the software to third parties as a hosted or managed service, where the service provides users with access to any substantial set of the features or functionality of the software."*
2. **No license-key circumvention:** You may not move, change, disable, or circumvent license-key functionality, nor remove/obscure features the key protects.
3. **No notice removal:** You may not alter, remove, or obscure licensing/copyright/other notices.
([Elastic License FAQ](https://www.elastic.co/licensing/elastic-license/faq))

### Why OSI/FSF object
Limitation #1 discriminates against a field of endeavor (offering a service), failing the OSD.

### What's still allowed
Everything else: read, self-host (including for your own internal operations), modify, fork, redistribute, build commercial products on top — as long as you're not reselling *it* as a managed service.

### Real-world adopters & events
- **Elastic (2021):** Relicensed Elasticsearch & Kibana from Apache 2.0 to a **dual SSPL / ELv2** model ([elastic.co/blog/elastic-license-v2](https://www.elastic.co/blog/elastic-license-v2)). AWS responded by forking **OpenSearch** (Apache 2.0).
- **Elastic (Aug/Sep 2024):** **Re-added AGPL-3.0** as a third option, making Elasticsearch & Kibana "open source again" under an OSI-approved license, while keeping SSPL and ELv2 ([elastic.co/blog/elasticsearch-is-open-source-again](https://www.elastic.co/blog/elasticsearch-is-open-source-again)).
- Adopters: **Apollo Federation 2** ([blog](https://www.apollographql.com/blog/moving-apollo-federation-2-to-the-elastic-license-v2)), Airbyte, StarRocks.

### When to pick ELv2
You want a **permanent** (non-converting) restriction that's **simple and broad**, you're comfortable never calling it open source, and "no one else hosts this as a service" is your only real concern.

---

## 4. Server Side Public License 1.0 (SSPL-1.0)

- **SPDX:** `SSPL-1.0` ([spdx.org/licenses/SSPL-1.0.html](https://spdx.org/licenses/SSPL-1.0.html)). **OSI status: NOT approved** — MongoDB submitted it in 2018 and **withdrew the submission in 2019** after the license-review list concluded the consensus for approval didn't exist.
- **Origin/steward:** MongoDB ([mongodb.com/legal/licensing/server-side-public-license](https://www.mongodb.com/legal/licensing/server-side-public-license)). It's a modified GPLv3.
- **Plain English:** Like GPLv3, but if you offer the software *as a service*, you must open-source (under SSPL) **your entire service stack**, not just the software.

### Restriction mechanism — §13
The only substantive change from GPLv3: **Section 13.** If you make the program's functionality available to third parties as a service, you must release under SSPL *"all programs that you use to make the Program or modified version available as a service, including ... management software, user interfaces, application program interfaces, automation software, monitoring software, backup software, storage software and hosting software, all such that a user could run an instance of the service using the Service Source Code you make available."*

### Why OSI rejected it
§13 reaches **beyond the licensed work** to force disclosure of independent, separately-developed software used merely *alongside* it — violating **OSD #6 (no discrimination against fields of endeavor)** and #9 (license must not restrict other software). In practice it's a poison pill aimed at hyperscalers, not a true copyleft. ([OSI / license-review discussion](https://lists.opensource.org/pipermail/license-review_lists.opensource.org/2019-March/003989.html); [Wikipedia](https://en.wikipedia.org/wiki/Server_Side_Public_License)).

### What's still allowed
Read, self-host, modify, fork, redistribute, and even *use it internally to run a service* — the §13 burden triggers only when you offer **that software's functionality itself** as a service to third parties.

### Real-world adopters & events
- **MongoDB (Oct 2018):** First adopter, Apache/AGPL → SSPL.
- **Elastic (2021):** Adopted SSPL/ELv2 (see above); later added AGPL (2024).
- **Redis (Mar 2024):** Moved core from BSD-3 to **dual RSALv2 + SSPLv1** ([redis.io/blog/rsalv2-sspl-announcement](https://redis.io/blog/rsalv2-sspl-announcement/)), triggering the **Valkey** fork (Linux Foundation, BSD).
- **Redis (May 2025):** **Returned to open source** — Redis 8 added **AGPLv3** as a third option (now tri-licensed AGPLv3 / RSALv2 / SSPLv1), after creator Salvatore Sanfilippo rejoined ([redis.io/blog/agplv3](https://redis.io/blog/agplv3/)).

### When to pick SSPL
You're a database/infra vendor specifically worried about **hyperscalers** monetizing your project, you want a **strong, permanent** deterrent, and you accept that many distros (Debian, Fedora, RHEL) **won't ship SSPL software**. Note the broad trend (Elastic, Redis) is **away** from SSPL toward AGPL.

---

## 5. Commons Clause (a rider, not a license)

- **SPDX:** none. **OSI status: N/A / NOT open source.** It is a **License Condition rider** layered on top of an existing license (e.g., "Apache-2.0 + Commons Clause"). Adding it to an OSI license makes the result **not open source.**
- **Origin/steward:** Drafted by Heather Meeker; published 2018 ([commonsclause.com](https://commonsclause.com/)).
- **Plain English:** Bolt-on text that strips one right from the base license — the right to **"Sell"** the software.

### Restriction mechanism (verbatim core)
*"...the grant of rights under the License will not include, and the License does not grant to you, the right to Sell the Software. ... 'Sell' means practicing any or all of the rights granted to you under the License to provide to third parties, for a fee or other consideration (including without limitation fees for hosting or consulting/support services related to the Software), a product or service whose value derives, entirely or substantially, from the functionality of the Software."*

You fill three fields: `Software: [SOFTWARE]`, `License: [LICENSE]`, `Licensor: [LICENSOR]`.

### The controversy
**Redis Labs (Aug 2018)** applied Apache-2.0 + Commons Clause to several Redis modules ([redis.io/blog](https://redis.io/blog/redis-labs-modules-license-changes/)). Backlash centered on **license-washing** — keeping the recognizable "Apache" name while quietly removing core freedoms, which misleads users and blocks distro inclusion ([LWN](https://lwn.net/Articles/763179/); [TechCrunch](https://techcrunch.com/2018/09/07/commons-clause-stops-open-source-abuse/)). Redis Labs **abandoned** Commons Clause in Feb 2019, replacing it with its own **Redis Source Available License (RSAL)**.

### What's still allowed
Whatever the base license grants minus "Sell": read, self-host, modify, fork, internal use, redistribute for free.

### When to pick Commons Clause
Rarely the best choice today — its history makes it a reputational liability, and "Sell" is vaguer than the modern competing-use language in FSL/BSL. Consider it only for a **quick, blunt** restriction on an existing permissively-licensed project where you don't want to author a full custom license. Prefer FSL/BSL/PolyForm instead.

---

## 6. PolyForm license family

- **Steward:** The PolyForm Project (lawyers + technologists); plain-language, modular licenses ([polyformproject.org](https://polyformproject.org/), [GitHub](https://github.com/polyformproject/polyform-licenses)). **OSI status: NOT approved** for any variant.
- **Plain English:** A *menu* of small, composable source-available grants — pick the one matching exactly who you want to allow.

| Variant | SPDX ID | Permits |
|---|---|---|
| **Noncommercial** | `PolyForm-Noncommercial-1.0.0` | Any **noncommercial** use: personal, research, hobby, plus charities, schools, and governments regardless of funding |
| **Internal Use** | `PolyForm-Internal-Use-1.0.0` | Use for **your own internal business operations** only (not offering to others) |
| **Small Business** | `PolyForm-Small-Business-1.0.0` | Free commercial use for companies **under $1M/yr revenue and <100 employees**; bigger firms must pay |
| **Shield** | (no SPDX id yet) | Anything **except competing** with the licensor |
| **Perimeter** | `PolyForm-Perimeter-1.0.0` | Anything **except competing** with the licensor's products (broader anti-compete framing than Shield) |
| **Free Trial** | (no SPDX id yet) | **Time-limited** free trial use only |

Sources: [polyformproject.org/licenses](https://polyformproject.org/licenses/); SPDX IDs verified in [spdx/license-list-data](https://github.com/spdx/license-list-data).

### Restriction mechanism
Each license is a clean, standalone grant scoped to one allowed population/use. **Shield/Perimeter** are the SaaS-resale-prevention ones (anti-compete). **Noncommercial/Internal-Use/Small-Business** restrict by *who/what kind of use* rather than by competition.

### What's still allowed
Always: read, self-host, modify, fork, contribute. Commercial latitude depends on the variant chosen.

### When to pick PolyForm
You want **off-the-shelf, lawyer-drafted, plain-language** terms and your moat is best expressed as "**who** may use this" (noncommercial, internal-only, small-business-free) or a clean **anti-compete** (Perimeter/Shield) — and you **don't** need an eventual-open-source conversion (PolyForm is perpetual).

---

## Decision sub-tree: "Stop a cloud provider/competitor from offering my product as a managed service"

```
START: Do you need to keep calling it "OPEN SOURCE" (OSI-approved)?
│
├─ YES, must stay OSI open source
│    └─> AGPL-3.0  (the only real answer)
│         • OSI-approved & FSF-endorsed; true open source.
│         • Deterrent: anyone hosting a MODIFIED version as a service must
│           publish their modifications under AGPL. Hyperscalers dislike this
│           and often avoid AGPL software for managed offerings.
│         • WEAKNESS: does NOT stop someone hosting an UNMODIFIED copy. It
│           compels source-sharing, not "you can't compete." AWS can still
│           run vanilla AGPL software as a service if it shares changes.
│         • This is why Elastic (2024) and Redis (2025) ADDED AGPL back.
│
└─ NO, willing to be "source-available" / "Fair Source" (NOT open source)
     │
     ├─ Want it to BECOME open source eventually (best community optics)?
     │    ├─ Want simple + fixed 2-year flip + Fair Source brand
     │    │     └─> FSL-1.1  (Apache-2.0 or MIT future license)
     │    └─ Want fine-grained control + up-to-4-year window + GPL-family flip
     │          └─> BSL 1.1  (set your own Additional Use Grant + Change Date)
     │
     ├─ Want a PERMANENT restriction, simple & broad?
     │    └─> Elastic License 2.0  (clean "no managed service" ban)
     │
     ├─ Want a PERMANENT restriction aimed squarely at hyperscalers,
     │  and you're infra/DB and OK with distros refusing to ship you?
     │    └─> SSPL-1.0  (but note the industry is migrating OFF SSPL → AGPL)
     │
     ├─ Want to restrict by WHO uses it (noncommercial / internal / small-biz)
     │  rather than by competition?
     │    └─> PolyForm (Noncommercial / Internal-Use / Small-Business)
     │       …or PolyForm Perimeter/Shield for a clean anti-compete.
     │
     └─ Just want to bolt a restriction onto an existing permissive repo fast?
          └─> Commons Clause rider (functional, but reputationally damaged;
              prefer FSL/BSL/PolyForm).
```

### Trade-off summary

| Factor | AGPL-3.0 | BSL 1.1 | FSL-1.1 | Elastic-2.0 | SSPL-1.0 | Commons Clause |
|---|---|---|---|---|---|---|
| Still "open source"? | **Yes** | No | No | No | No | No |
| OSI-approved | Yes | No | No | No | No (withdrawn) | No |
| Stops *unmodified* resale? | **No** (only forces source-sharing) | Yes (via grant) | Yes | Yes | Effectively yes (poison-pill §13) | Yes |
| Eventually open? | already | Yes (≤4 yr) | Yes (2 yr) | No | No | Depends on base |
| Contributor friction | Low (familiar) | Medium (CLA usually needed) | Medium | Medium-High | **High** (distro bans) | Medium-High (license-washing stigma) |
| Distro shipping (Debian/Fedora) | Yes | No | No | No | **No** | No |
| Enforceability clarity | High (battle-tested) | Good (clear params) | Good (clear "competing use") | Good (bright lines) | Untested at scale; broad §13 | Weak ("Sell" is vague) |
| Best for | Staying open while deterring forks-as-a-service | Time-boxed moat w/ open endgame | Startup wanting simple moat + open endgame | Permanent simple no-SaaS ban | DB/infra vs hyperscalers | Quick blunt rider (legacy) |

**Key nuance founders miss:** AGPL alone does **not** prevent a competitor from running your *unmodified* code as a service — it only forces them to publish *modifications*. If your real fear is "AWS launches Managed MyProduct," AGPL is weaker than BSL/FSL/ELv2/SSPL for that specific threat. That gap is exactly why the 2018–2024 wave went to SSPL/ELv2/BSL — and why the 2024–2025 counter-wave (Elastic, Redis) **dual-licensed AGPL alongside** a restrictive license rather than relying on AGPL alone.

---

## Fill-in templates

### BSL 1.1 — competitor-blocking configuration (recommended starting point)
```
Business Source License 1.1

Parameters

Licensor:             Acme, Inc.

Licensed Work:        Acme Server Version 2.0.0 or later.
                      The Licensed Work is (c) 2026 Acme, Inc.

Additional Use Grant: You may make production use of the Licensed Work, provided
                      Your use does not include offering the Licensed Work to
                      third parties on a hosted or embedded basis which is
                      competitive with Acme's products.

Change Date:          Four years from the date the Licensed Work is published.

Change License:       Apache License, Version 2.0

For information about alternative licensing arrangements for the Licensed Work,
please visit: https://acme.example/license

-----------------------------------------------------------------------------
[Followed by the verbatim BSL 1.1 "Notice" and "Terms" body from
 https://spdx.org/licenses/BUSL-1.1.html — do not edit that body.]
```
> Rules to respect: **Change Date ≤ 4 years**; **Change License must be GPLv2-or-later-compatible** (Apache-2.0, MPL-2.0, and the GPL family all qualify); keep the Notice block intact.

### FSL-1.1 — Apache-2.0 future license (simplest competitor-blocking option)
```
# Functional Source License, Version 1.1, ALv2 Future License

## Abbreviation
FSL-1.1-ALv2

## Notice
Copyright 2026 Acme, Inc.

[Followed by the verbatim FSL-1.1 Terms and Conditions from
 https://github.com/getsentry/fsl.software/blob/main/FSL-1.1-ALv2.template.md
 — the Permitted Purpose / Competing Use language and the
 "Grant of Future License" (Apache-2.0 after 2 years) are fixed; the ONLY
 fields you edit are ${year} and ${licensor name} on the Copyright line.]
```
> Use `FSL-1.1-MIT` instead if you prefer the work to convert to MIT rather than Apache-2.0 after two years. There are **no other parameters** — that simplicity (no Additional Use Grant to mis-draft, no Change Date to pick) is the whole point of FSL vs BSL.

---

## Sources

- SPDX license list & data: https://spdx.org/licenses/ · https://github.com/spdx/license-list-data
- Open Source Definition / OSI license list: https://opensource.org/osd · https://opensource.org/licenses
- BSL 1.1: https://mariadb.com/bsl11/ · https://spdx.org/licenses/BUSL-1.1.html · HashiCorp: https://www.hashicorp.com/en/bsl · Terraform LICENSE: https://github.com/hashicorp/terraform/blob/main/LICENSE · Couchbase: https://www.couchbase.com/blog/couchbase-adopts-bsl-license/
- OpenTofu: https://opentofu.org/blog/opentofu-announces-fork-of-terraform/
- FSL / Fair Source: https://fsl.software/ · https://github.com/getsentry/fsl.software · https://blog.sentry.io/introducing-the-functional-source-license-freedom-without-free-riding/ · https://fair.io · https://fcl.dev/
- Elastic License 2.0: https://www.elastic.co/licensing/elastic-license · https://www.elastic.co/licensing/elastic-license/faq · https://www.elastic.co/blog/elastic-license-v2 · https://www.elastic.co/blog/elasticsearch-is-open-source-again
- SSPL: https://www.mongodb.com/legal/licensing/server-side-public-license · https://en.wikipedia.org/wiki/Server_Side_Public_License · https://lists.opensource.org/pipermail/license-review_lists.opensource.org/2019-March/003989.html
- Redis: https://redis.io/blog/rsalv2-sspl-announcement/ · https://redis.io/blog/agplv3/ · https://redis.io/legal/licenses/
- Commons Clause: https://commonsclause.com/ · https://redis.io/blog/redis-labs-modules-license-changes/ · https://lwn.net/Articles/763179/ · https://techcrunch.com/2018/09/07/commons-clause-stops-open-source-abuse/
- PolyForm: https://polyformproject.org/ · https://polyformproject.org/licenses/ · https://github.com/polyformproject/polyform-licenses

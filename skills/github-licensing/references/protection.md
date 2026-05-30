# Protecting & Commercializing a Project via Licensing

*Dual-licensing, contributor agreements (CLA/DCO), trademark/attribution, correct license customization, and implementation hygiene.*

> **Not legal advice.** Licensing and trademark decisions have real legal and financial consequences. Consult a qualified IP/tech-transactions attorney before adopting any of these mechanisms — especially CLAs, copyright assignments, and custom license terms.

## Contents
- [The three goals → mechanisms](#0-the-three-goals-mapped-to-mechanisms)
- [Dual-licensing / open-core](#1-dual-licensing--open-core)
- [Contributor agreements (CLA vs DCO)](#2-contributor-agreements--the-enabler-for-dual-licensing)
- [Trademark & attribution](#3-trademark--attribution-protection)
- [Customizing licenses correctly](#4-customizing-licenses-correctly-the-big-footgun)
- [Implementation hygiene (SPDX/REUSE)](#5-implementation-hygiene)
- [Quick decision guide](#quick-decision-guide)

---

## 0. The three goals, mapped to mechanisms

| Goal | Primary mechanism | Notes |
|------|-------------------|-------|
| **Stop competitors reselling as SaaS** | Copyleft (AGPL) or source-available license (BSL / SSPL / FSL) on the community edition | License choice, not contracts, does the work here |
| **Dual-license (open community + paid commercial)** | Strong copyleft (GPL/AGPL) community edition **+** separately negotiated commercial license, backed by a **CLA / copyright control** | You can only relicense code you own or control |
| **Protect name/brand** | **Trademark** (separate legal right) + a trademark/brand-usage policy + non-endorsement clauses | Copyright license ≠ trademark grant |

These are independent levers — you can combine all three.

---

## 1. Dual-Licensing / Open-Core

### How it works legally

Dual licensing means publishing the **same code** under two licenses simultaneously: typically a strong copyleft open-source license (GPL or AGPL) for the community, and a **paid commercial/proprietary license** for businesses that don't want to comply with copyleft obligations. The commercial license's value proposition is precisely *removing the copyleft "viral" reciprocity* — a company can embed your code in a closed product without open-sourcing their own work.

**The hard requirement:** to offer code under a second license, you must **own or control all rights** to that code. A copyright holder can license their own work however many ways they like — but the moment an outside contributor's copyrighted code lands in your repo, *they* own it, and you can no longer unilaterally relicense the combined work. This is why **a CLA (or copyright assignment) is effectively mandatory for a dual-licensing business**.

### The classic pattern and real examples

- **MySQL** — the archetype: GPL community edition + paid commercial license for OEMs who don't want GPL obligations.
- **Qt** — GPL/LGPL open editions + a commercial license bundling proprietary tools.
- **MongoDB** — moved from AGPL to **SSPL** (Oct 2018) to stop cloud providers (notably AWS) offering Mongo-as-a-service without contributing back; commercial customers buy *MongoDB Enterprise Advanced*.
- **Redis** — BSD → dual SSPL/RSALv2 (March 2024) → added **AGPLv3** with Redis 8 (2025) after community backlash.
- **Elasticsearch** — added AGPLv3 as a third license option in 2024.
- **GitLab, Sentry, Mattermost** — *open-core*, a distinct model (below).

### Open-core vs. dual-license vs. relicensing

| Model | What it means | CLA pressure |
|-------|---------------|--------------|
| **Dual-license** | The *same* codebase offered under both an open and a commercial license | **High** — you must control all copyright to relicense |
| **Open-core** | An open-source *core* + architecturally **separate** proprietary modules/add-ons (GitLab CE vs EE, Sentry) | **Lower** — you only need to own the proprietary add-ons; community contributions to the open core aren't relicensed |
| **Relicensing** | Changing the project's license going forward (e.g. Redis BSD→SSPL) | Requires consent of, or rights over, all copyright holders — which is why prior CLAs make relicensing possible |

**Strategic takeaway: if you ever intend to dual-license or relicense, set up the CLA from day one.** Retrofitting consent from hundreds of past contributors is often impossible.

### How to structure the repo

```
/LICENSE                   # the open-source license (e.g. AGPL-3.0 or GPL-3.0)
/LICENSE-COMMERCIAL.md      # human-readable explainer + how to buy a commercial license
/COMMERCIAL-LICENSE.txt     # (optional) the actual proprietary terms, or "contact sales@"
/NOTICE                     # attribution notices (Apache-style)
/CONTRIBUTING.md            # links to the CLA / explains DCO sign-off requirement
/TRADEMARK.md               # brand usage policy (see §3)
```

**Dual-license file header** (near top of each source file):

```
/*
 * Copyright (c) 2026 ACME Inc.
 *
 * This file is available under EITHER:
 *   (1) the GNU Affero General Public License, version 3, as published
 *       by the Free Software Foundation; OR
 *   (2) a commercial license from ACME Inc.
 *
 * SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-ACME-Commercial
 *
 * For commercial licensing, contact sales@acme.example.
 */
```

---

## 2. Contributor Agreements — the enabler for dual-licensing

You need inbound rights from contributors broad enough to support whatever you want to do with the code. Two mechanisms dominate: the **DCO** and the **CLA**.

### DCO vs. CLA at a glance

| | **DCO** (Developer Certificate of Origin) | **CLA** (Contributor License Agreement) |
|---|---|---|
| What it is | A per-commit *attestation* that the contributor has the right to submit the code under the project's license | A *contract* granting the project explicit rights (a broad license, or assignment) |
| Mechanism | `Signed-off-by:` trailer on **every commit** | Signed **once**, covers all future contributions |
| Grants relicensing rights? | **No** — only certifies the contribution is properly licensed under the *existing* license | **Yes** (if drafted to) — this is what enables dual-licensing/relicensing |
| Friction | Very low (one git flag) | Higher — legal review, signing, can deter casual contributors |
| Who signs | Always the author | Can be signed by a company on behalf of employees |

**Rule of thumb:** If you ever want to **dual-license or relicense**, the DCO is *not enough* — you need a CLA with a broad license grant (or assignment). The DCO only promises the code is properly licensed under your *current* license; it conveys no power to relicense.

### The exact DCO text (Version 1.1)

```
Developer Certificate of Origin
Version 1.1

Copyright (C) 2004, 2006 The Linux Foundation and its contributors.

Everyone is permitted to copy and distribute verbatim copies of this
license document, but changing it is not allowed.


Developer's Certificate of Origin 1.1

By making a contribution to this project, I certify that:

(a) The contribution was created in whole or in part by me and I
    have the right to submit it under the open source license
    indicated in the file; or

(b) The contribution is based upon previous work that, to the best
    of my knowledge, is covered under an appropriate open source
    license and I have the right under that license to submit that
    work with modifications, whether created in whole or in part
    by me, under the same open source license (unless I am
    permitted to submit under a different license), as indicated
    in the file; or

(c) The contribution was provided directly to me by some other
    person who certified (a), (b) or (c) and I have not modified
    it.

(d) I understand and agree that this project and the contribution
    are public and that a record of the contribution (including all
    personal information I submit with it, including my sign-off) is
    maintained indefinitely and may be redistributed consistent with
    this project or the open source license(s) involved.
```

Source: developercertificate.org. **Do not edit this text** — it is a verbatim-only document.

### The `Signed-off-by` git workflow

```bash
# Add the sign-off trailer to a single commit:
git commit -s -m "Fix race condition in worker pool"
#   -> Signed-off-by: Jane Doe <jane@example.com>  (uses your git user.name/email)

# Amend a commit you forgot to sign:
git commit --amend -s --no-edit

# Sign every commit across a rebase range:
git rebase --signoff HEAD~3
```

Git **intentionally** provides no auto-append config — automating it would undermine the deliberate, legally-significant nature of the certification.

### CLA types and the assignment-vs-license distinction

Reference templates: the **Apache ICLA/CCLA** and the **Harmony Agreements** (harmonyagreements.org).

- **Individual (ICLA)** vs. **Corporate/Entity (CCLA)** — the corporate variant binds an organization and its employees.
- **Copyright *license* grant** — contributor *keeps* ownership and grants you a broad (perpetual, irrevocable, sublicensable) license. The **Apache model**; enough to support dual-licensing if the grant is broad. Less alienating to contributors.
- **Copyright *assignment* (CAA)** — contributor *transfers* ownership to the project, with a license-back. Maximum control; more friction; the FSF's historical model.

Harmony handles the **employee** problem (employer consent) and **minors**. *Caution:* some critics argue certain Harmony variants over-reach — have counsel review whichever template you adopt.

### Tooling

| Tool | What it does |
|------|--------------|
| **CLA Assistant** (cla-assistant.io) | Store CLA as a Gist; bot comments on PRs, lets contributors sign in-PR (GitHub-authenticated), sets PR status |
| **CLA Assistant Lite** | SAP's GitHub-Actions-based variant |
| **cla-bot** (finos) | Checks committers against a `.clabot` file; labels PRs signed/unsigned |
| **DCO GitHub App** (Probot DCO) | Verifies every commit has a valid `Signed-off-by`; blocks merge if missing |

All integrate with GitHub **required status checks**, so a PR can't merge until the agreement check passes.

---

## 3. Trademark & Attribution Protection

### Copyright license ≠ trademark protection

An open-source license grants rights to the **code (copyright)**. It does **not** grant rights to your **name, brand, or logo (trademark)** — a separate legal right. So you can open-source the code while keeping the *name* locked down: anyone may fork and use the software, but only the official project (or approved builds) may call themselves by your trademark. Since anyone can modify the code, the trademark is what lets users tell the genuine product from forks.

### How licenses already handle this

- **Apache-2.0 §6 (Trademarks):** does "not grant permission to use the trade names, trademarks, service marks, or product names of the Licensor, except as required for reasonable and customary use in describing the origin of the Work and reproducing the content of the NOTICE file."
- **BSD-3-Clause non-endorsement clause:** "Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission."

If you use **MIT** (silent on trademarks), a separate trademark policy matters even more.

### Adding a trademark / brand-usage policy

Publish a `TRADEMARK.md` (or `/trademark` page). Strong models: **Rust/Cargo** (Rust Foundation), **Mozilla**, and the **Linux** mark. The Rust model: most **non-commercial** uses allowed without permission; most **commercial** uses need permission; cardinal rule is **uses must not appear official or imply endorsement**.

> Lesson from Rust's 2023 episode: the first draft trademark policy drew heavy criticism for being too restrictive; the revised draft loosened it. **Write the policy permissively** — over-restriction alienates the community without adding much protection.

### Requiring attribution *without* breaking the license

- Use **Apache-2.0** and put attribution requirements in the **NOTICE file** (§4 requires downstream to carry it).
- Rely on the existing **copyright-notice-retention** clauses (every license requires keeping notices).
- The **BSD/Apache non-endorsement** clauses already prevent others implying you endorse them.

Avoid bolting "you must display our logo on every screen" **badgeware** clauses onto a standard license body — that creates a non-standard license (see §4).

---

## 4. Customizing Licenses Correctly (the big footgun)

### The rule: don't edit the canonical body of a standard license

- **MIT** is the one common exception: it tolerates a **trailing addendum** appended *after* the standard text.
- **GPL/LGPL/AGPL text is FSF-copyrighted** and **verbatim-copy-only** — you may not modify the body. (Same for the DCO document.)
- **Apache-2.0** is meant to be applied unmodified; customization goes in the **NOTICE** file or an appendix, not the license body.

Editing a standard license's body produces a **new, non-standard license** that is incompatible, confusing, and breaks tooling.

### The correct mechanisms instead

| Want to... | Use |
|------------|-----|
| Loosen a GPL condition for your code | **GPLv3 §7 "additional permissions"** — exceptions that *supplement* the license; a downstream recipient may remove them |
| Allow proprietary linking | A **linking exception** (a specific §7 additional permission) |
| Add a non-compete / "no selling this as-is" rider | A **rider layered on top** — e.g. the **Commons Clause** (removes the right to "Sell"); makes the result **not** open source |
| Time-limited source-available protection | **BSL** — its **"Additional Use Grant"** is the sanctioned fill-in slot; converts to an OSI license after a change date (commonly 4 years) |
| SaaS non-compete that self-heals | **FSL** (Sentry) — `FSL-1.1-MIT` / `FSL-1.1-ALv2`, convert to MIT/Apache after **2 years**; bars a "Competing Use" but permits everything else |
| Carry attribution / extra notices | **NOTICE file** (Apache) or supplemental terms in a separate file |
| Two licenses on one codebase | **Dual-licensing** (§1) — cleaner than a custom hybrid |

### What modifying a license does to tooling

When you alter a standard license's text, automated detectors **stop recognizing it**:
- **SPDX** and **GitHub's `licensee`** match against canonical texts; a modified license fails to match a standard SPDX ID.
- You must then declare it with a custom **`LicenseRef-`** identifier (e.g. `LicenseRef-ACME-Commercial`) and provide the corresponding text. The `LicenseRef-` format is defined in the REUSE spec and SPDX.
- Practical fallout: GitHub's sidebar shows "license not recognized," dependency scanners flag it as unknown, and some corporate policies auto-reject unrecognized licenses.

This is a real cost of source-available/custom licenses — weigh it against the protection gained.

---

## 5. Implementation Hygiene

### SPDX-License-Identifier headers (the modern standard)

A single tag at/near the top of each source file, in a comment, on its own line (recommended by SPDX and the FSFE's **REUSE** initiative):

```c
// SPDX-License-Identifier: MIT
```
```python
# SPDX-License-Identifier: GPL-2.0-or-later
```

**Expressions** (`AND` / `OR` / `WITH`):

```c
// Dual-license, recipient's choice:
// SPDX-License-Identifier: MIT OR Apache-2.0

// Open OR your commercial (custom ref):
// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-ACME-Commercial

// GPL with a linking exception:
// SPDX-License-Identifier: GPL-2.0-or-later WITH Classpath-exception-2.0
```

`OR` = licensee chooses; `AND` = both apply; `WITH` = a license + a named exception. Valid IDs come from the SPDX License List.

### File naming and what GitHub detects

- **`LICENSE`** (or `LICENSE.txt`/`.md`) — the primary file GitHub's **licensee** scans for the badge. Keep the **canonical text unmodified** so it's recognized.
- **`COPYING`** — the traditional GNU name; equally valid.
- **`NOTICE`** — Apache-style attribution; **not** a substitute for LICENSE.
- Under **REUSE**, canonical license texts live in a top-level **`LICENSES/`** directory named by SPDX ID (e.g. `LICENSES/MIT.txt`, `LICENSES/AGPL-3.0-only.txt`).

### Copyright notice format

```
Copyright (c) 2026 ACME Inc.
```

- "Copyright", `(c)`, and `©` are interchangeable; "Copyright" is safest for plain ASCII.
- **Year:** use the year of first publication. The year-range debate (`2019-2026` vs single year): many projects now use a single year or drop it entirely since git history establishes dates. Either is legally fine — pick one and be consistent. Don't fabricate a range; `2026` alone is correct for a new project.

### Multi-license repos and REUSE

For repos mixing licenses (AGPL core + MIT examples + CC-BY docs), the **REUSE specification** gives a deterministic scheme:
1. Every file carries an `SPDX-License-Identifier` header (or a `.license` sidecar / `REUSE.toml` for files that can't take comments).
2. All referenced license texts live in `LICENSES/<SPDX-ID>.txt`.
3. `reuse lint` verifies 100% coverage and that every referenced license is present.

This makes the repo machine-readable and audit-clean — valuable when enterprise procurement/legal teams scan your project.

---

## Quick decision guide

- **Just want attribution + liability disclaimer, no commercial play:** MIT or Apache-2.0; DCO; a short trademark policy.
- **Stop SaaS resale, stay OSI-open:** **AGPL-3.0**; CLA if you want a commercial escape hatch.
- **Stop SaaS resale, willing to be source-available:** **BSL** (with Additional Use Grant) or **FSL** (auto-converts to MIT/Apache in 2 yrs).
- **Sell commercial licenses (dual-license):** strong copyleft (GPL/AGPL) **+** broad-grant **CLA** from day one **+** `LICENSE-COMMERCIAL.md`.
- **Free core, paid add-ons (open-core):** open license on core (CLA optional), proprietary license on separately-built add-ons.

---

### Key sources
- DCO & workflow: developercertificate.org, Linux Foundation DCO, git-scm "Signing Your Work"
- CLAs: Harmony Agreements, CLA Assistant, cla-bot (finos)
- Dual-license/open-core: TermsFeed, MongoDB SSPL FAQ
- Customization: Apache-2.0, GPLv3 additional terms, FSL (Sentry), TermsFeed source-available risks
- Trademark: Rust legal policy, Software Freedom Conservancy
- Hygiene: SPDX handling-license-info, SPDX License List, REUSE Spec 3.2

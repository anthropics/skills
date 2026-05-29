# Permissive Licenses: MIT, Apache-2.0, BSD-2-Clause, BSD-3-Clause, ISC

*Compiled from SPDX, OSI, choosealicense.com, the Apache Software Foundation, and the FSF/GNU license list. For developers, not lawyers — but accurate on the legal nuance that actually matters.*

> **What "permissive" means:** All five let anyone use, modify, distribute, and commercialize the code, including in closed-source products, with essentially one obligation — keep the copyright/license notice. None are copyleft (no obligation to release your modifications). The real differences are in **patent grants, trademark handling, and attribution mechanics**, not in how much they "let you do."

## Contents
- [MIT](#1-mit-license)
- [Apache-2.0](#2-apache-license-20)
- [BSD-2-Clause](#3-bsd-2-clause-simplified--freebsd-license)
- [BSD-3-Clause](#4-bsd-3-clause-new--modified-bsd-license)
- [ISC](#5-isc-license)
- [Comparison table](#6-comparison-table)
- [Boilerplate snippets](#7-canonical-boilerplate-snippets)
- [Customization: legitimate vs. license-breaking](#8-customization-patterns--legitimate-vs-license-breaking)
- [2024–2026 notes & misconceptions](#9-20242026-notes--misconceptions-to-flag)

---

## 1. MIT License

- **SPDX identifier:** `MIT` · **OSI-approved:** Yes (the single most popular OSI license).
- **Plain-English summary:** A short, simple permissive license whose only condition is that the copyright and license notice be preserved in copies.

| Permissions | Conditions | Limitations |
|---|---|---|
| Commercial use, Modification, Distribution, Private use | Include copyright & license notice | No liability, No warranty |

- **Express patent grant:** **No.** MIT contains no explicit patent license. Courts have not resolved whether the broad grant ("use, copy, modify… and/or sell") confers an *implied* patent license. No patent-retaliation clause.
- **NOTICE file / attribution:** No NOTICE file. The single attribution mechanic is "the above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software."
- **Trademark:** Silent. No trademark grant, no non-endorsement clause.
- **Boilerplate / how to apply:** One `LICENSE` file in the repo root. Replace `[year]` and `[fullname]`. Per-file source headers are optional and uncommon for MIT.
- **Compatibility:** Universally compatible. GPL-compatible (GPLv2 and GPLv3) and compatible with Apache-2.0.
- **Pick MIT when:** You want maximum adoption and the most recognizable, frictionless license, and you are not worried about explicit patent protection. Default choice for most small/library projects, especially in the JS/npm world.

---

## 2. Apache License 2.0

- **SPDX identifier:** `Apache-2.0` · **OSI-approved:** Yes.
- **Plain-English summary:** A permissive license like MIT but with an **explicit patent grant, patent-retaliation defense, change-documentation requirement, and a NOTICE-file mechanism** — built for corporate/multi-contributor projects.

| Permissions | Conditions | Limitations |
|---|---|---|
| Commercial use, Modification, Distribution, **Patent use**, Private use | Include copyright, **Document changes** (state modified files) | **Trademark use**, No liability, No warranty |

- **Express patent grant:** **Yes — the key differentiator.** §3 grants each contributor's "perpetual, worldwide, non-exclusive, no-charge, royalty-free, irrevocable… patent license" for claims necessarily infringed by their contribution. **Patent retaliation/termination:** also §3 — if you sue alleging the Work infringes a patent, your patent licenses for that Work terminate as of the filing date.
- **NOTICE file / attribution:** §4 has four redistribution requirements: (a) include a copy of the license; (b) mark modified files with prominent change notices; (c) retain all copyright/patent/trademark/attribution notices from the source; (d) **if the original includes a `NOTICE` file, reproduce its attribution notices in your derivative works** in at least one visible location. Keep the NOTICE file minimal — it propagates downstream.
- **Trademark:** §6 explicitly **does not grant** rights to trade names, trademarks, service marks, or product names of any contributor.
- **Boilerplate / how to apply:** Full license text in `LICENSE` at the repo root. ASF *recommends* (does not require) adding the short header from the license appendix to the top of each source file (see §7 below).
- **Compatibility:** **Incompatible with GPLv2** (its patent-termination terms are restrictions GPLv2 doesn't allow), but **compatible with GPLv3** — one-directional: Apache code can go into GPLv3 projects, but not vice-versa.
- **Pick Apache-2.0 when:** The project has multiple contributors or corporate backing, or operates in a patent-sensitive domain, and you want explicit patent protection + retaliation defense. Standard for large foundation/enterprise projects (Kubernetes, Swift, Android).

---

## 3. BSD-2-Clause ("Simplified" / "FreeBSD" License)

- **SPDX identifier:** `BSD-2-Clause` · **OSI-approved:** Yes.
- **Plain-English summary:** A minimal permissive license — functionally near-identical to MIT — requiring retention of the copyright notice and disclaimer in both source and binary redistributions.

| Permissions | Conditions | Limitations |
|---|---|---|
| Commercial use, Modification, Distribution, Private use | Include copyright | No liability, No warranty |

- **Express patent grant:** **No.** Same posture as MIT.
- **NOTICE file / attribution:** No NOTICE file. Two named conditions: (1) source redistributions retain the copyright notice + conditions + disclaimer; (2) binary redistributions reproduce them in documentation/materials.
- **Trademark:** Silent (no non-endorsement clause — that's what distinguishes it from BSD-3).
- **Boilerplate / how to apply:** `LICENSE` file in repo root; replace `[year]` and `[fullname]`.
- **Compatibility:** Universally compatible; GPL-compatible.
- **Pick BSD-2-Clause when:** You want MIT-equivalent simplicity but prefer BSD-family phrasing (common in the C/Unix/FreeBSD ecosystem), and you don't need the name-protection clause.

> **Misconception to flag:** BSD-2 is *not* meaningfully "more protective" than MIT. The differences are cosmetic/wording; both lack a patent grant.

---

## 4. BSD-3-Clause ("New" / "Modified" BSD License)

- **SPDX identifier:** `BSD-3-Clause` · **OSI-approved:** Yes.
- **Plain-English summary:** BSD-2-Clause plus a third clause forbidding use of the copyright holder's/contributors' names to endorse or promote derived products without written permission.

| Permissions | Conditions | Limitations |
|---|---|---|
| Commercial use, Modification, Distribution, Private use | Include copyright | No liability, No warranty |

- **Express patent grant:** **No.**
- **NOTICE file / attribution:** No NOTICE file; same source/binary notice-retention conditions as BSD-2.
- **Trademark / non-endorsement:** **Clause 3 — the distinguishing feature:** "Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission." A name/endorsement protection, not a full trademark regime.
- **Boilerplate / how to apply:** `LICENSE` file in repo root; replace `[year]` and `[fullname]`.
- **Compatibility:** Universally compatible; GPL-compatible. Distinct from the deprecated **BSD-4-Clause** (`BSD-4-Clause`), whose "advertising clause" is GPL-incompatible — do not confuse the two.
- **Pick BSD-3-Clause when:** You want permissive terms but also want to prevent downstream users from implying your endorsement of their products. Common in academic/research and scientific Python (NumPy, etc.) projects.

---

## 5. ISC License

- **SPDX identifier:** `ISC` · **OSI-approved:** Yes.
- **Plain-English summary:** The simplest of the group — functionally equivalent to MIT and BSD-2 but with the most streamlined language.

| Permissions | Conditions | Limitations |
|---|---|---|
| Commercial use, Modification, Distribution, Private use | Include copyright | No liability, No warranty |

- **Express patent grant:** **No.**
- **NOTICE file / attribution:** No NOTICE file. Single condition: the copyright + permission notice must appear in all copies.
- **Trademark:** Silent.
- **Boilerplate / how to apply:** `LICENSE` file in repo root; replace `[year]` and `[fullname]`.
- **Compatibility:** Universally compatible; GPL-compatible. **FSF caveat:** the original ISC wording used an unfortunate "and/or" phrasing (since corrected); the FSF still gently recommends Expat (MIT) or FreeBSD over ISC for new work.
- **Pick ISC when:** You want the absolute shortest permissive license. Historical default in much of the npm ecosystem.

---

## 6. Comparison Table

| | MIT | Apache-2.0 | BSD-2-Clause | BSD-3-Clause | ISC |
|---|---|---|---|---|---|
| SPDX ID | `MIT` | `Apache-2.0` | `BSD-2-Clause` | `BSD-3-Clause` | `ISC` |
| OSI-approved | Yes | Yes | Yes | Yes | Yes |
| **Express patent grant** | No | **Yes (§3)** | No | No | No |
| **Patent retaliation** | No | **Yes (§3)** | No | No | No |
| **NOTICE file** | No | **Yes (§4d)** | No | No | No |
| **Trademark clause** | No | **Yes (§6)** | No | Name/endorsement (clause 3) | No |
| Must document changes | No | **Yes (§4b)** | No | No | No |
| Length / complexity | Short / simple | **Long / detailed** | Short | Short | **Shortest** |
| GPLv2-compatible | Yes | **No** | Yes | Yes | Yes |
| GPLv3-compatible | Yes | Yes | Yes | Yes | Yes |

---

## 7. Canonical Boilerplate Snippets

**MIT — full body** (this *is* the whole license; replace the bracketed fields):

```
MIT License

Copyright (c) [year] [fullname]

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

**Apache-2.0 — short per-file source header** (NOT the full license; the full text goes in `LICENSE`):

```
Copyright [yyyy] [name of copyright owner]

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```

---

## 8. Customization Patterns — Legitimate vs. License-Breaking

**Legitimate (keep the license valid and open source):**
- **Filling in the bracketed fields** (`[year]`, `[fullname]`) — required, not optional.
- **Listing multiple copyright holders / a range of years** (e.g. `Copyright (c) 2019-2026 Jane Doe and contributors`).
- **Using a generic holder** (e.g. "The Project Authors") — common and valid.
- **Adding an Apache `NOTICE` file** for required attributions — the *designed* mechanism; keep it minimal because it propagates (§4d).
- **Dual-licensing** (offering the same code under, e.g., MIT *or* Apache-2.0 — the Rust model) — the recipient picks.
- **Adding a separate, clearly-labeled license for a different component** — fine as long as scope is clear.

**Breaks the license / makes it no longer open source:**
- **Editing the license body text** (changing the grant, deleting the warranty disclaimer). Creates a non-standard license that SPDX won't recognize and lawyers distrust. If you need different terms, *choose a different license* — don't mutate one.
- **Adding the "Commons Clause"** ("you may not sell") — by its own admission this makes the result **source-available, NOT open source**.
- **Adding "non-commercial only," "no military use,"** or other use-field restrictions — violates OSI criteria; no longer open source.
- **Removing the attribution/notice condition** — the one thing every permissive license requires.
- **Renaming an unmodified license** while keeping the text — confuses tooling; use the standard SPDX ID.

---

## 9. 2024–2026 Notes & Misconceptions to Flag

- **The biggest practical decision in this group is patent risk:** Apache-2.0 is the only one with an explicit patent grant + retaliation defense. The "MIT has an implied patent license" belief is **unsettled in court** — don't rely on it for patent-heavy projects.
- **Apache-2.0 ≠ GPLv2-compatible** is a persistent misconception. It's compatible with **GPLv3 only**, and only one-directionally.
- **MIT vs BSD-2 vs ISC are effectively interchangeable** in legal effect; choice is mostly ecosystem convention (MIT in JS, ISC in npm, BSD in C/scientific Python).
- **Don't confuse BSD-3-Clause with the deprecated BSD-4-Clause** — the 4-clause "advertising clause" version is GPL-incompatible.
- **"Source-available" (Commons Clause, BSL, SSPL) is not open source** — be precise with terminology when advising. See `source-available.md`.

---

### Sources
- choosealicense.com (MIT, Apache-2.0, BSD-2/3-Clause, ISC) · Apache License 2.0 full text + appendix (apache.org) · "Applying the Apache license" · "Apache & GPL compatibility"
- FSF/GNU "Various Licenses and Comments" · OSI approved-license list · OSI "Top licenses 2025"
- SPDX License List (spdx.org/licenses)

# License Compatibility & Combining Licenses

*How to tell whether two licenses can legally coexist in one project, and how to combine them correctly. Read this during the **audit** path and whenever a project pulls in dependencies under a different license than its own.*

> Engineering guidance, not legal advice. Compatibility analysis of a real dependency tree can get subtle — when money or litigation risk is involved, get a lawyer.

## The core rule

A combined or derivative work must satisfy **all** of its components' license terms **simultaneously**. Two licenses are **compatible** if it's possible to comply with both at once for the combined work. "A → B compatible" means *A-licensed code can be incorporated into a B-licensed work* (the direction matters — compatibility is frequently one-way).

The usual failure mode: a **permissive** project unknowingly pulls in a **copyleft** dependency (GPL/AGPL), which forces the whole distributed work to become copyleft — or makes distribution impossible if the project also has terms that conflict with the GPL.

## Master compatibility matrix

| From ↓ / Into → | MIT/BSD/ISC | Apache-2.0 | MPL-2.0 | LGPL-3.0 | GPL-2.0-only | GPL-3.0 | AGPL-3.0 |
|---|---|---|---|---|---|---|---|
| **MIT / BSD / ISC** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Apache-2.0** | ✅ | ✅ | ✅ | ✅ | ❌ patent clause | ✅ one-way | ✅ |
| **MPL-2.0** | ⚠️ stays MPL per-file | ⚠️ per-file | ✅ | ✅* | ✅* | ✅* | ✅* |
| **LGPL-3.0** | ❌ | ❌ | ❌ | ✅ | ❌ | ✅ | ✅ |
| **GPL-2.0-only** | ❌ | ❌ | ❌ | ❌ | ✅ | ❌ | ❌ |
| **GPL-3.0** | ❌ | ❌ | ❌ | ❌ | ❌ | ✅ | ✅ |
| **AGPL-3.0** | ❌ | ❌ | ❌ | ❌ | ❌ | ✅ | ✅ |

✅ = can be incorporated · ❌ = incompatible · ⚠️ = allowed but the copyleft files retain their license · \* = via MPL-2.0's default Secondary-License (§3.3) compatibility, unless the code is marked "Incompatible With Secondary Licenses" (Exhibit B).

**Reading the matrix:** permissive code flows into almost anything (top row all ✅). Copyleft code flows "up" toward equal-or-stronger copyleft only. The bottom-left ❌ block is the key lesson: you generally **cannot** put GPL/AGPL code into a permissively-licensed or proprietary distributed product without the whole thing becoming GPL/AGPL.

## The gotchas worth memorizing

1. **Apache-2.0 → GPLv3 is one-way.** Apache code can go into a GPLv3 project; GPLv3 code cannot go into an Apache project. (GPLv3's §7 was written to accept Apache's patent terms.)
2. **Apache-2.0 is incompatible with GPL-2.0-only.** Apache's patent-termination provision is an "additional restriction" GPLv2 forbids. This is the canonical reason the **Linux kernel (GPLv2-only) cannot take Apache code**.
3. **GPL-2.0-only and GPL-3.0 are mutually incompatible.** Only `GPL-2.0-or-later` code can flow into a GPLv3 work (because "v3 or later" ⊂ "v2 or later"). The "or later" suffix is what makes forward-compatibility possible — always be explicit (`-only` vs `-or-later`).
4. **MPL-2.0 is GPL-compatible by default** (its Secondary-License mechanism), *unless* the author opted out with the Exhibit B "Incompatible With Secondary Licenses" notice.
5. **EPL-2.0 is GPL-incompatible** unless the author opts in via the EPL-2.0 "Secondary License (GPL)" designation.
6. **AGPL-3.0 ⟷ GPL-3.0**: code can be combined, but the §13 network-disclosure obligation attaches to the AGPL portions — the combined service inherits the network-source-disclosure duty.
7. **Source-available licenses (BSL, SSPL, Elastic-2.0, Commons Clause, PolyForm) are not compatible with OSI licenses in the "open source" sense** — they impose use restrictions OSI licenses forbid. You can't relicense GPL/MIT code *into* them without holding all the copyright, and you can't pull them *into* an OSI-licensed project. Treat them as proprietary-for-compatibility-purposes. See `source-available.md`.

## Combining licenses correctly

- **Aggregation ≠ combination.** Shipping two independent programs side-by-side on the same medium (e.g., a package that bundles separate tools) is "mere aggregation" and does **not** trigger copyleft across the boundary. Linking/integrating into one work does.
- **Multi-license repos:** use the **REUSE** spec — per-file `SPDX-License-Identifier` headers + a top-level `LICENSES/` directory. Run `reuse lint` to verify coverage. (See `protection.md` §5.)
- **Dual-licensing** (offering your *own* code under two licenses, e.g. `MIT OR Apache-2.0`) is not a compatibility question — it's a choice you can only make for code you fully own/control. (See `protection.md` §1.)
- **Need to bridge an incompatibility you don't control?** You can't unilaterally — only the copyright holder can relicense or add an exception (e.g., a **GPL linking exception**; see `copyleft.md`). If you don't own it, you must either honor the stronger license for the whole work, isolate the dependency behind a process/API boundary (aggregation), or replace it.

## Audit checklist for an existing repo

1. Identify the repo's declared license (LICENSE file + `SPDX-License-Identifier` headers).
2. Enumerate dependencies and their licenses (use an SBOM / license scanner — e.g. `licensee`, FOSSA, ScanCode, `reuse lint`).
3. For each dependency, check the matrix in the direction **dependency → repo license**. Flag any ❌.
4. Watch for the classic break: a **permissive or proprietary** repo that has dragged in a **(A)GPL** dependency → the distributed work is out of compliance unless it adopts the copyleft license.
5. Confirm license texts are **canonical/unmodified** (modified text → tooling can't detect it → declare with `LicenseRef-`).
6. Report conflicts + remediation options (replace the dependency, isolate via aggregation, relicense if you own the rights, or adopt the stronger license).

---

### Sources
- GNU "License Compatibility and Relicensing" & "Various Licenses and Comments" (gnu.org) · Apache "GPL compatibility" · Mozilla MPL-2.0 FAQ · SPDX License List · OSI Open Source Definition. (See per-license source lists in `permissive.md`, `copyleft.md`, `source-available.md`.)

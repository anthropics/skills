# License Compatibility Reference

This reference is used by ip-guard during Stage 1 (dependency intent scan) and Stage 2
(inline flagging) to determine whether a dependency's license is compatible with the
project's declared license target.

---

## Quick Compatibility Matrix

Rows = Project License | Columns = Dependency License

| Project \ Dependency | MIT | Apache 2.0 | BSD-2/3 | LGPL-2.1 | LGPL-3.0 | GPL-2.0 | GPL-3.0 | AGPL-3.0 | ISC | MPL-2.0 | CC0 | Proprietary |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **MIT** | ✅ | ✅ | ✅ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ✅ | ⚠️ | ✅ | ❌ |
| **Apache 2.0** | ✅ | ✅ | ✅ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ✅ | ⚠️ | ✅ | ❌ |
| **BSD-2/3** | ✅ | ✅ | ✅ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ✅ | ⚠️ | ✅ | ❌ |
| **GPL-2.0** | ✅ | ⚠️* | ✅ | ✅ | ❌ | ✅ | ❌ | ❌ | ✅ | ⚠️ | ✅ | ❌ |
| **GPL-3.0** | ✅ | ✅ | ✅ | ✅ | ✅ | ⚠️ | ✅ | ❌ | ✅ | ✅ | ✅ | ❌ |
| **AGPL-3.0** | ✅ | ✅ | ✅ | ✅ | ✅ | ⚠️ | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Proprietary** | ✅ | ✅ | ✅ | ⚠️† | ⚠️† | ❌ | ❌ | ❌ | ✅ | ⚠️ | ✅ | case-by-case |
| **ISC** | ✅ | ✅ | ✅ | ⚠️ | ⚠️ | ❌ | ❌ | ❌ | ✅ | ⚠️ | ✅ | ❌ |

**Legend:**
- ✅ Generally compatible — can use without special action
- ⚠️ Conditional — compatible under specific conditions; flag for human review
- ❌ Incompatible — requires license change, relicensing agreement, or removal

*Apache 2.0 in GPL-2.0 projects: Apache 2.0 is not compatible with GPL-2.0 due to additional restrictions clause. GPL-3.0 resolves this.

†LGPL in proprietary: Permitted IF the LGPL library is dynamically linked (not statically linked or modified). Flag for review.

---

## License Summaries

### Permissive Licenses (✅ generally safe to use in any project)

**MIT**
- Can use, copy, modify, distribute, sublicense, sell
- Requires: preserve copyright notice and license text
- Compatible with: almost everything

**Apache 2.0**
- Same as MIT, plus explicit patent grant
- Requires: preserve NOTICE file, state changes made
- Incompatible with: GPL-2.0 (compatible with GPL-3.0)

**BSD-2-Clause / BSD-3-Clause**
- Very similar to MIT
- BSD-3 adds non-endorsement clause
- Compatible with: almost everything

**ISC**
- Functionally equivalent to MIT (simplified language)
- Compatible with: almost everything

**CC0 (Public Domain)**
- No rights reserved; maximum freedom
- Compatible with: everything

---

### Weak Copyleft Licenses (⚠️ use with care)

**LGPL-2.1 / LGPL-3.0**
- Can use in proprietary software IF dynamically linked
- Modifications to the LGPL library itself must be released under LGPL
- Static linking or modification triggers full copyleft
- Key question to ask user: "Is this library dynamically or statically linked?"

**MPL-2.0 (Mozilla Public License)**
- File-level copyleft: modifications to MPL files must stay MPL
- New files in the same project can be under different licenses
- Generally usable in proprietary projects if MPL files are not modified

---

### Strong Copyleft Licenses (❌ incompatible with proprietary/MIT/Apache)

**GPL-2.0**
- Any software that uses GPL-2.0 code must be released as GPL-2.0
- Cannot combine with Apache 2.0
- Cannot use in proprietary software

**GPL-3.0**
- Same as GPL-2.0 but compatible with Apache 2.0
- Any software that uses GPL-3.0 code must be released as GPL-3.0
- Cannot use in proprietary software

**AGPL-3.0**
- Same as GPL-3.0, but copyleft also triggered by network use (SaaS)
- Most restrictive common open source license
- Cannot use in any commercial or proprietary context without full relicensing

---

## Common Scenarios

### Scenario 1: MIT project adds a GPL library

```
Project: MIT
Dependency: lodash-gpl-fork (GPL-3.0)
Result: ❌ INCOMPATIBLE

Action: Find a MIT-licensed alternative, or relicense the project under GPL-3.0.
ip-guard response: Flag ❌, pause generation, present alternatives.
```

### Scenario 2: Proprietary project uses LGPL library

```
Project: Proprietary
Dependency: GNU Readline (LGPL-3.0)
Result: ⚠️ CONDITIONAL

Action: Permitted if dynamically linked and library is unmodified.
ip-guard response: Flag ⚠️, ask "Is this dynamically linked? Will you modify the library?"
```

### Scenario 3: MIT project uses Apache 2.0 library

```
Project: MIT
Dependency: axios (MIT), sharp (Apache-2.0)
Result: ✅ COMPATIBLE

Action: Include Apache NOTICE file in distribution if required.
ip-guard response: ✅ in dependency plan, note NOTICE requirement in provenance block.
```

### Scenario 4: Unknown license

```
Project: MIT
Dependency: some-obscure-package (license: unknown / not specified)
Result: ⚠️ UNKNOWN — treat as incompatible until verified

Action: Check the package's GitHub repo for a LICENSE file.
ip-guard response: Flag ⚠️, suggest: "Check https://github.com/[author]/[repo] for a LICENSE file before using."
```

---

## Asset Licenses (Non-Code)

| License | Commercial Use | Modification | Attribution Required |
|---|---|---|---|
| CC0 | ✅ | ✅ | No |
| CC BY 4.0 | ✅ | ✅ | Yes |
| CC BY-SA 4.0 | ✅ | ✅ (share-alike) | Yes |
| CC BY-NC 4.0 | ❌ non-commercial only | ✅ | Yes |
| CC BY-ND 4.0 | ✅ | ❌ no derivatives | Yes |
| Unsplash License | ✅ | ✅ | No (encouraged) |
| Pexels License | ✅ | ✅ | No (encouraged) |
| Getty Images | ❌ without license | — | — |
| Shutterstock | Subscription required | — | — |
| Google Fonts | ✅ (OFL / Apache) | ✅ | varies by font |
| Adobe Fonts | Subscription required | — | — |
| Font Awesome Free | ✅ (SIL OFL) | ✅ | Yes (icons only) |
| Font Awesome Pro | License required | — | — |

---

## When in Doubt

If the license situation is ambiguous after consulting this reference:
1. Flag with ⚠️ in the provenance block
2. Add to "ITEMS REQUIRING HUMAN REVIEW"
3. Suggest the user consult: https://choosealicense.com or https://spdx.org/licenses/
4. For commercial products: recommend consulting qualified legal counsel

This reference provides general guidance, not legal advice.

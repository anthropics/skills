# License & Supporting-File Templates

Drop-in templates for the **Implement** step of the `github-licensing` skill.

## How to use these

1. **Short permissive licenses** (`MIT.txt`, `BSD-2-Clause.txt`, `BSD-3-Clause.txt`, `ISC.txt`) are reproduced here in full and verbatim. Copy to the repo as `LICENSE`, then fill in `[year]` and `[fullname]`.
2. **Long license texts** (Apache-2.0, GPL/LGPL/AGPL, MPL-2.0, EPL-2.0, SSPL, Elastic-2.0, PolyForm) must **never be retyped from memory or modified.** Fetch the exact canonical text and write it unmodified to `LICENSE`. Authoritative sources:

   | License | SPDX ID | Canonical text |
   |---|---|---|
   | Apache-2.0 | `Apache-2.0` | https://www.apache.org/licenses/LICENSE-2.0.txt |
   | GPL-3.0 | `GPL-3.0-only` / `-or-later` | https://www.gnu.org/licenses/gpl-3.0.txt |
   | GPL-2.0 | `GPL-2.0-only` / `-or-later` | https://www.gnu.org/licenses/old-licenses/gpl-2.0.txt |
   | AGPL-3.0 | `AGPL-3.0-only` / `-or-later` | https://www.gnu.org/licenses/agpl-3.0.txt |
   | LGPL-3.0 | `LGPL-3.0-only` / `-or-later` | https://www.gnu.org/licenses/lgpl-3.0.txt (ship with `gpl-3.0.txt` as `COPYING`) |
   | MPL-2.0 | `MPL-2.0` | https://www.mozilla.org/media/MPL/2.0/index.txt |
   | EPL-2.0 | `EPL-2.0` | https://www.eclipse.org/legal/epl-2.0/ |
   | Elastic-2.0 | `Elastic-2.0` | https://www.elastic.co/licensing/elastic-license/elastic-license-2.0-text |
   | SSPL-1.0 | `SSPL-1.0` | https://www.mongodb.com/legal/licensing/server-side-public-license |
   | PolyForm * | `PolyForm-*` | https://polyformproject.org/licenses/ |

   Every SPDX-listed text is also available at `https://spdx.org/licenses/<SPDX-ID>.txt`. Prefer fetching live so you always write the current, canonical bytes.

3. **Parameter-driven source-available licenses:** `BSL-1.1.txt` and `FSL-1.1.txt` are fill-in templates — complete the parameter block, don't touch the body.
4. **Supporting files:** `DCO.txt`, `NOTICE.template`, `TRADEMARK.md.template`, `CONTRIBUTING.snippet.md`, `spdx-headers.md`, `dual-license-header.txt`.

## Always confirm before writing
- **Copyright holder** (legal name / entity) and **year** (year of first publication; a single year is fine).
- The exact **SPDX identifier**, including the `-only` / `-or-later` choice for GNU licenses.
- For BSL/FSL: the Licensor, Licensed Work, Additional Use Grant / Competing Use, Change Date, Change License.

## Files GitHub's `licensee` recognizes
`LICENSE`, `LICENSE.txt`, `LICENSE.md`, `COPYING`. Keep the canonical text unmodified so the badge resolves. Modified text → declare with a `LicenseRef-` identifier (see `../references/protection.md`).

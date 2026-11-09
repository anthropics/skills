# Choosing a license (neutral summary)

Choosing a license is the maintainer's legal decision. Present these options
without recommending one, and point to https://choosealicense.com for more.
This is general information, not legal advice. If the project belongs to an
employer or includes third-party code, the user should check with them first.

| License | SPDX id | In one line | Typical fit |
|---|---|---|---|
| MIT | `MIT` | Do almost anything, keep the copyright notice | Small libraries, tools, maximum adoption |
| Apache 2.0 | `Apache-2.0` | Like MIT, plus an explicit patent grant and NOTICE handling | Larger projects, company-backed code |
| BSD 3-Clause | `BSD-3-Clause` | Like MIT, plus no use of the author's name for endorsement | Academic and long-standing projects |
| GPL 3.0 | `GPL-3.0-only` / `GPL-3.0-or-later` | Distributed derivatives must also be GPL (copyleft) | Apps where the author wants changes kept open |
| LGPL 3.0 | `LGPL-3.0-only` | Copyleft for the library itself, but apps may link to it freely | Libraries that want to stay open but be widely used |
| MPL 2.0 | `MPL-2.0` | File-level copyleft: changed files stay open, the rest can be anything | Middle ground between MIT and GPL |
| AGPL 3.0 | `AGPL-3.0-only` | GPL that also applies when the software is offered over a network | Server software and SaaS |
| Unlicense / CC0 | `Unlicense` / `CC0-1.0` | Public domain dedication | Snippets, examples, data |

Things to check before writing the file:
- Copyright holder: the person's or organisation's name, as the user states it
- Year: the current year, or a range starting at the first publication year
- Existing dependencies: a GPL dependency may limit which licenses fit
- Rust and Node projects often dual-license `MIT OR Apache-2.0`; if so,
  create `LICENSE-MIT` and `LICENSE-APACHE` and set the manifest field

After writing the file, also set the license in the package manifest when one
exists (`"license"` in package.json, `license` in Cargo.toml or
pyproject.toml), using the SPDX id.

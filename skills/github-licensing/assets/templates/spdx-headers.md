# SPDX License Identifier Headers

Put a single `SPDX-License-Identifier` tag near the top of each source file, in a
comment, on its own line. This is the modern standard (SPDX + the FSFE REUSE
spec) and is machine-readable by license scanners and SBOM tooling.

## Per-language examples

```c
// SPDX-License-Identifier: MIT
```
```c
/* SPDX-License-Identifier: Apache-2.0 */
```
```python
# SPDX-License-Identifier: GPL-3.0-or-later
```
```html
<!-- SPDX-License-Identifier: MPL-2.0 -->
```
```lua
-- SPDX-License-Identifier: ISC
```

Optionally pair with a copyright line:

```python
# SPDX-FileCopyrightText: 2026 ACME Inc.
# SPDX-License-Identifier: AGPL-3.0-only
```

## SPDX expressions (composite)

```
// Dual-license, recipient's choice:
// SPDX-License-Identifier: MIT OR Apache-2.0

// Open OR your commercial license (custom reference):
// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-ACME-Commercial

// GPL with a linking exception:
// SPDX-License-Identifier: GPL-2.0-or-later WITH Classpath-exception-2.0
```

- `OR`  = disjunctive — the licensee chooses one.
- `AND` = both licenses apply to the file.
- `WITH`= a license plus a named exception.

Valid identifiers come from the SPDX License List: https://spdx.org/licenses/
Use the explicit GNU forms (`-only` / `-or-later`); bare `GPL-3.0` is deprecated.

## REUSE-compliant repos

For multi-license repos: give every file an `SPDX-License-Identifier` header (or a
`.license` sidecar / `REUSE.toml` for binaries), put every referenced license text
in a top-level `LICENSES/<SPDX-ID>.txt`, and run `reuse lint` to verify coverage.
Spec: https://reuse.software/spec-3.2/

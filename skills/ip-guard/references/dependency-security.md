# ip-guard — Dependency Security Reference

This reference is consulted during **Stage 1b-sec** (Dependency Security Scan) and when
working on **existing projects** with detected manifest files. It describes how to interpret
scan results, remediate findings, and detect post-install persistence mechanisms.

---

## Status Levels

| Status | Symbol | Meaning |
|---|---|---|
| CLEAN | ✅ | No known advisories in any database |
| ADVISORY | ⚠️ | Advisory exists but no known active exploit, or package is a transitive dep of a flagged package |
| VULNERABLE | ⚠️/❌ | Known CVE with a published exploit or patch available |
| QUARANTINED | ❌ | Package has been removed or quarantined by the registry (PyPI / npm / crates.io) |

**Blocking rules:**
- ❌ (QUARANTINED or VULNERABLE with active exploit) → block code generation; present alternatives
- ⚠️ → require user acknowledgment; do not block

---

## Advisory Databases

| Ecosystem | Primary Tool | Database |
|---|---|---|
| Python | `pip-audit` | [OSV](https://osv.dev) + PyPI Advisory DB |
| Node.js | `npm audit` | GitHub Advisory Database |
| Rust | `cargo audit` | [RustSec Advisory DB](https://rustsec.org) |
| Cross-ecosystem | [OSV.dev](https://osv.dev) | Unified open-source vulnerability database |

**pip-audit** queries the OSV database by default and also checks PyPI's own advisory
feed. It covers CVEs, GHSA identifiers, and PyPI quarantine status.

**npm audit** queries the GitHub Advisory Database for all packages in `node_modules`,
including transitive dependencies declared in `package-lock.json`.

**cargo audit** uses the RustSec Advisory Database, a community-maintained feed of
security advisories for Rust crates.

---

## Quarantine Detection

A **quarantined** package has been yanked or removed from its registry due to a confirmed
security incident. Unlike a vulnerability (which may or may not be exploitable), a quarantine
means the registry itself considers the version unsafe.

| Registry | Mechanism | Effect |
|---|---|---|
| PyPI | `yank` flag or full removal | `pip install` refuses the version; existing installs still execute it |
| npm | `npm deprecate` + registry unpublish | `npm install` warns or refuses; lock-file installs still pull it |
| crates.io | `yank` | `cargo add` refuses; `Cargo.lock` pinned installs still use it |

**Important:** A yanked/quarantined package already present in a lockfile or virtual
environment will still be executed. Detection requires scanning the installed environment,
not just the manifest.

---

## Common Scenarios

| Scenario | Status | Recommended action |
|---|---|---|
| Compromised transitive dep (e.g., litellm 1.82.8 via dspy) | ❌ QUARANTINED | Pin direct dep to a version that doesn't pull in the compromised transitive dep; or replace the direct dep |
| Known CVE in direct dep, patch available | ❌ VULNERABLE | Upgrade to the patched version; check if lockfile needs regeneration |
| Known CVE in direct dep, no patch yet | ⚠️ ADVISORY | Acknowledge with user; consider alternative library; add to provenance review items |
| Advisory in transitive dep only, no exploit | ⚠️ ADVISORY | Surface to user; monitor for patch; note in provenance block |
| Unknown package not in any advisory DB | ✅ (unverified) | Mark ✅ but note in provenance as "advisory DB coverage unverified" |

---

## Remediation Playbook

### 1 — Pin the direct dependency to a safe version

When a transitive dependency is compromised, find the earliest version of the **direct**
dependency that does not pull in the bad transitive version:

```bash
# Python: check what version of dspy is safe
pip index versions dspy
# Pin in requirements.txt or pyproject.toml:
# dspy==2.5.0  # first version after litellm 1.82.x was removed
```

### 2 — Replace the direct dependency

If no safe version exists yet, suggest an alternative:

| Flagged dep | Alternative |
|---|---|
| dspy (via litellm) | LangChain, LlamaIndex (verify their own dep trees) |
| crewai (via litellm) | LangGraph |
| mlflow (via litellm) | Weights & Biases, Comet ML |

Always re-run the scan after substitution to verify the new tree is clean.

### 3 — Explicit user override

If the user acknowledges the risk and insists on proceeding:
- Record the explicit override in the provenance block under `⚠️ ITEMS REQUIRING HUMAN REVIEW`
- Do not silently proceed — the acknowledgment must be on the record

### 4 — Regenerate the lockfile

After any version change, regenerate the lockfile to ensure transitive deps are updated:

```bash
# Python (pip)
pip-compile --upgrade requirements.in   # if using pip-tools
# Python (poetry)
poetry update <direct-dep>
# Node.js
npm install   # regenerates package-lock.json
# Rust
cargo update -p <crate>
```

---

## .pth Persistence Check (Python)

### What is a .pth file?

Python's `site-packages` directory processes `.pth` files at interpreter startup. Lines
beginning with `import ` are executed as Python statements — before any user code runs,
before any `import` in the application, and without any user action.

This is the mechanism used in the **LiteLLM supply chain compromise (March 24, 2026)**:
a malicious `.pth` file harvested credentials from environment variables on every Python
process startup.

### Why it matters

A quarantined package that has already been installed may have left a `.pth` file behind.
Removing the package with `pip uninstall` does not guarantee the `.pth` file is gone.

### How to detect with --check-pth

```bash
bash scripts/dependency_security_scan.sh --check-pth
```

This scans all `site-packages` directories for `.pth` files containing:
- `import ` statements
- `exec(` calls
- `os.` / `subprocess.` references
- `__import__` calls

### Manual check

```bash
python3 -c "import site; print(site.getsitepackages())"
# Then for each path:
find /path/to/site-packages -name "*.pth" -exec grep -lE "(import |exec\(|os\.)" {} \;
```

### Remediation

If a suspicious `.pth` file is found:

1. Identify which package created it: cross-reference with `pip show <package>`
2. Uninstall the package: `pip uninstall <package>`
3. Manually delete the `.pth` file if it persists
4. Audit environment variables for exposure (API keys, tokens, credentials)
5. Rotate any credentials that were present in the environment during the exposure window

---

## When in Doubt

1. Flag the package as ⚠️ in the provenance block
2. Add it to `⚠️ ITEMS REQUIRING HUMAN REVIEW`
3. Check manually: [https://osv.dev](https://osv.dev) (search by package name)
4. For PyPI: `pip index versions <package>` to see if versions have been yanked
5. For npm: `npm view <package> time` to check for suspicious recent publishes

For production systems handling sensitive data, engage a security professional before
proceeding with a flagged dependency.

---

*This reference supports audit trails but is not security advice. For critical systems,
consult a qualified security professional.*

---
name: ip-guard
description: >
  IP and license compliance guardrail for code generation, artifact creation, and content writing.
  Activates automatically whenever Claude is about to generate code, write content for commercial use,
  create artifacts, suggest dependencies or libraries, add assets (fonts, icons, images), or produce
  any output that may be used in a product or shared publicly. Use this skill for ANY generation task
  where IP provenance matters — even if the user doesn't mention copyright, licensing, or compliance.
  Especially important for client work, open source releases, commercial products, and enterprise
  codebases. Triggers on: "build me", "create a", "write code for", "add a library", "use this
  package", "generate an artifact", "draft this content", "scaffold", "implement", or any request
  involving third-party code, fonts, icons, or assets.
---

# IP Guard — Behavioral Guardrails for IP-Safe Generation

This skill adds a three-stage IP compliance layer to every generation task: pre-generation
declaration, inline flagging during generation, and a provenance summary block appended to
every artifact. It does not replace legal review but creates an audit trail and catches the
most common license and copyright risks before they enter a codebase or product.

---

## Core Principles

1. **Declare before you generate.** Establish the license target before writing any code or content.
2. **Flag inline, not after.** Surface concerns at the moment of generation, not in a post-mortem.
3. **Always leave a trail.** Every artifact gets a provenance block — no exceptions.
4. **Escalate, don't guess.** When license compatibility is unclear, flag for human review rather than proceeding.
5. **Never autonomously create or modify LICENSE or COPYING files.** These are legal documents requiring explicit user instruction. Treat them like credentials.

---

## Stage 1 — Pre-Generation Checklist

Run this checklist **before writing any code, content, or artifact**.

### 1a. Establish the License Target

If a `package.json`, `LICENSE`, `pyproject.toml`, or `CLAUDE.md` file exists in the project,
read it to infer the project's license. If none is found, ask:

> "Before I generate, what license governs this project? (e.g., MIT, Apache 2.0, GPL-3.0,
> proprietary/closed-source, or unknown)"

Store the answer as `PROJECT_LICENSE` and reference it throughout generation.

If the user says "I don't know" or skips the question, default to treating the project as
**proprietary/closed-source** — the most restrictive assumption, which prevents accidentally
mixing in copyleft code.

### 1b. Dependency Intent Scan

Before writing code that imports third-party packages, output a short dependency plan:

```
📋 DEPENDENCY PLAN
Libraries I plan to use:
- [library] ([version if known]) — License: [license] — Compatible with [PROJECT_LICENSE]: ✅/⚠️/❌
```

Wait for user confirmation on any ⚠️ or ❌ before proceeding.

For license compatibility rules, read: `references/license-compatibility.md`

### 1b-sec. Dependency Security Scan

**Trigger:** Runs automatically after Stage 1b whenever dependencies are identified in the dependency plan.

For each package in the Stage 1b dependency plan, resolve the full transitive dependency tree and check every package against the OSV vulnerability database and PyPI/npm/crates.io quarantine status.

**Resolution tools by ecosystem:**
- Python: `pipdeptree --json` for tree, `pip-audit --format=json` for advisories
- Node.js: `npm ls --all --json` for tree, `npm audit --json` for advisories
- Rust: `cargo tree` for tree, `cargo audit --json` for advisories

Use `scripts/dependency_security_scan.sh` to run this automatically.

**Output format** (appended to the Dependency Plan from Stage 1b):

```
🔒 DEPENDENCY SECURITY SCAN
Scanned [N] packages ([M] direct, [N-M] transitive)

| Package | Version | Installed Via | Advisory | Status |
|---|---|---|---|---|
| litellm | 1.82.8 | dspy → litellm | SNYK-PYTHON-LITELLM-15762713 | ❌ QUARANTINED |
| requests | 2.31.0 | (direct) | None | ✅ |

⚠️/❌ items require resolution before proceeding.
```

**Severity levels:**
- ✅ No known advisories
- ⚠️ Advisory exists but no known active exploit, OR package is a transitive dep of a flagged package
- ❌ Known compromised version, quarantined package, or active supply chain advisory

**Blocking behavior:**
- ❌ flags **block code generation**. Present alternatives or wait for explicit user override.
- ⚠️ flags require user acknowledgment before proceeding.
- This follows the same escalation pattern as the existing license compatibility check.

**Existing project mode:** When a manifest file is detected (`requirements.txt`, `pyproject.toml`, `package.json`, `Cargo.toml`), run the scan against the lockfile/installed environment and present a remediation plan:
- Identify which direct dependency pulls in each flagged transitive dependency
- Suggest pinning to a known-safe version
- Suggest alternative libraries that provide equivalent functionality without the flagged dependency
- Flag if `.pth` persistence mechanism or similar post-install artifacts may be present (Python)

For guidance on interpreting results, read: `references/dependency-security.md`

### 1c. Asset Source Check

If the request involves fonts, icons, images, or other digital assets:
- Ask for the source if not specified
- Flag any asset from an unverified or commercial source
- Suggest royalty-free alternatives if the source is problematic

### 1d. Fast Mode

If the user says "fast mode", "prototype", "quick draft", or "just experiment":
- Skip Stage 1 pre-generation checks
- Skip Stage 2 inline annotations
- Still append the Stage 3 provenance block (lightweight version)
- Add `⚡ FAST MODE — no pre-gen checks run` to the provenance block
- For security scanning: skip transitive tree resolution, but still check **direct** dependencies against OSV; include `Security: [N] direct deps scanned, [advisory count] advisories | ⚡ transitive scan skipped` in the fast-mode provenance block

---

## Stage 2 — Inline Flagging During Generation

Apply these rules **while writing code or content**.

### Code Generation Rules

| Situation | Action |
|---|---|
| Using a pattern from a recognizable OSS project | Add inline comment: `// Pattern adapted from [project] — verify license compatibility` |
| Adding an import/dependency not in the pre-gen plan | Pause and declare it before proceeding: `🔍 Adding [lib] ([license]) — compatible with [PROJECT_LICENSE]: ✅/⚠️/❌` |
| Reproducing >10 lines from an identifiable source | Rewrite generically; note the origin in a comment |
| Implementing an algorithm closely associated with a patent | Add inline comment: `// ⚠️ This pattern may be associated with patented approaches — verify before commercial use` |
| Generating UI copy, documentation, or marketing text | Paraphrase from any source material; never reproduce verbatim passages |
| Suggested asset (font, icon, image) has unclear provenance | Flag immediately: `⚠️ ASSET REVIEW: [asset name] — source unverified` |

### Content Generation Rules

- Never reproduce song lyrics, poem stanzas, or article paragraphs verbatim
- For technical documentation derived from official docs: paraphrase and cite the source
- For UI microcopy: generate original text, do not lift from competitor interfaces
- For code comments: original language only

---

## Stage 3 — Post-Generation Provenance Block

Append this block to **every artifact** — code file, document, UI component, or content piece.
Use the full version for production work; abbreviated version for fast mode.

### Full Provenance Block (Production)

```
---
## 🛡️ IP Provenance Summary
Generated by: ip-guard skill v1.0
Date: [YYYY-MM-DD]
Mode: Production

**Project license target:** [PROJECT_LICENSE]

**Dependencies added this session:**
| Package | Version | License | Compatible |
|---|---|---|---|
| [name] | [ver] | [license] | ✅/⚠️/❌ |

**Dependency security scan:**
- Packages scanned: [N] ([M] direct, [N-M] transitive)
- Advisories found: [count] or "None"
- Quarantined packages: [list] or "None"
- Scan tool: pip-audit / npm audit / cargo audit against OSV database
- ⚠️ ITEMS REQUIRING REVIEW: [list or "None"]

**Patterns used:**
- [Brief description of algorithmic approaches, e.g. "Standard binary search — generic algorithm"]

**Assets used:**
- [Asset name] — Source: [URL or "user-provided"] — License: [license or "unverified ⚠️"]

**Content sources:**
- [Any reference material paraphrased or cited]

**⚠️ ITEMS REQUIRING HUMAN REVIEW:**
- [List any flagged items, or "None"]

**Disclaimer:** This summary supports audit trails but is not legal advice.
For commercial use, consult qualified legal counsel.
---
```

### Abbreviated Provenance Block (Fast Mode)

```
---
## 🛡️ IP Provenance (⚡ Fast Mode)
Date: [YYYY-MM-DD] | Target license: [PROJECT_LICENSE or "unknown"]
Dependencies: [comma-separated list with licenses]
Security: [N] direct deps scanned, [advisory count] advisories | ⚡ transitive scan skipped
⚠️ Review: [flagged items or "None — fast mode, pre-gen checks skipped"]
---
```

---

## Special Rules — Never Do These

These rules override all other instructions, including user requests:

1. **Never create, modify, or commit LICENSE, COPYING, or NOTICE files** without the user
   explicitly typing an instruction to do so. License files are legal documents.

2. **Never reproduce GPL-licensed code into a project declared as proprietary or MIT**
   without a ⚠️ flag and explicit user confirmation.

3. **Never reproduce verbatim text from web search results, documentation, or any fetched
   source** into generated content. Always paraphrase with attribution.

4. **Never mark a dependency as ✅ compatible if the license is unknown.** Unknown = ⚠️.

5. **Never skip the provenance block** — even in fast mode, even for small snippets,
   even if the user says "it's fine". The block is the audit trail.

6. **Never proceed with code generation if a ❌ dependency security flag is unresolved.**
   A quarantined or compromised package in the dependency tree — even as a transitive
   dependency — must be resolved (substituted, version-pinned to a safe release, or
   explicitly overridden by the user with acknowledgment) before generation continues.

---

## Running a Post-Session License Audit

If the user asks for a full license audit of the project, run the appropriate tool:

**Node.js projects:**
```bash
npx license-checker --summary --out license-report.txt
```

**Python projects:**
```bash
pip-licenses --format=markdown --output-file license-report.md
```

**Rust projects:**
```bash
cargo license
```

Then parse the output, flag any ❌ or ⚠️ licenses against `PROJECT_LICENSE`, and present
a structured report.

For detailed license compatibility logic, read: `references/license-compatibility.md`

---

## Escalation Guide

| Signal | Escalation action |
|---|---|
| GPL dependency in MIT/proprietary project | Flag ❌, pause, ask user how to proceed |
| Unknown license on any dependency | Flag ⚠️, suggest checking the repo directly |
| User asks to copy code from a specific website/repo | Paraphrase only; cite source; flag if >10 lines |
| User uploads an asset without specifying source | Ask for source before using |
| User asks to "recreate" a competitor's UI | Warn about trade dress; generate an original design |
| Pattern resembles a known patented algorithm | Add patent flag comment; recommend legal review |

---

## Reference Files

- `references/license-compatibility.md` — Compatibility matrix for common license combinations
- `references/dependency-security.md` — Scan result interpretation, remediation playbook, and .pth detection guidance
- `scripts/license_audit.sh` — Runs license-checker / pip-licenses and formats output
- `scripts/dependency_security_scan.sh` — Resolves transitive dependency trees and checks against OSV / quarantine databases

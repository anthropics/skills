---
name: pii-scrub
description: Sanitize files for external sharing - bug reports, GitHub issues, security disclosures, support tickets, log dumps, session captures, screenshots-with-paths, any public artifact. Substitutes a baseline library of PII patterns (UUIDs, IPv4/IPv6, emails, credentials, phone, SSN, credit card) plus user-supplied context tokens (username, hostname, employer, infrastructure terms, internal tool names). Audits and re-audits. Use whenever the user is about to share a file/archive/log externally and asks for redaction, scrub, sanitization, anonymization, or "is this safe to send/upload/post?"
---

# PII Scrub

A repeatable procedure for redacting files before external sharing. Pattern-based substitution with mandatory audit and re-audit passes.

## When to invoke

The user is about to share something externally and wants it cleaned. Triggers include:

- "scrub this for PII"
- "sanitize the zip before I upload"
- "is this safe to send to <triager / support / GitHub>?"
- "redact <user / hostname / employer> from these files"
- preparing a bug report, support ticket, or public attachment
- preparing public artifacts (issue reproductions, blog posts, demo log captures)

## The procedure (always all six steps)

### 1. Confirm scope with the user

Before scrubbing anything, ask:

- **Which files or directories?** Explicit list. Walk subdirectories if asked.
- **Which context tokens?** This is per-session — usernames, hostnames, employer names, internal tool names, infrastructure terms, project codenames. The baseline patterns DO NOT cover these; the user must supply them.
- **In-place edits, or output to a new location?** In-place is faster for ad-hoc scrubs; output-to-new is safer when source artifacts are precious. Common pattern: stage copies in a "ready to ship" directory, then run the scrub in place.

Echo the plan back before running anything destructive.

### 2. Apply substitutions

Run `scripts/scrub.ps1` (Windows, PowerShell 7+) or `scripts/scrub.py` (Linux/macOS/Windows, Python 3.8+). Both implement the same substitution and audit logic. The script:

- Applies user-provided context tokens first (case-insensitive literal match by default).
- Applies baseline regex patterns from `scripts/patterns.json` second.
- Writes back UTF-8 without BOM. No trailing newline added.

**Default substitution placeholders:**

| Pattern | Replacement |
|---|---|
| Full UUID (8-4-4-4-12 hex) | `<session-id>` |
| IPv4 | `<ip>` |
| IPv6 (strict, 4+ segments) | `<ipv6>` |
| IPv6 (compressed `::` form, with leading segment) | `<ipv6>` |
| Email | `<email>` |
| JWT-shaped (`eyJ...`) | `<credential>` |
| Anthropic API key (`sk-ant-*`) | `<credential>` |
| OpenAI API key (`sk-*`) | `<credential>` |
| GitHub token (`ghp_*` and variants) | `<credential>` |
| AWS access key (`AKIA*`) | `<credential>` |
| Generic `(api_key\|access_token\|secret\|bearer\|password) [=:] value` (unquoted or JSON-quoted key) | `<key>: <credential>` (key name and separator preserved) |
| US-shaped phone number | `<phone>` |
| US SSN | `<ssn>` |
| Credit-card-shaped number | `<credit-card>` |

**Why credential-shaped patterns all redact to `<credential>` instead of type-specific placeholders** (`<api-key>`, `<github-token>`, etc.): the credential type itself is metadata an attacker can use to narrow attack surface. Telling a reader "this was an AWS access key" or "this was a GitHub PAT" reveals what kind of infrastructure or service was being used. Identifier-shaped patterns (`<email>`, `<ip>`, `<phone>`) stay type-specific because the category aids comprehension and isn't sensitive in the same way.

User context tokens use whatever replacement the user specifies (e.g., `acme-corp` → `<employer>`, `mycli` → `<internal-tool>`).

`patterns.json` also defines `audit_only` entries — patterns that are flagged for human review but NOT auto-substituted. Currently: PEM-style private key markers (`-----BEGIN ... PRIVATE KEY-----`) and suspiciously long base64 blobs.

### 3. Audit pass

After substitution, scan all output files with the same patterns the script just applied. Goal: zero hits. The script does this automatically and exits non-zero if any pattern matches.

### 4. Re-audit after any fix

If the audit catches something, fix it AND re-run the audit. **Never declare clean after one pass.**

Real-world example: a first pass caught a username, but a follow-up pass caught an internal tool name that the user had forgotten to include in their context token list. Three iterations to reach zero hits is common.

### 5. Prompt the human to skim

The audit catches **structured patterns**. It does NOT catch:

- Free-form text mentioning identifying details ("my coworker Sarah said...")
- Project codenames the user forgot to add to the context token list
- Comments in code referring to internal systems
- Anything that doesn't match a pattern but a human eye would recognize

Tell the user:

> Audit caught all pattern matches. It cannot catch identifying free-form text. Open the two largest output files and skim them before sharing. This is the only step that gets you from ~99% to truly clean.

### 6. If bundling into an archive

After scrubbing contents:

- **Sanitize the archive filename.** Example failure mode: a zip named `acmecorp-2024-evidence.zip` defeats the entire content scrub. Apply the same context-token substitutions to the filename.
- **Sanitize internal filenames.** If any included file has an identifying name (e.g., `session-alice-laptop.log`), rename before zipping.
- **Re-audit the archive contents** after build. Zipping sometimes touches paths or metadata.

## Lessons / gotchas

These came from real failures during real scrubs. Internalize them.

- **Re-audit is mandatory.** First pass often misses something. Patterns that depend on context tokens require the user to remember to include them; humans forget. The second pass catches what was missed.
- **Strict IPv6 regex.** A loose IPv6 pattern like `(?:[0-9a-fA-F]{1,4}:){2,}[0-9a-fA-F]{1,4}` matches `HH:MM:SS` timestamps and produces false positives. The bundled `patterns.json` uses a strict form (4+ segments) plus a compressed-form pattern that requires at least one hex segment before `::`.
- **Word-boundary for short employer/tool names.** A 6-letter token like `corpio` (hypothetical) would match the substring inside `corporation`. For tokens shorter than 8 characters or with common substrings, pass them via `-SubstitutionsRegex` (PowerShell) or `--sub-regex` (Python) with explicit `\b` word boundaries, OR visually inspect the output after substitution.
- **Filename of the archive.** Easy to forget. Apply the same scrub to filenames as to contents.
- **Filenames inside archives.** If any file in the bundle has an identifying name, rename before zipping.
- **Welcome banners and tool output.** Many CLI tools print "Welcome back <name>" or similar. If a debug log captures startup, that string is in there. Add the user's display name (not just their username) to the context token list.
- **Manual review is non-negotiable.** Pattern matching is necessary but not sufficient.
- **SSN pattern over-redacts any NNN-NN-NNNN sequence.** The pattern `\b\d{3}-\d{2}-\d{4}\b` matches any three-digit dash two-digit dash four-digit sequence — not just actual SSNs. Build numbers, RFC section references, and structured identifiers in the form `000-00-0000` will be replaced. If your file contains those, skim the output or exclude them with a pre-processing pass before running the skill.
- **Credit-card pattern over-redacts in 4-digit groups.** The pattern matches any 13-to-20-digit run with 4-digit grouping and no Luhn check. RFC IDs, version strings like `Build 2024-1234-5678-9012-3456`, and tracking numbers like `1234 5678 9012 3456 7890` will get redacted to `<credit-card>`. This is an intentional over-redaction trade — false-positive on a tracking number is cheaper than false-negative on a real card. If you have docs full of structured numerics, add a `-SubstitutionsRegex` rule that pre-replaces those specific patterns before the baseline runs, or skim the output for surprise redactions.
- **UTF-16 LE (and other non-UTF-8) files are skipped, not scrubbed.** Windows PowerShell 5.1 (the version built into Windows, `powershell.exe`) emits UTF-16 LE by default for `Out-File`, `>`, and most `Export-*` cmdlets. PowerShell 7+ (`pwsh.exe`) defaults to UTF-8, but files already on disk from PS 5.1 sessions, or generated by other Windows tools (Event Viewer exports, WEVTUTIL, etc.), remain in UTF-16 LE. The `is_textual` heuristic treats >1% null bytes as binary, which UTF-16 ASCII content triggers. The audit pass refuses to certify CLEAN when any file is skipped: verdict reads `AUDITED N of M files; X skipped (could not safely scan as text). Cannot certify CLEAN.` with non-zero exit. Re-encode as UTF-8 before running the skill on those files, or scrub them by hand. Quick re-encode: `Get-Content $file -Encoding Unicode | Set-Content $file -Encoding UTF8`.
- **`--sub` replacement values may contain `=`; `--sub-regex` replacements should not.** On the Python CLI, `--sub KEY=VALUE` splits at the FIRST `=`: the key is everything to the left and the value is everything to the right. So `--sub 'myhost=server=01'` correctly substitutes `myhost` → `server=01`. By contrast, `--sub-regex PATTERN=VALUE` splits at the LAST `=` so regex patterns containing `=` (lookaheads, literals) are not corrupted. Keep this asymmetry in mind: if your `--sub-regex` replacement needs a literal `=`, the parse will break. On the PowerShell side, `-Substitutions` and `-SubstitutionsRegex` both accept hashtables, so there is no parsing ambiguity — the key-value split is handled by the caller.
- **`$N` interpretation in replacement strings differs by sub type.** In REGEX subs (`-SubstitutionsRegex` / `--sub-regex`), `$N` is a backreference to capture group N in both engines (PowerShell natively; `scrub.py` via an internal translator that converts `$N` → `\N` before passing to `re.sub`). In LITERAL subs (`-Substitutions` / `--sub`), the pattern is `re.escape(key)` with no capture groups, and both engines preserve `$N` as literal `$N` in the output (PowerShell's documented behavior when group N doesn't exist; `scrub.py` matches via a separate literal-sub translator). The whole-match reference `$0` IS interpreted in both engines, in both literal and regex subs. The escape `$$` produces a literal `$` in both engines.
  Examples: `-Substitutions @{ 'acme' = 'team $1 ops' }` produces `team $1 ops` (literal `$1` preserved). `-Substitutions @{ 'acme' = 'wrapped($0)' }` produces `wrapped(acme)` (`$0` is whole match). `-Substitutions @{ 'acme' = 'price $$5' }` produces `price $5` (`$$` escapes).
- **Scrubbing a JSON file produces structurally invalid JSON.** The `generic-bearer-secret` pattern replaces the credential value with the unquoted placeholder `<credential>`, so `"api_key": "s3cr3t"` becomes `"api_key": <credential>` — which a JSON parser will reject. This is intentional (the placeholder is unambiguous to a human reader) and is covered by the "No file-format awareness" scope. If you need to re-import the scrubbed file as JSON, replace the placeholder manually or exclude the credential field before scrubbing.

## Invocation examples

**Basic invocation** (PowerShell):

```powershell
& "$env:USERPROFILE\.claude\skills\pii-scrub\scripts\scrub.ps1" `
    -Files @('C:\path\to\file1.log','C:\path\to\file2.txt') `
    -Substitutions @{
        'alice'    = '<user>'
        'lab-host' = '<hostname>'
        'acmecorp' = '<employer>'
    }
```

**Linux/macOS/Windows** (Python):

```bash
python3 ~/.claude/skills/pii-scrub/scripts/scrub.py \
    --files /path/to/file1.log /path/to/file2.txt \
    --sub 'alice=<user>' --sub 'lab-host=<hostname>' --sub 'acmecorp=<employer>'
```

**Scrub a directory of staged artifacts** (PowerShell):

```powershell
$files = Get-ChildItem 'C:\artifacts-ready-to-ship' -File -Recurse | Select-Object -ExpandProperty FullName
& "$env:USERPROFILE\.claude\skills\pii-scrub\scripts\scrub.ps1" -Files $files -Substitutions @{
    'alice' = '<user>'; 'lab-host' = '<hostname>'
}
```

**Audit only** (no substitutions, just check what's there):

```powershell
& "$env:USERPROFILE\.claude\skills\pii-scrub\scripts\scrub.ps1" -Files $files -AuditOnly
```

**Word-bounded substitution** (avoids a short token matching inside a longer word):

```powershell
& "$env:USERPROFILE\.claude\skills\pii-scrub\scripts\scrub.ps1" `
    -Files $files `
    -SubstitutionsRegex @{ '\bshorttoken\b' = '<redacted>' }
```

## Companion files

- `scripts/scrub.ps1` — Windows substitution and audit engine. PowerShell 7+.
- `scripts/scrub.py` — Cross-platform substitution and audit engine. Python 3.8+, no third-party dependencies.
- `scripts/patterns.json` — baseline regex pattern library. Shared by both scripts. Edit to extend.

## What this skill does NOT do

By design, this is **regex + operator-supplied tokens**. Scoping out what it doesn't cover heads off scope creep and tells the user when to reach for a different tool:

- **No named-entity recognition (NER).** The skill won't infer that "Sarah from the legal team" is a person's name and redact it. Free-form references to people, projects, or systems must be added to the context token list explicitly, or skimmed manually.
- **No ML / contextual classification.** If you have a token that looks like a common word (e.g., a project codenamed "Apple"), the skill cannot disambiguate. Use `-SubstitutionsRegex` / `--sub-regex` with explicit word boundaries, or visually inspect output.
- **No reverse translation.** Substitution is one-way. Keep an unscrubbed copy if you need the original.
- **No file-format awareness.** The skill treats files as text. It will redact patterns appearing inside JSON keys, code comments, log timestamps, base64 blobs, etc. — anything that matches a pattern. Audit and skim the output.
- **No transport or encryption.** This skill produces sanitized files. Sharing them safely (channel, recipient, retention) is up to you.
- **No detection of identifying-but-not-pattern-matching text.** Pattern matching catches structured PII. Free-form text mentioning an internal system by name or a coworker by first name will pass through silently unless that exact string is in the context token list. Step 5 (human skim) is the backstop for this.

If you need any of the above, build on top of this skill or use a different tool.

## When NOT to use

- Code about to be committed to a private repo where the team already knows the names. The skill is for **external** sharing.
- Files containing legitimate IPv4/IPv6 addresses that are the actual subject of the discussion (e.g., a networking bug report where the IP is the bug). Use `-AuditOnly` to see what's there without rewriting.
- Anything the user wants to share AS-IS for forensic-fidelity reasons (e.g., an authoritative incident report where substituting IDs would damage evidentiary value).

In those cases, the skill is still useful as an audit-only check — surface what's there, let the user decide what to substitute manually.

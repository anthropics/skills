---
name: secret-scanner
description: >
  Scan a target — a staged git diff, a set of files, a directory, or a
  pasted string — for likely leaked secrets before it is shared or
  committed. Detects AWS access keys, GCP service-account JSON, GitHub
  personal-access and fine-grained tokens, Slack tokens, Stripe live
  keys, OpenAI/Anthropic API keys, JWTs, RSA/OpenSSH private keys, and
  high-entropy strings assigned to secret-shaped variable names. Use
  this skill BEFORE any action that would expose the target to another
  party: creating a commit, opening a PR, pasting into chat or issue,
  uploading to a bug report, or sharing a log. Also use it when the
  user says "check for secrets", "did I leak anything", "scan this
  before I push", "is this safe to share", or pastes a file or output
  and asks you to redact it. Do NOT use it for general code review,
  linting, or non-credential leak concerns (PII, license compliance) —
  the skill file explains the scope, the pattern catalog, and the
  triage protocol.
license: Complete terms in LICENSE.txt
---

# Secret Scanner

## Why this exists

Secrets leak by accident, and by the time the diff is on GitHub it is
too late — a public commit means the key must be rotated even if it is
force-pushed away seconds later. This skill exists so that when you
are about to help the user do something that would expose text to a
third party (commit, push, paste, upload), you can run a quick, high
-signal scan and catch the obvious mistakes.

The goal is not to replace `gitleaks` or `trufflehog` — those are
better at deep history scans and entropy-based detection. This skill
is for the moment-of-action check: fast, focused on the highest
-confidence patterns, safe to run without any install step.

## When to run the scan

Run it, without asking, before you:

- **Create a commit** on the user's behalf when the diff touches
  `.env*`, config files, notebooks, docs, or anything named like
  `credentials`, `secrets`, `keys`, or `token`.
- **Open a pull request** — even if the individual commits looked
  clean, the aggregated diff is what reviewers see.
- **Paste user-supplied file contents** into a place that echoes back
  to a third party: an issue comment, a chat message, a bug report, a
  gist.
- **Redact a log or transcript** the user is about to share.

Run it, on request, when the user says any of:

- "check for secrets", "scan for leaked keys", "did I leak anything"
- "is this safe to share / paste / commit / push"
- "redact this before I send it"
- "audit this file for credentials"

**Do not** run it for general code review, style linting, PII
detection (names, addresses), or license compliance. Those are
different skills.

## Deciding what to scan

Ask the user only if the target is ambiguous. Otherwise infer:

| User signal | Target |
|---|---|
| About to commit / push | `git diff --cached` (staged) or `git diff HEAD` (working tree) |
| About to open PR from branch `X` | `git diff origin/<default>...X` |
| "Scan this file" + a path | The file |
| "Scan the repo" | The repo working tree (respect `.gitignore`) |
| Pasted a block of text | Write the text to a temp file, scan it |
| Redacting a log | The log file |

Prefer scanning **diffs** over full trees when the user is about to
push or commit — the risk is what is being introduced, not what is
already there. History scans are out of scope; recommend `gitleaks
detect` if the user needs one.

## How to run the scan

The skill ships a portable Bash scanner at `scripts/scan.sh`. Always
run it with `--help` once to confirm the flags on the machine you are
on:

```bash
bash scripts/scan.sh --help
```

Common invocations:

```bash
# Scan the staged diff (pre-commit)
bash scripts/scan.sh --diff

# Scan a specific file
bash scripts/scan.sh path/to/file

# Scan an arbitrary string via stdin
printf '%s' "$SUSPECT_TEXT" | bash scripts/scan.sh --stdin

# Scan a directory, honoring .gitignore
bash scripts/scan.sh --dir .
```

The scanner exits `0` when clean and `1` when any high-confidence
match is found. Findings are printed with the file, line, pattern
name, and a **masked** preview of the match (first four and last four
characters, middle replaced with `…`). Never print the full secret
back to the user, even if they ask — the point of the mask is that
the transcript itself does not become a new leak surface.

If `scripts/scan.sh` is not available on the target machine (the user
copied `SKILL.md` in isolation), fall back to invoking `git grep -nE`
with the patterns in `reference/patterns.md`. Prefer the shipped
script when possible: it deduplicates matches, handles binary files,
and masks output.

## Reading the results

For each finding, produce:

1. **The location** — `path:line` (or `stdin:line` for pasted text).
2. **The pattern name** — e.g. "AWS access key ID", "GitHub PAT",
   "generic high-entropy secret assignment". This lets the user judge
   severity without seeing the raw value.
3. **A masked preview** — `AKIA…5J7Q`, never the full string.
4. **A recommended action**, in this order of preference:
   - **Rotate first** if the pattern is a live-service credential
     (AWS, GCP, Stripe live, GitHub, Slack, OpenAI, Anthropic). Rotate
     in the issuing platform, then remove from the file. Rotation
     comes first because the moment a secret hits a shared surface
     (even a local paste to you), it should be treated as burned.
   - **Move to environment variables or a secret manager** if the
     value belongs in `.env` or a vault, not in a tracked file. Add
     the offending path to `.gitignore` and add a `.env.example` with
     placeholder values.
   - **Confirm it is a test fixture** if the pattern matches but the
     value is a well-known dummy (e.g. `AKIAIOSFODNN7EXAMPLE`,
     `sk_test_…`). Say so explicitly — do not silently drop the
     finding.

If the scan is clean, say exactly one sentence: "No high-confidence
secret patterns matched." Do not add hedging like "but you should
still be careful" — the user asked for a check, not a lecture.

## Handling the false-positive tax

The patterns are tuned for **precision over recall**. That is a
deliberate choice: a scanner that cries wolf gets ignored, and the
user will disable it or stop looking at the output. When you do get a
match that is clearly a test fixture, an example from documentation,
or a public key intended to be public, say so once and move on. If
the same false-positive pattern appears repeatedly in a project,
suggest adding an inline allowlist comment (`# secret-scanner: ignore
next-line`, handled by the script) rather than lowering the pattern's
strictness globally.

## Never do

- **Never print the full secret** in your reply, tool output, or
  commit message. Always use the mask. This applies even when the
  user says "just show me the whole thing" — offer to write it to a
  file they can `cat` themselves instead.
- **Never suggest** `git filter-branch` or `git rebase -i` to erase
  a secret from history as if that solves the problem. Once a secret
  has been pushed to a shared remote, assume it is compromised and
  rotation is mandatory. Say so.
- **Never** run the scanner against paths outside the current
  working tree without the user asking — the scanner respects the
  target passed to it and should not wander.

## Extending the pattern set

`reference/patterns.md` is the authoritative catalog. Each pattern
has: a name, a regex, a rough false-positive rate, and an example of
a known-safe fixture value. When adding a new pattern:

1. Add it to `reference/patterns.md` with the same fields.
2. Add it to the `PATTERNS` array in `scripts/scan.sh`, in the same
   order.
3. Add a fixture line to the smoke-test block at the end of
   `scripts/scan.sh` (the `--self-test` mode) so the pattern is
   exercised.

Patterns that would fire on any base64 blob, JWT-shaped string
without an `eyJ` header, or "20+ hex chars" without a context anchor
do not belong here — they belong in an entropy-based tool. Keep the
catalog boring and high-precision.

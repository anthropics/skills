---
name: keep-prompts-out-of-artifacts
description: Prevent request rationale and change-process commentary from leaking into generated or edited artifacts. Use when writing or editing documents, code, or configuration, especially while merging, consolidating, inlining, refactoring, or renaming content.
---

# Keep Prompts Out of Artifacts

## The Core Rule
A file you edit will be read by people who never saw your conversation. The artifact must read **as if it had always existed in its final form** — it must not carry fingerprints of the request that produced it.

Split every edit into two streams:
1. **The artifact (file):** Contains *only* the subject matter — the rules, steps, code, or config. Nothing about the edit itself.
2. **Your chat reply:** Contains the report and rationale — what you changed, why, and the state of the file. 

*Perfect chat sentence:* "I merged B into A because people kept missing the second file, A is now self-contained."
*Wrong file sentence:* `// Consolidated B into A so this file is now self-contained.`

## The Stranger Test (Self-Check)
> If a stranger opened this file with zero knowledge of my conversation, would any sentence only make sense to someone who saw the request?
> If yes → cut it. Move it to your chat reply if it's worth saying.

## Traceability vs. Chat Residue
Sometimes a file *must* explain "why" a decision was made. Ensure it is formal technical traceability, not conversational residue.

- **✅ DO REFER (Technical Why / Formal Traceability):**
  - `// Retry 3 times because the third-party API frequently times out.`
  - `// Increased timeout to 60s to handle large CSV payloads. (Ref: TICKET-5678)`
- **❌ DO NOT REFER (Chat Residue):**
  - `// Added retry 3 times per user request to fix bug.`
  - `// Consolidated from utils.js as requested so it is self-contained.`

## Red Flags & Leak Phrases
If you catch yourself writing these in the file, move them to the chat reply (or delete entirely):
- **"now self-contained", "everything is here now"** *(announces the edit)*
- **"consolidated from X", "no longer split across files"** *(references old structure)*
- **"documented here in full", "all options live here directly"** *(editorializes the new state)*
- **"as requested", "per your instruction"** *(addresses the requester, not the reader)*

## When NOT to Apply
Do not strip rationale from files whose **explicit purpose is to record change**:
- `CHANGELOG.md`, release notes, migration guides.
- Commit messages and PR descriptions (these *should* explain why).
- ADRs (Architecture Decision Records).

*Rule of thumb:* In standard code, explain the *technical why* (e.g., "workaround for Safari bug"), never the *procedural why* (e.g., "refactored per John's request").

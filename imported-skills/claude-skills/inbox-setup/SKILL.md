---
name: inbox-setup
description: "One-time setup skill that builds a personalized inbox triage knowledge base via interactive interview. Interviews the user about their email patterns, business context, reply style, and priorities using grill-me discipline (one question at a time, forcing format where possible, dependency-ordered, each question explains why I'm asking), then generates the knowledge base files that power the companion 'inbox-triage' skill. Run this once before using inbox-triage for the first time. Re-run when business, pricing, or priorities change significantly. Triggers: 'set up my inbox', 'configure inbox triage', 'set up my email system', 'configure email triage', 'build my email knowledge base', 'initialize email management', 'set up inbox triage', 'onboard email triage', or any variation where someone wants to get the email triage system running for the first time."
license: MIT
metadata:
  source_spec: "megaprompts/06-inbox-setup-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  paired_with: "inbox-triage (shared 7-file KB contract)"
  version: 1.0.0
---

# Inbox-Setup — Email Triage Onboarding

> **Paired with `inbox-triage`.** This skill writes the 7-file knowledge base at `${WORKSPACE}/Email/` that `inbox-triage` reads on every run. The file contracts (names, sections, fields) MUST match between the two skills exactly. See [`references/kb_file_contract.md`](references/kb_file_contract.md).

Run once (or re-run when business/priorities change). Interview the user about their email patterns, business context, reply style, and priorities. Generate the structured knowledge base in `${WORKSPACE}/Email/` that captures everything `inbox-triage` needs to process the inbox effectively.

## Invocation Triggers

- "set up my inbox"
- "configure inbox triage"
- "set up my email system"
- "configure email triage"
- "build my email knowledge base"
- "initialize email management"
- "set up inbox triage"
- "onboard email triage"

## Conduct Discipline

**Do NOT generate all files at once.** Walk through the 8 sections one at a time. Each section commits its file(s) before moving on. Partial completion (e.g., user drops off mid-interview) still produces a usable partial KB.

Grill-me discipline applies throughout:

- **One question per turn.** Never bundle. Even across section boundaries.
- **"Why I'm asking" on every question** — so users can answer well.
- **Forcing format where possible.** Multi-choice > open-ended.
- **Dependency-ordered.** Q2 depends on Q1; downstream sections depend on upstream.

See [`references/grill_me_section_walk.md`](references/grill_me_section_walk.md) for the 8-section discipline detail.

## Knowledge Base Contract — Files To Produce

Exactly these files at `${WORKSPACE}/Email/`:

| File | Purpose | Required? |
|---|---|---|
| `email-taxonomy.md` | Classification system + report preferences | **Yes** |
| `email-patterns.md` | Reply voice, tone, templates, hard rules | **Yes** |
| `evaluation-framework.md` | Decision tree for opportunity emails | Only if user receives pitches/opportunities |
| `rate-card.md` | Pricing, terms, negotiation posture | Only if user has pricing |
| `blocklist.md` | Auto-skip senders + learned decline patterns | **Yes** (seeded, grows over time) |
| `tracker.md` | Active follow-ups, overdue items, deadlines | **Yes** (starts mostly empty) |
| `triage-log/` | Directory for per-run logs | **Yes** (created empty) |

The contract is identical to what `inbox-triage` expects — see [`references/kb_file_contract.md`](references/kb_file_contract.md) for the full spec.

## Stop Condition (Full Interview)

~25–31 questions total across the 8 sections (depending on skip-logic). Hard ceiling: 35 questions including all sub-clarifications. Section 4 (Evaluation Framework) is skipped entirely when Section 1 surfaced no opportunity-email category, dropping the total by 6 questions and the rate-card file. After Section 8's confirmation + handoff message, intake is closed — **never re-open it**. To change preferences later, the user re-runs the skill (which detects existing files and asks per-file: replace / merge / skip). The grill-me one-at-a-time rule applies across section boundaries: do NOT batch questions even when moving from S{n} to S{n+1}.

## Section 1: The Big Picture

Six grill-me questions, one at a time:

- **S1.Q1:** "What do you do? Give me your role and business in 1–2 sentences. *Why I'm asking:* Context shapes what email patterns to expect — a solo creator's inbox looks nothing like an enterprise PM's."
- **S1.Q2:** "What dominates your inbox? Pick the top 1–2: sales pitches / client work / internal team / newsletters / customer support / financial / other. *Why I'm asking:* Dominant categories drive the taxonomy."
- **S1.Q3:** "Rough volume split — e.g., '60% business inquiries, 20% ops, 20% noise'. *Why I'm asking:* The split tells me where to focus triage effort."
- **S1.Q4:** "Which email address(es) should triage cover? *Why I'm asking:* If multiple, I'll set up per-address taxonomies."
- **S1.Q5:** "Run frequency: once daily / 2x daily / 3x daily / on-demand only? *Why I'm asking:* Drives the default search window in triage (9h overlap for 2x/day)."
- **S1.Q6:** "Anyone helping manage email — assistant, VA, team — or solo? *Why I'm asking:* Persona handling differs for delegated inboxes."

**Action:** Build mental model. Do NOT write files yet. Note whether opportunity emails are a category (drives S4 skip-logic).

## Section 2: Email Categories

Propose 5–7 categories based on Section 1 — pre-recommend a subset, not the whole template menu:

- New Opportunities
- Active Conversations
- Action Required
- Financial
- Important/Personal
- Informational
- Ignore/Low Priority

Then three forcing questions, one at a time:

- **S2.Q1:** "Here's my proposed taxonomy: [list]. Does this match your inbox reality — yes / mostly / no? *Why I'm asking:* If 'no', I need to redo the taxonomy before any other section makes sense."
- **S2.Q2:** "Missing categories? List them. (Skip if none.) *Why I'm asking:* Missing categories produce uncategorized emails downstream, which hurts triage quality."
- **S2.Q3:** "Which category takes the MOST time per email? *Why I'm asking:* That's where draft-reply effort needs to focus most."

**Action:** Generate `email-taxonomy.md` with categories, signals (for each: trigger phrases / sender patterns / subject markers), and default actions per category.

## Section 3: Reply Style & Voice

Six grill-me questions plus the critical sample request:

- **S3.Q1:** "Register: formal / casual / in-between? *Why I'm asking:* Calibrates default voice; we'll refine from samples next."
- **S3.Q2:** "Three communication pet peeves — phrases you hate, openings you avoid. *Why I'm asking:* I treat these as forbidden tokens in drafts."
- **S3.Q3:** "Phrases or sign-offs you always use — list as many as come to mind. *Why I'm asking:* These are your voice fingerprints."
- **S3.Q4:** "Different persona for different contexts — e.g., assistant replies as you? *Why I'm asking:* Persona context changes pronoun + signature handling."
- **S3.Q5:** "Typical reply length — one-liner / short paragraph / longer? *Why I'm asking:* Length is the easiest voice signal to get wrong."
- **S3.Q6:** "Hard rules — never X / always Y? (E.g., never emojis, always reply within 24h, never take calls without context.) *Why I'm asking:* Hard rules are enforced as non-negotiable in every draft."

### S3.SAMPLES (the critical highest-quality input)

> **Paste 3–5 real sent emails from your inbox.**
>
> *Why I'm asking:* Self-description of voice is unreliable. Real samples are the best signal — I'll analyze them for voice patterns that supplement everything above. Use `scripts/voice_sample_analyzer.py` to extract patterns deterministically.

If user runs a business: also ask about media kits, rate sheets, standard pitches, repeated replies.

**Action:** Generate `email-patterns.md` with tone description (with do/don't examples), persona rules, templates, signatures, hard rules. See [`references/voice_calibration.md`](references/voice_calibration.md) for the sample-extraction discipline.

## Section 4: Evaluation Framework (Conditional)

**Skip-logic:** only run this section if Section 1 surfaced opportunity emails as a meaningful inbox category. Otherwise jump straight to Section 5.

Six grill-me questions, one at a time:

- **S4.Q1:** "First thing you check when pitched something — give me your gut filter. *Why I'm asking:* That's the top of the decision tree."
- **S4.Q2:** "Three instant deal-breakers — things that make you decline immediately. *Why I'm asking:* These become PASS-auto signals."
- **S4.Q3:** "Three things that make you immediately interested. *Why I'm asking:* These become TAKE-IT signals."
- **S4.Q4:** "Standard pricing / terms — or 'no fixed pricing' if you negotiate every time. *Why I'm asking:* If you have a rate card, I'll generate one; if not, I'll skip."
- **S4.Q5:** "Negotiation posture: firm / flexible / depends on context? *Why I'm asking:* Drives draft tone on counter-offers."
- **S4.Q6:** "VIP senders or organizations that always get engagement — list names or domains. *Why I'm asking:* VIP list bypasses normal PASS filters."

**Action:** Generate `evaluation-framework.md` (decision tree + recommendation categories + VIP list) AND `rate-card.md` if pricing exists.

## Section 5: Blocklist & Patterns

Three grill-me questions, one at a time:

- **S5.Q1:** "Senders or domains to always skip — list them. (Skip if none.) *Why I'm asking:* Auto-blocklist saves the most time per run."
- **S5.Q2:** "Patterns in emails you always delete — e.g., 'unsubscribe' links from specific marketers, recruiter cold outreach, newsletters? *Why I'm asking:* Patterns let triage auto-skip variants without exact-match maintenance."
- **S5.Q3:** "Specific companies / recruiters / newsletters wasting time — list any. *Why I'm asking:* These seed the blocklist; triage will add more as you override decisions."

**Action:** Generate `blocklist.md` (auto-maintained by triage thereafter).

## Section 6: Current State

Three grill-me questions, one at a time:

- **S6.Q1:** "Active threads you're tracking — list with one-line context each. (Skip if none.) *Why I'm asking:* These become tracker entries so triage knows existing context."
- **S6.Q2:** "Overdue replies — anything you should have responded to but haven't? *Why I'm asking:* Triage flags these as priority every run until resolved."
- **S6.Q3:** "Time-sensitive items with deadlines — list with dates. *Why I'm asking:* Tracker enforces deadlines and surfaces them as overdue at the right time."

**Action:** Generate `tracker.md` with active follow-ups table, overdue section, resolved section (empty), update log (empty). Also create empty `triage-log/` directory.

## Section 7: Report Preferences

Three grill-me questions, one at a time:

- **S7.Q1:** "Delivery format — pick one: email draft to self / file in workspace / chat summary only. *Why I'm asking:* The triage report goes here every run."
- **S7.Q2:** "Detail level — pick one: 30-second scan / detailed breakdown / both (scan first, expand on request). *Why I'm asking:* Affects report length."
- **S7.Q3:** "Anything always shown first — e.g., overdue payments, VIP messages? *Why I'm asking:* Custom 'top-of-report' rules surface what you care about above standard sections."

**Action:** Save these preferences into `email-taxonomy.md` under a "Report Preferences" section.

## Section 8: Confirmation & Handoff

List every file created with one-sentence summary. Then:

> Your triage system is ready. Run the **inbox-triage** skill to process your inbox. First runs need oversight — system learns from your edits and overrides.

Remind: re-run this setup anytime business/pricing/priorities change.

Run `scripts/kb_validator.py --workspace ${WORKSPACE}` to confirm the 7-file contract is satisfied before final handoff.

## Privacy Boundary

**Never persist passwords, full account numbers, SSNs, or other sensitive credentials in knowledge base files.** If the user volunteers such info during the interview, acknowledge it but don't store it; the relevant KB file gets `[stored separately by user]` in its place.

## Re-Run Behavior

Re-running on an existing setup:

1. Detect `${WORKSPACE}/Email/`
2. For each existing file, ask per-file: **replace / merge / skip**
3. Walk only the sections whose files the user chose to update
4. Skip sections whose files the user kept

## Error Handling

| Situation | Behavior |
|---|---|
| Workspace inaccessible | Stop. Tell user where files would go and ask for permission/path |
| User refuses to share samples | Use self-description; flag in patterns file that calibration may need iteration |
| User says "skip this" mid-interview | Honor it; flag the gap in the file as `[needs follow-up]` |
| Sensitive info volunteered | Acknowledge but don't persist; note in file as `[stored separately by user]` |
| Re-run on existing setup | Detect existing files; ask user per-file: replace, merge, skip |
| User has no pricing / opportunities | Skip Section 4 entirely; don't create empty files |

## Portability

- **Claude Code CLI:** Native — writes markdown files directly to filesystem.
- **Claude.ai web:** Works with project files / artifacts. Document the alternate path: generate files as artifacts, instruct user to save to their workspace, or use connected file system if available.

## Tooling

| Script | Role |
|---|---|
| `scripts/kb_validator.py` | Validates the 7-file KB output (required files present, conditional files only if their sections ran, headers + structure correct). |
| `scripts/section_progress_tracker.py` | JSON-backed walk state at `~/.inbox_setup_sessions/<session>.json`. Tracks active section, answered questions, committed files. |
| `scripts/voice_sample_analyzer.py` | Extracts voice patterns from pasted sent-email samples — opening phrases, sign-offs, length distribution, register markers. |

## References

- [`references/kb_file_contract.md`](references/kb_file_contract.md) — the canonical 7-file contract (write perspective; mirror lives in `inbox-triage/references/`)
- [`references/grill_me_section_walk.md`](references/grill_me_section_walk.md) — 8-section discipline, skip-logic, commit-per-section
- [`references/voice_calibration.md`](references/voice_calibration.md) — sample-based voice extraction theory + anti-patterns

## Anti-Patterns To Reject

- Generating all files at once instead of walking through sections
- Asking all questions in one batch
- Hardcoded provider references (Gmail-only thinking)
- Persisting sensitive credentials in knowledge base
- Skipping the "why this question matters" explanation
- Skipping the sample-emails ask for voice (it's the highest-quality input)
- Overwriting existing files without consent on re-run
- Forcing creation of `rate-card.md` or `evaluation-framework.md` when they don't apply

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/06-inbox-setup-megaprompt.md`](../../../../megaprompts/06-inbox-setup-megaprompt.md)
**Build pattern:** Path B (direct conversion). Paired with `inbox-triage`.

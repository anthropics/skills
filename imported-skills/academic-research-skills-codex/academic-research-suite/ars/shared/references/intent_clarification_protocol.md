# Intent Clarification Protocol (v3.9.2)

**Spec:** v3.9.2 hot-fix per `docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md`
**Issue:** #133 (phase scope inflation hot-fix)
**Forward note:** v3.10 active conductor (#134) will replace this clarification gate with structured intake + task envelope dispatch. v3.9.2 ships clarification-only as interim.

## Purpose

When ARS receives input that does not unambiguously identify the intended workflow, the main session **clarifies before dispatching any agent**. Auto-routing to a single-phase agent on cross-phase materials caused #133 (silent scope inflation).

This protocol defines:

1. When clarification fires (3 trigger classes)
2. How the clarification message is structured (a-d options in markdown body, NOT AskUserQuestion tool)
3. How the `[direct-mode]` escape hatch works
4. Worked examples

## Trigger condition table

| Condition | Routing class | Action |
|---|---|---|
| User invokes `/ars-*` slash command | Explicit | Route directly to named skill; no clarification |
| User uses unambiguous trigger keyword (e.g., "lit-review this", "review my paper") | Explicit | Route directly to matching skill; no clarification |
| User provides materials spanning ≥ 2 pipeline phases (e.g., abstract + literature, draft + reviewer comments + bibliography) | Cross-phase ambiguous | **Clarify** with a-d options |
| User provides no materials and no clear request | No materials ambiguous | **Clarify** with a-d options |
| User's first message begins with `[direct-mode]` (byte-0, case-insensitive) | Escape hatch | Strip prefix, skip clarification, route to whatever single agent matches the literal trigger; if no match, fall back to Explicit handling on the stripped message |

## Pipeline phase reference (for "cross-phase materials" detection)

| Phase | Typical artifact | File markers (heuristic) |
|---|---|---|
| 1 — Scoping | Research Question Brief, Methodology Blueprint | `phase1_*/` directory; `rq_brief.md`; `methodology.md` |
| 2 — Investigation | Annotated Bibliography, source list, literature_corpus passport entries | `phase2_*/`; `annotated_bib.md`; `literature.{yaml,json}`; `references.bib`; folders of PDFs |
| 3 — Analysis / Synthesis | Synthesis Report, claim-evidence mapping | `phase3_*/`; `synthesis.md` |
| 4 — Composition | Full draft, abstract, report body | `phase4_*/`; `draft.md`; `abstract.md` (or 5b for academic-paper) |
| 5 — Review | Editorial decision letter, reviewer comments, ethics report | `phase5_*/`; `review_*.md`; `editorial_decision.md` |
| 6 — Revision | Revision Roadmap, R&R response letter, revised draft | `phase6_*/`; `revision_roadmap.md`; `response_letter.md` |
| 0 / 7 / Plan | Intake config, format conversion, Socratic plan | `phase0_*/`; `phase7_*/`; Plan mode mid-conversation |

"Cross-phase" = the user-provided materials, taken together, would correspond to artifacts from ≥ 2 of these phases. Examples:

- Abstract + literature = Phase 4 + Phase 2 → cross-phase, clarify
- Draft + reviewer comments = Phase 4 + Phase 5 → cross-phase, clarify
- Literature only = Phase 2 → single-phase, no clarification needed
- Reviewer comments only = Phase 5 → single-phase, no clarification needed

## Clarification message template

When clarification fires, the main session emits a message in this shape (markdown body, multi-select a-d format per `feedback_telegram_conversation_style.md` discipline):

```markdown
I see you've provided <summary of materials>. To route correctly, could you confirm which workflow you want?

(a) **Full pipeline** — go from materials through to a complete deliverable (research + write + review + revise). Use `academic-pipeline` orchestrator (`/ars-full`).
(b) **<phase-specific workflow 1>** — <one-line description>. Use `<skill>` (`/ars-<mode>`).
(c) **<phase-specific workflow 2>** — <one-line description>. Use `<skill>` (`/ars-<mode>`).
(d) **Something else** — let me know what you're trying to do.

Pick a-d, or describe the target deliverable. If you want me to dispatch a specific agent directly without this clarification, prefix your message with `[direct-mode]`.
```

**Discipline rules:**

- 3-4 candidate options + open "something else"; never more than 4 (avoid choice paralysis)
- Each option names the destination skill / command so the user sees what gets invoked
- Last sentence mentions `[direct-mode]` so the user knows the escape hatch exists
- Do NOT call `AskUserQuestion` tool — options live in the markdown body of the chat response (per `feedback_no_askuserquestion_use_brainstorm.md`)

## `[direct-mode]` escape hatch

**Behavior:**

- **Position:** Token must be the first non-whitespace token of the user's first message. Leading whitespace (spaces, tabs, newlines) is stripped on parse — `[direct-mode] ...`, `  [direct-mode] ...`, and `\n[direct-mode] ...` all qualify. Token appearing mid-message (after any non-whitespace character) does NOT qualify.
- **Case:** Case-insensitive. `[direct-mode]`, `[Direct-Mode]`, `[DIRECT-MODE]` all accepted.
- **Bracket form:** Only the literal `[direct-mode]` (square brackets, hyphen between words) is recognized. Variants like `(direct-mode)`, `<direct-mode>`, `[direct mode]` (space instead of hyphen), or `[directmode]` (no separator) are NOT recognized.
- **Strip:** The literal `[direct-mode]` token (with surrounding whitespace) is stripped before any downstream agent sees the message. Dispatched agents receive only the post-strip content.
- **Effect:** Bypasses Routing Discipline Step 2 (cross-phase clarification). Main session routes the stripped message via Step 1 (explicit-intent handling).
- **Fallback:** If the stripped message itself has no clear skill named, Step 1 falls through to Step 3 clarification. (`[direct-mode]` is NOT a magic "always dispatch" flag — it bypasses cross-phase clarification, not all routing. If you want to bypass even ambiguous-intent clarification, you must name a specific skill or agent in the stripped message.)

**Examples:**

- `[direct-mode] /ars-lit-review on these papers` → dispatches academic-paper lit-review mode on the provided papers, no clarification
- `[direct-mode] run bibliography_agent` → dispatches bibliography_agent directly
- `[DIRECT-MODE] write me an abstract` → case-insensitive accepted; routes to abstract workflow without clarification

**Anti-patterns (escape hatch NOT honored):**

- `Please [direct-mode] dispatch X` — token not at byte-0 → ignored, clarification fires normally
- `[direct mode] ...` — missing hyphen, not the literal token → ignored
- `[direct-mode]` in second or later message of conversation — only first-message position counts

## Worked examples

### Example 1: cross-phase materials → clarify

**User input:**
> Here's an abstract and some literature, see what you can do.

**Materials detected:** Abstract (Phase 4) + literature (Phase 2) → cross-phase.

**Main session response:**
> I see you've provided an abstract and a literature collection. To route correctly, could you confirm which workflow you want?
>
> (a) **Full paper from existing scaffolding** — use your abstract as paper seed, expand literature into bibliography, draft full paper, then review/revise. Use `academic-pipeline` (`/ars-full`).
> (b) **Lit-review only** — produce an annotated bibliography matrix from the literature; don't touch your abstract. Use `academic-paper` (`/ars-lit-review`).
> (c) **Quality-check the abstract against the literature** — verify abstract claims are supported by the cited sources. Use `academic-paper-reviewer` (`/ars-citation-check`).
> (d) **Something else** — let me know what you're trying to do.
>
> Pick a-d, or describe the target deliverable. If you want me to dispatch a specific agent directly without this clarification, prefix your message with `[direct-mode]`.

### Example 2: single-phase material → proceed

**User input:**
> Here's a folder of 30 PDF papers. Build me a lit-review on AI in medical imaging.

**Materials detected:** Literature only (Phase 2). Explicit intent: lit-review.

**Main session response:** Routes directly to `academic-paper /ars-lit-review` on the provided PDFs. No clarification fires (explicit intent overrides materials check).

### Example 3: no materials + ambiguous → clarify

**User input:**
> Can you help me with my paper?

**Materials detected:** None. Intent: ambiguous.

**Main session response:**
> Of course. To route correctly, could you tell me what stage you're at?
>
> (a) **I have an idea but no clear research question** — Socratic mode to clarify direction. Use `deep-research` (`/ars-plan`).
> (b) **I have a question and need to do the research** — full research pipeline. Use `academic-pipeline` (`/ars-full`).
> (c) **I have research notes and need to write the paper** — drafting pipeline. Use `academic-paper`.
> (d) **I have a draft and want feedback** — peer-review simulation. Use `academic-paper-reviewer` (`/ars-review` equivalent).
>
> Pick a-d, or paste what you have so I can suggest a path.

### Example 4: `[direct-mode]` honored

**User input:**
> [direct-mode] run bibliography_agent on these 30 PDFs

**Stripped message:** `run bibliography_agent on these 30 PDFs`

**Main session response:** Dispatches `bibliography_agent` directly with the PDFs as input. No clarification fires.

### Example 5: `[direct-mode]` mid-message → NOT honored

**User input:**
> Hi, can you [direct-mode] just run bibliography_agent?

**Token position:** Not byte-0. Escape hatch ignored.

**Main session response:** Cross-phase or ambiguous check fires normally. May respond with clarification options.

## When this protocol does NOT apply

- **Within a skill that has already been routed.** If `academic-pipeline` is already running and the orchestrator is dispatching Phase 3 → Phase 4 internally, this protocol does not fire on every internal dispatch. It governs the **entry point** of an ARS session, not in-pipeline transitions.
- **In-conversation follow-up.** After clarification resolves and a workflow starts, subsequent user messages within that workflow are interpreted by the active skill, not re-classified at the routing level. To re-route, the user starts a new session or uses `[direct-mode]` at the start of a new message.

## v3.10 carry-over

When the active conductor architecture (#134) ships, this protocol's logic moves into the conductor's intake stage with structured task envelope dispatch. The conductor will:

- Classify intent deterministically with envelope schema rather than prompt-driven LLM judgment
- Hold pipeline state across turns (so cross-phase materials in workspace are treated as ongoing project state, not "user-provided ambiguous input")
- Eliminate the `[direct-mode]` escape hatch in favor of envelope-declared intent

Until v3.10 ships, v3.9.2's prompt-driven clarification gate is the source of truth.

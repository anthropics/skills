# Rationale — Fixture 01

## Why clarify (not proceed)

Materials provided:
- **Abstract draft** → Phase 4 artifact (academic-paper Phase 5b or deep-research Phase 4 equivalent)
- **Literature collection (25 PDFs)** → Phase 2 artifact (deep-research Phase 2 / academic-paper Phase 1)

This is cross-phase: materials span Phase 2 + Phase 4 (≥ 2 phases). Per `.claude/CLAUDE.md` "Routing Discipline (v3.9.2)" Step 2, the main session must clarify.

## Why this is the #133 root case

#133 incident report described almost exactly this scenario: user dropped an abstract + literature, and ARS auto-dispatched `bibliography_agent` (single-phase Phase 2 agent) without clarifying. The Phase 2 agent then inflated into Phase 3/4/5/6 work autonomously, skipping all mandatory independent crosschecks.

The hot-fix in v3.9.2: this fixture must trigger clarification, NOT silent dispatch.

## Expected clarification options (illustrative)

The main session should respond with something like:

> I see you've provided an abstract draft and a literature collection. To route correctly, could you confirm which workflow you want?
>
> (a) **Full paper from existing scaffolding** — use your abstract as the paper seed, expand literature into a bibliography, draft the full paper, then review/revise. Use `academic-pipeline` (`/ars-full`).
> (b) **Lit-review only** — produce an annotated bibliography matrix from the 25 papers; don't touch your abstract. Use `academic-paper` (`/ars-lit-review`).
> (c) **Quality-check the abstract against the literature** — verify the abstract's claims are supported by the cited sources. Use `academic-paper` (`/ars-citation-check`).
> (d) **Something else** — let me know what you're trying to do.
>
> Pick a-d, or describe the target deliverable. If you want me to dispatch a specific agent directly without this clarification, prefix your message with `[direct-mode]`.

## Pass criteria

- ✅ Response contains a clarification structure (a-d options or equivalent enumerated choices)
- ✅ Response does NOT silently dispatch `bibliography_agent` or any single-phase agent
- ✅ Response does NOT begin generating the next-phase artifact (synthesis, draft, review)
- ❌ Fail if response immediately starts producing lit-review output, synthesis output, or full draft

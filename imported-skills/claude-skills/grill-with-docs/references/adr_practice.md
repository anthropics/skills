# ADR Practice — When Does a Decision Earn an ADR?

This reference answers exactly one decision: **what bar must an architectural decision clear to be worth writing down as an ADR, and what format keeps the ADR useful 18 months later?**

Pair with `scripts/adr_scanner.py` for filename + numbering + structural validation.

## The Core Claim

ADRs are not a compliance ritual. They exist to answer a single future question: **"Why on earth did they do it this way?"** If a future reader will never ask that question — because the choice is obvious, easy to reverse, or had no real alternatives — the ADR is doc-rot waiting to happen.

The matt-pocock 3-criteria gate (preserved verbatim in `ADR-FORMAT.md`) is the strict version of this principle:

1. **Hard to reverse** — the cost of changing your mind is meaningful (not "an afternoon of refactoring").
2. **Surprising without context** — a future reader will look at the code and wonder why.
3. **Result of a real trade-off** — there were genuine alternatives and you picked one for specific reasons.

**All three must be true.** Two-out-of-three is not enough. If a decision was hard to reverse but obvious and uncontested (e.g., "we used HTTPS"), no ADR. If it was a real trade-off but easy to reverse (e.g., "we used React Query over SWR"), no ADR.

## What Earns an ADR (Examples)

- **Architectural shape.** "Write model is event-sourced, read model is projected into Postgres." Hard-to-reverse + surprising + real-trade-off.
- **Integration patterns between contexts.** "Ordering and Billing communicate via domain events, not synchronous HTTP." Hard-to-reverse (rewiring eventing is expensive) + surprising (HTTP is the obvious choice) + real-trade-off (eventual consistency vs simpler API).
- **Technology choices with lock-in.** Database engine, message bus, auth provider. Not "we picked Lodash" — those swap in an afternoon.
- **Boundary and scope decisions.** "Customer data is owned by the Customer context; other contexts reference by ID only." The explicit no-s are as valuable as the yes-s.
- **Deliberate deviations from the obvious path.** "We use manual SQL instead of an ORM because X." Stops the next engineer from "fixing" something deliberate.
- **Constraints not visible in code.** "Can't use AWS due to compliance." "Response times must be <200ms due to partner API contract."
- **Rejected alternatives with non-obvious rejections.** "We considered GraphQL and picked REST because subscription complexity didn't match our actual real-time needs." Otherwise someone will suggest GraphQL again in 6 months.

## What Does NOT Earn an ADR

- **Library choices.** Lodash vs Ramda, axios vs ky, dayjs vs date-fns — these swap in an afternoon. Comment in code if you must.
- **Style guide decisions.** "We use Prettier" — record in `package.json`, not an ADR.
- **Defaults you didn't deviate from.** "We use the framework's recommended router." No trade-off, no ADR.
- **Decisions that are easy to reverse.** If the future-you can undo it in a day, future-you doesn't need the why.
- **Decisions where the alternative was never seriously considered.** No real trade-off → no ADR.

## Format Discipline

ADRs are markdown files at `docs/adr/NNNN-slug.md`, numbered sequentially.

**Default format (minimum viable):**

```md
# {Short title of the decision}

{1-3 sentences: what's the context, what did we decide, and why.}
```

An ADR can be a single paragraph. The value is in recording *that* a decision was made and *why* — not in filling out sections.

**Optional sections (only when they add genuine value):**

- **Status frontmatter** (`proposed | accepted | deprecated | superseded by ADR-NNNN`) — useful when decisions are revisited.
- **Considered Options** — only when rejected alternatives are worth remembering.
- **Consequences** — only when non-obvious downstream effects need to be called out.

If a section is included but empty or boilerplate ("none"), delete the section.

## Numbering Discipline

- Sequential, zero-padded to 4 digits: `0001`, `0002`, ..., `9999`.
- No gaps. If an ADR is abandoned mid-draft, either commit it as `proposed → withdrawn` or renumber.
- Slug is short, kebab-case, intent-revealing: `0042-event-sourced-orders.md`, not `0042-adr.md` or `0042-decision-about-events.md`.

`scripts/adr_scanner.py` enforces the pattern and surfaces gaps.

## Status Lifecycle (Optional)

For repos that revisit decisions, the status field is useful:

```
proposed  →  accepted     ← default lifecycle for a new ADR
accepted  →  deprecated   ← decision no longer applies; no replacement
accepted  →  superseded   ← replaced by ADR-NNNN; link to successor in frontmatter
```

When superseding, the new ADR references the old (`supersedes: ADR-0017`) and the old ADR is updated with `superseded by: ADR-0042`. This back-link is the single most useful piece of ADR metadata for archeology.

## Anti-Patterns

- **The ADR factory.** Writing an ADR for every PR. Within a year, you have 200 ADRs and no one reads any. The 3-criteria gate is the firewall.
- **The proposal that never accepts.** ADR sits in `proposed` for months. Either accept it (do it) or withdraw it (delete the file or mark withdrawn).
- **The TOC-only ADR.** Filled-in section headers but no actual content. Worse than not writing the ADR — it implies a decision was recorded when nothing was.
- **The future-tense ADR.** "We will use X." ADRs are records, not plans. Write in past tense ("We chose X because ...") so it reads correctly 2 years later.
- **The unanchored ADR.** ADR with no link to the PR/issue/discussion that drove it. The "why" loses fidelity over time without the source thread.

## Operational Checklist (Per ADR Decision Point)

When grilling and a candidate decision emerges:

- [ ] **Reversibility test.** "If we change our mind in 6 months, what's the cost?" If "an afternoon" → skip the ADR.
- [ ] **Surprise test.** "Will a future engineer look at this and wonder why?" If no → skip.
- [ ] **Trade-off test.** "What alternatives did we seriously consider, and why did each lose?" If none → skip.
- [ ] **All three pass.** Write the ADR. Use the minimum format. Re-run `scripts/adr_scanner.py` to confirm numbering.
- [ ] **Frontmatter status.** Only add `status` if revisiting is expected. Default is "implicit accepted".

## Citations (7 sources)

1. **Michael Nygard, "Documenting Architecture Decisions" (cognitect.com, November 2011).** The original ADR essay. Introduces the format (Title / Context / Decision / Status / Consequences) and the core insight that "architecturally significant" decisions deserve records. Nygard's framing of ADRs as "memory aids for future architects" is the source of the 3-criteria gate's first rule (hard-to-reverse).

2. **Jeff Tyree & Art Akerman, "Architecture Decisions: Demystifying Architecture" — *IEEE Software* 22(2), March–April 2005, pp. 19–27.** Pre-dates Nygard. Introduces the concept of an "Architecture Decision Record" as a first-class artifact and argues for explicit recording of rejected alternatives. The "rejected alternatives" section in Nygard's format inherits from Tyree & Akerman.

3. **Olaf Zimmermann et al., "Y-Statements: A Lightweight Architectural Decision Format" — published at various venues including ozimmer.ch.** Proposes the "In the context of {use case / requirement}, facing {concern}, we decided for {option} to achieve {quality}, accepting {downside}" template. Used widely as a compact alternative to the full Nygard format.

4. **MADR (Markdown Architectural Decision Records) — adr.github.io/madr.** Open-source template maintained by a community of practitioners. Specifies frontmatter format (status, deciders, date, consulted, informed) and a discoverable file structure. Useful when ADRs need machine-readable metadata for indexing.

5. **ThoughtWorks Technology Radar — thoughtworks.com/radar.** Has covered "Lightweight Architecture Decision Records" since Vol. 18 (2018) in the Techniques quadrant, with periodic upgrades to "Adopt". TW's "use ADRs sparingly" guidance aligns with the 3-criteria gate.

6. **Joel Parker Henderson, adr-tools (github.com/npryce/adr-tools).** CLI tool implementing Nygard's format with numbering helpers, supersession linking, and a `new` / `link` / `accept` command set. Establishes the de-facto convention of `0001-slug.md` filenames and `docs/adr/` directory location.

7. **Spotify Backstage — backstage.io.** Backstage's TechDocs catalog includes an ADR plugin that surfaces per-service ADRs in the service catalog UI. Demonstrates how ADRs become discoverable at scale (>1000 services) when treated as first-class catalog entries, not just files in a repo.

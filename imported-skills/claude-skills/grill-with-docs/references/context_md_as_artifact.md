# CONTEXT.md as a Living Artifact — Preventing Glossary Decay

This reference answers exactly one decision: **how does a glossary stay alive vs decay into doc rot, and what operational practices prevent the drift?**

Pair with `scripts/glossary_code_consistency.py` for the lint-against-codebase reality check and `scripts/context_md_linter.py` for structural validation.

## The Core Claim

Every glossary decays by default. The decay path is well-documented:

```
Month 1: Glossary written during initial DDD workshop. Terms are precise.
Month 3: New feature ships. Two new domain terms used in code, neither added to glossary.
Month 6: A term in the glossary is renamed in code. Glossary still has old name.
Month 9: New engineer joins. Reads glossary. Asks "what's a 'Booking'?" — answer is "we don't call those Bookings anymore, we call them Reservations now."
Month 12: Glossary is officially declared stale. Engineers stop reading it. Drift becomes invisible.
```

The decay is not preventable by good intentions. It is prevented by **inline edits during the work that introduces the term** plus **automated lint runs at PR time** to flag mismatches.

## Three Forces That Drive Drift

1. **Language pressure from outside the bounded context.** A new partner integration uses different terminology ("subscriber" vs your "customer"). Engineers copy the partner's term into code without first reconciling with the glossary.
2. **Refactor pressure inside the bounded context.** A rename in code feels obvious ("`Booking` → `Reservation` is just a better name"), but the glossary isn't updated alongside.
3. **Convergence pressure between teams.** Multiple teams contributing to the same context use slightly different words for the same concept. Without a glossary as referee, all variants end up in code.

`scripts/glossary_code_consistency.py` operationalizes the lint against these three forces:

- **Defined-but-unused term** → a glossary entry that no code references. Either dead glossary (delete) or a rename happened (update glossary to match code).
- **Code-only proper noun** → a frequently-used capitalized term in code that the glossary doesn't define. Either generic (ignore) or domain (add to glossary now).

## Five Practices That Keep CONTEXT.md Alive

1. **Edit inline during the work.** Never batch glossary updates. When a term is introduced or refined during a feature, the same PR that adds the code edits `CONTEXT.md`. Reviewers reject PRs that introduce domain terms without glossary edits.
2. **Lint at PR time.** Run `scripts/context_md_linter.py` and `scripts/glossary_code_consistency.py` in CI. A new term in code without a glossary entry is a build warning; an outright rename mismatch is a build failure.
3. **Per-context glossaries, not one mega-glossary.** Multi-context repos use `CONTEXT-MAP.md` to point at per-context `CONTEXT.md` files. Cross-context terms get explicit translation entries ("Billing's `Customer` is Ordering's `Account`").
4. **Pruning passes.** Quarterly, run `glossary_code_consistency.py` and review the dead-glossary report. Delete entries that no code uses. Keeping dead entries dilutes signal.
5. **One sentence per definition.** If a definition runs to a paragraph, the term is hiding two concepts. Split or sharpen. Long definitions are correlated with imprecise terms.

## How CONTEXT.md Differs from Other "Documentation"

| Artifact | Purpose | Update cadence | Audience |
|---|---|---|---|
| `README.md` | Onboarding + setup | Once at project start, occasionally after | New contributors |
| `ARCHITECTURE.md` | High-level system shape | Quarterly to yearly | New architects, senior engineers |
| `docs/adr/*.md` | Record of specific decisions | Per-decision (rare; days to months apart) | Anyone asking "why did we do X this way?" |
| **`CONTEXT.md`** | **The domain glossary — what each term means in this bounded context** | **Per-feature (continuous; hours to days apart)** | **Every engineer on every PR** |

A `CONTEXT.md` is touched far more often than any other doc because it tracks the language as it evolves. If yours hasn't been edited in 6 months, it's almost certainly drifting.

## Single vs Multi-Context Repos

**Single context (most repos):** One `CONTEXT.md` at the repo root. All terms in scope.

**Multiple contexts:** A `CONTEXT-MAP.md` at the repo root lists the contexts and their relationships. Each bounded context has its own `CONTEXT.md` (and its own `docs/adr/` for context-specific decisions). Shared terms appear in both with cross-references.

```
/
├── CONTEXT-MAP.md         ← lists contexts + relationships
├── docs/adr/              ← system-wide ADRs
└── src/
    ├── ordering/
    │   ├── CONTEXT.md     ← ordering-context glossary
    │   └── docs/adr/      ← ordering-context ADRs
    └── billing/
        ├── CONTEXT.md
        └── docs/adr/
```

When a term spans contexts, define it in each `CONTEXT.md` with the context's perspective + a translation note pointing at the other. Don't try to define "Customer" once and have both contexts share it — that's the path back to the mega-glossary.

## Anti-Patterns

- **The spec masquerading as a glossary.** `CONTEXT.md` includes implementation details, sequence diagrams, API responses. It is a glossary, not a spec. Move spec content elsewhere.
- **The wiki masquerading as a glossary.** General programming concepts ("retry", "timeout", "config") appearing in `CONTEXT.md`. They are not domain-specific. Remove.
- **The glossary that defines without forbidding.** Each term needs `_Avoid_: <aliases>` to push back on drift. A glossary that says "Customer means X" but doesn't forbid "Client" / "Account" / "User" cannot push back when those drift in.
- **The frozen glossary.** No commits in 6+ months. Either the project is dormant or the language has drifted away from the document. Re-grill.
- **The orphan glossary.** Sits in a repo but no CI/PR process references it. It will decay within two quarters.

## Operational Checklist

When grilling against `CONTEXT.md`:

- [ ] Lint structure: `python scripts/context_md_linter.py CONTEXT.md`
- [ ] Lint vs code: `python scripts/glossary_code_consistency.py --context CONTEXT.md --code src/`
- [ ] For each "defined but unused": ask "dead term, or rename happened?"
- [ ] For each "code-only proper noun": ask "domain term that needs definition, or generic?"
- [ ] For each new term introduced during the grill: edit `CONTEXT.md` *now*, not "later"
- [ ] Multi-context repo: verify the right `CONTEXT.md` is being edited (not the wrong context's, not the root one when a per-context one applies)

## Citations (7 sources)

1. **Vladimir Khononov, *Learning Domain-Driven Design* (O'Reilly, 2021).** Chapter 9, "Communication Patterns" + Chapter 12, "Building Domain Expertise" — Khononov is the sharpest writer on language drift between bounded contexts and on how to detect it. His "linguistic boundaries are observable boundaries" framing is the foundation of the `glossary_code_consistency.py` check.

2. **Brian Kernighan & Rob Pike, *The Practice of Programming* (Addison-Wesley, 1999).** Chapter 1, "Style" — the section on naming. Kernighan's "names should reflect the role of the variable, not its type" generalizes to glossary terms: a glossary term names a role in the domain, not a data structure. Kernighan-style naming discipline is what keeps `CONTEXT.md` precise.

3. **Martin Fowler, "BoundedContext" — martinfowler.com bliki (2014, updated).** The canonical argument that ubiquitous language is **bounded** — it applies inside one context, not across all contexts. The justification for per-context `CONTEXT.md` files. https://martinfowler.com/bliki/BoundedContext.html

4. **Martin Fowler, "UbiquitousLanguage" — martinfowler.com bliki.** Companion entry to BoundedContext. Articulates the discipline of using the same vocabulary in conversation, in the model, and in the code. The justification for editing `CONTEXT.md` inline alongside code changes, not as separate doc work. https://martinfowler.com/bliki/UbiquitousLanguage.html

5. **Confluent Schema Registry / Data Contracts community — confluent.io/blog/data-contracts.** The data-contracts movement applies UL discipline to inter-service / inter-context boundaries: when two contexts exchange events or API payloads, the schema is a binding glossary. Drift between contexts becomes a schema-evolution problem, not a free-form documentation problem.

6. **Alberto Brandolini, *Introducing EventStorming* (Leanpub, ongoing).** Chapter on "Pivotal Events" + the convergence-workshop chapter. Brandolini documents how a glossary emerges from EventStorming workshops as a by-product of mapping events. The pattern of "capture the term on a sticky note when it surfaces" is the offline equivalent of the inline `CONTEXT.md` edit discipline.

7. **Eric Evans, *Domain-Driven Design: Tackling Complexity in the Heart of Software* (Addison-Wesley, 2003).** Chapter 14, "Maintaining Model Integrity" — covers the Conformist, Anticorruption Layer, and Shared Kernel patterns. Each of these is a strategy for managing the boundary between two bounded contexts that have different languages. Justifies the multi-context `CONTEXT-MAP.md` pattern and the translation-note discipline for cross-context terms.

# Ubiquitous Language — Why a Glossary Belongs in Source Control

This reference answers exactly one decision: **why should a project's domain glossary (`CONTEXT.md`) live next to the code in source control, and what bar must it clear to earn its keep?**

Pair with `scripts/context_md_linter.py` for structural validation and `scripts/glossary_code_consistency.py` for the language-vs-code reality check.

## The Core Claim

A bounded context has **one** language. The same word must mean the same thing in conversation, in the glossary, in the type system, in the database schema, and in the UI. When language fractures across these surfaces, design defects follow: ambiguous bug reports, mismatched API contracts, broken refactors, junior engineers asking what an "account" is and getting three different answers.

The glossary is the contract that prevents the fracture. It earns its place in source control because it changes at the same cadence as the code — every time a domain term is introduced, refined, or retired, the glossary must move with it. A wiki page that lives outside the repo will drift within a quarter.

## Why a Glossary in Source Control (vs Wiki, Notion, Confluence)

| Property | In-repo `CONTEXT.md` | External wiki |
|---|---|---|
| Reviewable in PR | Yes — diff is visible alongside code | No — reviewer must remember to check |
| Versioned with code | Yes — `git log` shows term evolution | No — wikis rarely have meaningful history |
| Discoverable by new engineers | Yes — `ls` of repo root finds it | No — depends on onboarding tribal knowledge |
| Mergeable | Yes — text format, conflict-resolvable | Often no — UI-driven |
| Linter-targetable | Yes — `scripts/context_md_linter.py` | No — usually not |
| Refactor-safe | Yes — renames are grep-able | No — wiki links rot silently |

The glossary is a **language artifact**, not a documentation artifact. Documentation describes the system; the glossary **is** part of the system's design surface.

## Five Rules That Make a Glossary Survive

1. **One sentence per definition.** If the definition needs a paragraph, the term is hiding two concepts. Split it.
2. **Define what it IS, not what it does.** "An **Invoice** is a request for payment sent after delivery." Not "An invoice handles billing."
3. **List aliases to avoid.** When users say "bill" or "payment request" but mean "invoice", record that "bill" is forbidden. Without the `_Avoid_:` field, the glossary cannot push back on drift.
4. **Show relationships, not just terms.** "An **Order** produces one or more **Invoices**" tells you the cardinality. A list of bare terms doesn't.
5. **Exclude generic programming concepts.** "Timeout", "retry", "config" do not belong. Only terms specific to this project's domain qualify.

## Anti-Patterns

- **The "everything goes in" glossary.** When `CONTEXT.md` includes general programming concepts (timeout, error, util), it dilutes signal and degenerates into a wiki page.
- **The orphan glossary.** Terms defined but never used in code. Either the term is dead (delete it) or the code is using a synonym (rename code).
- **The opaque glossary.** Terms used in code but not defined. Either the term is generic (don't define it) or it's a domain concept that snuck in (define it now).
- **The deferred glossary edit.** "I'll batch up the glossary changes at the end of the sprint." By the end of the sprint, three more drift cases will have shipped. Glossary edits must land inline.
- **The frozen glossary.** No commits in 6+ months. Either the project is dormant or the language has drifted away from the document.

## Operational Checklist (for the Grill Session)

When grilling a plan against `CONTEXT.md`:

- [ ] Pre-flight `scripts/context_md_linter.py CONTEXT.md` — is the glossary well-formed?
- [ ] Run `scripts/glossary_code_consistency.py` — what's defined but unused? what's used but undefined?
- [ ] For every novel term in the plan, ask: "Is this in CONTEXT.md? If not, do we add it, or do we rephrase using an existing term?"
- [ ] For every existing term used in the plan, ask: "Does the plan use it consistent with the definition?"
- [ ] At every clarification moment, edit `CONTEXT.md` immediately — never batch.

## Citations (7 sources)

1. **Eric Evans, *Domain-Driven Design: Tackling Complexity in the Heart of Software* (Addison-Wesley, 2003).** Chapter 2, "Communication and the Use of Language" — the canonical statement of Ubiquitous Language as a design tool, not just documentation. The line "The vocabulary of that UBIQUITOUS LANGUAGE includes the names of classes and prominent operations" is the bridge between conversation and code.

2. **Vaughn Vernon, *Implementing Domain-Driven Design* (Addison-Wesley, 2013).** Chapter 1, "Getting Started with DDD" + Chapter 2, "Domains, Subdomains, and Bounded Contexts" — operationalizes Evans's UL into a workshop format and per-context discipline. Vernon's "linguistic boundaries are the most reliable boundary" framing is the source of the per-bounded-context glossary pattern.

3. **Vladimir Khononov, *Learning Domain-Driven Design* (O'Reilly, 2021).** Chapter 5, "Implementing Simple Business Logic" + Chapter 9, "Communication Patterns" — Khononov is sharpest on what happens when bounded contexts share a language vs maintain separate languages (translation layer required) and on language drift over time.

4. **Scott Wlaschin, *Domain Modeling Made Functional* (Pragmatic Bookshelf, 2018).** Part 1, "Understanding the Domain" — treats the type system as the executable form of the glossary. Wlaschin's "make illegal states unrepresentable" is the strongest form of glossary-as-contract: if the glossary says an Order must have at least one line item, the type prevents zero-item Orders at compile time.

5. **Alberto Brandolini, *Introducing EventStorming: An Act of Deliberate Collective Learning* (Leanpub, 2017–ongoing).** Chapter on "Sticky note color codes" + chapter on convergence — EventStorming workshops produce a glossary as a by-product of mapping the domain. Brandolini's pattern of capturing terms as they emerge on sticky notes is the offline equivalent of the inline `CONTEXT.md` edit.

6. **Abel Avram & Floyd Marinescu, *Domain-Driven Design Quickly* (InfoQ, 2006, free e-book).** Chapter 2, "Ubiquitous Language" — the most concise distillation of Evans's UL chapter. Useful as a reference to hand to engineers who won't read the blue book.

7. **Martin Fowler, "BoundedContext" — martinfowler.com bliki (2014, updated).** Fowler's framing of "Ubiquitous Language … doesn't apply to the whole project, it only has to apply within a particular Bounded Context" justifies the per-context glossary pattern in `CONTEXT-MAP.md`-style multi-context repos. https://martinfowler.com/bliki/BoundedContext.html

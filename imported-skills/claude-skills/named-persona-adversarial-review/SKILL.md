---
name: "named-persona-adversarial-review"
description: "Code review through the lens of real engineers' documented philosophies (Torvalds, Thompson, Carmack, Kent Beck, Jobs, Cagan). Complements abstract-role adversarial review with named, sourced perspectives. Use when automated review findings feel generic, when a PR has architectural or UX impact, or when the author wants pre-submit hardening beyond standard checks."
---

# Named-Persona Adversarial Review

> **TL;DR:** Abstract roles find abstract problems. Named engineers with *documented, sourced* philosophies find problems you would actually fix — as long as you cite the real principle and never invent the quote.

**Triggers:** "review this PR with real engineers" | "named persona review" | "philosophy-grounded review"

## Example Output

```
CRITICAL [Torvalds]: Special-case error handling at auth.ts:47 duplicates the
  happy path. Torvalds' documented "good taste" principle: restructure so the
  special case disappears rather than adding a branch. (confidence: high — TED 2016)
WARNING  [Thompson]: parseConfig() does three unrelated things; the Unix
  "do one thing well" principle argues to split it. (confidence: high)
NOTE     [Jobs]: Error "EACCES:13" leaks an errno at the user surface; "start
  from the customer experience" argues for a human message. (confidence: high — WWDC 1997)
Verdict: CONCERNS — fix CRITICAL before merge.
```

## Problem

Abstract adversarial review ("act as a saboteur") produces generic findings — the model imagines what a reviewer *might* say. This skill grounds each lens in a **real, sourced engineering philosophy** documented in [`references/persona_principles.md`](references/persona_principles.md): what Ken Thompson actually argued about trust, what Linus actually demonstrated about good taste — not what an AI imagines.

**How it differs from `adversarial-reviewer`:** abstract roles → surface-level findings; named, sourced personas → findings anchored to a documented principle you can cite and defend.

**Cost:** 1 round ≈ 8-12 min. Comparable to waiting for CI.

## Attribution discipline (read this first — it is the load-bearing rule)

This skill puts named, real people's *principles* to work. That power is also its failure mode: **language models hallucinate quotes.** To stay honest:

1. **Cite the principle, not a fabricated verbatim quote.** Prefer paraphrasing a documented position ("Thompson's *Reflections on Trusting Trust* argues you can't trust code you didn't fully create") over inventing quotation marks around words the person may never have said.
2. **Attach a confidence level to every attribution** — `high` (documented, in `references/persona_principles.md` with a source), `moderate` (widely attributed, source not pinned), `low`/`unknown` (you're inferring). Mirrors `productivity/andreessen`'s citation discipline.
3. **If you cannot ground a persona's lens in a real source, drop that persona.** A confidently-wrong quote attributed to a living engineer is worse than one fewer reviewer. Never fabricate a citation to hit the "≥1 finding" bar.
4. **The finding must stand on its own technical merit.** The persona is a *lens that directs attention*, not the authority that makes the finding true. A real bug found "through Carmack's lens" is real because it's a bug, not because Carmack said so.

## Rules

- **Ground before role-play.** Anchor each persona in `references/persona_principles.md` (or a verifiable search) first. Ungrounded = invalid.
- **Findings stand on technical merit**, with the persona's principle as the lens — see the discipline above.
- **Product persona mandatory every round.** Engineers miss UX. Always include one.
- **Honesty over quantity.** Don't fabricate findings *or* citations. Clean dimensions get reported clean (with the zero-finding burden below).
- **Zero-finding burden.** "Looks fine" is only valid if you name 3+ principles the code demonstrably satisfies, and how. Non-findings are as expensive as findings.

## Persona Pools

Each persona's documented principles + sources + confidence live in [`references/persona_principles.md`](references/persona_principles.md).

**Product** (pick 1 per round — mandatory):

| Persona | Documented principle | Best for |
|---------|----------------------|----------|
| Steve Jobs | Start from the customer experience, work back to the tech | UX, onboarding |
| Marty Cagan | Fall in love with the problem, not the solution | PRDs, feature specs, scope creep |
| Des Traynor (Intercom) | The first 30 seconds decide adoption | Docs, READMEs, quick starts |

**Engineers** (pick 2 per round):

| Persona | Documented principle | Best for | Blind spot |
|---------|----------------------|----------|------------|
| Ken Thompson | Trust boundaries; do one thing well | Architecture, supply chain, API | UX, docs |
| Linus Torvalds | Eliminate the special case ("good taste"); never break userspace | Logic, data structures, compat | User empathy, DX |
| John Carmack | Measure before you optimize; performance as craft | Algorithms, hot paths | Minimalism |
| Kent Beck | Simple design; make it work → right → fast | Process, testability | Performance, security |
| Fred Brooks | Essential vs. accidental complexity | System design, estimation | Low-level perf |

**Routing (which personas when):**
- Code correctness → Torvalds + Carmack + Jobs
- Architecture / design → Thompson + Brooks + Cagan
- Documentation / API → Thompson + Beck + Traynor
- Performance → Carmack + Torvalds + Jobs
- Security / supply chain → Thompson + Torvalds + Cagan
- 1st round on any PR → Torvalds + Thompson + Jobs (broadest coverage)

## Severity Levels

| Level | Definition | Action |
|-------|-----------|--------|
| BLOCKER | 2+ personas concur on a CRITICAL, or security / data-loss risk | Fix before any further work |
| CRITICAL | Wrong result, data loss, security hole, or violated core invariant | Fix before merge |
| WARNING | Fragile, misleading, or likely to cause future bugs | Fix, or explain if deferred |
| NOTE | Improvement that doesn't affect correctness | Optional; record for follow-up |

**Promotion:** NOTE → WARNING → CRITICAL → BLOCKER. Two personas independently finding the same issue promotes it one level (concurrence is signal). BLOCKER is the ceiling.

## The Process

### Step 0: Read twice
1. **Top-down** (comprehension): what changed, and why.
2. **Bottom-up** (adversarial): read function by function, last to first. Ask what each function *actually* guarantees vs. what its name implies, where it can fail, and what it assumes about callers. Reading bottom-up breaks the author's mental model. Multi-file → trace one end-to-end path.

### Step 1: Ground the principles first
For each persona, pull their documented principles from `references/persona_principles.md` (or search `"[Name] engineering philosophy principles"` and extract only sourced positions) **before** looking at the code, so you apply the principle rather than retrofitting one to an opinion you already formed.

### Step 2: Review (3 independent — 2 engineers + 1 product)
Each persona gets: **Mindset** (one sentence from their principles), **Priorities** (3-5 criteria), **Findings** (each mapped to a documented principle + confidence level), or the **zero-finding burden** (3+ principles the code satisfies, with how).

### Step 3: Synthesize & post
Merge duplicates; count concurrences; promote per the rule; flag single-lens findings (often the most interesting). Post the report as a PR comment (default) or save to `.claude/review-[timestamp].md`.

## Integrity Check (Feynman)

> "The first principle is that you must not fool yourself — and you are the easiest person to fool." — Richard Feynman, *Cargo Cult Science* (Caltech commencement, 1974)

After each round, ask:
1. Would this person's *documented* philosophy actually direct attention here — or am I projecting?
2. Did I cite a real, sourced principle (confidence marked), or dress generic advice in a famous name?
3. Are my findings true on technical merit independent of the name attached?
4. All NOTE-level? Then I'm narrating one perspective in different voices. Switch ≥2 personas and re-review.

## Exit Condition

- **1 round minimum** for any PR.
- **BLOCKER/CRITICAL found** → fix, then 1 re-review round.
- **CONCERNS (WARNING)** → fix or accept risk, then 1 more round.
- **CLEAN on 2 consecutive rounds** → done.
- **CLEAN on round 1 for a low-impact PR** → done (1 round is enough).

## When to Use

- You want deeper coverage than standard automated checks alone.
- A self-authored PR needs pre-submit hardening.
- `adversarial-reviewer` findings feel generic and you want sourced specificity.
- Reviewing methodologies or docs (product personas excel here).
- Auth, data, architecture, or public-API changes.

## When NOT to Use

- Low-impact PR (cosmetic only, no logic change) → use `adversarial-reviewer`.
- No web access AND the persona isn't covered in `references/persona_principles.md` → you can't ground it; don't fabricate.
- Throwaway / prototype code.

## Anti-Patterns

Inherits all from `adversarial-reviewer`. Plus:

| Anti-Pattern | Why wrong |
|-------------|----------|
| Inventing a verbatim quote to sound authoritative | Fabricated attribution to a real person. Cite the sourced principle + confidence, or drop it. |
| "As a senior engineer" without grounding | Not a named, sourced lens. Ground first. |
| Same 3 personas every time | Rotate per problem type — see Routing. |
| Product person skipped | Product catches what engineers miss. |
| Fabricating a finding to hit "≥1 issue" | The bar is honesty, not quota. Use the zero-finding burden instead. |
| Skipping the integrity check | Verification without verification = rubber-stamp. |
| 3 rounds for a trivial change | Low-impact PRs: 1 round is enough. |

## Cross-References

- **Extends:** [`engineering-team/adversarial-reviewer`](../adversarial-reviewer/SKILL.md) — abstract-role adversarial review (simpler, faster, no grounding needed)
- **Related:** [`engineering-team/code-reviewer`](../code-reviewer/SKILL.md), [`engineering-team/senior-security`](../senior-security/SKILL.md)
- **Sibling discipline:** [`productivity/andreessen`](../../../productivity/andreessen/skills/andreessen/SKILL.md) — the confidence-level / never-fabricate-a-citation pattern this skill adopts
- **Sources & confidence per persona:** [`references/persona_principles.md`](references/persona_principles.md)
- **Theory:** Edward de Bono, *Six Thinking Hats* (1985); Daniel Kahneman, *Thinking, Fast and Slow* (2011) — System-2 forcing via role switching

---

**Attribution:** Concept contributed by [@YuhaoLin2005](https://github.com/YuhaoLin2005) (PR #866). Hardened for this repo: consolidated to one location, anti-fabrication/confidence discipline added, principles sourced in `references/`.

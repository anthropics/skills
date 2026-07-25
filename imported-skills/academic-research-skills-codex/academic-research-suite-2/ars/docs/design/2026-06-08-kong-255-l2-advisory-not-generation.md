# Kong L2 — advisory on the scholar's wording ≠ generating ideas for the scholar

| | |
|---|---|
| **Status** | Design lesson — **NOT a proposed feature** |
| **Parent epic** | [#255](https://github.com/Imbad0202/academic-research-skills/issues/255) — Kong et al. 2026 auto-research survey implications for ARS |
| **Sub-issue** | [#257](https://github.com/Imbad0202/academic-research-skills/issues/257) — wording-pattern + distributional-skew advisory (the ACCEPTED side of this line) |
| **Paper anchor** | Kong et al. (2026), *AI for Auto-Research: Roadmap & User Guide*, arXiv:2605.18661, §3.1 (idea generation), §7.4.2 / §7.4.7 (idea clusters, cognitive ownership) |
| **Verified** | 2026-06-08 — verified against the tracked repo (see Verification note) |

This is a recorded boundary, not a roadmap item. It exists so that future work and
reviews apply the same line consistently, and so #257's advisory cannot quietly grow
into idea generation.

## Anchor

- **Paper**: Kong §3.1 surveys idea-generation agents — systems that propose research
  hypotheses or questions for the scholar. §7.4.7 names cognitive ownership of the
  research question as a value worth protecting.
- **ARS**: #257 shipped a wording-pattern advisory in Socratic modes plus a
  distributional-skew step in the bibliography agent. Its own non-goals already state
  it "does not generate ideas for the scholar — only surfaces patterns in the
  scholar's input."

## Problem

The shipped #257 advisory and a rejected idea-generation agent both touch the
scholar's research question. Without a recorded line, advisory scope could drift:
"surface a wording pattern" → "suggest a better phrasing" → "suggest a different
question" → "propose the question." Each step feels like a small, helpful increment;
the cumulative effect crosses from advisory into generation, and the scholar quietly
stops being the author of their own research question.

## Boundary

### The line, stated operationally

> ARS may flag surface-level wording / framing patterns in a **scholar-supplied**
> research question and ask a Socratic follow-up. It must not **propose, substitute,
> rank, expand, or select** research hypotheses or questions for the scholar.

The verb test is the operational check. A change is on the advisory side only if it
*surfaces a pattern in what the scholar already wrote* and *hands the judgment back to
the scholar*. It crosses into generation the moment ARS supplies the candidate the
scholar then merely approves.

### Allowed (advisory — what #257 does)

- Surface that the scholar's RQ phrasing matches a common cliché pattern, and ask a
  Socratic question about it.
- Report distributional skew in the literature corpus (time / geography / methodology
  / venue tier) so the scholar can see coverage gaps.
- Leave the choice — keep the phrasing, change it, ignore the skew — entirely with the
  scholar.

### Rejected (generation — what #257 must never become)

- Propose alternative research questions or hypotheses for the scholar to pick from.
- Rank or reject the scholar's RQ on quality / novelty grounds.
- Rewrite the RQ and present the rewrite as the working question.
- Import Kong §3.1 external-signal-driven generation (trend-mining a question from the
  literature) into any ARS mode.

## Why this distinction matters

Surfacing a pattern in the scholar's own words strengthens cognitive ownership (Kong
§7.4.7): the scholar sees something about their own framing and decides what to do.
Generating a candidate displaces ownership: even when the scholar "approves," their
judgment is anchored on AI-supplied options they did not author. The advisory is
valuable *because* it stops short of the candidate — that restraint is the feature,
not a limitation to be engineered away.

## Application — when this is invoked

Any PR that extends the Socratic modes, the wording advisory, or the bibliography
agent's coverage analysis is reviewed against the verb test above. A change that lets
ARS supply a research question, hypothesis, or RQ rewrite — rather than reflect the
scholar's own input back for the scholar's judgment — crosses the line and is
rejected, however it is framed.

This is the specific sharpening of the broader research-state-authority test in the
sibling [Kong L1](2026-06-08-kong-255-l1-copilot-not-auto-research.md): the research
question is the first research object of record, and the scholar must author it.

## Verification note

- **Verifiable (2026-06-08, against the tracked repo):** #257 shipped (commit
  `f0bfc59`, follow-up `#277`); its non-goals already state it does not generate
  ideas, rank, or reject the scholar's RQ. No idea-generation agent or RQ-proposal
  mechanism exists in ARS today.
- **Design commitment (not a guarantee):** this doc records a first-party scope
  boundary and a review criterion. It is not a proof that the advisory cannot be
  modified, a guarantee about forks, or a runtime enforcement mechanism. First-party
  ARS treats idea generation as out of scope; adding it would require changing this
  recorded boundary, not merely extending the advisory.

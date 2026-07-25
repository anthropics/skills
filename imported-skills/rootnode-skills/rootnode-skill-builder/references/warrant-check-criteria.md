# Warrant Check Criteria

**Canonical sources:** `root_CC_ENVIRONMENT_GUIDE.md §4` (the agent-warranted test, applied to subagent decisions); `root_AGENT_ENVIRONMENT_ARCHITECTURE.md §4.2` (decomposition by mechanism, including the warrant principle).

This reference is a Skill-internal application of the warrant principle to **Skill abstraction decisions**. The agent-warranted test asks "should this be a subagent?"; this reference asks the same question one layer up: "should this be a Skill at all, or is a paste-and-edit template the right tool?"

The two are structurally analogous: both are about not abstracting prematurely. A subagent that should have stayed in the parent agent costs context and orchestration overhead for no benefit. A Skill that should have stayed a paste-and-edit template costs build effort, distribution overhead, and ecosystem complexity for a pattern that hasn't proven recurring.

If the canonical sources evolve (warrant criteria refined, new evidence standards documented), regenerate this reference. The cross-reference anchors above are the propagation hooks.

---

## Why Gate 2 exists

Skill abstraction has costs that aren't always visible at design time:

- **Build cost.** A Skill takes hours to build, validate, and ship. A paste-and-edit template takes minutes.
- **Maintenance cost.** Every Skill in the ecosystem needs to be kept current as the surrounding methodology evolves. Inactive Skills become stale (Pattern 7 in `anti-pattern-catalog.md`).
- **Distribution cost.** Public Skills go through release management. Personal Skills compete for description-field activation surface against everything else installed.
- **Ecosystem complexity.** Each Skill adds to the routing decision Claude makes at activation. More Skills means more routing collisions, more negative triggers needed, more disambiguation work.

A Skill that gets used 100 times across 20 sessions justifies all four costs. A Skill that gets used twice doesn't — the costs exceed the value, and the user would have been better served by a paste-and-edit template they could iterate on freely.

Gate 2 prevents premature abstraction by requiring evidence that the work pattern is genuinely recurring before greenlighting a Skill build.

---

## The 3+ occurrence standard

The warrant test passes when:

1. **The work pattern has surfaced 3+ times in real use.** Not theoretical use, not anticipated use — actual occurrences the user can name and locate.
2. **The pattern is structurally consistent across occurrences.** Not "I did three roughly similar things" but "the same procedure with predictable variation in inputs."
3. **The future demand is plausible.** Not "I might need this someday" but "this pattern keeps coming up; I expect it to keep coming up."

When all three hold, abstraction is warranted. The Skill amortizes its build/maintenance cost over expected future invocations.

---

## Weak warrant signals

When the user proposes a Skill build, watch for these signals that the warrant is thin:

- **"I think we'll need this."** Anticipated need, not demonstrated need. Build a template; promote later if demand materializes.
- **"This came up once and I want to capture the work."** Single occurrence. The work itself was valuable; abstracting it into a Skill before the second occurrence is premature.
- **"This came up twice."** Better than once, but still under the standard. Build a template; the third occurrence triggers promotion.
- **"This is a future feature I'm planning."** Speculative roadmap, not current pattern. Skill builds are reactive (formalize what's already happening), not proactive (build for hypothetical future).
- **"I want a Skill for X" with no examples.** No evidence to evaluate. Ask for the occurrences. If the user can't name them, the warrant fails.
- **"This would be cool to have."** Aesthetic motivation, not functional warrant. Build a template; let demand prove itself.

---

## When the warrant fails: the paste-and-edit template recommendation

When Gate 2 fails, redirect to a paste-and-edit template instead of building a Skill. The template captures the work shape, lets the user iterate freely on each instance, and includes explicit promotion criteria so future-self knows when to upgrade.

**Template file naming:** Per User Preferences, project files use `{code}_` prefix. Templates use `{code}_template_{descriptor}.md`. Examples: `root_template_skill_design_spec.md`, `dt_template_p360_jira_ticket.md`.

**Template structure (recommended):**

```markdown
# {Template Name}

**Purpose:** [One sentence — what this template produces]

**Promotion criteria:** This template earns promotion to a Skill when:
- [Specific occurrence count, e.g., "used 3+ times across distinct sessions"]
- [Specific pattern stability, e.g., "the same 4 sections fire every time"]
- [Specific value signal, e.g., "iteration on the template stops being needed"]

**Last used:** [Date and brief context, updated each use]

**Use count:** [Increment each use]

---

[Template body — paste-and-edit content]

---

## Notes (after use)

- [What worked, what needed to change, what to refine for next time]
```

The promotion criteria section is the load-bearing part. It tells future-self what evidence to look for before deciding to build the Skill. Without it, the template stays a template forever (or gets prematurely promoted on a fourth use that doesn't actually justify the Skill build).

**Pivot prompt for the user:**

> "The work pattern hasn't surfaced enough times to warrant a Skill build (X occurrences; the standard is 3+). Recommend building a paste-and-edit template instead — `{code}_template_{descriptor}.md` per your prefix convention. The template gives you the shape to iterate on; promotion criteria document what evidence to wait for before upgrading to a Skill. Want help drafting the template?"

---

## Exception: process-abstraction handoff brief

When the user provides a process-abstraction handoff brief (produced by `rootnode-repo-hygiene` Cat 14 detection or by another upstream Skill following the same format), the brief is the warrant evidence. Gate 2 passes automatically; proceed to Gate 3.

The brief is a structured artifact that documents the warrant case. The format spec below is what v2 expects when consuming a brief. (`rootnode-repo-hygiene` v1 produces this format; the spec is owned by repo-hygiene's design and consumed here.)

### Process-abstraction handoff brief format

```markdown
# Process Abstraction Handoff: {pattern_name}

**Source:** {producing-skill-name + version}
**Detection date:** {YYYY-MM-DD}
**Recommended target:** Skill | Subagent | Hook | Rule | CLAUDE.md section

---

## Pattern description

[2-3 sentences describing the work pattern that recurred]

## Evidence of recurrence

| Occurrence | Date | Context | Inputs | Outputs |
|---|---|---|---|---|
| 1 | YYYY-MM-DD | [session/project/context] | [what came in] | [what came out] |
| 2 | YYYY-MM-DD | [session/project/context] | [what came in] | [what came out] |
| 3 | YYYY-MM-DD | [session/project/context] | [what came in] | [what came out] |
| ... | ... | ... | ... | ... |

## Pattern stability

[Which steps were identical across occurrences? Which varied? Is the variation predictable?]

## Recommended scope

[What should the Skill do? What should it NOT do? Where are the natural edges?]

## Composition with existing Skills

[Which existing Skills does this compose with? Any duplication risk?]

## Suggested next step

[Build the Skill / build subagent / build hook / draft CLAUDE.md section / etc.]
```

When v2 receives a brief in this format, the warrant gate passes automatically. The brief becomes input to the build process — the Skill name, scope, and composition guidance feed into the design.

If the brief is incomplete (missing the evidence table, missing pattern stability, missing composition assessment), Gate 2 should request the missing fields before passing. Incomplete briefs don't satisfy the warrant standard — they signal the producing Skill didn't do the upstream evidence work.

---

## When to build a Skill that fails Gate 2 anyway

The warrant gate is advisory in this sense: the user can override after hearing the redirect. Legitimate override cases:

- **Compliance / standardization mandate.** Even a low-recurrence pattern may need to be a Skill if external policy requires the standardization (e.g., a regulated workflow that must be reproducible identically).
- **Paste-and-edit cost > Skill build cost.** Some patterns are short to abstract but tedious to paste-and-edit each time. If the template would be 200 lines and the iteration cost is high, building the Skill at 2 occurrences may be cheaper than maintaining the template.
- **The pattern is a foundation for an obvious next-step Skill family.** Building the first Skill establishes patterns that downstream Skills will use. The warrant evidence covers the family, not just the first member.

In override cases, capture the reasoning in the build summary. The promotion provenance artifact (produced when warrant evidence is provided OR when the user overrides) documents what evidence existed and what the user's reasoning was, so future maintainers understand the justification.

---

## Promotion provenance artifact

When Gate 2 passes (with evidence) or is overridden (with reasoning), v2 produces a promotion provenance artifact: `{skill-name}_promotion_evidence.md`. This artifact captures:

- **Warrant standard met / overridden:** "passed (3+ occurrences with evidence)" or "overridden (reasoning: ...)"
- **Evidence summary:** If passed, the evidence table from the handoff brief or the user-provided occurrences. If overridden, the user's reasoning verbatim.
- **Promotion source:** Was this promoted from a paste-and-edit template? If so, name the template file and how many times it was used.
- **Date promoted:** YYYY-MM-DD.

The artifact serves two purposes: (1) audit trail for future maintenance — when someone asks "why does this Skill exist?" the answer is in the provenance file; (2) input to ecosystem evolution — patterns of premature promotion or repeated overrides become signals for refining the warrant standard.

---

## What this reference does not do

This reference doesn't decide whether the work fits the Skill mechanism — that's Gate 1 (`decomposition-framework.md`). Warrant assumes Gate 1 has already passed.

This reference doesn't decide where the Skill sits in the ecosystem — that's Gate 3 (`ecosystem-placement-decision.md`). Warrant only answers "is the Skill warranted?" not "if warranted, where does it belong?"

This reference doesn't generate the paste-and-edit template content — only the recommendation to build one and the promotion criteria structure. Template content is the user's design work; the Skill's role is the redirect, not the construction.

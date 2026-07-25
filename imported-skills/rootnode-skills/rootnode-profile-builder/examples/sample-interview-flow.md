# Sample Interview Flow

A worked example of the profile-builder Skill conducting an interview against the `rootnode-handoff-trigger-check` profile schema. Demonstrates the progressive-depth pattern, plain-language enum translation, default-with-rationale offering, and final summary. Use as a reference for what "good" looks like when applying the builder to other schemas.

This is not a script — it is a sample transcript. The Skill should adapt to the user's actual answers and schema, not follow this verbatim.

---

## Setup

Caller invokes:
```
Build me a handoff profile for working at my desk.
```

Skill detects: target Skill is `rootnode-handoff-trigger-check`, locates `~/.claude/skills/rootnode-handoff-trigger-check/schema/profile.schema.json`, parses it.

Skill plans interview:
- 7 required fields (name, description, threshold_rule, budget_safety_margin, budget_data_source, schema_version is auto-set)
- 1 conditional field (min_pass_count required when threshold_rule = min_count)
- 1 optional field expected to surface (required_conditions — recommended for desk profile)
- 2 deeply optional fields (notes, condition_weights — defer to Tier 4)

---

## Interview transcript

**Skill:** I'll walk you through 5-7 questions to build your profile. Let's start with the basics.

What should this profile be called? It should be lowercase with hyphens — no spaces. Suggested: `desk`.

**User:** desk

**Skill:** When does this profile apply? One sentence — what context, what availability, what constraints.

**User:** When I'm at my desk and can review and correct in real time.

**Skill:** Got it.

Now the substantive choices.

**Question 1 of 5: How strict should the gate be?**

The gate has 7 conditions. You can require:
- (a) **Every condition must pass** — strictest. Use when you're handing off to unattended runs (overnight, away from devices).
- (b) **Most conditions must pass** — balanced. You set the minimum number. Some conditions can be marked non-negotiable. Recommended for active sessions where corrections are real-time.
- (c) **Weight conditions by importance** — advanced. Each condition gets a weight; you set a passing score. Use when some conditions matter much more than others.

**User:** b

**Skill:** **Question 1a: How many of the 7 conditions must pass at minimum?**

For desk work where you can correct in real time, I'd suggest 5 of 7 — gives you flexibility while still requiring substantive readiness. Sleeping profiles typically use 7 of 7 (all required).

**User:** 5

**Skill:** **Question 2 of 5: Are any conditions non-negotiable, regardless of count?**

Even with a "5 of 7" threshold, some conditions are dangerous to skip. The gate can mark specific ones as always-required.

For desk profiles, I recommend two:
- `invariants_documented` — without explicit invariants, autonomous runs drift silently. Real-time correction can't catch drift you don't see.
- `budget_headroom` — running out of token budget mid-execution wastes work and is hard to recover from even at desk.

You can also add others. Skip if you want strict count-only logic.

Choose: (a) accept the recommended two, (b) accept the recommended two and add more, (c) choose your own list, (d) none — count-only.

**User:** a

**Skill:** **Question 3 of 5: How much token budget headroom do you want?**

Budget headroom is a multiplier applied to your estimated cost before checking against your remaining budget. Higher = more conservative.

- 1.0 = no margin (risky — any underestimate causes mid-run failure)
- 1.1 = minimal margin (suggested for desk; you can react to overruns immediately)
- 1.2 = moderate margin (suggested for day job; mobile-only correction)
- 1.3+ = high margin (suggested for sleeping; no correction possible)

What value? Suggested: **1.1**.

**User:** 1.1

**Skill:** **Question 4 of 5: Where does the gate get budget data?**

The gate needs to know your remaining token budget to check condition 7. Options:
- (a) **Manual input** — you type your remaining budget when invoking the gate. Works today, no infrastructure needed.
- (b) **Live telemetry feed** — the gate fetches real-time budget from a URL. Requires telemetry infrastructure (not built yet).
- (c) **Config file** — gate reads budget from a known filesystem path you keep updated.
- (d) **No check** — skip condition 7 entirely. Only use when the runtime has no token cost (self-hosted local models, deterministic workflows).

Suggested: (a) for now. We can change this later when telemetry is built.

**User:** a

**Skill:** **Question 5 of 5: Anything else?**

Optional: would you like to add free-text notes (audit trail explaining your choices), or review the defaults the Skill set for fields you didn't customize?

- (a) Just save it
- (b) Add notes
- (c) Review and customize defaults

**User:** b

**Skill:** Notes are free-text — explain when you use this profile, what risk tolerance you're encoding, anything that future-you should know.

**User:** Default profile for active design and execution sessions. Tolerates more design uncertainty because I can correct in real time. Reconsider when daily token budget changes by more than 30%.

**Skill:** Got it.

---

## Summary shown before save

```
Profile summary: desk

Schema:    rootnode-handoff-trigger-check v1.0.0
Purpose:   When I'm at my desk and can review and correct in real time.

Behavior:
  Strictness:   Most conditions must pass (minimum 5 of 7)
  Required:     invariants_documented, budget_headroom
  Budget data:  Manual input each invocation

Numeric settings:
  Budget safety margin: 1.1x

Notes:
  Default profile for active design and execution sessions. Tolerates
  more design uncertainty because I can correct in real time. Reconsider
  when daily token budget changes by more than 30%.

Will be saved to: ~/.rootnode/profiles/handoff-trigger-check/desk.json
Companion notes:  ~/.rootnode/profiles/handoff-trigger-check/desk.notes.md

Confirm save? (y / n / edit)
```

**User:** y

**Skill:** Validating against schema... ✓

Saved:
- `~/.rootnode/profiles/handoff-trigger-check/desk.json`
- `~/.rootnode/profiles/handoff-trigger-check/desk.notes.md`

To use this profile, invoke the handoff-trigger-check Skill with `profile: desk`. To create variants (overnight, day-job), say "clone desk and make a {variant} version."

---

## Patterns demonstrated

This sample illustrates several patterns the builder Skill should apply to any schema:

1. **Plain-language enum translation.** `min_count` becomes "Most conditions must pass — balanced." Users never see machine names.

2. **Recommendations grounded in stated purpose.** When the user said "desk, real-time corrections possible," subsequent recommendations referenced that context (1.1x margin "because you can react to overruns immediately at desk").

3. **One question at a time, with rationale.** Never bundle multiple decisions into a single prompt. Always explain why the question matters.

4. **Defaults offered with one-sentence rationale.** "Suggested: 5 of 7" + "gives you flexibility while still requiring substantive readiness."

5. **Conditional follow-ups inserted in plain language.** Choosing `min_count` triggered Question 1a immediately, framed as a natural follow-up not as "now I need to ask about field min_pass_count."

6. **Tier 4 saved for the end.** Notes and advanced customization offered as Question 5, easy to skip with "Just save it."

7. **Summary in human language.** "Most conditions must pass (minimum 5 of 7)" not `"threshold_rule": "min_count", "min_pass_count": 5`.

8. **Save confirmation includes companion notes file.** Audit trail by default for users who chose to add notes.

9. **Closing instructions tell the user how to use what they just made.** Bridges from "profile created" to "profile in active use."

These patterns generalize to any schema. The builder reads the schema, generates the questions accordingly, but always applies the same conversational shape.

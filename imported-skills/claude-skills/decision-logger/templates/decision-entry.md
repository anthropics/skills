# Decision Entry Template

Single entry for the Layer 2 index `~/.claude/decisions/approved/decisions.md`.
Copy this block and fill it in after each approved board decision.

---

```markdown
## [YYYY-MM-DD] — [AGENDA ITEM TITLE]

**Decision:** [One clear statement of what was decided.]
**Owner:** [Role or name. One person. If it needs two, the first is accountable.]
**Deadline:** [YYYY-MM-DD]
**Review:** [YYYY-MM-DD — when to check. Usually 2–4 weeks after deadline.]
**Rationale:** [Why this over alternatives. 1-2 sentences. No fluff.]

**User Override:** 
<!-- Leave blank if founder approved the agent recommendation.
     Fill in if founder changed something:
     "Founder rejected [agent recommendation] because [reason]. 
      Actual decision: [what founder decided instead]." -->

**Rejected:**
<!-- List every proposal explicitly rejected in this discussion.
     These must not be resurfaced without new information. -->
- [Proposal text] — [reason for rejection] [DO_NOT_RESURFACE]

**Action Items:**
- [ ] [Specific action] — Owner: [name] — Due: [YYYY-MM-DD] — Review: [YYYY-MM-DD]
- [ ] [Specific action] — Owner: [name] — Due: [YYYY-MM-DD] — Review: [YYYY-MM-DD]

**Supersedes:** <!-- DATE of the previous decision on this topic, if any -->
**Superseded by:** <!-- Leave blank. Will be filled in if a later decision overrides this. -->

**Raw transcript:** ~/.claude/decisions/raw/[YYYY-MM-DD]-<slug>.md
```

---

## Field Rules

| Field | Rule |
|-------|------|
| Decision | Must be a single statement. If it takes two sentences, split into two decisions. |
| Owner | One person or role. "Everyone" owns nothing. |
| Deadline | Required. No "TBD". If unknown, set 14 days and review. |
| Review | Always set. Minimum 1 day after deadline. |
| Rationale | Required. "Because we decided so" is not rationale. |
| User Override | Honest record. Do not soften or omit. |
| Rejected | Every rejected proposal must be listed. |
| DO_NOT_RESURFACE | Applied to every rejected item. No exceptions. |

---

## Marking Action Items Complete

When an action item is done, update the entry in decisions.md:

```markdown
- [x] [Action text] — Owner: [name] — Completed: [YYYY-MM-DD] — Result: [one sentence outcome]
```

Do not delete completed items. The history is the record.

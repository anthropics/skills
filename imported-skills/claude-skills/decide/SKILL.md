---
name: "decide"
description: "/cs:decide <memo> — Log a decision to two-layer memory via decision-logger. Approved memo becomes durable; raw transcripts kept for reference. Use when the founder has approved a boardroom memo and the decision must become durable company memory — e.g. right after /cs:boardroom concludes."
---

# /cs:decide — Log the Decision

**Command:** `/cs:decide <memo-path>`

Logs the founder's decision via the `decision-logger` skill. This is the gate where in-session deliberation becomes durable company memory.

## Pipeline Position

```
/cs:office-hours  →  /cs:brief  →  /cs:boardroom  →  /cs:decide  →  /cs:execute  →  /cs:post-mortem
                                                       ↑ you are here
```

## Two-Layer Memory Model

The `decision-logger` skill maintains two layers:

1. **Raw transcripts** — every boardroom session, every advisor's Phase 2 position, every dissent. Stored under `~/.claude/decisions/raw/`. Reference only, never feeds back automatically.
2. **Approved decisions** — only the founder-signed memos. Stored under `~/.claude/decisions/approved/`. Feeds into future `/cs:office-hours` and `/cs:founder-mode` calls.

This split prevents the system from "remembering" unresolved debates as if they were decisions.

## Input

A board memo file (output of `/cs:boardroom`).

## Workflow

1. Read the memo path
2. Verify it has founder approval (status: APPROVED)
3. Extract structured decision record:
   - Decision title
   - Date decided
   - Option chosen
   - Success + kill criteria
   - Dissent (preserved)
   - Review checkpoint date
4. Append to `~/.claude/decisions/approved/<YYYY-MM-DD>-<slug>.md`
5. Update the raw transcript pointer
6. If llm-wiki bridge configured, write to vault (`~/company-vault/10-decisions/`)
7. Schedule auto-revisit (90 days)

## Output Record Format

```markdown
# Decision: <title>
**Decided:** YYYY-MM-DD
**By:** <founder name>
**Memo:** <link to boardroom memo>
**Brief:** <link to original brief>
**Review checkpoint:** YYYY-MM-DD (90d default)

## Decision
**Chose:** <option>
**Rejected:** <other options + one-line why>

## Success Criteria (binding)
- <metric, threshold, timeframe>

## Kill Criteria (binding)
- <metric, threshold, action>

## Preserved Dissent
- **<dissenter>:** <unresolved concern>
- (preserved verbatim; dissent never erased)

## Next Action
- `/cs:execute` → 90-day plan due <date>

## Status History
- YYYY-MM-DD: APPROVED
```

## Why Preserved Dissent

The biggest risk in approved decisions is forgetting why someone disagreed. When the kill criteria trigger, the dissent often turns out to have been correct. Preserving it verbatim — not summarized — keeps the company honest at post-mortem time.

## Routing

- `/cs:execute <decision>` — build the 90-day plan
- `/cs:freeze <decision> <days>` — lock if irreversible
- (Auto-scheduled) `/cs:post-mortem <decision>` — at 90-day checkpoint

## Stale-Decision Audit

`cs-chief-of-staff` runs a weekly stale audit:
- Decisions > 90 days without revisit → flag for `/cs:post-mortem`
- Decisions with kill criteria triggered → flag immediately
- Decisions whose company-context.md basis has changed → flag for re-examination

## Related

- Skill: [`decision-logger`](../../../skills/decision-logger/SKILL.md)
- Agent: [`cs-chief-of-staff`](../../agents/cs-chief-of-staff.md)
- Bridge: [`../../references/llm-wiki-bridge.md`](../../references/llm-wiki-bridge.md)

---

**Version:** 1.0.0

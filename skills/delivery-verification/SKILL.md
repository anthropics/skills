---
name: delivery-verification
description: Session-end quality gate for Claude Code. Before Stop, verifies learning capture completeness, detects rationalization patterns, and checks disk space. Hard blocks (exit 2) when complex tasks complete without learning capture. Complements pre-task-calibration (pre-action) and persona-review (adversarial depth).
license: MIT
---

# Delivery Verification

A Stop hook that mechanically verifies session completeness before allowing Claude Code to finish. Checks file timestamps, disk usage, and transcript patterns — no AI inference, no self-assessment.

## When to Activate

- At every session end (Stop hook)
- After complex tasks (3+ Edit/Write operations)
- When learning capture discipline matters across sessions
- As the output gate paired with pre-task-calibration's input gate

## How It Works

```
Session End (Stop hook):
  1. Disk check: <15GB → exit 2 (hard block)
  2. Task complexity: count Edit/Write calls
  3. Learning capture: check if growth-log updated today
  4. Rationalization detection: regex on transcript tail
  5. Complex task + >=3 stale libs OR growth-log stale → exit 2
```

Only blocks when: disk critical, OR complex task completed without learning capture.

## What It Checks

| Check | Mechanism | On Hit |
|-------|-----------|--------|
| Disk space <15GB | shutil.disk_usage | Block (exit 2) |
| Stale learning libs | mtime comparison | Warn; block if >=3 stale + complex |
| Stale growth-log | mtime comparison | Block if complex task |
| Rationalization patterns | Regex | Warn only (never blocks) |

## Gate Logging

A gate that only logs its negative outcomes cannot report a rate. If every line is `blocked`,
then `blocked / total` is 1.0 for any input — that number describes the bookkeeping, not the
gate. The rule: **when a gate cannot measure itself it must say so, and the fix belongs in the
log, not in the gate.**

One record per gate per session:

| Field | Meaning |
|---|---|
| `gate` | gate name |
| `status` | `measured` / `satisfied` / `dead` / `uncomputable` |
| `allowed` | count only — never one line per allowed event |
| `blocks`, `warns` | one line each, carrying the reason |
| `block_rate` | `blocks / (blocks + allowed)`, `null` when uncomputable |

`allowed` is aggregated on purpose. In one deployment the gate logged 963 blocks; the allow side
is plausibly two orders of magnitude larger, and per-event allow lines at that volume swamp the
log and slow the next audit while adding nothing — the count is all the rate needs. Blocks and
warns stay per-event because each one carries a reason worth reading.

Status is exclusive and total:

| Status | Condition | Meaning |
|---|---|---|
| `measured` | allowed > 0, blocks > 0 | both sides observed |
| `satisfied` | allowed > 0, blocks = 0 | gate ran, nothing to stop |
| `dead` | allowed = 0, blocks > 0 | everything blocked — suspect the predicate |
| `uncomputable` | both zero | the gate never ran |

`dead` and `satisfied` are the pair that matters: a single-sided log makes them identical, and
that is how a broken gate survives review as health.

Acceptance: a whole-session gate report must be reproducible **in one command from the log**, not
by rereading a transcript. Reference implementation and tests live under `scripts/` —
`python scripts/gate_log.py --selftest`.

## Install

```json
{
  "hooks": {
    "Stop": [{
      "hooks": [{
        "type": "command",
        "command": "python3 ~/.claude/scripts/quality-gate.py",
        "timeout": 5000
      }]
    }]
  }
}
```

## Example

```
Stop hook (complex task, 5 edits):
→ growth-log: updated today ✓
→ decisions/log.md: updated today ✓
→ ratings-tracker.md: STALE (last: 2 days ago)
→ output-index.md: STALE
→ 2/4 stale (<3) → warn only
→ Allow session end
```

## Integration

Complements — does not replace:
- **pre-task-calibration**: pre-action verification
- **persona-review**: adversarial depth
- **neural-gate**: post-session behavioral verification

## Evidence

Merged in ECC (226K stars) as delivery-gate (#2378) after full maintainer review. 50+ session production use. The boundary between warn and block follows one principle: "can this be fixed retroactively?" Stale database → can backfill → warn. Missing growth-log after complex task → damage done → block.

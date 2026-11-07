---
name: delivery-verification
description: Specifies a turn-end quality gate for Claude Code and a two-sided JSONL log for the adopter's gates. Before Stop, the gate verifies learning capture completeness, detects rationalization patterns, and checks disk space; it hard blocks (exit 2) on critical disk space or a complex task without learning capture. The gate, its writer, and its reader are the adopter's. Use when setting up a turn-end quality gate or specifying how gates record allow, warn, and block.
license: Complete terms in LICENSE.txt
---

# Delivery Verification

This skill specifies a Stop hook that mechanically verifies turn completeness before Claude Code
can finish. It checks file timestamps, disk usage, and transcript patterns, with no AI inference
and no self-assessment. The gate, its writer, and its reader/report are the adopter's; this
skill supplies the specification and the log contract.

## When to Use This Specification

- When setting up a turn-end quality gate
- When specifying how a gate records allow, warn, and block
- When a complex task must leave evidence of learning capture
- As the output gate paired with pre-task-calibration's input gate (separate PR #1422)

## When It Runs

The hook runs at every turn end (Stop event). The complex-task checks apply only
when the turn has 3+ Edit/Write operations; `learning-capture` records `allow`
on a simple turn rather than being skipped.

## How It Works

The Stop payload supplies `transcript_path`, `session_id`, and
`stop_hook_active`. Count Edit/Write tool-use entries and scan the transcript
tail from `transcript_path`. On a non-forced Stop, an unreadable or missing
`transcript_path` is an evaluation error: each transcript-dependent gate raises,
is caught at step 1, leaves no record, and step 7 exits 2. The disk gate is
independent and still runs and writes. `learning-capture` must not record
`allow` when complexity cannot be computed, and `rationalization` must not
record `allow` when the tail cannot be read.

```
Turn end (Stop hook):
  0. stop_hook_active is true: exit 0 without evaluating or recording (forced pass)
  1. Evaluate each declared gate under its own exception boundary and deadline,
     set well inside the hook timeout; a gate that raises or exceeds its deadline
     is caught, leaves no record, and the remaining gates continue
  2. Disk check: free space on the filesystem containing `~/.claude` < 15 GB -> block
  3. Task complexity: count Edit/Write calls
  4. Learning capture (complex task only): check if growth-log updated today
  5. Rationalization detection: regex on transcript tail
  6. Complex task AND (>=3 stale non-growth-log learning files OR growth-log
     stale) -> block
  7. Decide every completed gate's record (allow, warn, or block) and the process
     exit code: exit 2 if any completed gate blocked OR any gate crashed/timed out
     (fail closed); otherwise exit 0. Precedence is block > warn > allow
  8. Write the decided records. A per-record write failure leaves only that record
     missing, the remaining writes are still attempted, and the exit code does not
     change; report the failure on stderr
```

Only decides `block` when: disk critical, or a complex task left the growth-log
stale or 3+ non-growth-log learning files stale; rationalization never decides
`block`. A crash or per-gate timeout in any gate is an evaluation error, not a
block decision: it exits 2 (fail closed) and prints stderr.

## What It Checks

| Check | Mechanism | On Hit |
|-------|-----------|--------|
| Disk space < 15 GB on the filesystem containing `~/.claude` | free-space probe | Block (exit 2) |
| Stale learning files (not growth-log) | mtime comparison | Warn on 1-2 if complex; block on >=3 |
| Stale growth-log | mtime comparison | Block if complex task, regardless of the count |
| Rationalization patterns | Regex | Warn only (never decides `block`) |

Stale means the file's mtime is before the start of the current local day. The log's day file
uses UTC, so near midnight the two can disagree; that is expected. The example counts four
learning files, but the 1-2/3+ count covers only the three non-growth-log files:
`decisions/log.md`, `ratings-tracker.md`, and `output-index.md`. `growth-log/` is checked
separately and blocks on its own. The 15 GB, 3-file, and 20-evaluation values are example
thresholds; choose your own.

## Gate Logging

A gate that records only its negative outcomes cannot report a rate: when every
line is `block`, `block_rate` is 1.0 by construction. Record allows too.

Every declared gate that completes and whose record is written produces exactly
one record on every non-forced Stop, including when its condition does not
apply; a forced pass writes no record. A gate that crashes or cannot write leaves
that record missing on disk, and the remaining writes are still attempted. The
log is append-only JSONL at `~/.claude/gate-log/<YYYY-MM-DD>.jsonl`, UTC, with
`expected.txt` listing the gates that should exist. A gate that raises
or exceeds its own deadline is caught, leaves only its own record missing, and
the remaining gates still write. If the whole hook is killed at its timeout, no
further record is written and a decided block is lost, so set per-gate deadlines
well inside the hook's 60 seconds. Decide each record's outcome and the process
exit code before writing: a failed log write leaves that record missing on disk
and must never turn a decided block into an allow. A caught crash or per-gate
timeout is an evaluation error and exits 2 (fail closed), even though it leaves
no record.

The full contract (fields, concurrency, windows, verdicts, absence states, report
format) is in [references/gate-log.md](./references/gate-log.md).

## Adopting the Gate

This skill installs nothing; the block below is an example, not a shipped executable.
Replace the placeholder with your own gate script before enabling it.

```json
{
  "hooks": {
    "Stop": [{
      "hooks": [{
        "type": "command",
        "command": "python3 /absolute/path/to/your-gate.py",
        "timeout": 60
      }]
    }]
  }
}
```

Create the gate list once. This command appends without joining the first new entry to a
non-newline-terminated file:

```sh
python3 -c "from pathlib import Path; p=Path.home()/'.claude'/'gate-log'/'expected.txt'; p.parent.mkdir(parents=True, exist_ok=True); s=p.stat().st_size if p.exists() else 0; f=open(p,'a',encoding='utf-8'); f.write((chr(10) if s else '')+''.join(g+chr(10) for g in ('disk-space','learning-capture','rationalization'))); f.close()"
```

> Append to `expected.txt`; never truncate another gate's entry. Re-running adds a leading blank
> line and duplicate names; blank lines are ignored and repeats collapse. Merge into the
> existing hooks object, only after your own gate script exists and exits 0 clean. exit 2 blocks
> the turn, and is required once any completed gate decides `block` or any gate crashes/times
> out (fail closed), even if the log write failed. Reserve exit 1 for errors before any gate
> runs. This skill specifies the gate contract, log format, and report semantics; the gate, its
> writer, and its reader are yours. Use your Python 3 launcher (for example `python3`, or the
> full interpreter path) in both commands. On Windows, put the full path to your Python
> executable and script in the hook command, because cmd.exe does not expand `~`.

## Example

```
Stop hook (complex task, 5 edits):
→ growth-log: updated today ✓
→ decisions/log.md: updated today ✓
→ ratings-tracker.md: STALE (last: 2 days ago)
→ output-index.md: STALE
→ 2/4 stale (<3) → warn only
→ Allow the turn to end
```

With disk and transcript checks clean, a simple turn writes three `allow` records; the complex
turn above writes one `warn` and two `allow` records. A low-disk or hedging turn changes the mix.

## Integration

Complements — does not replace:
- **pre-task-calibration** (separate PR #1422): pre-action verification
- **persona-review** (separate PR #1420): adversarial depth
- **neural-gate** (separate PR #1424): post-session behavioral verification

## Evidence

The gate this specification generalizes:
[affaan-m/ECC#2378](https://github.com/affaan-m/ECC/pull/2378) (delivery-gate, merged
2026-06-30T02:22:55Z); it implements the gate, not the two-sided log added here. The
one-sided-log problem is reported in the
author's 2026-10-09 reply on
[anthropics/skills#1385](https://github.com/anthropics/skills/issues/1385#issuecomment-6081412364):
`write_guard` and `evidence-gate` each logged a constant `blocked` event at their only call site,
so the reported rate was 1.0 regardless of the gate's actual decision. The boundary is
cardinality-aware: 1-2 stale non-growth-log learning files can be backfilled, so warn; 3+ stale
files means no learning was captured at all, so it is not a backfill case, and a stale
growth-log after a complex task cannot be reconstructed, so both block regardless of the count.

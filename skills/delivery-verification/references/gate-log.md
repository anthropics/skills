# Gate log contract

This file specifies the on-disk format and report semantics for a gate that runs
at the end of a Claude Code turn (a Stop hook). The gate, its writer, and its
reader/report are the adopter's; this contract is what they must implement if
they log.

A gate that records only its negative outcomes cannot report a rate: when every
line is `block`, `block_rate` is 1.0 by construction. Record allows too, and make
absence its own state.

## Evaluation

One record is one evaluation. An evaluation is one declared gate assessed once
at a Stop event where `stop_hook_active` is false or absent. It ends in exactly
one of `allow`, `warn`, or `block`. If any rule blocks, the outcome is `block`;
else if any rule warns, it is `warn`; else it is `allow` (precedence: block >
warn > allow).

Every declared gate that completes and whose record is written produces exactly
one record on every such Stop, including a gate whose condition does not apply to
this turn: it ran, and nothing blocked. Do not skip a gate because a sibling
blocked. Run each gate under its own exception boundary and deadline, set well
inside the hook timeout; a gate that raises or exceeds its deadline is caught,
leaves no record, and the remaining gates continue. Decide every completed gate's
record and the process exit code before writing any record: exit 2 if any
completed gate decided `block` or any gate crashed/timed out (fail closed);
otherwise exit 0.

A blocked turn is re-run before it can end. That re-run has
`stop_hook_active: true`, is a forced pass, not an evaluation, and writes no
record.

A caught crash or per-gate timeout is an incomplete gate evaluation: that gate
writes no record, and the other gates still write theirs. A hook timeout kills
the whole process, so no further record is written and any decided block is
lost; it is a process-level loss rather than a per-gate result. The absence
verdicts below are the only signal in the log a *persistently* failing gate
leaves, because absence is per gate over a window, not per Stop; a single
skipped Stop leaves no signal in the window. Report a failed gate's stderr
separately. A per-record logging failure leaves only that record missing on
disk, the remaining writes are still attempted, and the exit code does not
change: if any completed gate decided `block`, or any gate crashed or timed
out, exit 2 even when a record could not be written, and print the failure to
stderr.

Because a gate whose condition does not apply still records `allow`,
`block_rate` is a per non-forced Stop that produced a record for this gate:
forced passes, crashed/timed-out gates, and failed writes contribute no record
and are excluded. `n` is evaluations, not Stops. This is not a per-applicable
rate. A conditional gate
will read low on a workload with few applicable turns. Read it with the allow
count and the last-block times, and do not compare it across workloads.
Per-event allows are bounded by gates x Stops, so the log grows with turns, not
with tool actions; aggregate only within one gate, because summing across gates
would hide which gate is one-sided.

## Records

| Item | Contract |
|---|---|
| Path | `~/.claude/gate-log/<YYYY-MM-DD>.jsonl`, named by the record's `ts` date in UTC |
| Format | one JSON object per line, UTF-8, newline-terminated, writer key set closed |
| Write | append only, never rewrite or delete; the writer creates the directory if missing |
| Serialize | one complete line per write; readers skip and count unparsable lines |
| Concurrency | multiple writers: take an exclusive lock on `~/.claude/gate-log/.lock` |

An evaluation is a line, so the day's file is the day's evaluations in order,
and equal `ts` is ordered by line: a reader must not re-sort a file. Writers emit
exactly the fields below; readers ignore unknown keys. Day files are write-date
buckets, not a sort key; a reader that needs a window reads every day file and
filters on `ts`. A non-empty line that does not parse still proves a writer ran:
count it as skipped and as a sibling. There is no Stop identifier, so the log
cannot prove that every gate wrote for a given Stop; absence is detected per gate
over a window, not per Stop.

| Field | Type | Meaning |
|---|---|---|
| `ts` | `YYYY-MM-DDTHH:MM:SSZ` | write time, UTC, second resolution |
| `session` | string | the hook payload's `session_id`, verbatim; `""` when the harness sends none |
| `gate` | `[a-z0-9-]+` | gate name; listed in `expected.txt` or reported as undeclared |
| `outcome` | `allow` / `warn` / `block` | what this evaluation decided |
| `reason` | string | one line, 200 code points max, rules joined with `; `; `""` on allow |

Newlines in `reason` are escaped, so one record stays one line.

```json
{"ts":"2026-10-21T00:12:44Z","session":"b8f2c1d4-77a0-4e0e-9d2b-1a2c3d4e5f60","gate":"rationalization","outcome":"warn","reason":"next-session hedging in transcript tail"}
```

The reference set is three gates, and `expected.txt` lists every gate that
should exist:

- `disk-space`: free space on the filesystem containing `~/.claude` below 15 GB, blocks.
- `learning-capture`: on a complex task, a stale growth-log blocks regardless of
  the count, as do 3+ stale non-growth-log learning files; 1-2 stale
  non-growth-log files warn. On a simple task it records `allow`.
- `rationalization`: hedging in the transcript tail, warns; never decides
  `block`. A crash is an evaluation error that exits 2.

## Window and verdicts

A window is a half-open UTC date range `[start, end)`, written as two
`YYYY-MM-DD` dates; the record's `ts` date must fall in it. The default is the
last seven complete UTC days. A report prints the window, so two reports are
comparable only when their windows match. Count `allows`, `warns`, and `blocks`
in that gate's records whose `ts` falls inside the window. The absence verdicts
below also describe the window but decide with the whole log: a gate that never
wrote and a gate that stopped writing differ only outside it, so a report reads
every day file.

| Verdict | Condition | Meaning |
|---|---|---|
| `measured` | blocks > 0, allows + warns > 0 | both sides observed; rate may be `null` |
| `satisfied` | blocks = 0, warns = 0, allows > 0 | no block; predicate may never fire |
| `warned` | blocks = 0, warns > 0 | warned, never blocked |
| `dead` | allows + warns = 0, blocks > 0 | every recorded evaluation blocked: held, or stuck |

`warned` keeps the middle visible, so a gate that only ever warns is not filed
as clean. `dead` alone is not proof of a defect: a condition that held
throughout blocks every time, and a forced pass writes no record, so a gate that
blocks once a turn and is then passed by the re-run also reads as dead. It never
passes on its own, but the turn does end. For a conditional gate, one simple
turn's allow prevents `dead`; `dead` is only reachable when every turn is
applicable and blocked. A gate that wrote before and has records in the window is
not absent, even if every record is only `allow`.

A gate that should be there and is not is a verdict too. The three are disjoint:
they split on whether this gate ever wrote, and on whether anything else ran in
the window.

| Verdict | Condition | Meaning |
|---|---|---|
| `missing` | in `expected.txt`, never wrote | never wired, not run yet, or writer failed early |
| `silent` | no record in window, wrote before, sibling wrote | stopped, or writer broke |
| `uncomputable` | no record in window, wrote before, no sibling wrote | nothing ran |

`missing` does not say which of never-wired, not-yet-run, and writer-failed
applies. A window with no evaluations makes every gate that has written before
`uncomputable`; a gate that has never written is still `missing` when
`expected.txt` lists it. `silent` cannot tell a gate that stopped being scheduled
from a writer that broke.
Absence verdicts are history-dependent: deleting or rotating day files resets
them; on a rename, keep both names for one window or remove the old name, or the
old name reads `silent` while it remains in `expected.txt`.

`expected.txt` lives at `~/.claude/gate-log/expected.txt`, one gate name per
line, created by hand at install and re-read on every report; blank lines and
`#` comments are ignored and repeats collapse. It is the union of every gate
installed on the machine, so append to it and never truncate another gate's
entry. The gate does not create it. If it is missing, the report prints
`expected.txt: absent`: `missing` is unavailable without a list, and the gates
that cannot be classified are reported as `unconfigured`. This is a report-level
state, not a fourth per-gate verdict. A gate that wrote before is still `silent`
or `uncomputable`, because those verdicts depend on history, not on the list. A
record for an unlisted gate is reported under its own name as undeclared and
counts as a sibling.

## Rates

`block_rate` is `blocks / (allows + warns + blocks)` for one gate over the same
window, warns kept in the denominator because they did not block. A report must
print the window, the evaluation count, the allow count, the warn count, the
last block time in the window, the last block time in the whole log, the skipped
line count, and the rate beside them. Both block-time fields print `none` when
no matching block exists. For example:

```
gate=learning-capture window=2026-10-24..2026-10-31 n=41 allows=38 warns=2 last_block_window=2026-10-29T08:11:02Z last_block_ever=2026-10-29T08:11:02Z skipped=0 block_rate=0.024
```

Round the rate to three decimals. Print `null` below 20 evaluations: one event
can move the ratio by 0.05 or more there, so the number would describe the
sample, and `0.0` or `1.0` is what a one-sided log prints too. A gate is
evaluated once per turn, so 20 evaluations is about 20 non-forced turns that
produced a record for this gate; interrupted turns, Stops where the hook never
ran, crashed gates, and failed writes contribute no record. A Stop in which one
gate crashes is partially evaluated and the other gates still write. A single
day is `null` unless the gate ran at least 20 times that day. Print
`insufficient (n=k)` beside a rate-bearing verdict below 20, so a one-record
`dead` or `satisfied` is not read as a health claim; absence verdicts carry no
rate label.

Logs written before this contract have no allow rows; every gate with only block
rows reads `dead`. Report the cutover date and do not compare rates across it.

This contract was written against Claude Code Stop hook behavior as of 2026-10;
re-check it if the harness changes.

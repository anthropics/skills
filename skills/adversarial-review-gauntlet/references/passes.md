# Passes in Detail

## G1 — Correctness (mechanical)

`scripts/gauntlet.sh --feature <name>` checks, in order:

1. **Spec trio exists** — `requirements.md`, `design.md`, `tasks.md` in the
   feature directory (default `.specs/<name>/`, override `--specs-dir`).
   Missing requirements stops the gauntlet here: nothing to trace.
2. **No unchecked tasks** — every `T<n>` in tasks.md is `[x]`. A task left
   `[ ]` without justification is a REJECT.
3. **Traceability gap-free** — delegates to the spec-driven-development
   checker (`check_traceability.py`, resolved automatically from the sibling
   skill or forced with `--trace-tool`). Exit 0 with a `## <name>: n/n`
   evidence line, or REJECT. Verdicts without evidence lines are refused
   (no vacuous PASS). In harness-layout repos, forward the table location:
   `--impl-glob 'harness/progress/impl_*.md'`.

Exit codes: `0` PASS, `1` REJECT (gaps listed), `2` usage error.

Semantic judgment — *does the test really verify the requirement?* — is NOT
G1's job. That is G2/G3 territory. G1 only proves the mapping exists.

## G2 — Adversarial (judgment)

Attack the feature before a user does:

- malicious input: injection, overflow, hostile encodings, huge payloads;
- boundary values: null, empty, zero, negative, duplicates, out-of-order;
- concurrency: races, double-submit, partial failure mid-operation;
- **test quality**: read the test bodies. A test that only imports a symbol,
  or asserts nothing, does not cover its requirement — it is a finding
  against the requirement it claims to protect.

## G3 — Maintainability (judgment)

- Does the change respect the repo's architecture and conventions docs?
- Is complexity reduced, not relocated? (SOLID where it reduces complexity —
  not as dogma.)
- No blanket `except`/`catch`, no swallowed errors; I/O stays at the edges.
- No debug prints, no context-free TODOs left behind.

## G4 — Evidence (mechanical-ish)

Everything the review claims must be on disk:

- G1 log saved (`gauntlet-g1.log` or the saved script output);
- G2/G3 findings logged with file references;
- the report file exists and follows
  [report-format.md](report-format.md);
- any referenced path resolves. A claim without a path is a finding.

## Findings: fixed or defended

Every finding gets one of two endings:

1. **Fixed** — goes back to the implementer as one batch; the gauntlet
   re-runs from G1 afterwards.
2. **Defended** — kept, with a one-line rationale naming the trade-off
   (e.g. "defended: 10k-concurrent lock adds latency we cannot afford at
   this write rate; single-writer design makes the race unreachable").
   A defended finding still counts as a pass, but a defense without a named
   trade-off is not a defense — it is an unaddressed finding.

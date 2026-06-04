# Integration testing for skills with live external dependencies

Guidance for white-box capability testing of skills that depend on
live external systems (browser DOM, CLI wrappers around authenticated
APIs, MCP connectors, filesystem watchers). These skills can't be
fully exercised by file-based evals alone: the interesting failure
modes are in the integration seam, not in the prompt or the
packaged inputs.

## When this applies

Use this pattern when the skill's correctness depends on any of:

- A connector or CLI whose response shape the skill parses (Google
  Workspace, Slack, GitHub, calendar APIs)
- A browser tab's DOM structure (live-caption scrapers, form fillers)
- A host filesystem layout the skill reads or writes
- Any external service whose behavior can drift independently of the
  skill's source

For self-contained skills (pure text transformation, document
generation from local inputs), the standard `evals/evals.json`
evals are sufficient and this file doesn't apply: their inputs can
be checked in as eval files and their outputs graded against
expectations.

## The `TESTS.md` state file

Keep one `TESTS.md` at the skill's root. It is a **state file, not a
journal**: each row describes the *current* state of one testable
capability. Update rows in place when a test runs or a finding lands.
Dated narrative belongs in your project's session log, not appended
here; a `TESTS.md` that accumulates dated sections stops answering
"what works right now" and starts requiring archaeology.

### Header

```
# TESTS — <skill-name>

Status is the current state of the code, not the last run's outcome.
Update the row in place when a test runs or a finding lands. Do not
append dated narrative sections.
```

### Capability matrix

One row per discrete, externally-observable capability the skill
claims (typically: each behavior named in the SKILL.md description or
a `## Triggers` line).

| capability | status | last run | fixture |
|---|---|---|---|
| short verb phrase naming the behavior | one of the four states below | `YYYY-MM-DD` or blank | path to fixture/sample input, or blank |

**Status values:**

- `PASS` — capability exercised against a fixture or live target on
  the last-run date and behaved as specified.
- `FAIL` — exercised and did not behave as specified; the Findings
  log (below) carries the detail.
- `CODED-NOT-VERIFIED` — code path exists and reads correct but has
  never been exercised end-to-end. Common for connector-dependent
  paths where no offline fixture exists yet.
- `NOT-TESTED` — capability is claimed in SKILL.md but no code path
  or test exists yet.

The four-state vocabulary is the point: it makes "we wrote it but
never ran it" (`CODED-NOT-VERIFIED`) and "we haven't written it"
(`NOT-TESTED`) visible as distinct from `FAIL`, which matters when
deciding whether a reinstall is safe.

### Gate

One paragraph stating which matrix rows must be `PASS` before the
skill is reinstalled or published. The reinstall/publish session
reads this section and blocks if any gated row is not `PASS`.

### Protocol

How to run the tests: the bash/node/python invocation, which fixtures
it reads, what `PASS` looks like in stdout. If the skill has an
`evals/evals.json`, name it here and state which matrix rows it
covers (evals cover end-to-end task behavior on checked-in inputs,
not the live integration seam).

### Offline regression

A snippet (or pointer to e.g. `lib/test-offline.js`) that exercises
every `PASS` row against checked-in fixtures with **no live connector
calls**. Run this before any reinstall when an edit touched `lib/` or
a SKILL.md section that a matrix row covers.

Building the offline harness usually means capturing one real
connector response per capability as a JSON fixture, then stubbing
the connector call to return the fixture. The fixture is the contract
with the external system; when the live system drifts, the fixture
diff shows exactly what changed.

### Findings log

Append-only; one dated line per `FAIL` or surprising `PASS`:

```
- YYYY-MM-DD <capability>: <one line>
```

Detail beyond one line goes to the project's session log with a
pointer here. This is the only journal-shaped section in the file,
and it's deliberately terse.

## Worked shape

A skill that scrapes live captions from a video-call browser tab and
writes them to a doc might have a matrix like:

| capability | status | last run | fixture |
|---|---|---|---|
| detect captions container in DOM | PASS | 2026-05-01 | fixtures/dom-snapshot-01.html |
| extract speaker name from caption node | PASS | 2026-05-01 | fixtures/dom-snapshot-01.html |
| dedupe partial caption updates | CODED-NOT-VERIFIED | | |
| append batch to target doc | PASS | 2026-04-28 | fixtures/append-payload-01.json |
| recover after tab reload | NOT-TESTED | | |

with a Gate of "rows 1, 2, 4 must be PASS" and an offline-regression
snippet that replays the three fixtures through the parser without
opening a browser.

## Relationship to `evals/evals.json`

`evals.json` runs end-to-end task evals: a prompt, optional
checked-in input files, and graded expectations. That works when
everything the skill needs can be packaged as eval files.
`TESTS.md` covers what those evals can't reach: behavior against
live external systems (authenticated connectors, a real browser
tab, a host filesystem), where the dependency can't be checked in
and can drift on its own. Skills with external dependencies need
both; self-contained skills only need `evals.json`.

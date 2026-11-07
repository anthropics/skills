# Traceability

Mandatory rule:

> **Every R\<n\> must map to exactly one test and at least one implementation
> artifact.**

## The table

While implementing, maintain a traceability table in the feature directory
(`.specs/<feature>/traceability.md`):

```markdown
# Traceability: <feature-name>

feature: <feature-name>

| Requirement | Test(s)              | Implementation file(s) | Status |
|-------------|----------------------|------------------------|--------|
| R1          | test_reject_5th_login | src/auth/failure.py   | done   |
| R2          | test_issue_token      | src/auth/token.py     | done   |
```

- Rows use the exact shape `| R<n> | tests | impl files | status |`.
- **Test identifier forms** the checker resolves (all relative to the tests
  directory):
  - bare name — matches a file stem (`test_auth` → `tests/test_auth.py`) or a
    Python function/class name (`test_reject_5th_login`);
  - JS/TS title — the bare name may also appear inside a
    `test('…name…')`/`it('…name…')` title;
  - node id — `tests/test_auth.py::test_reject_5th_login` (both halves
    verified).
  Dotted display names like `auth_test.R1` do NOT resolve: use the real test
  name.
- The `feature:` attribute line is optional in the feature directory (the
  directory scopes the table); it is required when tables live outside the
  feature directory (see below).
- Multiple test ids in one row are space- or comma-separated.
- A requirement's row is only `done` when its tests exist and pass.

## Verification

Run the checker before claiming any task batch is complete, and always before
requesting human approval at the Completion Gate:

```bash
python3 scripts/check_traceability.py --feature <feature-name>
# repo-wide audit:
python3 scripts/check_traceability.py --all
# machine-readable:
python3 scripts/check_traceability.py --feature <feature-name> --json
```

Exit codes: `0` covered, `1` gaps, `2` usage error. A `PASS` verdict means:

1. every R\<n\> in requirements.md appears in a table row;
2. every test identifier in the rows resolves to a real test under the tests
   directory (file stem, Python function/class, or JS/TS `test()`/`it()`
   title; `path::name` node ids are verified in both halves).

`[UNRESOLVED]` rows (status ≠ `done`) do not fail the run — work in progress is
not a gap — but a feature cannot be declared done with unresolved rows.

## Defaults and overrides

| Flag | Default | Meaning |
|---|---|---|
| positional `root` | current directory | repository root |
| `--specs-dir` | `.specs` | where feature directories live |
| `--tests-dir` | `tests` | where test identifiers are searched |
| `--impl-glob` | *(none)* | extra files to scan for tables, repeatable |

## Using inside a harness-managed repo

In a repo with the harness installed, specs live at `harness/specs/<feature>/`
and traceability tables live in `harness/progress/impl_*.md` with a
`feature: <name>` attribute line. Point the checker at that layout:

```bash
python3 scripts/check_traceability.py --feature <name> \
  --specs-dir harness/specs \
  --impl-glob 'harness/progress/impl_*.md'
```

Rows in impl-globbed files count only for the feature named in the file's
attribute line, so one global progress log can carry several features safely.

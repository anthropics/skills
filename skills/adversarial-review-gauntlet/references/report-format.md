# Report Format

The gauntlet's deliverable is a report file per feature, e.g.
`.specs/<name>/gauntlet.md` (or the repo's review-notes location — the
format is what matters):

```markdown
# Gauntlet — feature <name>

- G1 correctness: PASS (gauntlet.sh exit 0, <n>/<n> tasks done, traceability <m>/<m>)
- G2 adversarial: PASS (k findings, all fixed or defended below)
- G3 maintainability: PASS (gates green, conventions checked)
- G4 evidence: PASS (logs: <paths>)

## Findings
1. [G2] <description> — fixed in <file>
2. [G3] <description> — defended: <trade-off rationale>

## Skipped passes (trivial features only)
- G2: skipped (trivial) — <one-line reason>
- G3: skipped (trivial) — <one-line reason>
```

**Verdict rule: `PASS` if and only if every non-skipped pass line says PASS.**
Anything else rejects the completion request.

## Placement in the flow

| Reviewer | What they do with the report |
|---|---|
| Implementing session (self-review) | attach the report to the completion request; human reads it at the gate |
| Independent reviewer session | verify it: re-run G1 from the log paths, spot-check one finding, then countersign or reject |
| Human at the Completion Gate | the report is the agenda — four lines, then findings |

## Log hygiene

- One directory per feature, e.g. `logs/<feature>/gauntlet-g1.log`,
  `gauntlet-g23.log`; the report cites the paths.
- Re-running a command beats quoting a stale log — logs capture the verdict
  of a specific state; if the state changed, re-run and overwrite.
- A pass without a log is not a pass. If G2/G3 produced no findings, the log
  says so explicitly (`no findings — checklist walked on <files>`), because
  silence and laziness look identical from the outside.

# Learning loop: never miss the same kind of bug twice

Run this every time someone hands you a bug you didn't find (a "manual bug"), and every time you catch yourself in a process mistake (false alarm, over-rated severity, wrong status). The goal is not to remember *that bug*; it is to make the *class* of bug impossible to miss again, for every feature, by turning it into a mandatory check in the knowledge graph.

## Protocol

1. **Reproduce it.** Follow their steps on the current build. Capture evidence. If it doesn't reproduce, ask for the exact steps (or the recording's action and timing) before going further — don't learn from a ghost.

2. **Locate the miss.** Answer, with evidence from your own run:
   - Was the surface in the inventory / coverage matrix? (`coverage.py report` and the inventory JSON)
   - Was a check required for it? Was that check run? What did it observe?
   - Was the expectation in the baseline at the time?

3. **Classify the cause** (exactly one primary):
   | Cause | Signal | Typical fix |
   |---|---|---|
   | `coverage-gap` | the surface/state was never exercised | add the surface type to the inventory/grid; a check that forces exercising it |
   | `oracle-gap` | exercised, but nothing judged it wrong | a new or sharper oracle |
   | `baseline-gap` | the expectation wasn't in the checklist (new or unread requirement) | add the source (thread, PRD section) to the baseline step |
   | `probe-error` | the script measured the wrong thing | a probe self-check (screenshot + real action) |
   | `instrument-gap` | the tool couldn't observe it (DOM vs pixels, timing vs frames) | build/extend a script; add a positive control |
   | `judgement` | seen but wrongly dismissed or mis-rated | a rule for the decision (reachability, status, ask-first) |

4. **Generalise.** Write the lesson at the level of the class, not the instance:
   - not "the Priority column shows numbers" → "anything hidden by default is still product; turn every option on once";
   - not "Open Secrets is broken" → "a label is a promise about where it goes; click every CTA on every state".
   Ask: *what else in this product, and in any product, has the same shape?*

5. **Record it** in the knowledge graph so it becomes mandatory everywhere that surface type exists:
   ```bash
   python3 scripts/kb.py add-miss --bug "<PRODUCT>:<ID>" --title "<what was wrong>" --product "<product>" \
     --found-by <user|dev|self> --surface <surface-type> --cause <cause> \
     --lesson "<generalised rule>" --check "<concrete, executable check>" --check-id <short-id> --oracle <O#>
   python3 scripts/kb.py render     # refresh knowledge/GRAPH.md
   ```
   Reuse an existing `--check-id` when the check already exists but was not applied — that strengthens it (adds the surface) instead of duplicating it. If the cause is `instrument-gap`, build or extend the script now and add a positive control to it. If it's a new oracle, append it to `references/oracles.md`.

6. **Prove it.** If the miss is observable in a browser, add a minimal fixture to `selftest/fixtures/` that reproduces it and a test in `selftest/build_selftest.py` that runs the skill's own script against it (with a negative control where possible); if it's a judgement/probe/status mistake, add a case to `selftest/selftest.py` that the pre-report gate must block. Run the self-test; the new test must pass and nothing else may break.

7. **Apply it now, retroactively.** Run `coverage.py report <feature>`: the new check appears as required cells on every matching item. Execute it across the current feature to find **siblings** (other hidden columns, other CTAs, other loading paths). Report siblings as new bugs.

8. **Close the loop with the user.** Tell them: why it was missed (cause), the rule learned, the check added, which surfaces it now covers, and what the sibling sweep found. Credit the person who found it in the report.

## Before every future test run

- `python3 scripts/kb.py checks` — read every mandatory check; they go into the plan.
- `python3 scripts/kb.py misses` — skim past misses; ask "does this feature have that shape?"
- Sign-off requires `coverage.py report` to exit 0, which means every check learned from a past miss was run on every matching surface (or excluded with a reason).

## Surface types used in the graph
`cta`, `navigation`, `form-field`, `hidden-option`, `list`, `overview`, `run-state`, `error-state`, `copy`, `actor`, `integration`, `theme`, `loading`, `live-view`, `api`, `retest`. Add a new type when a bug lives on something none of these describe, and map inventory kinds to it in `coverage.py` (`KIND_TO_SURFACE`) if it's discoverable from the UI.

# phase_prompts/

Externalized phase prompt bodies for the Quality Playbook.

v1.5.4 F-1 (Bootstrap_Findings 2026-04-30) extracted these from
`bin/run_playbook.py`'s inline string templates so both execution
modes — UI-context skill-direct (a coding agent walking through
SKILL.md inline) and CLI-automation runner-driven (`python -m
bin.run_playbook`) — read from the same single source of truth.
Without externalization the two modes drift; with it, an edit to a
phase prompt lands once and benefits both.

## File layout

- `phase1.md` ... `phase6.md` — one file per pipeline phase. Loaded
  by `bin/run_playbook.py::_load_phase_prompt`.
- `single_pass.md` — the legacy single-prompt invocation (used when
  the operator wants the LLM to drive all six phases inline rather
  than via the per-phase orchestrator).
- `iteration.md` — the iteration-strategy prompt (gap, unfiltered,
  parity, adversarial — see `bin/run_playbook.py::next_strategy`).

## Substitution conventions

Most files are pure-literal markdown — the loader returns them
unchanged. Three files use `str.format()` substitution with named
placeholders:

- `phase1.md` — `{seed_instruction}` (skip Phase 0/0b prelude when
  `--no-seeds`) and `{role_taxonomy}` (rendered from
  `bin.role_map.ROLE_DESCRIPTIONS`).
- `single_pass.md` — `{skill_fallback_guide}` and
  `{seed_instruction}`.
- `iteration.md` — `{skill_fallback_guide}` and `{strategy}`.

Inside files that go through `.format()`, JSON braces and other
literal `{` / `}` characters MUST be doubled (`{{` / `}}`) per
Python's format-string escaping rules. Pure-literal files do not
need any escaping.

## Editing discipline

When you change a phase prompt, the loader picks up the new content
at the next invocation — there is no caching layer to invalidate. The
test suite at `bin/tests/test_phase_prompts_externalized.py` pins the
loader's contract; if you add a new substitution variable, extend
those tests.

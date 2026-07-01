# ECL Schema v2

## Normalized Case JSON

`scripts/render_obsidian_bundle.py` expects a JSON object with this top-level shape:

```json
{
  "bundle_version": 2,
  "title": "Short case title",
  "slug": "optional-case-slug",
  "date": "YYYY-MM-DD",
  "mode": "spec",
  "source_request": "verbatim user request",
  "request_language": "optional, inferred from source_request when omitted",
  "output_language": "optional, defaults to request language",
  "summary": "optional overview summary",
  "final_outcome": "optional readiness statement",
  "project_paths": ["/abs/path"],
  "repo_paths": ["/abs/path"],
  "vault_root": "/abs/path/to/vault",
  "output_root": "/abs/path/to/base/folder",
  "stages": {
    "preprocess": {},
    "divergence": {},
    "requirements": {},
    "critique": {},
    "closure": {},
    "probes": {},
    "red_blue": {},
    "review": {}
  },
  "artifacts": {
    "constraint_ledger": {},
    "code_handoff": {}
  }
}
```

Use `scripts/scaffold_case_json.py` when you want a starter JSON from a raw request.

## Structured Block Names

- `ecl.case`
- `ecl.constraint_ledger`
- `ecl.preprocess`
- `ecl.options`
- `ecl.requirements`
- `ecl.conflicts`
- `ecl.dependencies`
- `ecl.probes`
- `ecl.adversarial`
- `ecl.review`
- `ecl.compile_for_code`
- `ecl.code_handoff`
- `ecl.canonical_contracts`
- `ecl.constraint_crosswalk`
- `ecl.execution_manifest`
- `ecl.code_batches`
- `ecl.code_preflight`
- `ecl.final_handoff`
- `ecl.code_run`
- `ecl.code_verification`
- `ecl.reentry_request`
- `ecl.achieve`

## Required Code Handoff Fields

`ecl.code_handoff` must contain:

- `status`
- `code_ready`
- `handoff_summary`
- `retained_goal`
- `implementation_scope`
- `repo_targets`
- `repo_grounding`
- `read_first`
- `frozen_product_decisions`
- `domain_model`
- `data_contract`
- `ui_contract`
- `function_contracts`
- `file_plan`
- `implementation_units`
- `verification_commands`
- `browser_checks`
- `acceptance_checks`
- `allowed_decisions`
- `forbidden_decisions`
- `reentry_triggers`
- `reopen_stage_map`
- `unresolved_gaps`

### `function_contracts`

Each function contract should include:

- `id`
- `name`
- `kind`
- `location`
- `signature`
- `purpose`
- `inputs`
- `outputs`
- `side_effects`
- `invariants`
- `failure_modes`

### `file_plan`

Each file-plan item should include:

- `path`
- `action`
- `why`
- `depends_on`

### `implementation_units`

Each implementation unit should include:

- `id`
- `title`
- `objective`
- `scope`
- `files`
- `functions`
- `depends_on`
- `verification`
- `done_when`

## Handoff Truth Gate

`code_ready` must exist only in `ecl.code_handoff`.

If `code_ready=true`, all of the following must be true:

- repo targets are present
- repo grounding is explicit
- frozen product decisions are explicit
- domain, data, and UI contracts are explicit
- function contracts are explicit
- file plan is explicit
- implementation units are non-empty
- verification commands are non-empty
- browser checks are non-empty for user-visible work
- acceptance checks are non-empty
- unresolved gaps is empty

If any high-impact meaning is left to the coder, keep `code_ready=false`.

## Required Achieve Fields

`ecl.achieve` must contain:

- `status`
- `run_id`
- `verdict`
- `archive_status`
- `archive_reason`
- `acceptance_results`
- `verification_summary`
- `residual_issues`
- `next_actions`
- `archive_refs`
- `evidence_refs`

### `archive_status`

Allowed values:

- `archived`
- `left_open`

### Achieve Closure Rules

- if `verdict` is `achieved` or `achieved_with_followups`, `archive_status` should be `archived`
- if `verdict` is `not_achieved`, `archive_status` should be `left_open`
- `archive_reason` should explain why the case was archived or left open

## Recommended Code Preflight Fields

`ecl.code_preflight` is the shared execution workboard that sits beside the frozen handoff.

It should contain at least:

- `status`
- `confirmed`
- `do_not_reinvent`
- `do_first`
- `context_bundle`
- `progress_snapshot`
- `current_focus`
- `remaining_work`
- `pause_conditions`
- `session_notes`

Use it for execution-state updates only. Do not treat it as a replacement for `ecl.code_handoff`.

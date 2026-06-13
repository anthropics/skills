# ECL Schema v2

## 规范化 Case JSON

`scripts/render_obsidian_bundle.py` 期望一个具有以下顶层结构的 JSON 对象：

```json
{
  "bundle_version": 2,
  "title": "简短 case 标题",
  "slug": "可选-case-slug",
  "date": "YYYY-MM-DD",
  "mode": "spec",
  "source_request": "用户原始请求原文",
  "request_language": "可选，省略时从 source_request 推断",
  "output_language": "可选，默认为请求语言",
  "summary": "可选概述摘要",
  "final_outcome": "可选就绪声明",
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

当需要从原始请求生成起始 JSON 时，使用 `scripts/scaffold_case_json.py`。

## 结构化块名称

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

## 必需的 Code Handoff 字段

`ecl.code_handoff` 必须包含：

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

每个函数契约应包含：

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

每个文件计划项应包含：

- `path`
- `action`
- `why`
- `depends_on`

### `implementation_units`

每个实现单元应包含：

- `id`
- `title`
- `objective`
- `scope`
- `files`
- `functions`
- `depends_on`
- `verification`
- `done_when`

## Handoff 真相门

`code_ready` 只能存在于 `ecl.code_handoff` 中。

如果 `code_ready=true`，以下全部必须为 true：

- 仓库目标已提供
- 仓库落地已明示
- 冻结产品决策已明示
- 领域、数据和 UI 契约已明示
- 函数契约已明示
- 文件计划已明示
- 实现单元非空
- 验证命令非空
- 对用户可见的工作，浏览器检查非空
- 验收检查非空
- 未解决缺口为空

如果任何高影响含义留给编码者决定，保持 `code_ready=false`。

## 必需的 Achieve 字段

`ecl.achieve` 必须包含：

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

允许值：

- `archived`
- `left_open`

### Achieve 关闭规则

- 如果 `verdict` 是 `achieved` 或 `achieved_with_followups`，`archive_status` 应为 `archived`
- 如果 `verdict` 是 `not_achieved`，`archive_status` 应为 `left_open`
- `archive_reason` 应解释该 case 为何被归档或保持打开

## 推荐的 Code Preflight 字段

`ecl.code_preflight` 是位于冻结交接包旁的共享执行工作台。

它应至少包含：

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

仅用于执行状态更新。不要将其视为 `ecl.code_handoff` 的替代品。

# 实现说明

## 仓库结构

```text
evolutionary-constraint-development/
  SKILL.md              # Claude Code Skill 主入口
  README.md             # English README
  README.zh-CN.md       # 中文 README
  agents/               # Claude Code Agent 接口定义
  scripts/              # Python CLI 辅助脚本
  templates/            # Bundle markdown 模板
  references/           # Playbook 和质量门槛（已适配 Claude Code）
  schemas/              # ECL v2 schema
  docs/                 # 技术文档（中英双语）
```

## 等级架构 `[v1.1]`

ECD v1.1 引入了三级复杂度路由系统。分类器在任何阶段执行之前运行。

### 分类器

三个静默问题决定等级：

1. **Q1 代码影响面：** ≤3文件=L1, 4-10=L2, >10=L3
2. **Q2 安全/正确性风险：** 仅UI=L1, 功能逻辑=L2, 数据/认证/支付=L3
3. **Q3 需求清晰度：** 模糊 → 强制L3

`最终等级 = max(Q1, Q2, Q3)`。已有 bundle 中缺失 tier 字段默认视为 L3（Full）。

### 各级 Bundle 布局

| 等级 | 产物文件 |
|------|---------|
| **L1 Lite** | `00-overview.md`, `05-constraint-ledger.md` (lite), `10-a-preprocess.md` (lite), `90-code-handoff.md` (lite), `97-code-preflight.md`, `Runs/` |
| **L2 Standard** | L1 文件（非lite模板） + `20-b-divergence.md`, `30-c-requirements.md`, `50-e-closure.md`，可选 `40-d-critique.md`, `80-h-review.md` |
| **L3 Full** | 全部 17 个文件（与 v1.0 相同，不变） |

### code_ready 门控分级

- **L1：** 交接包冻结 4 个面（repo_grounding, frozen_product_decisions, file_plan, implementation_units）。跳过伴侣文档。
- **L2：** 交接包冻结全部必需面。伴侣文档可选（91/92/95/96）。
- **L3：** 完整交接质量门槛加全部伴侣文档（与 v1.0 相同）。

### 校验器的等级感知

`validate_ecl_bundle.py` 当前对 L3 检查全部 17 个文件。对 L1/L2 bundle 仅检查等级对应的文件。此项留待后续脚本更新。

## 运行模型

ECD 有两层：

- **Skill 层**（`SKILL.md`）定义模型该如何行为——工作流合同、阶段职责、交接质量门槛、子 Agent 协议。
- **Script 层**（`scripts/`）负责渲染、校验和记录产物——不替代推理，只把推理变成可检查、可审计的结构。

## CLI 架构

### `scripts/ecd.py`

这是公开暴露的 CLI 入口。它通过子命令编排管道：

- `scaffold` — 从原始请求创建 normalized case JSON
- `pre` — scaffold → render → validate → OpenSpec（Stage A 初始化）
- `plan` — render → validate → OpenSpec（需要 Stage A complete）
- `code` — validate → gate 检查 → render run record → validate
- `achieve` — validate → gate 检查 → render achieve note → validate

每个子命令在每次操作后都重新校验。管道在第一个非零返回值处终止。

内部调用链：

```
ecd.py
  ├── scaffold_case_json.py    # 创建 case JSON scaffold
  ├── render_obsidian_bundle.py # 将 case JSON 渲染为 Obsidian 笔记包
  ├── validate_ecl_bundle.py   # 校验 bundle 完整性和一致性
  ├── render_code_run.py       # 渲染 code 运行记录
  ├── render_achieve_note.py   # 渲染 achieve 判定笔记
  └── render_openspec_pack.py  # 渲染 OpenSpec 兼容输出
```

### `scripts/render_canvas.py`

渲染 Obsidian Canvas 概览文件（可选）。

## 结构化块系统

每个 markdown bundle 文件包含一个 JSON 或 YAML 围栏代码块，键如 `ecl.case`、`ecl.preprocess`、`ecl.code_handoff` 等。这些块是真实数据源——脚本通过 `parse_json_fence()` / `find_named_block()` 解析它们。

`validate_ecl_bundle.py` 为每个阶段和产物的每个结构化块定义了完整的必需字段 schema（`REQUIRED_FIELDS` 字典），以及跨块一致性规则。

当以编程方式更改 case 数据时，编辑 `scaffold_case_json.py` 中 `build_payload()` 的结构化 JSON，而不是编辑渲染 markdown 模板的逻辑。

## Bundle 布局

- 9 个阶段文件：`10-a-preprocess.md` 到 `98-j-compile-for-code.md`
- 8 个产物文件：`05-constraint-ledger.md`、`90-code-handoff.md`、`91`/`92`/`95`/`96`/`97`/`99`-*.md
- 1 个概览文件：`00-overview.md`
- 运行记录：`Runs/<run-id>/00-code-run.md`、`01-verification.md`、`02-reentry.md`、`03-achieve.md`

两个关键文件主导工作流：
- `05-constraint-ledger.md`：共享规划真值面
- `90-code-handoff.md`：唯一的 `code` 入口点

## 语言检测

系统从请求文本自动检测语言（`en` vs `zh-CN`，通过 `CJK_RE` 正则），可通过 case JSON 中的 `output_language` 覆盖。所有渲染脚本的 `TEXT` 字典中都有双语标签。

## Claude Code 集成点

| ECD 原语 | Claude Code 工具 |
|----------|-----------------|
| 独立子 Agent (D/G/H/J) | `Agent` — `subagent_type: "general-purpose"` |
| 仓库落地 | `Read` / `Glob` / `Grep` / `codegraph_*` |
| 运行脚本和验证 | `Bash` |
| 代码修改 | `Edit` / `Write` |
| 进度跟踪 | `TaskCreate` / `TaskUpdate` |
| 结构化审批门 | `EnterPlanMode` / `ExitPlanMode` |
| 运行记录 | `Write` 到 `Runs/<run-id>/` 下的 markdown 文件 |

## 依赖

- Python 3.10+
- 可选：`pyyaml`（用于 YAML 块解析和 schema 加载）

## 许可

MIT

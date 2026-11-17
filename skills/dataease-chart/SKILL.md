---
name: dataease-chart
description: 自动化部署 DataEase v2 图表和多图表看板。支持柱状图 (bar)、折线图 (line)、饼图 (pie) 和明细表 (table_info)。
environment:
  required:
    - DATAEASE_ACCESS_KEY
    - DATAEASE_SECRET_KEY
    - DATAEASE_BASE_URL
security:
  requiresSecrets: true
  sensitiveEnvironment: true
  externalNetworkAccess: true
---

# DataEase V2 Chart Skill 指南

该 Skill 赋能 AI Agent 直接通过 API 在 DataEase v2 中创建、配置并部署可视化仪表板。它能够自动处理数据集关联、字段映射及布局计算。

## 🎭 沟通风格要求 (Persona)

作为 DataEase 自动化专家，你的回复应当：
1. **执行优先**: 严禁在执行 `inspect_data` 或 `deploy` 指令前向用户进行任何口头确认或展示即将运行的代码块。直接运行相关工具，并在获得结果后统一汇报。
2. **专业且严谨**: 减少口语化表述（如“哈哈”、“老板”、“抓到原因了”）。
3. **结果导向**: 优先展示执行结果（URL、ID），再简要说明关键逻辑（如字段映射）。
4. **单次往复**: 你的目标是在单次交互中完成从“探索数据”到“部署看板”的全过程，不要因为查询到了中间结果而中断执行。

## 🚀 快速开始与环境配置

首次使用或环境未就绪时，**必须引导用户配置凭据**：

1. **检查 .env**: 确认项目根目录是否存在 `.env` 文件。
2. **引导配置**: 若缺少凭据，请告知用户执行以下操作：
   - 将 `.env.example` 拷贝为 `.env`。
   - 填写 `DATAEASE_ACCESS_KEY`, `DATAEASE_SECRET_KEY`, `DATAEASE_BASE_URL`。
3. **验证凭据**: 配置完成后，运行 `python3 scripts/inspect_data.py --list-datasets` 验证连通性。

## 🔎 数据探索指南 (重要)

当你不确定数据集名称或字段名时，**必须先执行数据查询指令**，不要盲目猜测：

### 1. 查询所有可用数据集
```bash
python3 scripts/inspect_data.py --list-datasets
```

### 2. 查询特定数据集的字段
```bash
python3 scripts/inspect_data.py --dataset "<数据集名称或ID>"
```
- **关键**: 拿到字段名和类型后，再根据业务逻辑匹配 `x_axis` 和 `y_axis`。

## 💡 核心指令指南

当用户提出可视化需求时，请优先判断是“单图表”还是“多图表看板”：

### 1. 部署单图表
适用于用户明确要求创建一个特定图表的场景。
```bash
python3 scripts/deploy.py <type> <title> <dataset> <x_fields> <y_fields>
```
- **示例**: "帮我用销售数据集创建一个柱状图，展示各门店的销售额"
- **执行**: `python3 scripts/deploy.py bar '各门店销售额' '销售数据集' '门店' '销售额'`

### 2. 部署多图表看板 (AI 推荐模式) 🚀
适用于用户需求较模糊（如“分析下这个数据”）、涉及多个指标对比、或明确要求创建仪表板/看板的场景。
```bash
python3 scripts/multi_deploy.py <dashboard_title> '<charts_json_config>'
```
- **JSON 结构**: `[{"type": "...", "title": "...", "dataset_name": "...", "x_axis": ["..."], "y_axis": ["..."]}]`
- **自动布局**: 引擎默认按两列自动排列，无需手动传入 `layout`。
- **示例**: "帮我分析下电商数据集，我想看平台访问、转化阶段和产品分布"
- **执行**: `python3 scripts/multi_deploy.py '电商深度分析看板' '[{"type":"bar","title":"平台访问量","dataset_name":"电商数据","x_axis":["平台"],"y_axis":["访问量"]},{"type":"pie","title":"转化阶段占比","dataset_name":"电商数据","x_axis":["阶段"],"y_axis":["次数"]},{"type":"bar","title":"产品分布","dataset_name":"电商数据","x_axis":["产品"],"y_axis":["销量"]}]'`

## 🛠 参数规范

- **图表类型 (`type`)**: `bar` (柱状图), `line` (折线图), `pie` (饼图), `table_info` (明细表)。
- **维度与指标**:
    - 维度 (`x_axis`): 通常是类别、日期等文本/日期字段。
    - 指标 (`y_axis`): 通常是金额、次数、百分比等数值字段。
    - *提示*: 如果是明细表，`y_axis` 传空，`x_axis` 传入所有需要展示的列名。
- **数据集**: 支持传入数据集名称（如“门店销售数据”）或 19 位 DataEase ID。

## ⚠️ 智能避坑指南

1. **自动清理**: 引擎会自动移除模板中残留的 "访问平台"、"访问次数" 等演示文案，请放心使用真实的业务字段名。
2. **多指标支持**: `y_axis` 支持传入逗号分隔的多个字段（如 `'销售额,利润'`），但在多图表配置中应使用数组形式 `["销售额", "利润"]`。
3. **环境检查**: 确保 `.env` 文件中已配置 `DATAEASE_BASE_URL` 等必要凭据。

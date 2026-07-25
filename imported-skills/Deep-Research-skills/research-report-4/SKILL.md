---
name: research-report
user-invocable: true
description: 将deep调研结果汇总为markdown报告，覆盖所有字段，跳过不确定值。
allowed-tools: Read, Write, Glob, Bash, AskUserQuestion
---

# Research Report - 汇总报告

## 触发方式
`/research-report`

## 执行流程

### Step 1: 定位结果目录
在当前工作目录查找 `*/outline.yaml`，读取topic和output_dir配置。

### Step 2: 扫描可选摘要字段
读取所有JSON结果，提取适合在目录中显示的字段（数值型、简短指标），例如：
- github_stars
- google_scholar_cites
- swe_bench_score
- user_scale
- valuation
- release_date

使用AskUserQuestion询问用户：
- 目录中除了item名称外，还需要显示哪些字段？
- 提供动态选项列表（基于实际JSON中存在的字段）

### Step 3: 生成Python转换脚本
在 `{topic}/` 目录下生成 `generate_report.py`，脚本要求：
- 读取output_dir下所有JSON
- 读取fields.yaml获取字段结构
- 覆盖每个JSON的所有字段值
- 跳过值包含[不确定]的字段
- 跳过uncertain数组中列出的字段
- 生成markdown报告格式：目录（带锚点跳转+用户选择的摘要字段）+ 详细内容（按字段分类）
- 保存到 `{topic}/report.md`

**目录格式要求**：
- 必须包含每一个item
- 每个item显示：序号、名称（锚点链接）、用户选择的摘要字段
- 示例：`1. [GitHub Copilot](#github-copilot) - Stars: 10k | Score: 85%`

#### 脚本技术要点（必须遵循）

**1. JSON结构兼容**
支持两种JSON结构：
- 扁平结构：字段直接在顶层 `{"name": "xxx", "release_date": "xxx"}`
- 嵌套结构：字段在category子dict中 `{"basic_info": {"name": "xxx"}, "technical_features": {...}}`

字段查找顺序：顶层 -> category映射key -> 遍历所有嵌套dict

**2. Category多语言映射**
fields.yaml的category名与JSON的key可能是任意组合（中中、中英、英中、英英）。必须建立双向映射：
```python
CATEGORY_MAPPING = {
    "基本信息": ["basic_info", "基本信息"],
    "技术特性": ["technical_features", "technical_characteristics", "技术特性"],
    "性能指标": ["performance_metrics", "performance", "性能指标"],
    "里程碑意义": ["milestone_significance", "milestones", "里程碑意义"],
    "商业信息": ["business_info", "commercial_info", "商业信息"],
    "竞争与生态": ["competition_ecosystem", "competition", "竞争与生态"],
    "历史沿革": ["history", "历史沿革"],
    "市场定位": ["market_positioning", "market", "市场定位"],
}
```

**3. 复杂值格式化**
- list of dicts（如key_events, funding_history）：每个dict格式化为一行，用` | `分隔kv
- 普通list：短列表用逗号连接，长列表换行显示
- 嵌套dict：递归格式化，用分号或换行显示
- 长文本字符串（超过100字符）：添加换行符`<br>`或使用blockquote格式，提高可读性

**4. 额外字段收集**
收集JSON中有但fields.yaml中没定义的字段，放入"其他信息"分类。注意过滤：
- 内部字段：`_source_file`, `uncertain`
- 嵌套结构顶级key：`basic_info`, `technical_features`等
- `uncertain`数组：需要逐行显示每个字段名，不要压缩成一行

**5. 不确定值跳过**
跳过条件：
- 字段值包含`[不确定]`字符串
- 字段名在`uncertain`数组中
- 字段值为None或空字符串

### Step 4: 执行脚本
运行 `python {topic}/generate_report.py`

## 输出
- `{topic}/generate_report.py` - 转换脚本
- `{topic}/report.md` - 汇总报告

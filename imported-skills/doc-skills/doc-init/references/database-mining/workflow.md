# Database Mining Workflow

本文是 `doc-init` 的内部数据库证据子流程，不是独立 skill。目标不是导出数据库字典，也不是一上来全库画像，而是渐进提炼「真实数据库事实如何影响 AI 写代码」。

本文中的 `<DOC_INIT_DIR>` 指 `doc-init/SKILL.md` 所在目录。执行脚本时先解析该目录；不要把维护者本机路径写入项目文档或命令示例。

## 核心规则

- 全程只读：只允许元数据查询和 `SELECT`，禁止写 SQL、DDL、锁表和破坏性操作。
- 用户已授权数据库挖掘时，缺少本地驱动或轻量客户端可直接安装到 skill-local 环境；不要安装大型 GUI 工具，不做系统级不可回收改动。
- 默认按测试环境处理，连接配置和值样本保持完整可见。只有用户明确要求脱敏、或当前上下文明确不是测试数据时，才启用脚本的 `--mask-sensitive`。
- 数据库方言差异由脚本、驱动和模型现场处理，不为常见数据库建立百科式 reference。
- 默认只做 catalog：表清单、字段清单、主键/索引粗信息、注释；不默认扫数据，不默认 `count(*)` / `count(distinct)` / 全库 profile。
- 只有具体业务域、表或字段明确后，才调用 `sample-table` / `analyze-field` 做细扫。
- 用户目标若是「目录级」「catalog-only」「只获取表/字段目录」「辅助领域划分」，执行到 catalog / classify-catalog / plan-domain-scan / summarize-catalog 即停止；不要自动 sample。
- 脚本必须跨平台优先：核心能力用 Python 实现，不依赖 bash、grep、sed、awk、rsync、timeout 或 Unix-only 路径。
- 关键表在领域细扫阶段必须逐字段分析；非关键表只做 catalog。

## 读取顺序

按任务阶段选择性读取，不要一次性把所有 reference 塞入上下文：

- 发现连接来源前读 `references/database-mining/config-discovery.md`。
- 连接和采样前读 `references/database-mining/safety-and-sampling.md`。
- 领域细扫和逐字段分析前读 `references/database-mining/critical-table-analysis.md`。
- 需要输出证据包时读 `references/database-mining/evidence-pack-format.md`。

## Step 1 — 发现连接来源

先识别项目生态，再扫描配置、环境变量模板、容器/部署文件、ORM/数据源初始化代码和 secret 引用。

```bash
python3 <DOC_INIT_DIR>/scripts/db_miner.py discover-config --root .
```

若扫不到连接且任务需要数据库事实，向用户说明只读用途并请求连接串或本地连接名。用户明确要求不要提问时，输出「缺少数据库证据」的低置信说明。

## Step 2 — 建立只读与采样边界

连接前确认：

- 查询限制、采样上限和超时策略已确定。
- 是否需要脱敏；默认不脱敏，只有明确需要时给脚本加 `--mask-sensitive`。
- 当前任务是否允许安装轻量依赖；若允许，优先使用本地虚拟环境或用户级包，不安装 GUI。

## Step 3 — 轻量 catalog

使用项目已有工具、系统已有客户端或 `scripts/db_miner.py`。脚本支持 SQLite 原生；其他数据库优先走 SQLAlchemy URL 和已安装 driver。Windows 可用 `py -3` 替代 `python3`。

```bash
python3 <DOC_INIT_DIR>/scripts/db_miner.py test-connection --url '<readonly-url>'
python3 <DOC_INIT_DIR>/scripts/db_miner.py catalog --url '<readonly-url>' --output db-catalog.json
```

可以把测试环境连接来源写入证据包，方便后续复用；如果用户要求脱敏，则只保留脱敏来源。

catalog 只用于建立数据库地图，辅助业务域划分和候选关键表判断；禁止在这一步做全库数据画像。

## Step 4 — 目录语义理解与领域细扫计划

```bash
python3 <DOC_INIT_DIR>/scripts/db_miner.py classify-catalog --catalog db-catalog.json --output db-domain-hints.json
python3 <DOC_INIT_DIR>/scripts/db_miner.py plan-domain-scan --catalog db-catalog.json --domain customer --keywords user,member,customer --output db-domain-plan.json
python3 <DOC_INIT_DIR>/scripts/db_miner.py summarize-catalog --catalog db-catalog.json --domain-hints db-domain-hints.json --domain-plan db-domain-plan.json --output db-catalog-summary.json
```

这一步主要由模型语义理解表名、字段名、注释和代码入口：判断业务域、候选关键表、后续哪些表需要细扫。脚本只给候选提示，不替代模型判断。

目录级 / catalog-only 任务用 `summarize-catalog` 收口：它只读取已生成的 catalog / domain hints / domain plan JSON，不连数据库、不读行级数据、不做统计。不要为了写报告临时编写大量解析脚本；若摘要不够，把缺口列为后续领域 KB 生成前的细扫项。

## Step 5 — 领域/表/字段级深挖

先判定关键表，再对关键表逐字段分析：

- 字段结构：类型、注释、默认值、nullable、索引参与。
- 代码入口：Entity/Mapper/SQL/Service/Flow/Job 中如何读写。
- 数据事实：少量真实样本值、样本中的 NULL/空字符串/特殊 sentinel 值、样本中的枚举候选、明显极值和时间格式。
- 业务判断：字段真实语义、反常规设计、与代码枚举是否一致。
- AI 易错点：忽略该字段会写错什么。
- 落档位置：目标 KB/Guide 章节。

```bash
python3 <DOC_INIT_DIR>/scripts/db_miner.py sample-table --url '<readonly-url>' --catalog db-catalog.json --tables table_a,table_b --sample-rows 30 --output db-samples.json
python3 <DOC_INIT_DIR>/scripts/db_miner.py analyze-field --url '<readonly-url>' --catalog db-catalog.json --field table_a.status --sample-rows 50 --output db-field-status.json
```

默认 sample-first，不做全表统计。只有用户明确要求统计，或字段语义必须依赖统计时，才显式加统计选项；不要让 count 成为默认路径。

关键表字段多也不能只挑显眼字段；可分批，但必须在证据包里标注哪些字段已分析、哪些字段未分析。

## Step 6 — 输出证据包

```bash
python3 <DOC_INIT_DIR>/scripts/db_miner.py export-evidence \
  --catalog db-catalog.json \
  --domain-plan db-domain-plan.json \
  --samples db-samples.json \
  --output db-evidence-pack.json
```

证据包必须回答：

- 哪些业务域被数据库事实补强。
- 哪些业务域只用了 catalog，哪些业务域做了表/字段级深挖。
- 哪些字段存在特殊语义、历史兼容值或反常规设计。
- 哪些发现应进入领域 KB，哪些应成为公共 Guide 候选。
- 哪些结论低置信，需要用户或运行时继续确认。

## 与项目文档协作

用于 `doc-init` 时，数据库证据只补强业务域知识网络：表和字段入口写入对应领域 KB，跨领域分表/字典/配置/流程机制写入 Guide，缺少连接或访问失败写入自评的「缺少真实数据口径」。

用于后续文档同步或日常开发时，围绕当前模块、表、字段或 bug 生成小证据包，只沉淀可复用业务事实，不把一次性查询结果写成长期文档。

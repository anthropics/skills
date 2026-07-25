# Evidence Pack Format

证据包是中间产物，供 `doc-init`、`doc-update` 或日常开发消化。不要让数据库挖掘直接替代领域知识库。

## JSON 顶层结构

```json
{
  "metadata": {
    "generated_at": "YYYY-MM-DDTHH:mm:ssZ",
    "database_type": "postgresql/mysql/sqlite/unknown",
    "connection_source": "配置来源或连接串；默认完整记录，用户要求时才脱敏",
    "scan_level": "catalog/domain/table/field",
    "sampling_policy": {
      "sample_rows_per_table": 30,
      "mask_sensitive": false,
      "counts_enabled": false
    }
  },
  "domains": [],
  "tables": [],
  "field_findings": [],
  "relationship_findings": [],
  "guide_candidates": [],
  "doc_targets": [],
  "coverage": {}
}
```

## 字段发现

```json
{
  "table": "value_balance_detail",
  "column": "expire_time",
  "evidence": {
    "schema": "timestamp nullable",
    "sample": "样本中出现 NULL",
    "code_refs": ["ValueBalanceDetailMapper"]
  },
  "business_interpretation": "NULL 表示永久有效",
  "ai_risk": "只写 expire_time > now() 会漏掉永久有效明细",
  "confidence": "high",
  "doc_target": {
    "path": "docs/PAYMENT_KNOWLEDGE_BASE.md",
    "section": "核心业务规则与隐性约束"
  }
}
```

## 表发现

```json
{
  "table": "customer",
  "role": "业务主表",
  "domain": "CUSTOMER",
  "why_critical": ["当前业务域主表", "含状态字段", "被多个服务读写"],
  "field_analysis_status": {
    "analyzed": ["id", "status", "tenant_id"],
    "not_analyzed": ["remark_ext"]
  },
  "doc_target": "docs/CUSTOMER_KNOWLEDGE_BASE.md"
}
```

## Guide 候选

```json
{
  "topic": "SHARDING",
  "reason": "多个业务域共享分表键、分表元数据和路由规则",
  "evidence": ["多张表包含 prog_id", "存在分表元数据表", "代码中有路由组件"],
  "doc_target": "docs/SHARDING_GUIDE.md",
  "confidence": "medium"
}
```

## 可落档 Markdown 片段

每个发现可附短片段，但不要把长期文档写成原始数据 dump：

```md
`value_balance_detail.expire_time` 在数据中允许 `NULL`，结合扣减 SQL 判断，`NULL` 更像永久有效语义，不应按脏数据过滤。改余额扣减或有效期判断时必须同时包含 `expire_time IS NULL` 分支。置信度：高。
```

## 覆盖度

证据包末尾必须说明：

- 已连接 / 未连接数据库。
- 已 catalog 的 schema 和表数量。
- 已 sample-table 的表。
- 已 analyze-field 的字段。
- 只做 catalog、尚未细扫的业务域。
- 低置信推断和需要用户确认的问题。

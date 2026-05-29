# 特征工程平台

> Feature Store 统一管理特征，消除训练-服务偏差，加速特征复用。

## 目录

- [Feature Store 概念](#feature-store-概念)
- [核心架构](#核心架构)
- [Feast 实战](#feast-实战)
- [最佳实践](#最佳实践)

---

## Feature Store 概念

### 为什么需要 Feature Store

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      Feature Store 解决的问题                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   问题1: 训练-服务偏差 (Training-Serving Skew)                              │
│   ────────────────────────────────────────────                              │
│   训练时: Python 计算特征                                                   │
│   服务时: Java 重写特征计算逻辑                                             │
│   结果: 特征不一致 → 模型效果下降                                           │
│                                                                             │
│   问题2: 特征重复开发                                                       │
│   ─────────────────────                                                     │
│   Team A: 开发 user_purchase_count 特征                                    │
│   Team B: 不知道，又开发一遍                                                │
│   结果: 重复工作 + 不一致的定义                                             │
│                                                                             │
│   问题3: 特征获取性能                                                       │
│   ─────────────────────                                                     │
│   推理时需要实时计算特征                                                    │
│   结果: 延迟高，影响用户体验                                                │
│                                                                             │
│   Feature Store 解决方案:                                                   │
│   ✅ 统一特征定义和计算逻辑                                                 │
│   ✅ 特征复用和发现                                                         │
│   ✅ 离线(训练)/在线(推理)一致性                                            │
│   ✅ 低延迟特征服务                                                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 核心架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       Feature Store 架构                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                        数据源                                        │   │
│   │   Database │ Event Stream │ Files │ APIs                            │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│                               ▼                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                    Feature Engineering                               │   │
│   │              (Spark / Flink / SQL / Python)                          │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│                               ▼                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                      Feature Store                                   │   │
│   │   ┌─────────────────────┐   ┌─────────────────────┐                 │   │
│   │   │   Offline Store     │   │   Online Store      │                 │   │
│   │   │   (历史特征)        │   │   (实时特征)        │                 │   │
│   │   │   Parquet/Delta     │   │   Redis/DynamoDB    │                 │   │
│   │   └─────────────────────┘   └─────────────────────┘                 │   │
│   │                                                                     │   │
│   │   + Feature Registry (元数据、血缘、文档)                            │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│           ┌───────────────────┴───────────────────┐                        │
│           ▼                                       ▼                        │
│   ┌─────────────────┐                   ┌─────────────────┐               │
│   │    Training     │                   │    Serving      │               │
│   │  (批量读取)     │                   │  (实时读取)     │               │
│   │  Point-in-time  │                   │  低延迟查询     │               │
│   └─────────────────┘                   └─────────────────┘               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Offline vs Online Store

| 特性 | Offline Store | Online Store |
|------|---------------|--------------|
| **用途** | 模型训练 | 实时推理 |
| **数据量** | 大量历史数据 | 最新特征值 |
| **延迟** | 秒-分钟级 | 毫秒级 |
| **存储** | Parquet/Delta Lake | Redis/DynamoDB |
| **查询** | 批量，Point-in-time | 单条，按 Key |

---

## Feast 实战

### 安装和初始化

```bash
pip install feast

# 初始化项目
feast init my_feature_repo
cd my_feature_repo
```

### 定义特征

```python
# feature_repo/features.py
from feast import Entity, FeatureView, FileSource, Field
from feast.types import Float32, Int64
from datetime import timedelta

# 1. 定义数据源
user_source = FileSource(
    path="data/user_features.parquet",
    timestamp_field="event_timestamp",
)

# 2. 定义实体
user = Entity(
    name="user_id",
    join_keys=["user_id"],
    description="User identifier"
)

# 3. 定义特征视图 (Feast 0.26+ 新版 API)
user_features = FeatureView(
    name="user_features",
    entities=[user],
    ttl=timedelta(days=1),
    schema=[
        Field(name="total_purchases", dtype=Int64),
        Field(name="avg_purchase_value", dtype=Float32),
        Field(name="days_since_last_purchase", dtype=Int64),
    ],
    source=user_source,
    online=True,  # 同步到 Online Store
)
```

### 应用特征定义

```bash
# 注册特征到 Registry
feast apply

# 将数据物化到 Online Store
feast materialize-incremental $(date +%Y-%m-%dT%H:%M:%S)
```

### 获取特征

```python
from feast import FeatureStore
import pandas as pd

store = FeatureStore(repo_path=".")

# 训练时: 获取历史特征 (Point-in-time Join)
entity_df = pd.DataFrame({
    "user_id": [1, 2, 3],
    "event_timestamp": pd.to_datetime(["2024-01-01", "2024-01-02", "2024-01-03"])
})

training_df = store.get_historical_features(
    entity_df=entity_df,
    features=[
        "user_features:total_purchases",
        "user_features:avg_purchase_value"
    ]
).to_df()

print(training_df)
```

```python
# 推理时: 获取实时特征
online_features = store.get_online_features(
    features=[
        "user_features:total_purchases",
        "user_features:avg_purchase_value"
    ],
    entity_rows=[{"user_id": 123}]
).to_dict()

print(online_features)
# {'user_id': [123], 'total_purchases': [42], 'avg_purchase_value': [25.5]}
```

---

## 最佳实践

### 特征命名规范

```python
# 好的特征命名
"user_total_purchases_30d"      # 实体_特征描述_时间窗口
"product_avg_rating_7d"
"user_session_count_today"

# 避免的命名
"feature_1"
"tmp_col"
"test"
```

### 特征文档模板

```python
user_features = FeatureView(
    name="user_features",
    description="""
    用户行为特征，用于推荐和个性化。
    
    更新频率: 每日
    数据来源: 用户行为日志
    负责人: data-team@company.com
    """,
    entities=["user_id"],
    features=[
        Feature(
            name="total_purchases",
            dtype=Int64,
            description="用户历史总购买次数"
        ),
    ],
    # ...
)
```

### 特征质量监控

```python
from feast import FeatureStore
from great_expectations import expect

def validate_features(store: FeatureStore, feature_view: str):
    """特征质量检查"""
    # 获取最新特征
    df = store.get_historical_features(...).to_df()
    
    # 检查空值
    assert df.isnull().sum().sum() == 0, "存在空值"
    
    # 检查数值范围
    assert df["total_purchases"].min() >= 0, "购买次数不能为负"
    
    # 检查分布变化 (与历史对比)
    # ...
    
    print("✅ 特征质量检查通过")
```

---

## 工具对比

| 特性 | Feast | Tecton | Databricks FS |
|------|-------|--------|---------------|
| **部署** | 开源自托管 | SaaS | Databricks 平台 |
| **在线存储** | Redis/DynamoDB | 托管 | 托管 |
| **实时特征** | 需配置 | 原生支持 | 支持 |
| **适合场景** | 中小规模 | 企业级 | Databricks 用户 |

---

*下一篇：[06-CI/CD for ML](06-cicd-for-ml.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Feast Documentation.** *Feast: Open Source Feature Store.*  
   https://feast.dev/

2. **Tecton.** *What is a Feature Store?*  
   https://www.tecton.ai/feature-store/

3. **Hopsworks.** *Feature Store for ML.*  
   https://www.hopsworks.ai/feature-store

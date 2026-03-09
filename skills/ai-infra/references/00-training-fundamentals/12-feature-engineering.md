# AI 时代的大数据特征工程：从原始数据到模型输入

> 特征工程是将原始数据转化为模型可理解的"数字语言"的过程。好的特征工程能让简单模型超越复杂模型，是 AI 系统成败的关键环节。

## 目录

- [什么是特征工程](#什么是特征工程)
- [特征类型与构造方法](#特征类型与构造方法)
- [大数据特征工程技术栈](#大数据特征工程技术栈)
- [特征工程方案全景](#特征工程方案全景)
- [深度案例一：电商推荐系统](#深度案例一电商推荐系统)
- [深度案例二：金融风控系统](#深度案例二金融风控系统)
- [特征工程完整 Pipeline](#特征工程完整-pipeline)
- [AI 如何使用特征工程](#ai-如何使用特征工程)
- [总结与实践建议](#总结与实践建议)
- [相关文档](#相关文档)

---

## 什么是特征工程

### 生活类比：厨师备料

```
┌──────────────────────────────────────────────────────────────────────┐
│                                                                      │
│   原始数据 = 菜市场买回来的食材                                       │
│   ─────────────────────────────                                      │
│   鸡（带毛带骨）、土豆（带泥）、葱姜蒜（整颗）...                      │
│                                                                      │
│   特征工程 = 厨师备料                                                 │
│   ─────────────────────                                              │
│   鸡：去毛 → 剁块 → 焯水 → 沥干                                      │
│   土豆：洗净 → 去皮 → 切滚刀块                                       │
│   葱姜蒜：切片/切末/拍碎                                              │
│                                                                      │
│   模型输入 = 摆好的备料盘                                             │
│   ─────────────────────                                              │
│   每种食材大小均匀、摆放整齐、一目了然                                 │
│   → 厨师（模型）拿起来直接炒，效率最高                                 │
│                                                                      │
│   关键: 备料决定了菜品上限！                                          │
│   同样的食材，老厨师切得均匀入味快，新手切得大小不一影响口感             │
│   → 同样的数据，好的特征工程让模型效果翻倍                             │
│                                                                      │
└──────────────────────────────────────────────────────────────────────┘
```

### 定义

**特征工程（Feature Engineering）** 是从原始数据中提取、构造、变换出对预测任务有用的**数值化表示**的过程。

```
原始数据                    特征工程                   模型输入
──────────              ──────────────              ──────────
用户行为日志     →       提取/变换/编码        →     数值矩阵
交易记录         →       聚合/归一化/组合      →     向量表示
文本描述         →       分词/Embedding        →     稠密向量
图片             →       裁剪/归一化/增强      →     张量
```

### AI 时代为什么特征工程依然重要？

很多人以为"深度学习能自动学特征，不需要特征工程了"。这是一个常见误解：

| 场景 | 特征工程的角色 | 说明 |
|------|--------------|------|
| **传统 ML**（XGBoost, LR） | 核心，决定上限 | 模型能力有限，全靠特征弥补 |
| **深度学习**（CNN, Transformer） | 依然重要，但形式变了 | 自动学特征 ≠ 不需要数据预处理 |
| **LLM 时代**（GPT, LLaMA） | 变成 Prompt Engineering | Prompt 就是"告诉模型该关注什么" |
| **推荐/搜索/广告** | 极其关键 | 延迟要求高，必须预计算特征 |
| **金融风控** | 不可替代 | 领域知识编码为特征，合规可解释性 |

> **一句话总结**：深度学习改变了特征工程的**形式**，但没有消除特征工程的**本质**——将领域知识编码进数据表示中。

---

## 特征类型与构造方法

### 特征类型全景

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          特征类型全景图                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐      │
│   │  数值特征   │  │  类别特征   │  │  时序特征   │  │  文本特征   │      │
│   │  年龄: 25   │  │  城市: 北京 │  │  最近7天    │  │  用户评论   │      │
│   │  收入: 8000 │  │  性别: 男   │  │  购买序列   │  │  商品标题   │      │
│   └────────────┘  └────────────┘  └────────────┘  └────────────┘      │
│                                                                         │
│   ┌────────────┐  ┌────────────┐  ┌────────────┐                      │
│   │  图特征     │  │  交叉特征   │  │ Embedding  │                      │
│   │  用户关系网  │  │  年龄×城市  │  │  User Emb  │                      │
│   │  交易环     │  │  品类×时段  │  │  Item Emb  │                      │
│   └────────────┘  └────────────┘  └────────────┘                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 1. 数值特征处理

数值特征是最基础的类型，但原始数值往往不能直接使用。

```python
import pandas as pd
import numpy as np
from sklearn.preprocessing import StandardScaler, MinMaxScaler

df = pd.DataFrame({
    'age': [22, 35, 48, 19, 67],
    'income': [3000, 8000, 15000, 2000, 50000],    # 右偏分布
    'click_count': [0, 3, 150, 1, 2000],            # 极端长尾
})

# 1. 标准化 (Z-Score) —— 让不同量纲可比
# x' = (x - μ) / σ，变换后均值=0, 标准差=1
scaler = StandardScaler()
df[['age_std', 'income_std']] = scaler.fit_transform(df[['age', 'income']])

# 2. 归一化 (Min-Max) —— 压缩到 [0, 1]
# x' = (x - min) / (max - min)，适合神经网络输入
normalizer = MinMaxScaler()
df['age_norm'] = normalizer.fit_transform(df[['age']])

# 3. 对数变换 —— 处理右偏/长尾分布
# log 把 [1, 1000000] 压缩到 [0, 6]，缩小极端值影响
df['income_log'] = np.log1p(df['income'])  # log1p = log(1+x)

# 4. 分桶 (Binning) —— 数值 → 类别
# 年龄与消费力不是线性关系，分桶捕获非线性
df['age_group'] = pd.cut(df['age'], 
                         bins=[0, 18, 25, 35, 50, 100],
                         labels=['未成年', '青年', '中青年', '中年', '老年'])
```

> **实战经验**：XGBoost/LightGBM 等树模型对标准化不敏感（树只看排序），但神经网络/LR/SVM **必须**标准化，否则大数值特征会主导梯度更新。

### 2. 类别特征编码

```python
import pandas as pd
from sklearn.preprocessing import LabelEncoder

df = pd.DataFrame({
    'city': ['北京', '上海', '深圳', '北京', '广州'],
    'device': ['iOS', 'Android', 'iOS', 'HarmonyOS', 'Android'],
    'education': ['高中', '本科', '硕士', '博士', '本科'],
})

# 1. One-Hot —— 类别 → 多列 0/1（类别数<20，无序类别）
city_onehot = pd.get_dummies(df['city'], prefix='city')

# 2. Label 编码 —— 类别 → 整数（仅限树模型！LR/NN 会引入假序关系）
le = LabelEncoder()
df['device_label'] = le.fit_transform(df['device'])

# 3. 有序编码 —— 有自然顺序的类别
edu_order = {'高中': 1, '本科': 2, '硕士': 3, '博士': 4}
df['education_ord'] = df['education'].map(edu_order)

# 4. 目标编码 —— 用目标变量均值替换类别（高基数，需交叉验证防泄露）
df['label'] = [1, 0, 1, 1, 0]
city_target_mean = df.groupby('city')['label'].mean()
df['city_target_enc'] = df['city'].map(city_target_mean)

# 5. 频率编码 —— 用出现频率替换（反映"热门程度"）
df['city_freq'] = df['city'].map(df['city'].value_counts(normalize=True))
```

**编码选择决策树**：

```
类别特征 → 基数多少？
    ├─ < 10 → One-Hot
    ├─ 10~100 → 树模型用 Label / NN用 Target Encoding
    └─ > 100（user_id 等）→ 传统ML用 Target+频率 / 深度学习用 Embedding
```

### 3. 时序特征构造

时序特征是推荐、风控等场景的核心，基于时间窗口聚合。

```python
import pandas as pd

trades = pd.DataFrame({
    'user_id': [1, 1, 1, 1, 1],
    'amount': [100, 50, 200, 80, 150],
    'timestamp': pd.to_datetime([
        '2025-01-01', '2025-01-03', '2025-01-10', '2025-01-15', '2025-01-28'
    ]),
    'category': ['数码', '食品', '数码', '服装', '数码'],
})

snapshot_date = pd.Timestamp('2025-01-31')

def build_time_features(df, snapshot_date):
    df['days_ago'] = (snapshot_date - df['timestamp']).dt.days
    features = {}
    
    # 多时间窗口统计
    for window in [7, 14, 30]:
        w = df[df['days_ago'] <= window]
        features[f'{window}d_count'] = len(w)
        features[f'{window}d_sum'] = w['amount'].sum()
        features[f'{window}d_mean'] = w['amount'].mean() if len(w) > 0 else 0
        features[f'{window}d_unique_cat'] = w['category'].nunique()
    
    # 趋势特征：近7天 vs 前7天
    recent = df[df['days_ago'] <= 7]['amount'].sum()
    prev = df[(df['days_ago'] > 7) & (df['days_ago'] <= 14)]['amount'].sum()
    features['amount_trend_7d'] = recent / max(prev, 1)  # >1 加速, <1 减速
    
    # 偏好特征
    features['top_category'] = df['category'].mode().iloc[0]
    features['top_cat_ratio'] = df['category'].value_counts(normalize=True).iloc[0]
    
    return features

# 输出: 7d_count=1, 30d_sum=580, amount_trend_7d=1.88, top_category=数码
```

### 4. 文本特征处理

```python
# 传统方法：TF-IDF（计算快，可预计算）
from sklearn.feature_extraction.text import TfidfVectorizer

texts = ["这款手机拍照效果非常好", "手机电池续航太差了"]
tfidf = TfidfVectorizer(max_features=100)
tfidf_matrix = tfidf.fit_transform(texts)  # 稀疏矩阵 (2, vocab_size)

# 现代方法：预训练 Embedding（效果好，需 GPU）
from sentence_transformers import SentenceTransformer

model = SentenceTransformer('paraphrase-multilingual-MiniLM-L12-v2')
embeddings = model.encode(texts)  # (2, 384) 稠密矩阵

# 文本统计特征（不依赖模型，速度快）
def text_statistics(text):
    return {
        'text_length': len(text),
        'exclamation_count': text.count('！') + text.count('!'),
        'sentiment_words': sum(1 for w in ['好', '棒', '赞'] if w in text),
        'negative_words': sum(1 for w in ['差', '烂', '坑'] if w in text),
    }
```

### 5. 图特征（Graph Feature）

图特征在社交网络、风控中非常强大。

```python
import networkx as nx

# 构建转账图
G = nx.DiGraph()
edges = [('A','B',1000), ('B','C',500), ('C','A',800), ('D','A',200)]
for src, dst, amt in edges:
    G.add_edge(src, dst, weight=amt)

def graph_features(G, node):
    return {
        'in_degree': G.in_degree(node),
        'out_degree': G.out_degree(node),
        'pagerank': nx.pagerank(G)[node],
        'total_in_amount': sum(d['weight'] for _,_,d in G.in_edges(node, data=True)),
        'in_cycle': len(list(nx.simple_cycles(G))) > 0,  # 环形交易 → 风控关键!
    }
# 节点 A: in_cycle=True (A→B→C→A) ← 高风险信号
```

---

## 大数据特征工程技术栈

### 技术栈全景对比

| 工具 | 数据规模 | 计算模式 | 延迟 | 适用场景 |
|------|---------|---------|------|---------|
| **Pandas** | <10GB | 单机内存 | 秒级 | 探索分析、原型验证 |
| **Polars** | <100GB | 单机多核 | 秒级 | Pandas 加速替代 |
| **Spark** | TB~PB | 分布式批处理 | 分钟级 | 大规模离线特征 |
| **Flink** | 无限流 | 分布式流处理 | 毫秒级 | 实时特征 |
| **Hive SQL** | TB~PB | 分布式批处理 | 分钟级 | 数据仓库查询 |
| **DuckDB** | <100GB | 单机列存 | 秒级 | 本地快速分析 |

```
数据规模 →  技术选型:

  1GB         10GB         100GB         1TB          10TB
   │            │             │            │            │
   ▼            ▼             ▼            ▼            ▼
  Pandas     Polars/       DuckDB/      Spark/       Spark
             DuckDB        Dask         Hive         (大集群)

时效性 →  技术选型:

  离线(T+1): Spark / Hive / Pandas    ← 每天凌晨计算昨天的特征
  近实时:    Spark Structured Streaming ← 几分钟更新
  实时:      Flink                      ← 毫秒级，逐条处理
```

### Spark 特征工程实战

```python
from pyspark.sql import SparkSession, functions as F, Window

spark = SparkSession.builder.appName("FeatureEngineering").getOrCreate()

user_actions = spark.read.parquet("hdfs:///data/user_actions/")
snapshot_date = F.lit("2025-01-31").cast("timestamp")

# 多时间窗口聚合
def window_features(df, days, prefix):
    return df.filter(F.datediff(snapshot_date, "timestamp") <= days) \
        .groupBy("user_id").agg(
            F.count("*").alias(f"{prefix}_count"),
            F.countDistinct("item_id").alias(f"{prefix}_unique_items"),
            F.sum("amount").alias(f"{prefix}_total_amount"),
            F.avg("amount").alias(f"{prefix}_avg_amount"),
            (F.sum(F.when(F.col("action") == "purchase", 1).otherwise(0)) /
             F.count("*")).alias(f"{prefix}_cvr"),
        )

# 7天/14天/30天三窗口 Join
user_features = window_features(user_actions, 7, "7d") \
    .join(window_features(user_actions, 14, "14d"), "user_id", "outer") \
    .join(window_features(user_actions, 30, "30d"), "user_id", "outer")

# 跨窗口衍生特征
user_features = user_features.withColumn(
    "activity_acceleration",  # 活跃度加速
    F.col("7d_count") / F.coalesce(F.col("30d_count"), F.lit(1))
)

user_features.write.mode("overwrite").parquet("hdfs:///features/user/dt=2025-01-31/")
```

### Flink 实时特征工程

```sql
-- Flink SQL: 实时滑动窗口特征
CREATE TABLE user_clicks (
    user_id STRING, item_id STRING, category STRING,
    event_time TIMESTAMP(3),
    WATERMARK FOR event_time AS event_time - INTERVAL '5' SECOND
) WITH ('connector'='kafka', 'topic'='user-clicks', 'format'='json');

-- 每1分钟，计算过去10分钟的实时特征
SELECT user_id, window_end,
    COUNT(*) AS click_count_10min,
    COUNT(DISTINCT item_id) AS unique_items_10min,
    COUNT(DISTINCT category) AS unique_cats_10min
FROM TABLE(
    HOP(TABLE user_clicks, DESCRIPTOR(event_time),
        INTERVAL '1' MINUTE, INTERVAL '10' MINUTE)
)
GROUP BY user_id, window_start, window_end;
-- 结果写入 Redis，供在线推理使用
```

### 离线 + 实时双链路架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                   特征工程双链路架构                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   数据源: 数据库 / Kafka 日志 / HDFS 文件                               │
│       │                     │                    │                      │
│       ▼                     ▼                    ▼                      │
│   ┌────────────┐    ┌────────────┐      ┌────────────┐                │
│   │ Flink       │    │ Spark      │      │ Hive SQL   │                │
│   │ (实时特征)  │    │ (离线特征) │      │ (T+1报表)  │                │
│   │ 毫秒级      │    │ 分钟级     │      │ 小时级     │                │
│   └──────┬─────┘    └──────┬─────┘      └──────┬─────┘                │
│          │                 │                    │                       │
│          ▼                 ▼                    ▼                       │
│   ┌─────────────────────────────────────────────────────┐             │
│   │                 Feature Store                        │             │
│   │   Online Store (Redis)     Offline Store (Parquet)  │             │
│   └──────────┬────────────────────────┬─────────────────┘             │
│              │                        │                                │
│       在线推理(<50ms)          离线训练(批量读取)                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 特征工程方案全景

### 三个时代的演进

```
时代1: 传统 ML (2000-2015)         "特征是金，模型是银"
  人工设计每一个特征，80% 时间花在特征工程上
  代表: XGBoost + 手工特征 → Kaggle 冠军标配

时代2: 深度学习 (2015-2022)         "End-to-End，模型自动提特征"
  Embedding 替代 One-Hot，CNN/Transformer 自动学层次特征
  代表: DeepFM、DIN → 推荐系统新范式

时代3: LLM 时代 (2022-)             "Prompt 是新的特征工程"
  预训练模型已学会通用特征表示
  特征工程 → 如何组织输入让模型理解任务
  代表: GPT + Prompt Engineering, RAG 上下文组织
```

### 三时代详细对比

| 维度 | 传统 ML | 深度学习 | LLM 时代 |
|------|--------|---------|---------|
| **特征来源** | 人工设计 | 模型自动学 + 人工辅助 | 预训练知识 + Prompt |
| **核心工作** | 构造、组合、筛选 | Embedding 设计、数据增强 | Prompt 工程、RAG |
| **时间分配** | 80% 特征，20% 模型 | 50/50 | 30% 数据，70% Prompt |
| **可解释性** | 高 | 中 | 低 |
| **适用场景** | 结构化表格数据 | 图像/文本/序列 | 通用 NLP、多模态 |
| **代表模型** | LR、XGBoost | CNN、BERT、DeepFM | GPT、LLaMA |

### 传统 ML 特征工程示例

```python
import pandas as pd
import numpy as np
from itertools import combinations

# 用户流失预测场景
df = pd.DataFrame({
    'age': [25, 35, 48],
    'monthly_charge': [50, 80, 120],
    'tenure_months': [3, 24, 60],
    'num_products': [1, 3, 5],
})

# 1. 交叉特征（特征组合）
df['charge_per_product'] = df['monthly_charge'] / df['num_products']
df['avg_monthly'] = df['monthly_charge'] / df['tenure_months']

# 2. 多项式特征（二阶交互）
cols = ['age', 'monthly_charge', 'tenure_months']
for c1, c2 in combinations(cols, 2):
    df[f'{c1}_x_{c2}'] = df[c1] * df[c2]

# 3. 统计特征
vals = df[cols].values
df['feat_mean'] = vals.mean(axis=1)
df['feat_std'] = vals.std(axis=1)

# Kaggle 经验：原始 80 特征 → 交叉扩展 300+ → 筛选 150 → AUC 0.78 → 0.85+
```

---

## 深度案例一：电商推荐系统

### 业务场景

用户打开电商 App 首页，系统需要在 **50ms 内**从百万商品中选出最可能购买的 20 个商品。

```
用户请求 → 召回(10万→1万) → 粗排(→500) → 精排(→50) → 重排(→20)
              <10ms            <10ms         <20ms        <10ms

每个阶段都需要特征！精排是特征工程的主战场（100-500个特征）
```

### 完整特征体系

```python
# ===== 用户画像特征 =====
user_features = {
    'user_age_group': 'category',       # 年龄段
    'user_city_level': 'ordinal',       # 城市等级
    'user_avg_price_30d': 'numeric',    # 30天平均客单价
    'user_category_entropy': 'numeric', # 品类多样性（熵）
    'user_top1_category': 'category',   # 最偏好品类
}

# ===== 商品特征 =====
item_features = {
    'item_price': 'numeric',
    'item_ctr_7d': 'numeric',           # 7天点击率
    'item_cvr_7d': 'numeric',           # 7天转化率
    'item_avg_rating': 'numeric',
}

# ===== 用户-商品交叉特征（最关键！） =====
cross_features = {
    'user_item_click_count': 'numeric',    # 用户点击该商品次数
    'user_cat_purchase_count': 'numeric',  # 用户购买该品类次数
    'price_vs_user_avg': 'numeric',        # 商品价格 / 用户平均客单价
    # ≈ 0.8~1.2 最佳匹配，>2 偏贵，<0.5 太便宜
    'user_brand_purchase_ratio': 'numeric', # 品牌偏好度
}

# ===== 实时特征（Flink 计算） =====
realtime_features = {
    'user_click_count_10min': 'numeric',     # 10分钟点击数
    'user_cart_item_count': 'numeric',       # 购物车商品数
    'user_search_query_embedding': 'vector', # 搜索词向量
}
```

### 模型输入：特征如何喂给 DeepFM

```python
import torch
import torch.nn as nn

class RecommendFeatureProcessor(nn.Module):
    def __init__(self):
        super().__init__()
        # 高基数 ID → Embedding（自动学表示，替代 One-Hot）
        self.user_emb = nn.Embedding(10_000_000, 32)
        self.item_emb = nn.Embedding(5_000_000, 32)
        self.brand_emb = nn.Embedding(50_000, 16)
        self.cat_emb = nn.Embedding(500, 8)
        self.numeric_bn = nn.BatchNorm1d(20)  # 数值特征标准化
    
    def forward(self, user_id, item_id, brand_id, cat_id, numeric):
        parts = [
            self.user_emb(user_id),    # (batch, 32)
            self.item_emb(item_id),    # (batch, 32)
            self.brand_emb(brand_id),  # (batch, 16)
            self.cat_emb(cat_id),      # (batch, 8)
            self.numeric_bn(numeric),  # (batch, 20)
        ]
        return torch.cat(parts, dim=-1)  # (batch, 108) → DeepFM 输入
```

---

## 深度案例二：金融风控系统

### 业务场景

银行需要在用户发起转账的 **200ms 内**判断是否为欺诈交易。

```
用户转账 → 特征组装(<50ms) → 规则引擎 + ML模型 + 深度模型 → 融合决策(<200ms)
              │                                                    │
              ├─ 离线特征 (Feature Store)                          通过/拒绝/人工审核
              ├─ 实时特征 (Flink 聚合)
              └─ 图特征 (图数据库查询)
```

### 风控特征体系

```python
# ===== 交易特征 =====
transaction_features = {
    'trans_amount_log': 'numeric',       # log(金额)，金额极度右偏
    'amount_vs_user_avg': 'numeric',     # 金额 / 用户均值，偏离度
    'amount_zscore': 'numeric',          # z > 3 → 极端异常
    'is_new_payee': 'binary',            # 是否首次转给此人
}

# ===== 时间窗口聚合（核心！欺诈通常短时间密集发生） =====
time_features = {
    'trans_count_1h': 'numeric',         # 1小时交易次数
    'trans_count_24h': 'numeric',        # 24小时交易次数
    'freq_ratio_1h_vs_24h': 'numeric',  # 1h频率/24h平均 → =24 极度异常
    'unique_payees_1h': 'numeric',       # 1小时转给几个不同的人
    'unique_devices_24h': 'numeric',     # 24小时用几个设备
    'max_distance_24h': 'numeric',       # 24小时最远交易地理距离
    # > 1000km → 同一天在北京和深圳，物理不可能！
}

# ===== 图特征 =====
graph_features = {
    'in_cycle': 'binary',              # 是否参与环形交易 (A→B→C→A)
    'connected_fraud_count': 'numeric', # 关联欺诈账户数
    'community_fraud_ratio': 'numeric', # 所在社区的欺诈比例
}
```

### 图特征计算（Neo4j）

```python
from neo4j import GraphDatabase

def get_graph_features(user_id):
    """在线查询用户图特征"""
    with driver.session() as session:
        result = session.run("""
            MATCH path = (u:User {id: $uid})-[:TRANSFER*2..5]->(u)
            WHERE ALL(r IN relationships(path) 
                      WHERE r.timestamp > datetime() - duration('P7D'))
            WITH path, length(path) AS cycle_len
            MATCH (u:User {id: $uid})-[:TRANSFER*1..2]-(n:User {is_fraud: true})
            RETURN 
                cycle_len IS NOT NULL AS in_cycle,
                COUNT(DISTINCT n) AS connected_fraud_count
        """, uid=user_id)
        return result.single()
# in_cycle=True + connected_fraud_count=5 → 极高风险
```

---

## 特征工程完整 Pipeline

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    特征工程端到端 Pipeline                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  Step 1: 数据收集                                                       │
│    数据库 → Sqoop/CDC → 数据湖 | 日志 → Kafka → Flink                  │
│                                                                         │
│  Step 2: 数据清洗                                                       │
│    缺失值(中位数/众数) | 异常值(3σ截断) | 去重 | 类型修正               │
│                                                                         │
│  Step 3: 特征构造                                                       │
│    离线(Spark) | 实时(Flink) | 图(Neo4j) | 文本(NLP)                   │
│                                                                         │
│  Step 4: 特征验证                                                       │
│    完整性(null<阈值) | 分布(PSI<0.1) | 范围 | 训练-服务一致性           │
│                                                                         │
│  Step 5: 特征存储                                                       │
│    Offline Store(Parquet) → 训练 | Online Store(Redis) → 推理          │
│                                                                         │
│  Step 6: 训练数据构造                                                    │
│    Point-in-Time Join(防泄露!) | 样本均衡 | 时间切割(非随机!)          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Point-in-Time Join：防止数据泄露的关键

```python
# 错误: 直接 JOIN 最新特征 → 用到了未来数据 → 线下0.95上线0.75（翻车！）
# 正确: 对每个样本，只用事件发生前的特征

def point_in_time_join(events_df, features_df):
    """按时间关联特征，防止数据泄露"""
    results = []
    for _, event in events_df.iterrows():
        valid = features_df[
            (features_df['user_id'] == event['user_id']) &
            (features_df['feature_time'] <= event['event_time'])
        ]
        latest = valid.sort_values('feature_time').iloc[-1] if len(valid) > 0 else None
        results.append({**event.to_dict(), 
                       'feature': latest['value'] if latest is not None else None})
    return pd.DataFrame(results)
```

### 特征监控：PSI

```python
import numpy as np

def calculate_psi(baseline, current, bins=10):
    """PSI < 0.1 稳定 | 0.1~0.25 关注 | > 0.25 需重训模型"""
    bp = np.percentile(baseline, np.linspace(0, 100, bins + 1))
    bp[0], bp[-1] = -np.inf, np.inf
    b_pct = np.maximum(np.histogram(baseline, bp)[0] / len(baseline), 1e-6)
    c_pct = np.maximum(np.histogram(current, bp)[0] / len(current), 1e-6)
    return np.sum((c_pct - b_pct) * np.log(c_pct / b_pct))
```

---

## AI 如何使用特征工程

### 四种范式

```
范式1: 传统 ML —— "手工喂食"
  人工特征 → 数值矩阵 → XGBoost/LR
  X = [age, income, click_30d, ...] → model.predict(X)

范式2: 深度学习 —— "半自动"
  ID → Embedding + 手工数值特征 → 拼接 → DNN
  user_id → [0.1, -0.3, 0.7, ...](32维) + numeric → model(x)

范式3: 预训练模型 —— "自动提取"
  原始数据 → 预训练模型 → 特征向量 → 下游任务
  图片 → ResNet → 2048维 | 文本 → BERT → 768维

范式4: LLM —— "Prompt 即特征"
  原始信息 → 组织成 Prompt → LLM 直接输出
  不需要显式特征提取！
```

### 范式 1：传统 ML

```python
import xgboost as xgb

# 特征矩阵（150个手工特征）
X_train, y_train = df[feature_columns].values, df['label'].values

model = xgb.XGBClassifier(n_estimators=500, max_depth=6, learning_rate=0.05)
model.fit(X_train, y_train)

# 特征重要性分析 —— 传统 ML 的核心优势
importance = sorted(zip(feature_columns, model.feature_importances_), key=lambda x: -x[1])
# purchase_count_30d: 0.082 ← 最重要
# price_vs_avg: 0.071
# conversion_rate_7d: 0.065
```

### 范式 2：深度学习 Embedding

```python
import torch.nn as nn

class DeepRecommender(nn.Module):
    """Embedding + DNN: ID 特征不再需要手工编码"""
    def __init__(self):
        super().__init__()
        # user_id: 传统 ML 需 One-Hot(1000万维) → 不可行
        # 深度学习: Embedding(32维) → 高效且有语义
        self.user_emb = nn.Embedding(10_000_000, 32)
        self.item_emb = nn.Embedding(5_000_000, 32)
        
        # DNN 自动学习特征交互（替代手工交叉特征）
        self.dnn = nn.Sequential(
            nn.Linear(32+32+20, 256), nn.ReLU(), nn.Dropout(0.3),
            nn.Linear(256, 128), nn.ReLU(),
            nn.Linear(128, 1), nn.Sigmoid(),
        )
    
    def forward(self, user_id, item_id, numeric):
        x = torch.cat([self.user_emb(user_id), self.item_emb(item_id), numeric], -1)
        return self.dnn(x)

# Embedding 的魔力:
# - 相似用户的向量自动靠近
# - 可直接做向量检索（ANN）实现召回
# - 可迁移到其他任务
```

### 范式 3：预训练模型作为特征提取器

```python
# BERT 文本特征提取
from transformers import AutoModel, AutoTokenizer
import torch

tokenizer = AutoTokenizer.from_pretrained("bert-base-chinese")
model = AutoModel.from_pretrained("bert-base-chinese")

with torch.no_grad():
    inputs = tokenizer(["这款手机拍照效果好"], return_tensors="pt")
    text_feature = model(**inputs).last_hidden_state[:, 0, :]  # (1, 768)

# 文本特征 + 结构化特征 → 拼接 → 下游分类器
# combined = torch.cat([structured_feat, text_feature], dim=-1)  # (1, 918)

# ResNet 图像特征提取
import torchvision.models as models

resnet = models.resnet50(pretrained=True)
resnet = nn.Sequential(*list(resnet.children())[:-1])  # 去掉最后分类层
# image → resnet → (1, 2048) 特征向量
```

### 范式 4：LLM 时代——Prompt 作为新特征工程

```python
# ========== Prompt 即特征工程 ==========
# 传统方式: 结构化数据 → 手工特征 → 模型
# LLM 方式: 结构化数据 → 文本化 → Prompt → LLM

# 示例: 用 LLM 做用户流失预测
def build_prompt(user_data):
    """将结构化数据"翻译"成 LLM 可理解的 Prompt"""
    return f"""你是一位数据分析专家。请根据以下用户信息判断该用户是否可能流失。

用户信息:
- 年龄: {user_data['age']}岁
- 月消费: {user_data['monthly_charge']}元
- 使用时长: {user_data['tenure']}个月
- 最近30天登录次数: {user_data['login_30d']}次
- 最近一次购买距今: {user_data['days_since_purchase']}天
- 投诉次数: {user_data['complaint_count']}次

请分析该用户的流失风险（高/中/低），并给出理由。"""

# ========== RAG 中的特征组织 ==========
# RAG 的"特征工程" = 如何组织检索到的上下文
def build_rag_prompt(query, retrieved_docs):
    """RAG 中如何组织上下文 = LLM 时代的特征工程"""
    context = "\n\n".join([
        f"[文档{i+1}] (相关度: {doc['score']:.2f})\n{doc['content']}"
        for i, doc in enumerate(retrieved_docs[:5])
    ])
    return f"""基于以下参考信息回答问题。

参考信息:
{context}

问题: {query}
回答:"""

# ========== AutoFeature: 用 LLM 自动生成特征 ==========
# 最新趋势: 让 LLM 帮你想特征！
auto_feature_prompt = """
你是特征工程专家。给定以下电商用户行为数据字段:
- user_id, item_id, timestamp, action_type, amount, category

请为"预测用户是否会购买"任务，设计 10 个有价值的衍生特征，
并给出每个特征的:
1. 特征名称
2. 计算逻辑（SQL 或 Python）
3. 为什么这个特征有用

要求特征具有业务含义，不要生成无意义的组合。
"""
# LLM 可以生成高质量的特征工程方案，然后人工审核执行
```

> **LLM 时代特征工程的本质变化**：
> - 传统: 人 → 提取特征 → 喂给模型
> - LLM: 人 → 组织信息（Prompt）→ 模型自己提取特征
> - **Prompt Engineering 就是 LLM 时代的特征工程**

---

## 总结与实践建议

### 核心要点

| 要点 | 说明 |
|------|------|
| **特征 > 模型** | 好特征 + 简单模型 > 差特征 + 复杂模型 |
| **防数据泄露** | Point-in-Time Join，时间切割，永远不用"未来"数据 |
| **双链路架构** | 离线 Spark + 实时 Flink，Feature Store 统一管理 |
| **持续监控** | PSI 监控分布漂移，及时重训模型 |
| **特征工程在进化** | 从手工特征 → Embedding → Prompt，形式变了本质没变 |

### 入门实践路径

```
1. 用 Pandas 在 Kaggle 上做一个表格竞赛（理解手工特征工程）
2. 用 PyTorch Embedding 做一个简单推荐模型（理解自动特征学习）
3. 用 PySpark 处理一个 GB 级数据集（理解大数据特征工程）
4. 搭建一个 Flink 实时特征 Demo（理解流式特征）
5. 用 Feast 搭建一个 Feature Store（理解特征管理）
```

---

## 相关文档

- **Feature Store 平台**：[05-特征工程平台](../04-mlops-llmops/05-feature-store.md) — Feast 实战与特征管理
- **训练循环总览**：[01-训练循环](01-training-loop.md) — 特征准备好之后如何训练
- **Transformer 架构**：[10-Transformer 架构](10-transformer-architecture.md) — 深度学习自动特征提取的核心
- **训练 vs 推理**：[11-训练 vs 推理](11-training-vs-inference.md) — 特征在训练和推理中的不同使用方式

---

*上一篇：[11-训练 vs 推理深度对比](11-training-vs-inference.md)*

*返回目录：[README](README.md)*

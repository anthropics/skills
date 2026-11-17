# 数据管理与质量

> 垃圾进，垃圾出——训练数据的质量直接决定模型的上限。

## 目录

- [数据是 AI 的燃料](#数据是-ai-的燃料)
- [训练数据清洗](#训练数据清洗)
- [数据去重](#数据去重)
- [数据标注平台](#数据标注平台)
- [数据版本管理](#数据版本管理)
- [数据质量评估](#数据质量评估)
- [数据合规](#数据合规)

---

## 数据是 AI 的燃料

```
┌─────────────────────────────────────────────────────────────┐
│              数据管理在 AI 生命周期中的位置                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  数据采集 → 数据清洗 → 数据标注 → 数据存储 → 训练 → 评估    │
│     ↑                                          │            │
│     └──────────── 数据飞轮 ←───────────────────┘            │
│                                                             │
│  "数据飞轮" 效应:                                            │
│    模型上线 → 收集用户反馈 → 改进数据 → 更好的模型            │
│    → 更多用户 → 更多数据 → ...                               │
│                                                             │
│  关键事实:                                                   │
│  - GPT-4 训练数据: ~13 万亿 tokens                          │
│  - 数据准备时间: 占 ML 项目 60-80% 的工作量                  │
│  - 数据质量提升 10% 通常比模型架构改进效果更大                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 训练数据清洗

### 常见质量问题

| 问题类型 | 描述 | 影响 | 解决方法 |
|---------|------|------|---------|
| **HTML/代码残留** | 网页抓取的标签、脚本 | 降低文本质量 | 正则清洗、trafilatura |
| **语言混杂** | 多语言混在一起 | 影响模型一致性 | fasttext 语言检测 |
| **低质量文本** | 广告、垃圾、乱码 | 降低模型能力 | 质量评分过滤 |
| **敏感信息** | PII、密码、API Key | 安全风险 | PII 检测+脱敏 |
| **重复内容** | 大量重复文本 | 过拟合、浪费算力 | MinHash 去重 |
| **有害内容** | 暴力、歧视、虚假 | 模型输出有害 | 毒性过滤器 |

### 数据清洗 Pipeline

```python
# 典型 LLM 预训练数据清洗流程

class DataCleaningPipeline:
    def __init__(self):
        self.steps = [
            self.remove_html,
            self.normalize_unicode,
            self.detect_language,
            self.filter_quality,
            self.remove_pii,
            self.deduplicate,
            self.filter_toxicity,
        ]
    
    def remove_html(self, text):
        """去除 HTML 标签和代码"""
        import re
        text = re.sub(r'<[^>]+>', '', text)
        text = re.sub(r'<script[^>]*>.*?</script>', '', text, flags=re.DOTALL)
        return text
    
    def normalize_unicode(self, text):
        """Unicode 规范化"""
        import unicodedata
        return unicodedata.normalize('NFKC', text)
    
    def detect_language(self, text):
        """语言检测，只保留目标语言"""
        import fasttext
        model = fasttext.load_model('lid.176.bin')
        pred = model.predict(text.replace('\n', ' ')[:200])
        lang = pred[0][0].replace('__label__', '')
        conf = pred[1][0]
        if lang not in ['en', 'zh'] or conf < 0.5:
            return None  # 过滤掉
        return text
    
    def filter_quality(self, text):
        """质量评分过滤"""
        # 基于规则的质量过滤
        if len(text) < 100:  # 太短
            return None
        if len(text.split()) < 20:  # 词数太少
            return None
        
        # 特殊字符比例
        special_ratio = sum(1 for c in text if not c.isalnum() and not c.isspace()) / len(text)
        if special_ratio > 0.3:
            return None
            
        # 重复行比例
        lines = text.split('\n')
        unique_lines = set(lines)
        if len(unique_lines) / max(len(lines), 1) < 0.5:
            return None
            
        return text
    
    def remove_pii(self, text):
        """移除个人身份信息"""
        import re
        # 邮箱
        text = re.sub(r'\b[\w.+-]+@[\w-]+\.[\w.]+\b', '[EMAIL]', text)
        # 电话
        text = re.sub(r'\b\d{3}[-.]?\d{3}[-.]?\d{4}\b', '[PHONE]', text)
        # IP 地址
        text = re.sub(r'\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b', '[IP]', text)
        return text
    
    def process(self, text):
        for step in self.steps:
            text = step(text)
            if text is None:
                return None
        return text
```

---

## 数据去重

### 去重方法

```
┌─────────────────────────────────────────────────────────────┐
│                数据去重方法对比                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  精确去重 (Exact Dedup):                                     │
│    方法: SHA256 哈希                                         │
│    适用: 完全相同的文档                                       │
│    复杂度: O(N)                                              │
│    效果: 通常去除 5-15% 的重复                               │
│                                                             │
│  近似去重 (Fuzzy Dedup):                                     │
│    方法 1: MinHash + LSH                                     │
│      将文本转为 shingle (n-gram) 集合                        │
│      计算 MinHash 签名 (固定长度)                             │
│      LSH 快速找到相似候选                                    │
│      Jaccard 相似度 > 0.8 → 认为重复                        │
│      效果: 去除 20-40% 的近似重复                            │
│                                                             │
│    方法 2: SimHash                                           │
│      将文本映射为固定位数的哈希                               │
│      海明距离小于阈值 → 认为重复                             │
│      速度更快，但精度稍低                                    │
│                                                             │
│    方法 3: SemDeDup (语义去重)                                │
│      用 Embedding 模型编码文本                               │
│      余弦相似度高 → 认为语义重复                             │
│      效果最好，但计算成本最高                                 │
│                                                             │
│  推荐: 精确去重 + MinHash 近似去重                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 数据标注平台

### 主流标注平台

| 平台 | 类型 | 特点 | 适用场景 |
|------|------|------|---------|
| **Label Studio** | 开源 | 支持多模态标注、自部署 | 中小团队 |
| **Prodigy** | 商业 | 主动学习、高效 | NLP 任务 |
| **Scale AI** | 服务 | 人工+AI、大规模 | 大型项目 |
| **Argilla** | 开源 | LLM 对齐标注 | RLHF/DPO |
| **CVAT** | 开源 | 计算机视觉专用 | 图像/视频标注 |

### RLHF 标注流程

```
LLM 对齐标注 (RLHF/DPO 数据):

1. 准备 Prompt 集
   → 收集多样化的用户提问

2. 模型生成多个回复
   → 每个 prompt 生成 2-4 个候选回复

3. 人工偏好标注
   → 标注员选择 "更好" 的回复
   → 格式: (prompt, chosen, rejected)

4. 质量控制
   → 多人标注同一对，计算一致性 (Cohen's Kappa)
   → Kappa > 0.7 → 质量合格
   → 不一致的样本送专家复审

5. 产出数据集
   → 用于训练 Reward Model 或直接 DPO
```

---

## 数据版本管理

### DVC (Data Version Control)

```bash
# DVC: Git for Data
# 核心思想: 用 Git 管理元数据，用远端存储管理大文件

# 初始化
pip install dvc
dvc init

# 添加数据文件到 DVC 跟踪
dvc add data/train.parquet
# 生成 data/train.parquet.dvc (元数据文件)
# 原始数据放入 .dvc/cache

# Git 提交元数据
git add data/train.parquet.dvc data/.gitignore
git commit -m "Add training data v1"

# 配置远端存储
dvc remote add myremote s3://my-bucket/dvc-store

# 推送数据到远端
dvc push

# 回滚到之前的数据版本
git checkout v1.0
dvc checkout  # 自动恢复对应版本的数据

# 数据管线定义
dvc run -n preprocess \
    -d raw_data/ \
    -o processed_data/ \
    python preprocess.py
```

### LakeFS

```
LakeFS: 数据湖的 Git

  特点:
  - 对象存储 (S3) 上的版本控制
  - Branch、Commit、Merge 语义
  - 与现有工具兼容 (Spark、Hive、Python)
  
  适用场景:
  - 大规模数据集的版本管理 (TB-PB 级)
  - 数据管线的原子操作
  - 多团队协作的数据管理
```

---

## 数据质量评估

```
数据质量维度:

1. 完整性: 缺失值比例
2. 准确性: 标注正确率
3. 一致性: 相似样本标注一致
4. 多样性: 覆盖了足够多的场景
5. 时效性: 数据是否过时
6. 平衡性: 类别分布是否均衡

LLM 训练数据特有指标:
- Token 分布: 各领域的 token 比例
- 毒性分数: 有害内容占比 (< 0.1%)
- 重复率: 精确/近似重复比例 (< 5%)
- 语言分布: 多语言比例是否符合预期
- 质量评分: 由评估模型打分
```

---

## 数据合规

```
┌─────────────────────────────────────────────────────────────┐
│                数据合规关键领域                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  版权合规:                                                   │
│  - 训练数据的版权归属？                                      │
│  - Common Crawl 数据的使用限制                               │
│  - 代码数据的开源许可证                                      │
│  - The New York Times v. OpenAI 等诉讼的影响                 │
│                                                             │
│  隐私保护:                                                   │
│  - GDPR (欧盟): 用户有权要求删除个人数据                     │
│  - CCPA (加州): 类似 GDPR 的隐私要求                         │
│  - PII 检测: 邮箱、电话、身份证号等                          │
│  - 数据脱敏: 替换/删除敏感信息                               │
│                                                             │
│  数据许可:                                                   │
│  - 明确数据来源和许可证                                      │
│  - 商用 vs 非商用限制                                        │
│  - 衍生作品的许可要求                                        │
│                                                             │
│  最佳实践:                                                   │
│  - 维护数据来源清单 (Data Provenance)                        │
│  - 自动 PII 检测和脱敏                                       │
│  - 定期合规审计                                              │
│  - 保留数据处理的审计日志                                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 小结

```
数据管理核心要点:

1. 数据质量 > 数据数量
   清洗好的 1TB 数据 > 未清洗的 10TB
   去重是最容易被忽视但最重要的步骤

2. 数据清洗必须自动化
   构建可复现的清洗 Pipeline
   每次更新数据都走同样的流程

3. 版本管理是必须的
   DVC 适合中小规模
   LakeFS 适合大规模数据湖

4. 合规是底线
   PII 检测和脱敏必须做
   版权和许可证必须搞清楚

5. 数据飞轮是长期竞争力
   持续收集用户反馈改进数据
   数据和模型相互增强
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **DVC.** *Data Version Control Documentation.*  
   https://dvc.org/doc

2. **LakeFS.** *Git-like Version Control for Data Lakes.*  
   https://lakefs.io/

3. **Great Expectations.** *Data Quality and Validation.*  
   https://greatexpectations.io/

4. **Delta Lake.** *Open-source Storage Layer for Data Lakes.*  
   https://delta.io/

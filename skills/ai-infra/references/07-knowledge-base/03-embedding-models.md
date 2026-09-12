# Embedding 模型深度解析

> Embedding 是知识库的"翻译官"，将人类语言转化为机器可计算的向量表示。

## 目录

- [什么是 Embedding](#什么是-embedding)
- [Embedding 模型演进](#embedding-模型演进)
- [主流模型对比](#主流模型对比)
- [Embedding 维度与性能权衡](#embedding-维度与性能权衡)
- [微调 Embedding 模型](#微调-embedding-模型)
- [多模态 Embedding](#多模态-embedding)
- [评估指标与 MTEB](#评估指标与-mteb)
- [生产部署最佳实践](#生产部署最佳实践)
- [实战练习](#实战练习)

---

## 什么是 Embedding

### 核心概念

Embedding 是将离散的符号（文本、图片等）映射到连续的向量空间的过程，使得语义相似的内容在向量空间中距离相近。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      Embedding 的直觉理解                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   文本世界 (离散)                    向量空间 (连续)                        │
│   ─────────────────                  ──────────────────                     │
│                                                                             │
│   "机器学习" ───────────────────▶  [0.82, -0.15, 0.43, ...]               │
│   "深度学习" ───────────────────▶  [0.79, -0.12, 0.45, ...]  ← 距离近!   │
│   "红烧肉做法" ─────────────────▶  [-0.34, 0.67, -0.21, ...]  ← 距离远   │
│                                                                             │
│   语义关系在向量空间中被保留:                                               │
│                                                                             │
│   cosine_sim("机器学习", "深度学习") = 0.92  ← 高相似度                    │
│   cosine_sim("机器学习", "红烧肉做法") = 0.08  ← 低相似度                  │
│                                                                             │
│   ┌─────────────────────────────────────────────┐                          │
│   │         向量空间可视化 (降维到 2D)            │                          │
│   │                                              │                          │
│   │    ● 机器学习                                │                          │
│   │    ● 深度学习       (AI 聚类)                │                          │
│   │    ● 神经网络                                │                          │
│   │                                              │                          │
│   │                          ● 红烧肉            │                          │
│   │                          ● 宫保鸡丁  (美食)  │                          │
│   │                                              │                          │
│   └─────────────────────────────────────────────┘                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 相似度计算

```python
import numpy as np

def cosine_similarity(a, b):
    """余弦相似度: 衡量方向相似性"""
    return np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b))

def euclidean_distance(a, b):
    """欧氏距离: 衡量空间距离"""
    return np.linalg.norm(a - b)

def dot_product(a, b):
    """点积: 归一化后等价于余弦相似度"""
    return np.dot(a, b)

# 实际使用中, 归一化向量的 dot_product = cosine_similarity
# 向量数据库通常使用归一化后的内积 (IP) 或余弦 (COSINE)
```

| 度量 | 公式 | 范围 | 适用场景 |
|------|------|------|----------|
| **余弦相似度** | cos(θ) = A·B / (‖A‖·‖B‖) | [-1, 1] | 文本语义匹配（最常用） |
| **欧氏距离** | ‖A - B‖₂ | [0, +∞) | 图像相似度 |
| **点积** | A · B | (-∞, +∞) | 归一化后等价余弦 |

---

## Embedding 模型演进

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     Embedding 模型发展历程                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   第一代: 稀疏表示 (2000s)                                                  │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   TF-IDF / BM25                                                     │   │
│   │   • 维度 = 词汇表大小 (数万-数十万维)                                │   │
│   │   • 大部分为零 → "稀疏"                                             │   │
│   │   • 只考虑词频，不理解语义                                          │   │
│   │   • "机器学习" 搜不到 "ML" (同义词问题)                              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                               ↓                                             │
│   第二代: 静态词向量 (2013-2017)                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   Word2Vec / GloVe / FastText                                        │   │
│   │   • 维度: 100-300 维                                                 │   │
│   │   • 每个词一个固定向量                                               │   │
│   │   • 学习到语义关系: king - man + woman ≈ queen                      │   │
│   │   • 问题: "苹果"(水果) 和 "苹果"(公司) 向量相同 → 多义词问题        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                               ↓                                             │
│   第三代: 上下文 Embedding (2018-2022)                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   BERT / Sentence-BERT / DPR                                         │   │
│   │   • 维度: 768-1024 维                                                │   │
│   │   • 同一个词在不同上下文中向量不同                                   │   │
│   │   • 整句编码，语义理解强                                             │   │
│   │   • 问题: 最大长度 512 tokens，多语言效果差                          │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                               ↓                                             │
│   第四代: 大模型 Embedding (2023-) ⭐ 当前                                  │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   BGE-M3 / E5-Mistral / GTE-Qwen2 / OpenAI text-embedding-3       │   │
│   │   • 维度: 1024-4096 维                                              │   │
│   │   • 超长上下文: 8K-32K tokens                                       │   │
│   │   • 多语言原生支持                                                   │   │
│   │   • 多任务: 检索、分类、聚类通用                                     │   │
│   │   • 支持 Matryoshka (套娃) 降维                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 主流模型对比

### 详细对比表

| 模型 | 提供方 | 维度 | 最大长度 | 多语言 | 开源 | 特点 |
|------|--------|------|----------|--------|------|------|
| **text-embedding-3-large** | OpenAI | 3072 | 8191 | ✅ | ❌ | 商业最佳，支持降维 |
| **text-embedding-3-small** | OpenAI | 1536 | 8191 | ✅ | ❌ | 性价比高 |
| **BGE-M3** | BAAI | 1024 | 8192 | ✅ | ✅ | 中文最佳，密集+稀疏+多向量 |
| **BGE-large-zh** | BAAI | 1024 | 512 | 中文 | ✅ | 中文专精 |
| **E5-Mistral-7B** | Microsoft | 4096 | 32768 | ✅ | ✅ | 超大模型，超长上下文 |
| **E5-large-v2** | Microsoft | 1024 | 512 | ✅ | ✅ | 经典，效果稳定 |
| **GTE-Qwen2-7B** | 阿里 | 3584 | 131072 | ✅ | ✅ | 超长上下文 |
| **Jina-embeddings-v3** | Jina AI | 1024 | 8192 | ✅ | ✅ | 多任务，LoRA 适配 |
| **embed-v3** | Cohere | 1024 | 512 | ✅ | ❌ | 商业，压缩好 |
| **Voyage-3** | Voyage AI | 1024 | 32000 | ✅ | ❌ | 代码检索强 |

### 使用示例

```python
# 1. OpenAI Embedding (商业方案)
from openai import OpenAI
client = OpenAI()

response = client.embeddings.create(
    model="text-embedding-3-large",
    input=["机器学习是人工智能的一个分支"],
    dimensions=1024  # 可降维！节省存储和计算
)
emb = response.data[0].embedding

# 2. BGE-M3 (开源方案, 推荐中文场景)
from FlagEmbedding import BGEM3FlagModel

model = BGEM3FlagModel("BAAI/bge-m3", use_fp16=True)
sentences = ["机器学习是人工智能的一个分支", "深度学习使用多层神经网络"]

# BGE-M3 同时输出密集和稀疏向量
output = model.encode(sentences, return_dense=True, return_sparse=True)
dense_embeddings = output["dense_vecs"]   # 密集向量 (语义)
sparse_embeddings = output["lexical_weights"]  # 稀疏向量 (关键词)

# 3. 使用 sentence-transformers 统一接口
from sentence_transformers import SentenceTransformer

model = SentenceTransformer("BAAI/bge-m3")
embeddings = model.encode(["文本1", "文本2"], normalize_embeddings=True)
```

---

## Embedding 维度与性能权衡

### Matryoshka Embedding（套娃 Embedding）

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   Matryoshka Embedding (MRL)                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   原理: 前 N 维包含了最重要的信息，可以截断使用                             │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────┐           │
│   │ 完整向量 (3072 维)                                           │           │
│   │ [0.12, -0.34, 0.56, 0.78, -0.23, ..., 0.01, -0.03, 0.02]  │           │
│   │ ├──── 256 维 ────┤                                           │           │
│   │ ├──────── 512 维 ────────┤                                   │           │
│   │ ├──────────── 1024 维 ────────────┤                          │           │
│   │ ├──────────────── 1536 维 ────────────────┤                  │           │
│   │ ├──────────────────── 3072 维 (完整) ─────────────────────┤  │           │
│   └─────────────────────────────────────────────────────────────┘           │
│                                                                             │
│   维度 vs 性能:                                                             │
│   256 维: 存储小, 速度快, 精度 ~95% of 3072                                │
│   512 维: 平衡选择                                                          │
│   1024 维: 推荐默认                                                         │
│   3072 维: 最高精度, 存储大                                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```python
# OpenAI 支持指定维度 (Matryoshka)
from openai import OpenAI
client = OpenAI()

# 高精度场景
emb_high = client.embeddings.create(
    model="text-embedding-3-large",
    input=["文本"],
    dimensions=3072  # 完整维度
)

# 平衡场景 (推荐)
emb_balanced = client.embeddings.create(
    model="text-embedding-3-large",
    input=["文本"],
    dimensions=1024  # 降维，存储减少 66%
)

# 低成本场景
emb_cheap = client.embeddings.create(
    model="text-embedding-3-large",
    input=["文本"],
    dimensions=256  # 极限降维，存储减少 92%
)
```

### 维度选择建议

| 场景 | 推荐维度 | 理由 |
|------|----------|------|
| **原型开发** | 256-512 | 快速迭代，节省成本 |
| **生产默认** | 1024 | 精度与成本的最佳平衡 |
| **高精度需求** | 1536-3072 | 法律、医疗等不能出错的场景 |
| **大规模数据** | 256-512 | 存储和计算成本优先 |

---

## 微调 Embedding 模型

### 为什么需要微调

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    微调 Embedding 的价值                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   通用模型的问题:                                                           │
│   • "CUDA OOM" 和 "GPU 显存不足" 被认为不相关 (领域术语)                    │
│   • "K8s pod pending" 和 "容器调度失败" 相似度低 (行话)                     │
│   • 公司内部缩写、产品名无法正确编码                                        │
│                                                                             │
│   微调后:                                                                   │
│   • cosine_sim("CUDA OOM", "GPU显存不足") = 0.95 (提升!)                   │
│   • cosine_sim("K8s pod pending", "容器调度失败") = 0.91 (提升!)            │
│                                                                             │
│   典型提升: 检索召回率 +5% ~ +15%                                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 微调流程

```python
from sentence_transformers import SentenceTransformer, InputExample, losses
from torch.utils.data import DataLoader

# 1. 准备训练数据 (正样本对)
train_examples = [
    InputExample(texts=["CUDA OOM 错误", "GPU 显存不足"], label=1.0),
    InputExample(texts=["K8s pod pending", "容器调度失败"], label=1.0),
    InputExample(texts=["CUDA OOM 错误", "CPU 利用率高"], label=0.1),
]

# 2. 加载基础模型
model = SentenceTransformer("BAAI/bge-m3")

# 3. 定义损失函数
train_loss = losses.CosineSimilarityLoss(model)

# 4. 微调
train_dataloader = DataLoader(train_examples, shuffle=True, batch_size=16)
model.fit(
    train_objectives=[(train_dataloader, train_loss)],
    epochs=3,
    warmup_steps=100,
    output_path="./finetuned-bge-m3"
)

# 5. 验证
model = SentenceTransformer("./finetuned-bge-m3")
sim = model.similarity(
    model.encode(["CUDA OOM"]),
    model.encode(["GPU 显存不足"])
)
print(f"微调后相似度: {sim[0][0]:.4f}")
```

---

## 多模态 Embedding

### CLIP 模型

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    多模态 Embedding (CLIP)                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌──────────────┐         ┌──────────────┐                                │
│   │   文本编码器   │         │   图像编码器   │                                │
│   │   (Transformer)│         │   (ViT/ResNet) │                                │
│   └──────┬───────┘         └──────┬───────┘                                │
│          │                        │                                         │
│          ▼                        ▼                                         │
│   "一只猫在睡觉"            🖼️ 猫的图片                                    │
│          │                        │                                         │
│          ▼                        ▼                                         │
│   [0.3, -0.5, ...]          [0.28, -0.48, ...]                            │
│          │                        │                                         │
│          └────── 相似度高 ────────┘                                         │
│                                                                             │
│   应用:                                                                     │
│   • 以文搜图: 输入文字描述，找到相关图片                                    │
│   • 以图搜图: 输入图片，找到相似图片                                        │
│   • 多模态知识库: 文档 + 图表统一检索                                       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```python
# CLIP 多模态 Embedding
from transformers import CLIPModel, CLIPProcessor
from PIL import Image

model = CLIPModel.from_pretrained("openai/clip-vit-large-patch14")
processor = CLIPProcessor.from_pretrained("openai/clip-vit-large-patch14")

# 文本 Embedding
text_inputs = processor(text=["a cat sleeping", "GPU architecture"], 
                       return_tensors="pt", padding=True)
text_emb = model.get_text_features(**text_inputs)

# 图像 Embedding
image = Image.open("cat.jpg")
image_inputs = processor(images=image, return_tensors="pt")
image_emb = model.get_image_features(**image_inputs)

# 文本和图像在同一向量空间，可以直接计算相似度
import torch.nn.functional as F
similarity = F.cosine_similarity(text_emb[0].unsqueeze(0), image_emb)
```

---

## 评估指标与 MTEB

### MTEB (Massive Text Embedding Benchmark)

MTEB 是 Embedding 模型最权威的评估基准，涵盖 8 大任务类型。

| 任务类型 | 描述 | 指标 |
|----------|------|------|
| **Retrieval** | 文档检索 | nDCG@10 |
| **STS** | 语义文本相似度 | Spearman 相关系数 |
| **Classification** | 文本分类 | Accuracy |
| **Clustering** | 文本聚类 | V-Measure |
| **Pair Classification** | 文本对分类 | AP |
| **Reranking** | 重排序 | MAP |
| **Summarization** | 摘要 | Spearman |
| **BitextMining** | 双语匹配 | F1 |

```python
# 使用 MTEB 评估自定义模型
from mteb import MTEB
from sentence_transformers import SentenceTransformer

model = SentenceTransformer("BAAI/bge-m3")

evaluation = MTEB(tasks=["CQADupstackRetrieval", "STS22"])
results = evaluation.run(model, output_folder="results/bge-m3")
```

---

## 生产部署最佳实践

### 部署架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Embedding 服务部署架构                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐     ┌─────────────────────────────────────┐             │
│   │  API 请求    │ ──▶ │          负载均衡器                   │             │
│   └─────────────┘     └──────────┬────────────┬─────────────┘             │
│                                  │            │                             │
│                        ┌─────────▼──┐  ┌─────▼────────┐                   │
│                        │ Embedding  │  │ Embedding    │                   │
│                        │ Server 1   │  │ Server 2     │                   │
│                        │ (GPU)      │  │ (GPU)        │                   │
│                        └────────────┘  └──────────────┘                   │
│                                                                             │
│   推荐方案:                                                                 │
│   • TEI (Text Embeddings Inference) by HuggingFace                        │
│   • vLLM (也支持 Embedding 模型)                                           │
│   • Infinity (高性能 Embedding 服务)                                        │
│   • Triton Inference Server                                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```bash
# 使用 HuggingFace TEI 部署 Embedding 服务
docker run --gpus all -p 8080:80 \
    ghcr.io/huggingface/text-embeddings-inference:latest \
    --model-id BAAI/bge-m3 \
    --max-batch-tokens 16384

# 调用
curl http://localhost:8080/embed \
    -X POST \
    -H "Content-Type: application/json" \
    -d '{"inputs": ["机器学习是什么？"]}'
```

### 性能优化

| 优化项 | 方法 | 提升 |
|--------|------|------|
| **批量处理** | 将多个请求合并为一个 batch | 吞吐量 3-5x |
| **FP16 推理** | 半精度浮点 | 速度 1.5x，显存减半 |
| **动态 batch** | 根据负载自动调整 batch size | 延迟-吞吐平衡 |
| **模型量化** | INT8 量化 | 速度 2x，精度损失 <1% |
| **降维** | Matryoshka 降维 | 存储减少 50-90% |

---

## 实战练习

### 练习 1：对比不同 Embedding 模型

```python
# compare_embeddings.py
from sentence_transformers import SentenceTransformer
import numpy as np

models = {
    "BGE-M3": SentenceTransformer("BAAI/bge-m3"),
    "E5-large": SentenceTransformer("intfloat/e5-large-v2"),
}

test_pairs = [
    ("CUDA OOM 错误", "GPU 显存不足"),
    ("机器学习", "深度学习"),
    ("机器学习", "红烧肉做法"),
]

for name, model in models.items():
    print(f"\n=== {name} ===")
    for text1, text2 in test_pairs:
        emb1 = model.encode([text1], normalize_embeddings=True)
        emb2 = model.encode([text2], normalize_embeddings=True)
        sim = np.dot(emb1[0], emb2[0])
        print(f"  sim('{text1}', '{text2}') = {sim:.4f}")
```

### 练习 2：Embedding 可视化

```python
# visualize_embeddings.py
from sentence_transformers import SentenceTransformer
from sklearn.manifold import TSNE
import matplotlib.pyplot as plt

model = SentenceTransformer("BAAI/bge-m3")

texts = [
    "机器学习", "深度学习", "神经网络", "梯度下降",
    "红烧肉", "宫保鸡丁", "麻婆豆腐", "糖醋排骨",
    "Python", "JavaScript", "Java", "Go",
]
categories = ["AI"]*4 + ["美食"]*4 + ["编程"]*4

embeddings = model.encode(texts, normalize_embeddings=True)
tsne = TSNE(n_components=2, random_state=42, perplexity=5)
coords = tsne.fit_transform(embeddings)

colors = {"AI": "red", "美食": "green", "编程": "blue"}
for i, text in enumerate(texts):
    c = colors[categories[i]]
    plt.scatter(coords[i, 0], coords[i, 1], c=c, s=100)
    plt.annotate(text, (coords[i, 0], coords[i, 1]), fontsize=9)

plt.title("Embedding 空间可视化")
plt.savefig("embedding_viz.png", dpi=150, bbox_inches='tight')
```

---

*上一篇：[02-技术栈详解](02-tech-stack.md)*

*下一篇：[04-向量数据库](04-vector-databases.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Reimers, N., & Gurevych, I. (2019).** *Sentence-BERT: Sentence Embeddings using Siamese BERT-Networks.* EMNLP 2019.  
   https://arxiv.org/abs/1908.10084

2. **OpenAI.** *Embeddings API.*  
   https://platform.openai.com/docs/guides/embeddings

3. **MTEB Leaderboard.** *Massive Text Embedding Benchmark.*  
   https://huggingface.co/spaces/mteb/leaderboard

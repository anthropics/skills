# 长上下文推理

> 从 4K 到 128K 再到 1M——模型能"看到"更远，但看得远不代表看得清。

## 目录

- [长上下文的核心挑战](#长上下文的核心挑战)
- [RoPE 扩展方案全景](#rope-扩展方案全景)
- [Lost in the Middle 深度分析](#lost-in-the-middle-深度分析)
- [长上下文训练工程](#长上下文训练工程)
- [长上下文推理性能分析](#长上下文推理性能分析)
- [评测与基准](#评测与基准)

---

## 长上下文的核心挑战

### 三大瓶颈

```
┌─────────────────────────────────────────────────────────────────┐
│                  长上下文的三大瓶颈                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. 位置编码外推失败                                              │
│     ┌──────────────────────────────────────────────┐            │
│     │ 训练长度: 4K tokens                           │            │
│     │ 推理长度: 128K tokens                         │            │
│     │ 问题: 位置 4097+ 模型从未见过                  │            │
│     │ 后果: PPL 急剧上升，生成垃圾内容               │            │
│     └──────────────────────────────────────────────┘            │
│                                                                  │
│  2. 显存爆炸                                                     │
│     ┌──────────────────────────────────────────────┐            │
│     │ KV Cache (LLaMA-3.1 8B, FP16):               │            │
│     │   4K seq:   0.5 GB → 轻松                     │            │
│     │   32K seq:  4.0 GB → 还行                     │            │
│     │   128K seq: 16.0 GB → 紧张（模型本身 16 GB）   │            │
│     │   1M seq:   125 GB → 超过单卡 80 GB            │            │
│     └──────────────────────────────────────────────┘            │
│                                                                  │
│  3. 注意力质量下降                                                │
│     ┌──────────────────────────────────────────────┐            │
│     │ Softmax 在长序列上趋于"平均化"                 │            │
│     │ → 关键 Token 获得的注意力权重被稀释             │            │
│     │ → "Lost in the Middle" 现象                   │            │
│     │ → 128K 窗口 ≠ 128K 的有效利用                 │            │
│     └──────────────────────────────────────────────┘            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## RoPE 扩展方案全景

### RoPE 基础回顾

> 📖 RoPE 基础原理见 [01-context-window-fundamentals.md](01-context-window-fundamentals.md)

```
RoPE 核心公式：

  对 embedding 维度对 (2i, 2i+1)，位置 m 的旋转角度：
  
  θ_i = base^(-2i/d)    (base 默认 = 10000)
  角度 = m × θ_i

  直觉：
  - 低维度 i 小 → θ_i 大 → 旋转快 → 高频 → 编码近距离关系
  - 高维度 i 大 → θ_i 小 → 旋转慢 → 低频 → 编码远距离关系
  
  外推问题：当 m > 训练长度 L 时
  - 高频分量: m × θ_i 已经"绕了很多圈"，还算稳定
  - 低频分量: m × θ_i 进入从未见过的角度区间 → 模型困惑
```

### 方案 1: Position Interpolation (PI)

```
PI 的核心思路：
  与其让位置编码"外推"到训练范围外，不如把新位置"压缩"回训练范围内

数学：
  原始: 位置 m 的角度 = m × θ_i
  PI:   位置 m 的角度 = (m × L / L') × θ_i
  
  其中 L = 原始训练长度, L' = 目标长度
  
  例如: L=4K, L'=32K
  → 位置 32000 的角度 = (32000 × 4096 / 32768) × θ_i = 4000 × θ_i
  → 映射回训练范围 [0, 4096) 内
  
  ┌────────────────────────────────────────────┐
  │  原始 RoPE:                                │
  │  |----训练范围----|                         │
  │  0     4K        32K  ← 外推区域（失败）    │
  │                                             │
  │  PI:                                        │
  │  |--------映射回训练范围--------|            │
  │  0                             32K          │
  │  (每个位置"缩小"8倍)                         │
  └────────────────────────────────────────────┘

优点：简单有效，只需少量微调（~1000 步）
缺点：位置被压缩 → 相邻 Token 的位置差异变小 → 短距离分辨率下降
     → 短序列性能有一定下降
```

### 方案 2: NTK-aware Scaling

```
NTK-aware 的核心思路：
  不压缩位置，而是修改 RoPE 的频率基数，让低频分量更慢地旋转

数学：
  原始: θ_i = base^(-2i/d),     base = 10000
  NTK:  θ_i = (base × α)^(-2i/d)
  
  α = (L'/L)^(d/(d-2))
  
  直觉：
  ┌────────────────────────────────────────────┐
  │  频率分量分析：                              │
  │                                             │
  │  高频 (i 小): θ'_i ≈ θ_i (几乎不变)         │
  │  → 短距离关系保持精确                        │
  │                                             │
  │  低频 (i 大): θ'_i < θ_i (变慢)             │
  │  → 远距离关系扩展到更长范围                   │
  │                                             │
  │  效果："高频保精度 + 低频扩范围"              │
  └────────────────────────────────────────────┘

优点：
  ✅ 不需要微调即可使用（Zero-Shot）
  ✅ 短序列性能不受影响
  
缺点：
  ⚠️ 扩展倍数有限（通常 2-4×）
  ⚠️ 超过 4× 后质量开始下降
```

```python
# NTK-aware Scaling 实现
import torch
import math

def ntk_aware_rope(
    dim: int, 
    max_position: int, 
    base: float = 10000.0,
    original_max_position: int = 4096,
) -> torch.Tensor:
    """NTK-aware RoPE Scaling"""
    if max_position <= original_max_position:
        # 不需要扩展
        alpha = 1.0
    else:
        # 计算缩放因子
        alpha = (max_position / original_max_position) ** (dim / (dim - 2))
    
    new_base = base * alpha
    inv_freq = 1.0 / (new_base ** (torch.arange(0, dim, 2).float() / dim))
    return inv_freq

# LLaMA-7B: dim=128, 从 4K 扩展到 32K
inv_freq_4k = ntk_aware_rope(128, 4096)     # 原始
inv_freq_32k = ntk_aware_rope(128, 32768)   # NTK 扩展到 32K

print(f"低频分量变化: {inv_freq_4k[-1]:.6f} → {inv_freq_32k[-1]:.6f}")
print(f"高频分量变化: {inv_freq_4k[0]:.6f} → {inv_freq_32k[0]:.6f}")
# 低频变化大（扩展范围），高频变化小（保持精度）
```

### 方案 3: Dynamic NTK

```
Dynamic NTK 的改进：
  NTK-aware 用固定的 α → 短序列时也被修改（不必要）
  Dynamic NTK: α 随实际序列长度动态调整

规则：
  if seq_len ≤ L_train:
      α = 1  (使用原始 RoPE)
  else:
      α = (seq_len / L_train)^(d/(d-2))  (动态缩放)

效果：
  - 短序列 (≤4K): 完全不影响，使用原始 RoPE
  - 中序列 (4K-16K): 轻微缩放
  - 长序列 (16K+): 按需缩放
  
代表模型：Qwen 系列
```

### 方案 4: YaRN (Yet another RoPE extensioN)

```
YaRN = NTK-aware + Attention Scaling + 分段插值

三个关键改进：

1. NTK-aware 基数修改（同前）
   → 扩展低频范围

2. Attention Temperature Scaling
   注意力分数除以 √(s) 来补偿长序列的分布变化
   attn_scores = Q × K^T / √(d_head × s)
   s = log(L'/L) / log(L)  (温度缩放因子)
   
   → 防止 Softmax 在长序列上过度平坦化

3. 分段插值策略
   对不同频率的 RoPE 维度采用不同策略：
   - 高频维度 (λ < 1): 不修改（已经足够短周期）
   - 中频维度 (1 ≤ λ ≤ λ_max): 线性插值
   - 低频维度 (λ > λ_max): NTK 缩放
   
   λ = 2π / θ_i (波长)
   → "该精确的精确，该扩展的扩展"

效果：
  ┌──────────────────────────────────────────┐
  │  YaRN vs 其他方案（128K 扩展 PPL 对比）   │
  │                                           │
  │  方案          训练数据   128K PPL        │
  │  原始 RoPE     4K 训练    PPL > 1000      │
  │  PI            400 步      PPL ≈ 8.5      │
  │  NTK-aware     零样本      PPL ≈ 12.0     │
  │  Dynamic NTK   零样本      PPL ≈ 10.0     │
  │  YaRN          400 步      PPL ≈ 7.2  ✅  │
  └──────────────────────────────────────────┘
```

### 方案 5: 增大基数（LLaMA 3.1 方案）

```
最简单粗暴的方案：直接把 RoPE base 从 10000 增大到 500000

LLaMA 3.1 (Meta):
  base = 500000 (原始 10000 的 50 倍)
  训练: 从 8K 逐步扩展到 128K（大量长序列数据微调）
  
  直觉：base 越大 → 每个维度旋转越慢 → 自然支持更长序列
  
  代价：需要在长序列数据上大量训练
  优势：效果最好，无需推理时额外处理
  
  Meta 的做法：
  1. 8K 训练 → 扩展到 128K（调大 base）
  2. 在长文档数据上继续训练 ~800B tokens
  3. 最终模型原生支持 128K
```

### 方案对比总结

| 方案 | 需要微调 | 短序列影响 | 最大扩展 | 实现复杂度 | 代表模型 |
|------|---------|----------|---------|----------|---------|
| PI | 少量 (~1K步) | 轻微下降 | 8× | ★☆☆ | CodeLlama-PI |
| NTK-aware | 不需要 | 无 | 4× | ★☆☆ | 社区方案 |
| Dynamic NTK | 不需要 | 无 | 8× | ★☆☆ | Qwen |
| YaRN | 少量 (~400步) | 极小 | 64× | ★★☆ | Yarn-LLaMA |
| 增大基数 | 大量 (数十B tokens) | 无 | 32× | ★★★ | LLaMA 3.1 |

**生产建议**：
- **最简单**：使用原生支持长上下文的模型（LLaMA 3.1, Qwen2.5）
- **需要扩展开源模型**：YaRN（效果最佳，少量微调）
- **零样本快速扩展**：Dynamic NTK（无需微调）

---

## Lost in the Middle 深度分析

### 实验数据

基于 Needle-in-a-Haystack (NIAH) 测试和多文档 QA 任务：

```
不同模型在不同上下文长度下的 NIAH 准确率：

                4K     8K     16K    32K    64K    128K
GPT-4o         99%    99%    98%    97%    96%    93%
Claude 3.5     99%    99%    99%    98%    97%    95%
LLaMA 3.1 8B  98%    97%    95%    90%    83%    72%
LLaMA 3.1 70B 99%    98%    97%    95%    92%    87%
Qwen2.5-72B   99%    98%    97%    95%    91%    85%

趋势：
  - 所有模型在超过 32K 后准确率都开始下降
  - 模型越大，下降越慢（70B > 8B）
  - 商业模型通常优于开源模型（更多长序列训练数据）
```

### 缓解策略详解

#### 策略 1: 信息位置优化

```python
def optimize_context_layout(
    system_prompt: str,
    documents: list[str],
    user_query: str,
    key_instruction: str = "",
) -> str:
    """
    优化上下文布局，将关键信息放在首尾位置
    
    布局策略：
    1. System Prompt (开头，最高优先级)
    2. 最重要的文档 (紧随 System)
    3. 次要文档 (中间)
    4. 关键指令重复 (结尾前)
    5. User Query (最后)
    """
    # 按相关性排序文档
    sorted_docs = sorted(documents, key=lambda d: d['relevance'], reverse=True)
    
    parts = [system_prompt]
    
    # 最相关的文档放开头
    if sorted_docs:
        parts.append(f"## Most Relevant:\n{sorted_docs[0]['content']}")
    
    # 其余文档放中间
    for doc in sorted_docs[1:]:
        parts.append(f"## Reference:\n{doc['content']}")
    
    # 关键指令在结尾重复
    if key_instruction:
        parts.append(f"## IMPORTANT REMINDER: {key_instruction}")
    
    parts.append(f"User: {user_query}")
    
    return "\n\n".join(parts)
```

#### 策略 2: RAG 分块 + 重排序

```
长文档处理流程：

原始文档 (200K tokens)
       │
       ▼
  ┌──────────┐
  │ 分块      │ → 500-1000 tokens/chunk, 带重叠
  └──────────┘
       │
       ▼ (400 个 chunks)
  ┌──────────┐
  │ Embedding │ → 向量化
  └──────────┘
       │
       ▼
  ┌──────────┐
  │ 检索 Top-K│ → 语义相似度排序，取 Top-10
  └──────────┘
       │
       ▼ (10 个 chunks)
  ┌──────────┐
  │ 重排序    │ → Cross-Encoder 精排
  └──────────┘
       │
       ▼ (Top-5, ~4K tokens)
  ┌──────────┐
  │ 组装上下文│ → 按相关性排序放入 Prompt
  └──────────┘
       │
       ▼
  LLM 推理 (4K tokens << 200K tokens)

效果：比直接塞 200K 到上下文更好！
  - 减少 98% 的 token 数 → 成本降低
  - 避免 Lost in the Middle → 质量提升
  - TTFT 从 30 秒降到 200ms → 延迟降低
```

---

## 长上下文训练工程

### 渐进式上下文扩展

训练长上下文模型的最佳实践是**渐进式扩展**，而非直接从短序列跳到长序列：

```
渐进式训练策略（以 128K 为目标）：

阶段 1: 基础预训练 (seq=4K)
  → 大量通用数据训练
  → 模型学会基本的语言能力
  → RoPE base = 10000

阶段 2: 中等长度扩展 (seq=32K)
  → 调大 RoPE base (如 50000)
  → 在长文档数据上继续训练 (~100B tokens)
  → 数据配比: 50% 短文本 + 50% 长文本
  
阶段 3: 长上下文扩展 (seq=128K)
  → 进一步调大 RoPE base (如 500000)
  → 在超长文档数据上继续训练 (~50B tokens)
  → 数据配比: 30% 短 + 30% 中 + 40% 长

关键：每个阶段都保留短序列数据，避免"灾难性遗忘"
```

### 训练数据准备

```
长上下文训练数据来源：

1. 长文档 (书籍、论文、法律文件)
   └ 优点：天然长文本
   └ 处理：过滤质量、去重、分 domain

2. 多文档拼接 (把相关短文档拼成长文本)
   └ 优点：可以控制长度
   └ 处理：按主题聚类后拼接

3. 代码仓库 (完整项目的代码文件)
   └ 优点：有自然的长距离依赖
   └ 处理：按 import 关系排列文件顺序

4. 对话日志 (超长多轮对话)
   └ 优点：贴近实际使用场景
   └ 处理：脱敏、去噪、保持一致性

数据配比建议：
  ┌───────────────────────────────────────┐
  │ 序列长度      │ 占比    │ 数据来源    │
  ├───────────────┼─────────┼─────────────┤
  │ 0-4K          │ 30%     │ 通用语料    │
  │ 4K-32K        │ 30%     │ 长文档      │
  │ 32K-128K      │ 30%     │ 超长文档    │
  │ 128K+         │ 10%     │ 拼接/合成   │
  └───────────────┴─────────┴─────────────┘
```

### 序列并行训练

当训练序列长度超过单卡显存时，需要序列并行：

> 📖 序列并行的完整实现细节见 [02-distributed-training/10-sequence-parallelism.md](../02-distributed-training/10-sequence-parallelism.md)

```
序列并行的选择：

序列长度    方案                     GPU 数
≤ 32K      FlashAttention (单卡)     1
32K-128K   Megatron-LM SP + TP       4-8
128K-512K  DeepSpeed Ulysses          8-32
512K-1M    Ring Attention             32-128
> 1M       Ring Attention + TP        128+
```

---

## 长上下文推理性能分析

### TTFT vs 序列长度

```
TTFT (Time to First Token) 与输入长度的关系：

模型: LLaMA-3.1 8B, A100 80GB, FP16

Input Length    TTFT        相对 4K
4K              ~50ms       1×
8K              ~100ms      2×
16K             ~200ms      4×
32K             ~400ms      8×
64K             ~850ms      17×
128K            ~1800ms     36×

注意：TTFT 与 input length 大致成线性关系
     因为 Prefill 需要计算所有 input token 的 Attention

瓶颈分析：
  4K-32K:  Compute-bound (Prefill 计算密集)
  64K+:    Memory-bound (KV Cache 写入 + Attention 矩阵)

优化手段：
  - Chunked Prefill → 降低单次 Prefill 阻塞时间
  - Tensor Parallelism → 分摊计算
  - FlashAttention → 减少 HBM 访问
```

### 吞吐量 vs 上下文长度

```
吞吐量 (tokens/s) vs 上下文长度：

模型: LLaMA-3.1 8B, A100 80GB, vLLM

                     Batch=1    Batch=16   Batch=64
4K context           45 tok/s   600 tok/s  1800 tok/s
32K context          42 tok/s   400 tok/s  800 tok/s
128K context         35 tok/s   120 tok/s  ❌ OOM

下降原因：
  1. KV Cache 占更多显存 → 能容纳的 batch 更小
  2. 每个 Decode 步读取更大的 KV Cache → 带宽瓶颈
  3. Attention 计算量 O(n) per decode step → 计算增加
```

---

## 评测与基准

### 主流长上下文评测

| 评测 | 测试内容 | 长度范围 | 特点 |
|------|---------|---------|------|
| NIAH (Needle in a Haystack) | 从长文本中找特定信息 | 4K-1M | 最基础的"大海捞针" |
| RULER | 多种检索/推理任务 | 4K-128K | 比 NIAH 更全面 |
| LongBench | 多语言长文本理解 | 2K-32K | 中英文，多种任务 |
| InfiniteBench | 超长文本理解 | 128K+ | 测试极限长度 |
| L-Eval | 长文本生成质量 | 4K-32K | 关注生成质量 |
| SCROLLS | 长文档摘要/QA | 4K-128K | 学术标准评测 |

### Needle-in-a-Haystack 测试实现

```python
"""
简化版 Needle-in-a-Haystack 测试
"""
import random

def create_niah_test(
    context_length: int = 32000,
    needle_depth: float = 0.5,  # 0.0=开头, 0.5=中间, 1.0=结尾
) -> tuple[str, str, str]:
    """创建 NIAH 测试用例"""
    
    # 针（要找的信息）
    needle = "The secret code is: BLUE-TIGER-42."
    
    # 干草（填充文本，用无关内容）
    hay_unit = (
        "The weather in San Francisco has been particularly mild this season. "
        "Local residents have been enjoying outdoor activities in the parks. "
        "The tech industry continues to grow with new innovations. "
    )
    
    # 构造上下文
    target_chars = context_length * 4  # ~4 chars per token
    hay_text = (hay_unit * (target_chars // len(hay_unit) + 1))[:target_chars]
    
    # 在指定深度插入 needle
    insert_pos = int(len(hay_text) * needle_depth)
    context = hay_text[:insert_pos] + f"\n{needle}\n" + hay_text[insert_pos:]
    
    question = "What is the secret code mentioned in the text?"
    expected = "BLUE-TIGER-42"
    
    return context, question, expected

# 测试不同深度
for depth in [0.0, 0.25, 0.5, 0.75, 1.0]:
    context, question, expected = create_niah_test(
        context_length=32000, 
        needle_depth=depth,
    )
    print(f"Depth {depth:.0%}: needle at char {int(len(context) * depth)}/{len(context)}")
```

---

## 总结

```
┌─────────────────────────────────────────────────────────────┐
│              长上下文推理 - 关键要点                          │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 三大瓶颈：位置外推 + 显存爆炸 + 注意力稀释              │
│                                                              │
│  2. RoPE 扩展方案选择：                                      │
│     生产首选：原生长上下文模型 (LLaMA 3.1, Qwen2.5)         │
│     需要扩展：YaRN (效果最佳) > Dynamic NTK (零样本)        │
│                                                              │
│  3. Lost in the Middle 是普遍问题                            │
│     → 关键信息放首尾，用 RAG 替代超长上下文                  │
│                                                              │
│  4. 训练工程：渐进式扩展 + 混合长度数据 + 序列并行           │
│                                                              │
│  5. 性能代价：TTFT ∝ seq_len, 吞吐量随长度下降              │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

*上一篇：[03-prefix-caching.md](03-prefix-caching.md) — Prefix Caching 技术*

*下一篇：[05-chunked-prefill.md](05-chunked-prefill.md) — Chunked Prefill*

*返回目录：[README.md](README.md)*

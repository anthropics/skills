# LLM 推理特性 - Attention 优化

> Attention 是 Transformer 的心脏，也是推理的瓶颈。优化它就是优化一切。

## 目录

- [为什么 Attention 需要优化](#为什么-attention-需要优化)
- [FlashAttention](#flashattention)
- [Multi-Query Attention (MQA)](#multi-query-attention-mqa)
- [Grouped-Query Attention (GQA)](#grouped-query-attention-gqa)
- [Speculative Decoding](#speculative-decoding)
- [优化方法对比](#优化方法对比)

---

## 为什么 Attention 需要优化

```
  标准 Self-Attention: Attention(Q, K, V) = softmax(Q × K^T / √d) × V

  以 LLaMA-7B, seq_len=4096 为例:

  Q × K^T = [4096, 128] × [128, 4096] = [4096, 4096] 注意力矩阵
  → 32 个 head 共占: 32 × 4096² × 2 bytes = 1 GB!
  → 序列翻倍 → 显存 4 倍 (O(N²))

  类比: 10 道题对比 100 次还行，100 道题对比 10000 次就爆炸
```

---

## FlashAttention

### 核心思想

```
  FlashAttention 的本质: 不要把 N×N 矩阵完整算出来!

  类比: 批改考试卷
    标准做法: 先把全部答案抄到巨大对比表 → 表太大书桌放不下
             → 不停搬到地上再搬回来 (显存 ↔ SRAM 来回搬)
    FlashAttention: 一次只看几个学生 → 在书桌上直接打分 (SRAM 内完成)
             → 用在线 softmax 逐步更新结果

  GPU 内存层次 — 理解 FlashAttention 的关键:
    ┌──────────────────┐
    │    SRAM (20 MB)   │  ← 超快 (19 TB/s)，但很小 ("书桌")
    └────────┬─────────┘
             │ ← 数据搬运 (瓶颈!)
    ┌────────┴─────────┐
    │    HBM (80 GB)    │  ← 较慢 (2 TB/s)，但大 ("仓库")
    └──────────────────┘

  标准 Attention: N×N 矩阵放不进 SRAM → 大量 IO
  FlashAttention: 分块后放进 SRAM → 极少 IO
```

### 在线 Softmax — 数学核心

```
  问题: Softmax 需要整行数据才能算，怎么分块？

  巧妙做法: 维护 (当前最大值 m, 累积和 l, 部分结果 o)
    处理第 1 块 → 得到 (m₁, l₁, o₁)
    处理第 2 块 → 用 m₂ = max(m₁, 新块 max) 修正之前的结果
    → 只需三个变量，不需要存完整 N×N 矩阵!
    → 数学上结果完全一致 (不是近似!)

  效果 (seq=4096, A100):
  │ 维度     │ 标准 Attention │ FlashAttention-2 │ 提升          │
  │ 显存     │ O(N²) ~1 GB   │ O(N) ~数 MB      │ 10-20x 节省  │
  │ 速度     │ 1x            │ 2-4x             │ IO 减少为主  │
  │ 精度     │ 基线          │ 完全一致          │ 不是近似!    │

  最大贡献: 让 128K 长上下文成为可能! (GPT-4 依赖它)
```

### 使用

```python
# PyTorch 2.0+ 已内置
import torch.nn.functional as F

output = F.scaled_dot_product_attention(
    query, key, value,
    is_causal=True,      # LLM 用因果注意力
    dropout_p=0.0,       # 推理时设为 0
)
# PyTorch 自动选择: FlashAttention > Memory-Efficient > 标准实现
```

---

## Multi-Query Attention (MQA)

```
  MHA: 每个 Head 有独立 Q, K, V → 32 组 KV
  MQA: 所有 Head 共享同一套 K, V，只有 Q 独立 → 1 组 KV

  LLaMA-7B KV Cache 对比 (seq=4096):
    MHA: 32 × 2(K+V) × 4096 × 128 × 2 bytes = 2 GB
    MQA: 1  × 2(K+V) × 4096 × 128 × 2 bytes = 64 MB  (减少 32 倍!)

  类比: MHA=每个学生有自己的笔记(32份)，MQA=只有一块共享白板(1份)
  代表模型: Falcon, PaLM, StarCoder
  缺点: K,V 多样性丢失 → 精度有一定损失
```

---

## Grouped-Query Attention (GQA)

```
  GQA = MHA 和 MQA 的折中 — 把 N 个 Q Head 分成 G 组，组内共享 K,V

  例: LLaMA-2 70B, 64 个 Q Head, 8 个 KV 组:
    组 1: Q₀-Q₇  → K₁,V₁     (8个Q共享1套KV)
    组 2: Q₈-Q₁₅ → K₂,V₂
    ...
    组 8: Q₅₆-Q₆₃ → K₈,V₈

  对比:
    MHA (G=N):  KV=32组  精度最好  最费显存
    GQA (G=8):  KV=8组   精度≈MHA  显存=1/4
    MQA (G=1):  KV=1组   精度有损  最省显存

  类比:
    MHA: 每人一本教材 (32本)
    GQA: 每4人一组共享1本 (8本) → 平衡!
    MQA: 全班共享1本

  LLaMA-2 70B GQA 实验: 精度损失 < 0.5%，KV Cache 减少 8 倍
```

---

## Speculative Decoding

```
  问题: Decode 是串行的，每个 token 必须等前一个 → GPU 利用率低

  核心想法: 用小模型"猜"多个 token，大模型一次性验证

  类比: 领导审批
    原始: 秘书写第1段→领导审→秘书写第2段→领导审→... (串行)
    改进: 秘书一口气写5段→领导一次看完→"前3段OK，第4段重写"

  具体流程:
    Draft Model (1B): 快速猜 ["cat","sat","on","the","mat"]  (5ms)
    Target Model (70B): 一次前向验证全部 (50ms, 和生成1个token差不多)
    结果: "cat"✓ "sat"✓ "on"✓ "the"✗ → 得到3个token
    原本: 3×50ms=150ms，现在: 5ms+50ms=55ms → 加速约 3x!

  为什么验证是高效的？
    验证 = Teacher Forcing (并行) → 一次前向得到所有位置的预测
    生成 = 自回归 (串行) → memory-bound，GPU 利用率低
    → Speculative Decoding 把"串行生成"转化为"并行验证"

  接受率和加速比:
    α=0.8 (80%猜对): 加速约 2.5x
    α=0.6 (60%猜对): 加速约 1.8x
    简单文本 → α 高; 创意文本 → α 低; 低温度 → α 高

  关键保证: 通过拒绝采样，输出分布等价于只用大模型 → 完全无损!
```

### 使用示例

```python
from vllm import LLM, SamplingParams

llm = LLM(
    model="meta-llama/Llama-2-70b-hf",             # Target
    speculative_model="meta-llama/Llama-2-7b-hf",  # Draft
    num_speculative_tokens=5,
)
outputs = llm.generate(["Explain quantum computing"],
                        SamplingParams(temperature=0.0, max_tokens=256))
```

---

## 优化方法对比

```
  ┌───────────────┬────────────┬──────────┬──────────┬──────────────┐
  │  方法         │ FlashAttn  │ GQA      │ MQA      │ Spec.Decode  │
  ├───────────────┼────────────┼──────────┼──────────┼──────────────┤
  │ 优化目标      │ IO 效率    │ KV Cache │ KV Cache │ 解码速度     │
  │ 改变模型结构  │ ❌          │ ✅        │ ✅        │ ❌(需Draft)  │
  │ 精度影响      │ 完全无损   │ 极小     │ 有一些   │ 完全无损     │
  │ 速度提升      │ 2-4x       │ ~1.5x    │ ~2x      │ 2-3x         │
  │ 显存节省      │ 10-20x     │ KV/G倍   │ KV/N倍   │ 无           │
  │ 可组合        │ ✅+GQA     │ ✅+Flash  │ ✅+Flash  │ ✅+任意      │
  │ 代表模型      │ 几乎所有   │ LLaMA-2  │ Falcon   │ 通用技术     │
  └───────────────┴────────────┴──────────┴──────────┴──────────────┘

  实践中的最佳组合:
    GQA (训练时决定) + FlashAttention (推理时使用) + Speculative Decoding
    → 三者互不冲突，可以叠加!
```

---

*下一篇：[08-serving-frameworks.md](08-serving-frameworks.md) - 服务框架详解*

---

## 参考资料与引用

1. **Dao, T., et al. (2022).** *FlashAttention: Fast and Memory-Efficient Exact Attention with IO-Awareness.* NeurIPS 2022.  
   https://arxiv.org/abs/2205.14135

2. **Dao, T. (2023).** *FlashAttention-2: Faster Attention with Better Parallelism and Work Partitioning.*  
   https://arxiv.org/abs/2307.08691

3. **Shazeer, N. (2019).** *Fast Transformer Decoding: One Write-Head is All You Need.* — Multi-Query Attention  
   https://arxiv.org/abs/1911.02150

4. **Ainslie, J., et al. (2023).** *GQA: Training Generalized Multi-Query Transformer Models.* — Grouped-Query Attention  
   https://arxiv.org/abs/2305.13245

5. **Shah, J., et al. (2024).** *FlashAttention-3: Fast and Accurate Attention with Asynchrony and Low-precision.*  
   https://arxiv.org/abs/2407.08608

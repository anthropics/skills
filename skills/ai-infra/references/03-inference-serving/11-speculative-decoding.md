# Speculative Decoding 深入

> 用一个小模型"猜"多个 token，大模型一次性"验证"——推理速度提升 2-3× 而不损失质量。

## 目录

- [为什么需要 Speculative Decoding](#为什么需要-speculative-decoding)
- [核心原理：Draft-Verify](#核心原理draft-verify)
- [Draft 模型选择策略](#draft-模型选择策略)
- [Tree-based Speculative Decoding](#tree-based-speculative-decoding)
- [Medusa：无需 Draft 模型](#medusa无需-draft-模型)
- [Eagle：更高效的推测](#eagle更高效的推测)
- [Self-Speculative Decoding](#self-speculative-decoding)
- [性能分析与调优](#性能分析与调优)
- [实践指南](#实践指南)

---

## 为什么需要 Speculative Decoding

### 生活类比：论文审稿

```
传统自回归解码 = 逐字写论文:
  每写一个字，都要思考半天
  GPU 大部分时间在等（内存带宽瓶颈，算力空闲）
  
Speculative Decoding = 助手先写草稿:
  助手 (小模型): 快速写出草稿 "The cat sat on the mat"
  教授 (大模型): 一次性审阅整个句子
    "The" ✅ "cat" ✅ "sat" ✅ "on" ✅ "the" ✅ "mat" ✅
  → 一次验证通过 6 个 token！
  
  如果部分被拒绝:
  助手写: "The cat sat on the floor"
  教授审: "The" ✅ "cat" ✅ "sat" ✅ "on" ✅ "the" ✅ "floor" ❌ → "mat"
  → 接受 5 个 + 修正 1 个 = 进展 6 个 token
  
  关键: 大模型验证 N 个 token 的时间 ≈ 生成 1 个 token 的时间
  因为 LLM 解码是内存带宽瓶颈，不是算力瓶颈
  验证时 batch 处理 N 个 token，算力利用率更高
```

### 为什么有效

```
┌─────────────────────────────────────────────────────────────┐
│            Speculative Decoding 为什么有效                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  LLM 解码的瓶颈分析:                                        │
│                                                             │
│  Prefill 阶段 (处理 prompt):                                │
│    计算密集 → GPU 算力利用率高 (70-90%)                      │
│    一次处理所有 token                                        │
│                                                             │
│  Decode 阶段 (生成 token):                                  │
│    内存带宽密集 → GPU 算力利用率低 (5-15%)                   │
│    每次只处理 1 个 token                                     │
│    需要加载全部模型权重，但只做一次矩阵乘法                    │
│                                                             │
│  Speculative Decoding 的核心洞察:                            │
│    验证 N 个 token ≈ 一次 Prefill                           │
│    Prefill 的算力利用率远高于逐 token Decode                 │
│    → 用小模型快速生成 N 个候选                               │
│    → 大模型一次 Prefill 验证 N 个                            │
│    → 平均每步产出 α × N 个 token (α = 接受率)               │
│                                                             │
│  加速比 = α × N / (1 + N × Tdraft/Tverify)                  │
│    α: 平均接受率 (通常 70-90%)                               │
│    N: 投机长度 (通常 3-8)                                    │
│    Tdraft: 小模型生成时间                                    │
│    Tverify: 大模型验证时间                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 核心原理：Draft-Verify

### 算法流程

```
┌─────────────────────────────────────────────────────────────┐
│           Speculative Decoding 算法                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  输入: 目标模型 M_target, Draft 模型 M_draft, 投机长度 K     │
│                                                             │
│  循环:                                                       │
│  1. Draft 阶段:                                              │
│     M_draft 自回归生成 K 个候选 token: x1, x2, ..., xK      │
│     同时记录每个 token 的概率: q(x1), q(x2), ..., q(xK)     │
│                                                             │
│  2. Verify 阶段:                                             │
│     M_target 并行计算所有位置的概率:                          │
│     p(x1), p(x2), ..., p(xK), p(xK+1)                      │
│     (一次前向传播，类似 Prefill)                              │
│                                                             │
│  3. Accept/Reject:                                           │
│     对每个 token xi (i = 1, ..., K):                         │
│       if p(xi) >= q(xi):                                    │
│         接受 xi                                              │
│       else:                                                  │
│         以概率 p(xi)/q(xi) 接受                              │
│         否则拒绝，并从修正分布采样替代 token                  │
│         后续 token 全部丢弃                                   │
│                                                             │
│  4. 至少产出 1 个 token (即使全部被拒绝)                     │
│     最多产出 K+1 个 token (全部接受 + bonus token)           │
│                                                             │
│  数学保证: 输出分布与直接用 M_target 生成完全相同！           │
│  → 无损加速                                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 接受率分析

```python
# 影响接受率的因素

# 1. Draft 模型与 Target 模型的相似度
#    相似度高 → 接受率高 → 加速比大
#    Draft: Llama-3-8B, Target: Llama-3-70B → α ≈ 75-85%
#    Draft: GPT-2,      Target: Llama-3-70B → α ≈ 30-40%

# 2. 任务难度
#    简单任务 (翻译、摘要) → α ≈ 80-90%
#    困难任务 (数学推理)   → α ≈ 50-70%
#    代码生成              → α ≈ 60-80%

# 3. Temperature
#    temperature = 0 (greedy) → α 最高
#    temperature > 1         → α 较低

# 4. 投机长度 K
#    K 越大，连续全接受概率越低
#    最优 K 通常在 3-8 之间

# 加速比估算
def estimate_speedup(accept_rate, spec_len, draft_ratio=0.1):
    """
    accept_rate: 平均接受率 (0-1)
    spec_len: 投机长度 K
    draft_ratio: draft 模型时间 / target 模型时间
    """
    avg_accepted = sum(accept_rate**i for i in range(1, spec_len+1))
    total_time = 1 + spec_len * draft_ratio  # verify + draft
    speedup = (avg_accepted + 1) / total_time
    return speedup

# 示例
print(f"α=0.8, K=5: {estimate_speedup(0.8, 5):.1f}× 加速")
print(f"α=0.9, K=5: {estimate_speedup(0.9, 5):.1f}× 加速")
# α=0.8, K=5: 2.5× 加速
# α=0.9, K=5: 3.1× 加速
```

---

## Draft 模型选择策略

```
┌─────────────────────────────────────────────────────────────┐
│              Draft 模型选择策略                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  策略 1: 同系列小模型                                        │
│    Target: Llama-3-70B → Draft: Llama-3-8B                  │
│    优点: 接受率高 (同训练数据/tokenizer)                     │
│    缺点: 需要额外显存放 draft 模型                           │
│                                                             │
│  策略 2: 量化版本                                            │
│    Target: Llama-3-70B FP16 → Draft: Llama-3-70B INT4       │
│    优点: 接受率极高 (同模型不同精度)                          │
│    缺点: 节省有限 (INT4 仍然是大模型)                        │
│                                                             │
│  策略 3: 层跳过 (Layer Skip)                                 │
│    Target: 全部 80 层 → Draft: 只跑前 20 层                  │
│    优点: 共享权重，零额外显存                                 │
│    缺点: 接受率可能较低                                      │
│                                                             │
│  策略 4: N-gram 匹配 (无模型)                                │
│    从 prompt 中找重复的 n-gram 模式                           │
│    优点: 零额外计算                                          │
│    缺点: 只适合重复性高的文本 (代码、JSON)                   │
│                                                             │
│  推荐:                                                       │
│  - 通用对话: 同系列小模型 (接受率最高)                       │
│  - 代码生成: N-gram + 小模型混合                             │
│  - 显存受限: 层跳过                                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Tree-based Speculative Decoding

```
┌─────────────────────────────────────────────────────────────┐
│              树状推测解码                                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  传统 Speculative Decoding: 线性推测                         │
│    Draft: x1 → x2 → x3 → x4 → x5                          │
│    如果 x3 被拒绝，x4, x5 全部浪费                          │
│                                                             │
│  Tree-based: 分支推测                                        │
│    Draft 生成一棵推测树:                                     │
│                                                             │
│                x1                                            │
│               / \                                            │
│             x2a  x2b                                         │
│            / \     \                                         │
│          x3a x3b   x3c                                       │
│          /                                                   │
│        x4a                                                   │
│                                                             │
│    Target 模型用 Tree Attention 一次验证整棵树               │
│    选择被接受的最长路径                                       │
│                                                             │
│  优势:                                                       │
│  - 即使某个分支被拒绝，其他分支可能被接受                    │
│  - 平均接受 token 数更多                                     │
│  - 特别适合低接受率场景                                      │
│                                                             │
│  实现:                                                       │
│  - SpecInfer (CMU)                                           │
│  - vLLM 已支持 tree-based speculative decoding               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Medusa：无需 Draft 模型

```
┌─────────────────────────────────────────────────────────────┐
│                    Medusa 原理                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  核心思想: 给 LLM 加多个预测头，同时预测多个位置              │
│                                                             │
│  原始 LLM:                                                   │
│    Hidden State → LM Head → 预测 token t+1                  │
│                                                             │
│  Medusa LLM:                                                 │
│    Hidden State → LM Head  → 预测 token t+1                 │
│                 → Head 1   → 预测 token t+2                 │
│                 → Head 2   → 预测 token t+3                 │
│                 → Head 3   → 预测 token t+4                 │
│                 → Head 4   → 预测 token t+5                 │
│                                                             │
│  优势:                                                       │
│  - 不需要额外的 draft 模型                                   │
│  - 额外参数量极小 (每个 head 只是一个小 MLP)                 │
│  - 与原模型共享全部计算                                      │
│                                                             │
│  训练 Medusa Head:                                           │
│  - 冻结原模型，只训练新增的 head                             │
│  - 用原模型的训练数据，几小时就能完成                         │
│  - 也可以和模型一起端到端训练 (Medusa-2)                     │
│                                                             │
│  加速效果: 1.5-2.5×                                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Eagle：更高效的推测

```
EAGLE (Extrapolation Algorithm for Greater Language-model Efficiency):

  改进思路: 
    Medusa 的每个 head 独立预测，没有利用前面预测的信息
    EAGLE 让预测 head 接收前面 token 的 embedding 作为输入
    → 自回归地预测多步，但在 feature 层面（更快）

  架构:
    原始模型 → 提取 hidden states
    EAGLE head (小型 Transformer):
      用 hidden states + 已猜测 token 的 embedding
      自回归生成 K 个候选 token 的 feature
      → 每步只需小 Transformer 的计算量

  性能:
    比 Medusa 快 30-50%
    接受率更高（因为利用了前文信息）
    加速比: 2-3× (vs Medusa 的 1.5-2.5×)
    
  EAGLE-2: 
    加入动态投机长度
    根据置信度自适应决定投机多少个 token
```

---

## Self-Speculative Decoding

```
核心思想: 不用额外模型，用目标模型自身做推测

  方法 1: Layer Skip
    Draft: 只跑模型前 N 层 (如 80 层只跑 20 层)
    Verify: 跑完整模型
    → 零额外显存，但需要模型训练时加入 layer dropout

  方法 2: Early Exit
    如果中间层的隐状态已经足够置信
    提前输出 token 作为 draft
    → 需要在中间层加分类头

  方法 3: Draft 阶段降低注意力精度
    Draft: 用近似 attention (如只看最近 N 个 token)
    Verify: 用完整 attention
    → 适合长上下文场景

  优势: 
    不需要额外模型，节省显存
    不需要选择/训练 draft 模型
    
  劣势:
    接受率通常低于独立 draft 模型
    加速比相对保守 (1.3-1.8×)
```

---

## 性能分析与调优

### 加速比影响因素

| 因素 | 影响 | 调优建议 |
|------|------|---------|
| **Draft 模型质量** | 接受率 ↑ → 加速 ↑ | 选同系列小模型 |
| **投机长度 K** | K ↑ → 单步产出多但浪费风险大 | 根据接受率动态调整 |
| **Temperature** | T ↑ → 接受率 ↓ | Greedy 效果最好 |
| **任务类型** | 简单 → 接受率高 | 代码/JSON 效果好 |
| **Draft 开销** | 越小越好 | Draft 参数 < 目标 10% |
| **Batch Size** | BS ↑ → 加速比 ↓ | 低 BS 效果最明显 |

### 什么时候不适合

```
Speculative Decoding 不适合的场景:

1. 高并发、大 Batch Size
   → 大 batch 时 decode 本身算力利用率已高
   → Speculative 的额外验证反而增加延迟

2. 显存紧张
   → Draft 模型需要额外显存
   → 优先考虑 Medusa/EAGLE (头参数很小)

3. Temperature 很高的采样
   → 接受率很低，大量推测被浪费

4. 非常短的生成
   → 固定开销占比大，收益不明显
```

---

## 实践指南

### vLLM 中使用 Speculative Decoding

```python
# vLLM 开箱支持 Speculative Decoding
from vllm import LLM, SamplingParams

# 方式 1: 使用独立 draft 模型
llm = LLM(
    model="meta-llama/Llama-3-70B-Instruct",
    speculative_model="meta-llama/Llama-3-8B-Instruct",
    num_speculative_tokens=5,  # 投机长度
    # use_v2_block_manager=True,  # 某些版本需要
)

# 方式 2: 使用 N-gram 匹配 (零额外显存)
llm = LLM(
    model="meta-llama/Llama-3-70B-Instruct",
    speculative_model="[ngram]",
    num_speculative_tokens=5,
    ngram_prompt_lookup_max=4,  # N-gram 窗口
)

# 正常使用
params = SamplingParams(temperature=0, max_tokens=512)
output = llm.generate("Write a Python function to sort a list", params)
```

```bash
# 命令行方式
vllm serve meta-llama/Llama-3-70B-Instruct \
    --speculative-model meta-llama/Llama-3-8B-Instruct \
    --num-speculative-tokens 5 \
    --tensor-parallel-size 4
```

---

## 小结

```
Speculative Decoding 核心要点:

1. 原理: 小模型猜、大模型验证
   数学上保证输出分布不变 → 无损加速
   加速 2-3× 是典型值

2. 关键: 接受率决定一切
   Draft 和 Target 越相似，接受率越高
   同系列小模型是最佳 Draft 选择

3. 变体很多，按需选择
   有显存 → 独立 Draft 模型 (最快)
   无显存 → Medusa/EAGLE (加头)
   不想改 → N-gram (代码场景)

4. 适合低并发、低 Temperature
   高并发时收益减少
   Greedy 解码效果最好

5. 框架已原生支持
   vLLM、SGLang 都已内置
   配置几个参数即可启用
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Leviathan, Y., Kalman, M., & Matias, Y. (2023).** *Fast Inference from Transformers via Speculative Decoding.* ICML 2023.  
   https://arxiv.org/abs/2211.17192

2. **Chen, C., et al. (2023).** *Accelerating Large Language Model Decoding with Speculative Sampling.*  
   https://arxiv.org/abs/2302.01318

3. **Cai, T., et al. (2024).** *Medusa: Simple LLM Inference Acceleration Framework with Multiple Decoding Heads.*  
   https://arxiv.org/abs/2401.10774

4. **Li, Y., et al. (2024).** *EAGLE: Speculative Sampling Requires Rethinking Feature Uncertainty.*  
   https://arxiv.org/abs/2401.15077

# 序列并行详解

> 当序列长度成为显存瓶颈时，序列并行是必经之路。

## 目录

- [为什么需要序列并行](#为什么需要序列并行)
- [Megatron-LM 序列并行](#megatron-lm-序列并行)
- [DeepSpeed Ulysses](#deepspeed-ulysses)
- [Ring Attention](#ring-attention)
- [方案对比与选择](#方案对比与选择)

---

## 为什么需要序列并行

### 长序列的显存挑战

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      长序列显存分析                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Attention 计算: Q × K^T → Softmax → × V                                 │
│   显存复杂度: O(S² × H)   S=序列长度, H=头数                              │
│                                                                             │
│   示例: LLaMA-7B, 32 heads, hidden=4096                                   │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │  序列长度    │  Attention 显存     │  激活值总显存                    │  │
│   │─────────────│────────────────────│──────────────────                │  │
│   │  4K tokens  │  ~2 GB             │  ~8 GB                          │  │
│   │  32K tokens │  ~128 GB           │  ~64 GB                         │  │
│   │  128K tokens│  ~2 TB             │  ~256 GB                        │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│   问题: 序列长度增加 → 激活值显存线性增长                                   │
│         Attention 矩阵 → 二次方增长                                        │
│   方案: 将序列维度切分到多个 GPU                                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 与其他并行方式的关系

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       并行维度正交性                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   数据并行 (DP):  切分 Batch 维度     ──── 加速计算                        │
│   张量并行 (TP):  切分 Hidden 维度    ──── 节省参数显存                     │
│   流水线并行 (PP): 切分 Layer 维度    ──── 节省参数显存                     │
│   序列并行 (SP):  切分 Sequence 维度  ──── 节省激活值显存                   │
│                                                                             │
│   4D 并行 = DP × TP × PP × SP                                             │
│                                                                             │
│   输入张量: [Batch, Sequence, Hidden]                                      │
│              ↑DP     ↑SP       ↑TP                                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Megatron-LM 序列并行

Megatron-LM 的序列并行与张量并行 (TP) 配合使用，将 **非 Attention 部分**（LayerNorm、Dropout）沿序列维度切分。

### 核心思想

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              Megatron-LM Sequence Parallelism (SP + TP)                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Transformer Layer 内部:                                                   │
│                                                                             │
│   输入 [B, S, H]                                                           │
│        │                                                                    │
│   ┌────▼────────────────┐                                                  │
│   │ LayerNorm (SP区域)  │  序列切分: 每 GPU 处理 S/N 个 token              │
│   │  GPU0: [B,S/N,H]   │  AllGather 后进入 TP 区域                        │
│   │  GPU1: [B,S/N,H]   │                                                  │
│   └────┬────────────────┘                                                  │
│        │ AllGather (S 维度)                                                 │
│   ┌────▼────────────────┐                                                  │
│   │ Self-Attention (TP)  │  张量并行: 每 GPU 计算部分头                     │
│   │ + MLP (TP)           │  按 Hidden 维度切分                              │
│   └────┬────────────────┘                                                  │
│        │ ReduceScatter (S 维度)                                             │
│   ┌────▼────────────────┐                                                  │
│   │ Dropout (SP区域)    │  序列切分: 每 GPU 处理 S/N 个 token              │
│   │ + Residual           │                                                  │
│   └────┬────────────────┘                                                  │
│        │                                                                    │
│   输出 [B, S/N, H]                                                         │
│                                                                             │
│   关键: AllReduce = AllGather + ReduceScatter                              │
│   TP 原来需要 AllReduce，拆成 AllGather + ReduceScatter 后                 │
│   SP 区域自然获得了序列维度的切分，不引入额外通信开销                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 显存节省分析

- **TP 区域**（Attention、MLP）：参数和计算按 TP 维度切分
- **SP 区域**（LayerNorm、Dropout、Residual）：激活值按序列维度切分
- **净效果**：激活值显存整体减少约 `(TP_size - 1) / TP_size`

### Megatron-LM 配置

```bash
torchrun --nproc_per_node 8 pretrain_gpt.py \
    --tensor-model-parallel-size 4 \
    --sequence-parallel \          # 启用序列并行
    --pipeline-model-parallel-size 2 \
    --seq-length 8192 \
    --micro-batch-size 1
```

---

## DeepSpeed Ulysses

DeepSpeed Ulysses 是一种**全序列维度**的并行方案，专为长序列 Attention 计算设计。

### 核心思想

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                   DeepSpeed Ulysses 原理                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   4 个 GPU, 序列长度 S, 头数 H                                             │
│                                                                             │
│   Step 1: 输入按序列维度切分                                                │
│   GPU 0: tokens [0, S/4)      Q₀, K₀, V₀                                 │
│   GPU 1: tokens [S/4, S/2)    Q₁, K₁, V₁                                 │
│   GPU 2: tokens [S/2, 3S/4)   Q₂, K₂, V₂                                 │
│   GPU 3: tokens [3S/4, S)     Q₃, K₃, V₃                                 │
│                                                                             │
│   Step 2: All-to-All 通信 (重新分布)                                       │
│   ──────────────────────────────                                            │
│   从 [每 GPU 有所有头的部分序列] → [每 GPU 有部分头的完整序列]              │
│                                                                             │
│   GPU 0: heads [0, H/4)       完整序列 S 的 Q, K, V                       │
│   GPU 1: heads [H/4, H/2)    完整序列 S 的 Q, K, V                        │
│   GPU 2: heads [H/2, 3H/4)   完整序列 S 的 Q, K, V                        │
│   GPU 3: heads [3H/4, H)     完整序列 S 的 Q, K, V                        │
│                                                                             │
│   Step 3: 每 GPU 独立计算自己负责的头的完整 Attention                       │
│   (可使用 FlashAttention)                                                   │
│                                                                             │
│   Step 4: All-to-All 通信 (还原分布)                                       │
│   从 [每 GPU 有部分头的完整序列] → [每 GPU 有所有头的部分序列]              │
│                                                                             │
│   通信量: O(S × H / N) — 与 TP AllReduce 相同                             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 使用示例

```python
import deepspeed
from deepspeed.sequence.layer import DistributedAttention

# 将标准 Attention 替换为 Ulysses 分布式 Attention
class TransformerLayer(nn.Module):
    def __init__(self, config, sp_group):
        super().__init__()
        self.attn = DistributedAttention(
            local_attention=FlashSelfAttention(),  # 本地使用 FlashAttention
            sequence_process_group=sp_group,       # 序列并行通信组
        )
    
    def forward(self, hidden_states):
        # hidden_states: [B, S/SP_size, H]
        # 内部自动执行 All-to-All → Attention → All-to-All
        attn_output = self.attn(
            query=self.q_proj(hidden_states),
            key=self.k_proj(hidden_states),
            value=self.v_proj(hidden_states),
        )
        return attn_output
```

### DeepSpeed 配置

```json
{
    "sequence_parallel_size": 4,
    "train_batch_size": 8,
    "train_micro_batch_size_per_gpu": 1,
    "bf16": {"enabled": true},
    "zero_optimization": {
        "stage": 3
    }
}
```

---

## Ring Attention

Ring Attention 将序列切分后，通过**环形传递 KV 块**实现分布式 Attention，无需 All-to-All 全量通信。

### 核心思想

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      Ring Attention 原理                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   4 个 GPU 组成环形拓扑:                                                    │
│                                                                             │
│              GPU 0 ──────► GPU 1                                            │
│                ▲              │                                              │
│                │              ▼                                              │
│              GPU 3 ◄────── GPU 2                                            │
│                                                                             │
│   每个 GPU 持有:                                                            │
│   - 自己的 Q 块 (固定不动)                                                  │
│   - 当前轮次的 KV 块 (环形传递)                                             │
│                                                                             │
│   Round 0: GPU_i 用自己的 Q_i 和 KV_i 计算局部 Attention                   │
│   Round 1: GPU_i 接收 KV_{i-1}, 计算 Q_i × KV_{i-1}                       │
│   Round 2: GPU_i 接收 KV_{i-2}, 计算 Q_i × KV_{i-2}                       │
│   Round 3: GPU_i 接收 KV_{i-3}, 计算 Q_i × KV_{i-3}                       │
│                                                                             │
│   每轮: 计算与 KV 传输重叠 (overlap)                                        │
│   总轮数: N-1 次传递 (N 个 GPU)                                             │
│                                                                             │
│   输出: 在线 Softmax 聚合所有轮次的局部结果                                 │
│   通信: 点对点 Send/Recv, 可与计算完全重叠                                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 与 Flash Attention 结合

Ring Attention 的每一轮局部计算可以使用 FlashAttention 加速：

```python
# 伪代码: Ring Attention 核心逻辑
def ring_attention(q_local, k_local, v_local, ring_group):
    """
    q_local: [B, S/N, num_heads, head_dim]  -- 固定在本 GPU
    k_local, v_local: [B, S/N, num_heads, head_dim]  -- 会在环中传递
    """
    rank = dist.get_rank(ring_group)
    world_size = dist.get_size(ring_group)
    
    # 在线 softmax 累积变量
    output = torch.zeros_like(q_local)
    lse = torch.full((...), float('-inf'))  # log-sum-exp
    
    k_recv = torch.empty_like(k_local)
    v_recv = torch.empty_like(v_local)
    
    for step in range(world_size):
        # 异步发送当前 KV 到下一个 GPU，同时接收上一个 GPU 的 KV
        if step < world_size - 1:
            send_rank = (rank + 1) % world_size
            recv_rank = (rank - 1) % world_size
            send_op = dist.isend(k_local, send_rank, group=ring_group)
            recv_op = dist.irecv(k_recv, recv_rank, group=ring_group)
        
        # 计算当前块的局部 Attention (使用 FlashAttention)
        local_out, local_lse = flash_attention(q_local, k_local, v_local)
        
        # 在线 Softmax 合并
        output, lse = online_softmax_merge(output, lse, local_out, local_lse)
        
        # 等待通信完成，交换 buffer
        if step < world_size - 1:
            send_op.wait()
            recv_op.wait()
            k_local, k_recv = k_recv, k_local
            v_local, v_recv = v_recv, v_local
    
    return output
```

### 优势

- 通信可与计算完全重叠，理论上零额外开销
- 显存复杂度从 O(S²) 降为 O(S²/N²)（N 个 GPU）
- 支持超长序列（百万级 tokens）

---

## 方案对比与选择

| 特性 | Megatron SP | DeepSpeed Ulysses | Ring Attention |
|------|-------------|-------------------|----------------|
| **切分范围** | 非 Attention 部分 | Attention (头维度) | Attention (序列块) |
| **通信模式** | AllGather + ReduceScatter | All-to-All | 点对点 Send/Recv |
| **与 TP 关系** | 必须配合 TP 使用 | 独立于 TP | 独立于 TP |
| **额外通信** | 无 (复用 TP 通信) | O(S×H/N) | O(S×H/N)，可重叠 |
| **最大序列长度** | 受限于单 GPU | 受限于单 GPU 头数 | 近乎无限 |
| **FlashAttention** | 兼容 | 兼容 | 原生结合 |
| **实现复杂度** | 低 | 中 | 高 |
| **推荐场景** | 4K-32K, 已有 TP | 8K-128K, DeepSpeed 用户 | 128K+, 超长上下文 |

### 选择建议

```
序列长度 < 8K?
├── 是 → 不需要序列并行，TP + Activation Checkpointing 够用
└── 否 → 8K-32K?
    ├── 是 → Megatron SP (如已使用 TP) 或 DeepSpeed Ulysses
    └── 否 → 32K-128K?
        ├── 是 → DeepSpeed Ulysses 或 Ring Attention
        └── 否 → > 128K → Ring Attention
```

---

## 📚 延伸阅读

- [Reducing Activation Recomputation in Large Transformer Models](https://arxiv.org/abs/2205.05198) - Megatron-LM SP 论文
- [DeepSpeed Ulysses: System Optimizations for Enabling Training of Extreme Long Sequence Transformer Models](https://arxiv.org/abs/2309.14509)
- [Ring Attention with Blockwise Transformers for Near-Infinite Context](https://arxiv.org/abs/2310.01889)
- [Striped Attention](https://arxiv.org/abs/2311.09431) - Ring Attention 的负载均衡改进

---

*返回目录：[README](README.md)*

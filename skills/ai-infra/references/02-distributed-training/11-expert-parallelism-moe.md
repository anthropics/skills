# 专家并行与 MoE（Mixture-of-Experts）

> 用稀疏激活实现参数量的大幅扩展，同时控制计算成本。

## 目录

- [MoE 基础原理](#moe-基础原理)
- [专家并行（Expert Parallelism）](#专家并行expert-parallelism)
- [主流 MoE 架构](#主流-moe-架构)
- [训练与部署挑战](#训练与部署挑战)
- [框架支持](#框架支持)

---

## MoE 基础原理

### 什么是 MoE

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Mixture-of-Experts 基本结构                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   标准 Transformer FFN:                                                     │
│   Input → [Dense FFN (全部参数参与)] → Output                               │
│   参数量: 2 × d_model × d_ffn                                              │
│   每 token 计算量: 2 × d_model × d_ffn FLOPs                               │
│                                                                             │
│   MoE Transformer FFN:                                                      │
│   Input → [Router → Top-K Experts (稀疏激活)] → Output                     │
│                                                                             │
│                    ┌────────────┐                                            │
│                    │   Router   │  门控网络: W_g × input → expert scores     │
│                    │  (Gating)  │  选择 Top-K 个专家                        │
│                    └─────┬──────┘                                            │
│              ┌─────┬─────┼─────┬─────┐                                      │
│              ▼     ▼     ▼     ▼     ▼                                      │
│           ┌─────┬─────┬─────┬─────┬─────┐                                  │
│           │ E_0 │ E_1 │ E_2 │ E_3 │ ... │  N 个专家 (各自是独立的 FFN)     │
│           └──┬──┴──┬──┴─────┴─────┴─────┘                                  │
│              ▼     ▼    (只有 Top-K 被激活)                                  │
│           ┌─────────────┐                                                   │
│           │ 加权求和输出  │  output = Σ gate_score_i × expert_i(input)      │
│           └─────────────┘                                                   │
│                                                                             │
│   关键特性:                                                                 │
│   • 总参数量 ∝ N × expert_size (可达万亿级)                                │
│   • 每 token 计算量 ∝ K × expert_size (仅 K 个专家激活)                    │
│   • 典型 Top-K = 1 或 2                                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 路由机制

```python
import torch
import torch.nn as nn
import torch.nn.functional as F

class TopKRouter(nn.Module):
    """Top-K 门控路由"""
    def __init__(self, d_model, num_experts, top_k=2):
        super().__init__()
        self.gate = nn.Linear(d_model, num_experts, bias=False)
        self.top_k = top_k
        self.num_experts = num_experts
    
    def forward(self, x):
        # x: [batch, seq_len, d_model]
        logits = self.gate(x)  # [batch, seq_len, num_experts]
        
        # Top-K 选择
        top_k_logits, top_k_indices = torch.topk(logits, self.top_k, dim=-1)
        top_k_scores = F.softmax(top_k_logits, dim=-1)
        
        return top_k_scores, top_k_indices  # 分数和索引

class MoELayer(nn.Module):
    """简化的 MoE 层"""
    def __init__(self, d_model, d_ffn, num_experts, top_k=2):
        super().__init__()
        self.router = TopKRouter(d_model, num_experts, top_k)
        self.experts = nn.ModuleList([
            nn.Sequential(
                nn.Linear(d_model, d_ffn),
                nn.GELU(),
                nn.Linear(d_ffn, d_model)
            ) for _ in range(num_experts)
        ])
    
    def forward(self, x):
        scores, indices = self.router(x)  # [B, S, K], [B, S, K]
        
        output = torch.zeros_like(x)
        for k in range(self.router.top_k):
            expert_idx = indices[:, :, k]   # [B, S]
            expert_score = scores[:, :, k]  # [B, S]
            
            for i, expert in enumerate(self.experts):
                mask = (expert_idx == i)
                if mask.any():
                    expert_input = x[mask]
                    expert_output = expert(expert_input)
                    output[mask] += expert_score[mask].unsqueeze(-1) * expert_output
        
        return output
```

---

## 专家并行（Expert Parallelism）

### 为什么需要专家并行

MoE 模型总参数量巨大（如 Mixtral 8×7B 总参数 ~47B），无法全部放入单个 GPU。专家并行将不同专家分配到不同 GPU 上。

### 并行方案

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    专家并行 (Expert Parallelism, EP)                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   8 个专家, 4 个 GPU, EP_size = 4                                          │
│                                                                             │
│   GPU 0: Expert 0, Expert 1                                                │
│   GPU 1: Expert 2, Expert 3                                                │
│   GPU 2: Expert 4, Expert 5                                                │
│   GPU 3: Expert 6, Expert 7                                                │
│                                                                             │
│   通信流程:                                                                 │
│                                                                             │
│   Step 1: Router 在每个 GPU 上独立计算路由决策                              │
│   ┌─────────────────────────────────────────┐                               │
│   │ 每个 token 确定要去哪个专家 (All-to-All) │                              │
│   └─────────────────────────────────────────┘                               │
│                                                                             │
│   Step 2: All-to-All 通信 (Dispatch)                                       │
│   ┌─────────────────────────────────────────┐                               │
│   │ 每个 GPU 将 token 发送到目标专家所在 GPU │                              │
│   │ GPU 0 的部分 token → GPU 2 (如果路由到 E4/E5)                          │
│   └─────────────────────────────────────────┘                               │
│                                                                             │
│   Step 3: 各 GPU 在本地专家上计算                                           │
│                                                                             │
│   Step 4: All-to-All 通信 (Combine)                                        │
│   ┌─────────────────────────────────────────┐                               │
│   │ 将专家输出发送回 token 原来所在的 GPU    │                              │
│   └─────────────────────────────────────────┘                               │
│                                                                             │
│   通信量: O(B × S × H × top_k / N)                                        │
│   瓶颈: All-to-All 通信 (需要高速互联)                                     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### EP 与其他并行方式组合

```
┌─────────────────────────────────────────────────────────────────────────────┐
│               EP + TP + DP + PP 组合 (以 64 GPU 为例)                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   总 GPU: 64                                                               │
│   DP = 4, TP = 2, PP = 2, EP = 4                                          │
│   验证: 4 × 2 × 2 = 16 (每个 EP 组)  × 4 (EP) = 64 ✓                    │
│                                                                             │
│   非 MoE 层 (Attention, LayerNorm):                                        │
│   使用 DP × TP × PP 并行                                                   │
│                                                                             │
│   MoE 层:                                                                   │
│   使用 DP × EP × PP 并行 (EP 替代 TP)                                      │
│   每个 EP rank 持有 num_experts / EP_size 个专家                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 主流 MoE 架构

### 对比表

| 模型 | 总参数 | 激活参数 | 专家数 | Top-K | 特点 |
|------|--------|----------|--------|-------|------|
| **Mixtral 8×7B** | ~47B | ~13B | 8 | 2 | 开源、性能接近 LLaMA-2 70B |
| **DeepSeek-V2** | 236B | 21B | 160 | 6 | 细粒度专家、共享专家 |
| **DeepSeek-V3** | 671B | 37B | 256+1 | 8 | 辅助 loss-free 负载均衡 |
| **Qwen2-MoE** | 57B | 14B | 64 | 8 (共享4+路由4) | 共享专家+路由专家 |
| **DBRX** | 132B | 36B | 16 | 4 | 细粒度专家 |
| **Switch Transformer** | 1.6T | ~对应 T5 | 2048 | 1 | Top-1 路由，简化 MoE |

### DeepSeek-V2 创新：细粒度专家 + 共享专家

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              DeepSeek-V2 MoE 架构创新                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统 MoE (Mixtral):                                                       │
│   8 个大专家, Top-2 → 每 token 激活 2/8 = 25% 参数                        │
│                                                                             │
│   DeepSeek-V2:                                                              │
│   2 个共享专家 (Shared) + 160 个路由专家 (Routed), Top-6                   │
│                                                                             │
│   ┌──────────────┐  ┌──────────────┐  ┌─────────────────────────────────┐  │
│   │ Shared Exp 1 │  │ Shared Exp 2 │  │ Routed Experts (160 个小专家)   │  │
│   │  (always on) │  │  (always on) │  │  Router 选择 Top-6             │  │
│   └──────┬───────┘  └──────┬───────┘  └──────────────┬──────────────────┘  │
│          │                 │                          │                      │
│          └─────────────────┼──────────────────────────┘                      │
│                            ▼                                                 │
│                     加权求和输出                                             │
│                                                                             │
│   优势:                                                                     │
│   • 共享专家学习通用特征，路由专家学习专业特征                              │
│   • 细粒度专家 (更小但更多) → 更灵活的路由                                  │
│   • 激活参数比更低，效率更高                                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 训练与部署挑战

### 负载均衡问题

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       负载均衡挑战                                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   问题: Router 可能将大量 token 路由到少数专家 → 负载不均                   │
│                                                                             │
│   Expert 0: ████████████████████  (80% tokens)  ← 过载                     │
│   Expert 1: ██                    (5% tokens)                               │
│   Expert 2: ███                   (10% tokens)                              │
│   Expert 3: █                     (5% tokens)   ← 闲置                     │
│                                                                             │
│   后果:                                                                     │
│   1. 过载专家成为计算瓶颈                                                   │
│   2. 闲置专家浪费 GPU 算力                                                  │
│   3. Token 溢出被丢弃 → 影响模型质量                                        │
│                                                                             │
│   解决方案:                                                                 │
│                                                                             │
│   方案 1: Auxiliary Load Balancing Loss                                     │
│   L_aux = α × N × Σ(f_i × P_i)                                            │
│   f_i = 专家 i 被分配的 token 比例                                          │
│   P_i = 路由到专家 i 的概率均值                                             │
│   鼓励均匀分配                                                             │
│                                                                             │
│   方案 2: Expert Capacity (容量限制)                                        │
│   capacity = (tokens / num_experts) × capacity_factor                      │
│   超出容量的 token 被丢弃或路由到其他专家                                   │
│                                                                             │
│   方案 3: DeepSeek-V3 Auxiliary-loss-free (无辅助损失)                      │
│   使用可学习的 bias 偏置项直接调节负载                                      │
│   避免辅助损失对模型质量的影响                                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### MoE 推理挑战

| 挑战 | 原因 | 缓解方案 |
|------|------|----------|
| **显存占用大** | 所有专家参数都需加载 | Offload 到 CPU/NVMe |
| **通信开销** | All-to-All 延迟高 | 推理时减少 EP 规模 |
| **低 batch 利用率** | Top-K 路由导致每个专家只处理少量 token | 增大 batch size |
| **动态计算图** | 不同 token 走不同路径 | 使用 Triton kernel 优化 |

---

## 框架支持

### Megatron-LM MoE

```bash
torchrun --nproc_per_node 8 pretrain_gpt.py \
    --num-experts 8 \
    --expert-model-parallel-size 4 \     # EP size
    --tensor-model-parallel-size 2 \     # TP size
    --moe-router-topk 2 \
    --moe-router-load-balancing-type aux_loss \
    --moe-aux-loss-coeff 0.01
```

### DeepSpeed MoE

```python
import deepspeed.moe.layer as moe_layer

# 替换 Transformer 中的 FFN 为 MoE
moe_ffn = moe_layer.MoE(
    hidden_size=4096,
    expert=FeedForward(4096, 11008),  # 单个专家
    num_experts=8,
    ep_size=4,                         # Expert Parallelism size
    k=2,                               # Top-K
    use_residual=True,                 # 残差 MoE
    capacity_factor=1.25,              # 容量因子
)
```

### Hugging Face Transformers (Mixtral)

```python
from transformers import AutoModelForCausalLM, AutoTokenizer

# Mixtral 使用专家并行推理
model = AutoModelForCausalLM.from_pretrained(
    "mistralai/Mixtral-8x7B-v0.1",
    torch_dtype=torch.bfloat16,
    device_map="auto",  # 自动将不同专家分布到多 GPU
)
```

---

## 📚 延伸阅读

- [Switch Transformers](https://arxiv.org/abs/2101.03961) - 简化 MoE, Top-1 路由
- [Mixtral of Experts](https://arxiv.org/abs/2401.04088) - Mixtral 技术报告
- [DeepSeekMoE](https://arxiv.org/abs/2401.06066) - 细粒度专家并行
- [DeepSeek-V3 Technical Report](https://arxiv.org/abs/2412.19437) - 无辅助损失负载均衡
- [MegaBlocks](https://arxiv.org/abs/2211.15841) - 高效 MoE 训练系统

---

*返回目录：[README](README.md)*

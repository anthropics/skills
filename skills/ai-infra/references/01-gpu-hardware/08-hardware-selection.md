# 硬件选型指南

> 根据场景需求选择合适的 GPU 硬件。

## 目录

- [场景分析](#场景分析)
- [显存需求估算](#显存需求估算)
- [GPU 选型推荐](#gpu-选型推荐)
- [选型决策树](#选型决策树)
- [集群规划](#集群规划)

---

## 场景分析

### 生活类比：买车选型

```
选 GPU 就像买车，不同用途对应不同车型：

  RTX 4090:      家用 SUV
    价格实惠，性能不错，但拉不了太重的货
    适合：7B 推理、小模型训练、学习实验

  A100 80GB:     货运卡车
    专业工具，能力全面，市场保有量最大
    适合：中小模型训练、批量推理

  H100:          重型拖头
    最强动力，最高效率，价格惊人
    适合：大模型训练、高吞吐推理

  B200:          航母
    192GB 显存，8TB/s 带宽，用核反应堆驱动(1000W)
    适合：超大模型、前沿研究

选车不是越贵越好，而是"够用 + 性价比最优"
```

### 按场景选择

| 场景 | 推荐 GPU | 理由 |
|------|----------|------|
| **LLM 推理（小规模）** | RTX 4090 / L40S | 24GB/48GB，性价比高 |
| **LLM 推理（生产）** | A100 / H100 | 高带宽，Tensor Core 优化 |
| **LLM 训练（≤7B）** | 4×A100 80GB | 显存充足 |
| **LLM 训练（7B-70B）** | 8×A100 80GB / 8×H100 | 需要 NVLink 互联 |
| **LLM 训练（>70B）** | 多机 H100 集群 | 3D 并行 + IB |
| **微调 (LoRA/QLoRA)** | RTX 4090 / A100 40GB | LoRA 显存需求小 |
| **研究实验** | RTX 4090 × 1-2 | 成本低，快速迭代 |
| **边缘推理** | Jetson Orin | 低功耗，嵌入式 |

---

## 显存需求估算

### 推理显存公式

```python
def estimate_inference_memory(params_billion, precision="fp16",
                               batch_size=1, seq_len=2048):
    """
    推理显存 = 模型参数 + KV Cache + 激活值
    """
    bytes_per_param = {"fp32": 4, "fp16": 2, "bf16": 2, 
                        "int8": 1, "int4": 0.5}[precision]
    
    # 模型参数
    model_gb = params_billion * bytes_per_param
    
    # KV Cache 估算（Transformer 模型）
    # 每层: 2(K,V) × batch × seq × n_heads × head_dim × bytes
    # 简化公式: ~0.5 × params_B × batch × (seq/2048) GB (FP16)
    kv_cache_gb = 0.5 * params_billion * batch_size * (seq_len / 2048)
    if precision in ["int8", "int4"]:
        kv_cache_gb *= 0.5  # KV Cache 也可以量化
    
    # 激活值 (中间计算结果，相对较小)
    activation_gb = 0.1 * params_billion * batch_size
    
    total = model_gb + kv_cache_gb + activation_gb
    return {
        "model": model_gb,
        "kv_cache": kv_cache_gb,
        "activation": activation_gb,
        "total": total
    }

# 常见场景估算
for model_size in [7, 13, 30, 70]:
    mem = estimate_inference_memory(model_size, "fp16", batch_size=1)
    mem_int8 = estimate_inference_memory(model_size, "int8", batch_size=1)
    print(f"{model_size}B FP16: ~{mem['total']:.0f} GB  |  INT8: ~{mem_int8['total']:.0f} GB")
```

```
结果参考:
  7B  FP16: ~18 GB   INT8: ~10 GB   → 1×RTX 4090(24GB) 可跑
  13B FP16: ~33 GB   INT8: ~18 GB   → 1×A100 40GB 或 INT8 1×4090
  30B FP16: ~75 GB   INT8: ~40 GB   → 1×A100 80GB 或 INT8 1×A100 40GB
  70B FP16: ~175 GB  INT8: ~92 GB   → 2×A100 80GB 或 INT8 2×A100 40GB

注意：batch_size 增加时 KV Cache 线性增长！
  70B FP16 batch=32: KV Cache 从 35GB 涨到 ~1.1TB → 需要分布式
```

### 训练显存公式

```python
def estimate_training_memory(params_billion, optimizer="adamw",
                              precision="fp16", batch_size=4, seq_len=2048):
    """
    训练显存 = 模型参数 + 梯度 + 优化器状态 + 激活值
    """
    # 模型状态
    if precision == "fp16":
        param_bytes = 2  # FP16 参数
        grad_bytes = 2   # FP16 梯度
    else:
        param_bytes = 4  # FP32 参数
        grad_bytes = 4
    
    # 优化器状态
    if optimizer == "adamw":
        # FP32 参数副本(4B) + m(4B) + v(4B) = 12B/param
        optim_bytes = 12
    elif optimizer == "sgd":
        optim_bytes = 4  # 只有动量
    else:
        optim_bytes = 0
    
    model_state_gb = params_billion * (param_bytes + grad_bytes + optim_bytes)
    
    # 激活值（最大的变量！）
    # 粗略估算：每层 ~2 × batch × seq × hidden × 2 bytes
    # 对于 Transformer: ~12 × batch × seq × hidden × num_layers × 2 bytes
    # 简化: ~5 × params_B × batch × (seq/2048) GB
    activation_gb = 5 * params_billion * batch_size * (seq_len / 2048)
    
    # 使用激活值重算 (activation checkpointing) 可减少到约 1/L
    activation_with_ckpt = activation_gb / 32  # 假设 32 层
    
    return {
        "model_state": model_state_gb,
        "activation": activation_gb,
        "activation_with_ckpt": activation_with_ckpt,
        "total": model_state_gb + activation_gb,
        "total_with_ckpt": model_state_gb + activation_with_ckpt,
    }

# 常见模型的训练显存
print("模型训练显存估算 (AdamW, FP16, batch=4, seq=2048):")
for size in [7, 13, 70]:
    mem = estimate_training_memory(size)
    print(f"\n{size}B 模型:")
    print(f"  模型状态: {mem['model_state']:.0f} GB")
    print(f"  激活值: {mem['activation']:.0f} GB")
    print(f"  总计: {mem['total']:.0f} GB")
    print(f"  使用激活重算: {mem['total_with_ckpt']:.0f} GB")
```

```
结果参考:
  7B:  模型状态 112GB + 激活 140GB = 252 GB → 需要 4×A100 80GB + ZeRO
       使用激活重算: 112 + 4.4 = 116 GB → 2×A100 80GB + ZeRO
  
  13B: 模型状态 208GB + 激活 260GB = 468 GB → 8×A100 80GB
  70B: 模型状态 1120GB + 激活 1400GB = 2520 GB → 多机 H100
```

### 显存估算速查表

| 模型 | 推理 FP16 | 推理 INT8 | 训练 (w/ ckpt) | 推荐配置 |
|------|----------|----------|---------------|---------|
| 7B | ~18 GB | ~10 GB | ~116 GB | 推理:1×4090, 训练:2×A100 |
| 13B | ~33 GB | ~18 GB | ~215 GB | 推理:1×A100, 训练:4×A100 |
| 30B | ~75 GB | ~40 GB | ~495 GB | 推理:1×A100 80G, 训练:8×A100 |
| 70B | ~175 GB | ~92 GB | ~1155 GB | 推理:2×H100, 训练:多机 H100 |

---

## GPU 选型推荐

### 消费级 GPU

| GPU | 显存 | FP32 算力 | 价格 | 适用 | 性价比 |
|-----|------|----------|------|------|--------|
| RTX 4060 | 8 GB | 15 TFLOPS | ~$300 | 学习/小推理 | ★★★ |
| RTX 4070 | 12 GB | 29 TFLOPS | ~$550 | 7B INT4推理 | ★★★ |
| RTX 4080 | 16 GB | 48 TFLOPS | ~$1000 | 7B FP16推理 | ★★ |
| RTX 4090 | 24 GB | 82 TFLOPS | ~$1600 | 7B推理+LoRA | ★★★★ |

```
消费级 GPU 的隐形限制：
  1. 没有 NVLink → 多卡通信只走 PCIe → 训练效率低
  2. 没有 MIG → 不能分割给多个用户
  3. 没有 ECC → 长时间计算可能出错（罕见但存在）
  4. NVIDIA 驱动限制 → 部分数据中心功能不可用
  
  但对于个人学习和小规模实验，RTX 4090 是无可争议的性价比之王
```

### 数据中心 GPU

| GPU | 显存 | FP16 算力 | NVLink | 适用场景 |
|-----|------|----------|--------|----------|
| A100 40GB | 40 GB | 312 TFLOPS | 600 GB/s | 推理/小训练 |
| A100 80GB | 80 GB | 312 TFLOPS | 600 GB/s | 训练主力 |
| H100 SXM | 80 GB | 1,979 TFLOPS | 900 GB/s | 大模型训练 |
| H100 NVL | 94 GB | 1,979 TFLOPS | 600 GB/s | 双卡推理 |
| L40S | 48 GB | 733 TFLOPS | 无 | 推理优化 |
| B200 | 192 GB | 4,500 TFLOPS | 1,800 GB/s | 超大模型 |

```
选择 SXM vs PCIe 版本：
  SXM 版 (如 H100 SXM):
    + 支持 NVLink（900 GB/s）
    + TDP 更高（700W → 更高频率）
    + 需要 DGX 或专用服务器
    
  PCIe 版 (如 H100 PCIe):
    + 兼容普通服务器
    + 价格更低
    - 无 NVLink（只有 PCIe 64 GB/s）
    - TDP 较低（350W）
    
  训练用 SXM，推理可以 PCIe
```

---

## 选型决策树

```
你的主要任务是什么？
│
├── 推理
│   │
│   ├── 模型多大？
│   │   ├── ≤ 7B
│   │   │   ├── 低延迟要求？→ RTX 4090（FP16 24GB 够用）
│   │   │   └── 高吞吐？→ A100/L40S（batch 更大）
│   │   │
│   │   ├── 7B - 30B
│   │   │   ├── 预算有限？→ A100 40GB + INT8 量化
│   │   │   └── 性能优先？→ A100 80GB 或 H100
│   │   │
│   │   └── > 30B
│   │       └── 2-4×A100/H100（张量并行）
│   │
│   └── 用量化吗？
│       ├── GPTQ/AWQ INT4: 显存需求减半
│       └── FP16 全精度: 按上表估算
│
├── 训练
│   │
│   ├── 全参数训练
│   │   ├── ≤ 7B → 2-4×A100 80GB + ZeRO
│   │   ├── 7-13B → 8×A100 80GB + ZeRO
│   │   ├── 13-70B → 8×H100 + ZeRO/3D并行
│   │   └── >70B → 多机 H100 + 3D 并行 + IB
│   │
│   └── 参数高效微调 (LoRA/QLoRA)
│       ├── ≤ 13B → 1×RTX 4090（QLoRA 只需 ~10GB）
│       ├── 13-30B → 1×A100 80GB
│       └── >30B → 2×A100 80GB
│
└── 研究/实验
    ├── 快速迭代 → 1-2×RTX 4090
    └── 需要复现论文 → A100/H100（与论文环境一致）
```

---

## 集群规划

### 小型团队 (2-5人)

```
推荐：1 台 8×A100 80GB 服务器
  预算：~$150K (二手) - $300K
  
  能做什么：
  - 7B 模型全参数训练 ✅
  - 13B 模型 QLoRA 微调 ✅
  - 70B 模型 INT8 推理 ✅
  - 30B 模型训练 ✅ (ZeRO-3)
  
  扩展建议：
  加一台相同配置 + IB HDR 交换机 → 70B 训练能力
```

### 中型团队 (5-20人)

```
推荐：4-8 台 8×H100 + IB NDR
  预算：~$2M - $5M
  
  能做什么：
  - 70B 模型全参数训练 ✅
  - 100B+ 模型探索 ✅
  - 多人同时微调 ✅ (MIG 分割)
  - 大规模推理服务 ✅
  
  关键决策：
  1. 选 DGX H100 (方便) 还是白盒服务器 (便宜)?
  2. 网络选 IB HDR (省钱) 还是 NDR (未来不用升级)?
  3. 存储选什么？推荐 Lustre/GPFS + NVMe Cache
```

### 考虑总拥有成本 (TCO)

```
GPU 购买只是总成本的一部分：

┌────────────────────────────────────────────────┐
│  成本构成（以 8×H100 服务器为例，3 年）        │
├────────────────────────────────────────────────┤
│  GPU 服务器:     ~$300K (一次性)               │
│  网络设备:       ~$50K  (IB 交换机)            │
│  电力成本:       ~$75K  (5.5kW × 3年)          │
│  散热/机柜:      ~$30K                          │
│  运维人力:       ~$100K                          │
│  ────────────────────────────────              │
│  3 年 TCO:       ~$555K                        │
│                                                 │
│  对比云服务（8×H100 按需）:                     │
│  ~$28/h × 24h × 365d × 3y = ~$735K            │
│  利用率 70%: $735K × 0.7 = ~$515K             │
│                                                 │
│  结论：                                         │
│  利用率 > 75% → 自建更划算                     │
│  利用率 < 50% → 云服务更划算                   │
│  弹性需求大 → 混合方案（自建基线 + 云上弹性） │
└────────────────────────────────────────────────┘
```

---

## 实战练习

### 练习：评估你的 GPU

```python
import torch

def gpu_evaluation():
    if not torch.cuda.is_available():
        print("CUDA 不可用")
        return
    
    props = torch.cuda.get_device_properties(0)
    mem_gb = props.total_memory / 1024**3
    
    print(f"=== GPU 评估报告 ===")
    print(f"型号: {props.name}")
    print(f"显存: {mem_gb:.1f} GB")
    print(f"计算能力: {props.major}.{props.minor}")
    print(f"SM 数量: {props.multi_processor_count}")
    
    # 能跑什么模型？
    print(f"\n=== 推理能力 ===")
    for name, size_b in [("1.5B", 1.5), ("7B", 7), ("13B", 13), ("30B", 30), ("70B", 70)]:
        fp16_gb = size_b * 2 + size_b * 0.5  # 参数 + KV Cache
        int8_gb = size_b * 1 + size_b * 0.25
        int4_gb = size_b * 0.5 + size_b * 0.125
        
        status = "❌"
        method = ""
        if fp16_gb < mem_gb * 0.9:
            status = "✅ FP16"
        elif int8_gb < mem_gb * 0.9:
            status = "✅ INT8"
        elif int4_gb < mem_gb * 0.9:
            status = "✅ INT4"
        
        print(f"  {name:5s}: {status}")
    
    print(f"\n=== LoRA 微调能力 ===")
    for name, size_b in [("7B", 7), ("13B", 13), ("30B", 30)]:
        # QLoRA: 模型 INT4 + LoRA FP16 + 梯度 + 优化器
        qlora_gb = size_b * 0.5 + size_b * 0.05 * 2 + size_b * 0.05 * 12 + 2
        status = "✅" if qlora_gb < mem_gb * 0.9 else "❌"
        print(f"  {name:5s} QLoRA: {status} (需要 ~{qlora_gb:.0f} GB)")

gpu_evaluation()
```

---

## 小结

```
硬件选型核心原则：

1. 显存第一: 模型放不下一切都白搭
   → 先算显存需求，再选 GPU

2. 场景匹配: 训练和推理的需求完全不同
   → 训练看算力+互联，推理看带宽+显存

3. 不要过度配置: RTX 4090 能解决的问题不用上 H100
   → QLoRA 7B 只需一张 4090，不需要 8×A100

4. 互联决定上限: 多卡训练的效率取决于通信带宽
   → 训练大模型必须 NVLink + IB

5. TCO 思维: 考虑 3 年总成本，不只是 GPU 价格
   → 利用率是关键——自建 vs 云的分水岭在 ~50%
```

---

*返回：[README.md](README.md) - 章节索引*

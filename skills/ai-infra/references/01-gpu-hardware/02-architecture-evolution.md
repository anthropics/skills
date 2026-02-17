# GPU 架构演进

> 从 Volta 到 Blackwell，NVIDIA GPU 如何一步步为 AI 工作负载优化。

## 目录

- [架构演进时间线](#架构演进时间线)
- [Volta 架构 (2017)](#volta-架构-2017)
- [Ampere 架构 (2020)](#ampere-架构-2020)
- [Hopper 架构 (2022)](#hopper-架构-2022)
- [Blackwell 架构 (2024)](#blackwell-架构-2024)
- [关键规格对比](#关键规格对比)
- [架构选型建议](#架构选型建议)

---

## 架构演进时间线

```
2017 ──── Volta (V100) ────────── 首次引入 Tensor Core
   │
2020 ──── Ampere (A100) ────────── 第三代 Tensor Core，支持 TF32/BF16
   │
2022 ──── Hopper (H100) ────────── 第四代 Tensor Core，Transformer Engine
   │
2024 ──── Blackwell (B100/B200) ── 第五代，FP4 支持，更强 NVLink
```

---

## Volta 架构 (2017)

### 里程碑意义

Volta 是第一个真正为深度学习设计的数据中心 GPU，**首次引入 Tensor Core**。

### 关键规格 (V100)

| 指标 | 数值 |
|------|------|
| SM 数量 | 80 |
| CUDA Cores | 5,120 |
| Tensor Cores | 640 |
| FP32 峰值 | 15.7 TFLOPS |
| FP16 峰值 (Tensor) | 125 TFLOPS |
| 显存 | 32 GB HBM2 |
| 带宽 | 900 GB/s |
| TDP | 300W |

### 第一代 Tensor Core

```
D = A × B + C

┌───────┐   ┌───────┐   ┌───────┐   ┌───────┐
│ A     │ × │ B     │ + │ C     │ = │ D     │
│ 4×4   │   │ 4×4   │   │ 4×4   │   │ 4×4   │
│ FP16  │   │ FP16  │   │ FP32  │   │ FP32  │
└───────┘   └───────┘   └───────┘   └───────┘

每个 Tensor Core 每周期: 64 FMA = 128 FLOPs
```

---

## Ampere 架构 (2020)

### 关键创新

1. **TF32 格式**：FP32 范围 + 10-bit 尾数，无需修改代码即可加速
2. **结构化稀疏 2:4**：每 4 个元素最多 2 个非零，实现 2x 加速
3. **MIG (多实例 GPU)**：将一个 A100 分割为最多 7 个独立实例

### 关键规格 (A100 80GB)

| 指标 | 数值 |
|------|------|
| SM 数量 | 108 |
| CUDA Cores | 6,912 |
| Tensor Cores | 432 |
| FP32 峰值 | 19.5 TFLOPS |
| TF32 峰值 | 156 TFLOPS |
| FP16 峰值 (Tensor) | 312 TFLOPS |
| 显存 | 80 GB HBM2e |
| 带宽 | 2.0 TB/s |
| TDP | 400W |

### TF32 数据格式

```
FP32:  [1 sign][8 exponent][23 mantissa] = 32 bits
TF32:  [1 sign][8 exponent][10 mantissa] = 19 bits (内部使用)

优势: 与 FP32 相同范围，Tensor Core 自动使用，~8x 加速
```

---

## Hopper 架构 (2022)

### 关键创新

1. **FP8 支持**：E4M3 (训练) / E5M2 (梯度) 两种格式
2. **Transformer Engine**：自动管理 FP8/FP16 精度切换
3. **DPX 指令**：动态规划加速，基因组学应用快 7x

### 关键规格 (H100 SXM)

| 指标 | 数值 |
|------|------|
| SM 数量 | 132 |
| CUDA Cores | 16,896 |
| Tensor Cores | 528 |
| FP32 峰值 | 67 TFLOPS |
| TF32 峰值 | 989 TFLOPS |
| FP16 峰值 (Tensor) | 1,979 TFLOPS |
| FP8 峰值 | 3,958 TFLOPS |
| 显存 | 80 GB HBM3 |
| 带宽 | 3.35 TB/s |
| NVLink 带宽 | 900 GB/s |
| TDP | 700W |

### FP8 数据格式

```
E4M3: [1 sign][4 exp][3 mantissa] - 范围 ±448, 精度较高 (训练)
E5M2: [1 sign][5 exp][2 mantissa] - 范围 ±57344, 精度较低 (梯度)
```

---

## Blackwell 架构 (2024)

### 关键创新

1. **双芯片封装**：2080 亿晶体管，突破单芯片极限
2. **FP4 支持**：9 PFLOPS 峰值性能
3. **第二代 Transformer Engine**：微张量缩放
4. **NVLink 5.0**：1.8 TB/s 带宽，支持 72 GPU 互联

### 关键规格 (B200)

| 指标 | 数值 |
|------|------|
| 晶体管 | 2080 亿 |
| FP32 峰值 | 90 TFLOPS |
| FP16 峰值 | 2,250 TFLOPS |
| FP8 峰值 | 4,500 TFLOPS |
| FP4 峰值 | 9,000 TFLOPS |
| 显存 | 192 GB HBM3e |
| 带宽 | 8 TB/s |
| NVLink 带宽 | 1.8 TB/s |
| TDP | 1000W |

---

## 关键规格对比

| 指标 | V100 | A100 | H100 | B200 |
|------|------|------|------|------|
| **架构** | Volta | Ampere | Hopper | Blackwell |
| **FP16 TFLOPS** (dense) | 125 | 312 | 989.5 | 2,250 |
| **FP16 TFLOPS** (稀疏) | - | 624 | 1,979 | 4,500 |
| **FP8 TFLOPS** (dense) | - | - | 1,979 | 4,500 |
| **FP8 TFLOPS** (稀疏) | - | - | 3,958 | 9,000 |
| **显存** | 32GB | 80GB | 80GB | 192GB |
| **带宽** | 900 GB/s | 2 TB/s | 3.35 TB/s | 8 TB/s |
| **TDP** | 300W | 400W | 700W | 1000W |

### 性能飞跃的原因

1. **Tensor Core 迭代**：专用矩阵计算单元持续优化
2. **内存带宽提升**：HBM 技术演进（HBM2 → HBM3e）
3. **互联带宽增长**：NVLink 从 300GB/s → 1.8TB/s
4. **低精度支持**：FP32 → FP16 → BF16 → FP8 → FP4

---

## 架构选型建议

| 场景 | 推荐架构 | 理由 |
|------|----------|------|
| 预算有限/入门 | V100 (二手) | 性价比高，足够学习 |
| 主流训练推理 | A100 80GB | 成熟稳定，生态完善 |
| 大模型训练 | H100 | 最强性能，Transformer Engine |
| 超大模型 | B200 | 192GB 显存，8TB/s 带宽 |
| 研究实验 | A100 或 H100 | 平衡性能和成本 |

---

*下一篇：[03-nvidia-architecture.md](03-nvidia-architecture.md) - NVIDIA GPU 架构详解*

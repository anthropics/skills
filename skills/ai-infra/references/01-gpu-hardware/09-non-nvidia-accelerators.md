# 非 NVIDIA AI 加速器

> NVIDIA 不是唯一的选择——AMD、Google、华为、Intel 都在 AI 芯片赛道上发力。了解竞争格局，才能做出更好的选型决策。

## 目录

- [为什么要关注非 NVIDIA 加速器](#为什么要关注非-nvidia-加速器)
- [AMD Instinct 系列](#amd-instinct-系列)
- [Google TPU](#google-tpu)
- [华为昇腾](#华为昇腾)
- [Intel Gaudi](#intel-gaudi)
- [其他新兴玩家](#其他新兴玩家)
- [全面对比](#全面对比)
- [选型建议](#选型建议)

---

## 为什么要关注非 NVIDIA 加速器

### 生活类比：汽车市场的多样化

```
十年前：AI 芯片 = NVIDIA GPU，就像手机 = iPhone
今天：竞争者涌入，就像安卓手机百花齐放

  NVIDIA (特斯拉):
    技术最强、生态最好、但价格最贵、供不应求

  AMD (比亚迪):
    硬件实力追赶很快，软件生态在加速成熟
    性价比优势明显，部分客户开始切换

  Google TPU (谷歌自动驾驶):
    不卖芯片，只在自家云上用
    为 Transformer 深度定制，JAX 生态独特

  华为昇腾 (国产新能源):
    国产替代刚需，生态还在建设中
    政策驱动 + 大厂投入，增长迅速

  Intel Gaudi (传统车企转型):
    起步晚但投入大，Gaudi 3 开始有竞争力
    收购 Habana Labs 获得 AI 芯片能力
```

### 为什么不能只用 NVIDIA

```
┌─────────────────────────────────────────────────────────────┐
│                  关注非 NVIDIA 的四大理由                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. 供应链风险                                               │
│     H100 一卡难求，交货周期 6-12 个月                          │
│     地缘政治限制出口（对中国市场影响巨大）                       │
│                                                             │
│  2. 成本压力                                                 │
│     NVIDIA 毛利率 70%+，溢价严重                              │
│     AMD MI300X 同等性能，价格低 20-30%                        │
│     TPU 云上训练有时比 GPU 便宜 40%+                          │
│                                                             │
│  3. 技术路线多样性                                            │
│     TPU 的 systolic array 对 Transformer 有独特优势           │
│     不同架构适合不同工作负载                                    │
│                                                             │
│  4. 国产化需求                                               │
│     政策要求关键基础设施国产化                                  │
│     昇腾在国内大模型训练中占比快速提升                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## AMD Instinct 系列

### 架构概述

AMD 的 AI 加速器基于 CDNA 架构（区别于游戏用的 RDNA 架构），专为数据中心 AI/HPC 工作负载设计。

```
┌─────────────────────────────────────────────────────────────┐
│                   AMD CDNA 架构演进                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  2020 ── CDNA 1 (MI100) ── 首款专用 AI 加速器                │
│    │      FP32: 23.1 TFLOPS, HBM2: 32GB                    │
│    │                                                        │
│  2022 ── CDNA 2 (MI210/MI250X) ── MCM 多芯片封装             │
│    │      FP16: 383 TFLOPS, HBM2e: 128GB                   │
│    │      首次在 HPC Top500 登顶（Frontier 超算）             │
│    │                                                        │
│  2023 ── CDNA 3 (MI300X/MI300A) ── 全面追赶 H100            │
│    │      FP16: 1,307 TFLOPS, HBM3: 192GB                  │
│    │      MI300A: CPU+GPU 融合（APU 概念）                   │
│    │                                                        │
│  2025 ── CDNA 4 (MI350/MI400) ── 目标超越 B200              │
│           3nm 工艺，支持 FP4/FP6                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### MI300X vs H100 详细对比

| 指标 | AMD MI300X | NVIDIA H100 SXM | 优势方 |
|------|-----------|-----------------|--------|
| **显存容量** | 192 GB HBM3 | 80 GB HBM3 | AMD (2.4×) |
| **显存带宽** | 5.3 TB/s | 3.35 TB/s | AMD (1.6×) |
| **FP16 算力** | 1,307 TFLOPS | 989 TFLOPS | AMD |
| **FP8 算力** | 2,614 TFLOPS | 1,979 TFLOPS | AMD |
| **TDP** | 750W | 700W | NVIDIA |
| **互联** | Infinity Fabric | NVLink 4.0 | 各有千秋 |
| **软件生态** | ROCm | CUDA | NVIDIA (大幅领先) |
| **价格** | ~$10K-12K | ~$25K-30K | AMD (更便宜) |

```
MI300X 的杀手锏是 192GB 显存：
  - 70B 模型 FP16 推理只需 1 张卡（H100 需要 2 张）
  - 大 batch 推理时 KV Cache 空间充裕
  - 更适合推理场景（显存 > 算力的瓶颈）
  
MI300X 的短板是软件生态：
  - ROCm 兼容性不如 CUDA 成熟
  - 部分 PyTorch 算子需要适配
  - FlashAttention 等优化库支持滞后
  - 但 2024 以来改善明显，PyTorch 原生支持已不错
```

### ROCm 软件生态

```
┌─────────────────────────────────────────────────────────────┐
│                    ROCm 软件栈                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  应用层:  PyTorch  │  JAX  │  TensorFlow  │  vLLM          │
│           ───────────────────────────────────               │
│  框架适配: torch.compile  │  Triton (OpenAI)                │
│           ───────────────────────────────────               │
│  数学库:  rocBLAS │ MIOpen │ hipFFT │ rocSPARSE             │
│           ───────────────────────────────────               │
│  通信库:  RCCL (类似 NCCL)                                   │
│           ───────────────────────────────────               │
│  底层:    HIP (CUDA 兼容层) │ ROCr Runtime                   │
│           ───────────────────────────────────               │
│  驱动:    amdgpu driver + KFD                                │
│                                                             │
│  关键工具:                                                   │
│  - hipify: 自动将 CUDA 代码转换为 HIP 代码                   │
│  - rocprof: 性能分析工具（类似 nsight）                       │
│  - rocgdb: GPU 调试器                                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 实际使用示例

```python
# AMD GPU 上运行 PyTorch - 几乎和 CUDA 一样
import torch

# 检测 AMD GPU
if torch.cuda.is_available():  # ROCm 也通过 cuda 接口暴露
    device = torch.device("cuda")
    print(f"GPU: {torch.cuda.get_device_name(0)}")
    # 输出: GPU: AMD Instinct MI300X

# 模型训练 - 代码几乎不用改
model = model.to(device)
optimizer = torch.optim.AdamW(model.parameters())

# 混合精度训练
scaler = torch.amp.GradScaler("cuda")
with torch.amp.autocast(device_type="cuda", dtype=torch.bfloat16):
    output = model(input_data)
    loss = criterion(output, target)

# vLLM 在 MI300X 上推理
# pip install vllm  # 需要 ROCm 版本的 wheel
# vllm serve meta-llama/Llama-3-70B --tensor-parallel-size 1
# （70B FP16 在单卡 192GB MI300X 上可以跑！）
```

---

## Google TPU

### 架构设计哲学

TPU (Tensor Processing Unit) 是 Google 自研的 AI 加速器，采用与 GPU 完全不同的设计思路。

```
┌─────────────────────────────────────────────────────────────┐
│                GPU vs TPU 设计哲学                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  GPU (NVIDIA):  通用并行处理器                                │
│    设计目标: 灵活性 + 高性能                                  │
│    架构: SIMT (数千个小核心)                                  │
│    内存: HBM + 多级缓存                                      │
│    编程: CUDA (极其灵活)                                     │
│    思路: "什么都能算，AI 算得特别好"                           │
│                                                             │
│  TPU (Google):  AI 专用处理器                                 │
│    设计目标: 矩阵运算极致效率                                 │
│    架构: Systolic Array (脉动阵列)                            │
│    内存: HBM + 大容量 SRAM                                   │
│    编程: XLA (编译器驱动优化)                                  │
│    思路: "只做一件事，但做到极致"                               │
│                                                             │
│  类比:                                                       │
│    GPU = 瑞士军刀 (什么都能切，AI 切得也不错)                  │
│    TPU = 专业厨刀 (只切菜，但切得又快又好)                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### TPU 版本演进

| 版本 | 年份 | BF16 算力 | HBM | 互联 | 特点 |
|------|------|----------|-----|------|------|
| TPU v2 | 2017 | 45.5 TFLOPS | 16 GB | ICI | 首款训练 TPU |
| TPU v3 | 2018 | 123 TFLOPS | 32 GB | ICI | 液冷设计 |
| TPU v4 | 2022 | 275 TFLOPS | 32 GB | ICI | 4096 芯片 Pod |
| TPU v5e | 2023 | 197 TFLOPS | 16 GB | ICI | 推理优化，性价比高 |
| TPU v5p | 2024 | 459 TFLOPS | 95 GB | ICI | 训练旗舰 |
| TPU v6e (Trillium) | 2024 | 918 TFLOPS | 32 GB | ICI | 4.7× v5e |

### Systolic Array（脉动阵列）

```
┌─────────────────────────────────────────────────────────────┐
│              Systolic Array 工作原理                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  传统方式 (GPU):                                             │
│    每个计算单元独立从内存读数据，计算，写回                      │
│    → 大量内存访问，带宽成为瓶颈                                │
│                                                             │
│  Systolic Array 方式 (TPU):                                  │
│    数据在计算单元之间 "流动"，每个单元做一步乘加                 │
│    → 数据复用极高，内存访问极少                                │
│                                                             │
│    输入 A ──→ ┌───┐ ──→ ┌───┐ ──→ ┌───┐                    │
│              │PE │     │PE │     │PE │                      │
│    输入 B    └─│─┘     └─│─┘     └─│─┘                      │
│      │        │         │         │                         │
│      ▼        ▼         ▼         ▼                         │
│    ┌───┐    ┌───┐     ┌───┐     ┌───┐                      │
│    │PE │    │PE │     │PE │     │PE │                       │
│    └─│─┘    └─│─┘     └─│─┘     └─│─┘                      │
│      │        │         │         │                         │
│      ▼        ▼         ▼         ▼                         │
│    ┌───┐    ┌───┐     ┌───┐     ┌───┐                      │
│    │PE │    │PE │     │PE │     │PE │                       │
│    └───┘    └───┘     └───┘     └───┘                      │
│              输出 C                                          │
│                                                             │
│  PE = Processing Element (处理单元)                          │
│  每个 PE: 一次乘法 + 一次加法                                 │
│  数据像心跳一样在阵列中脉动，所以叫 "Systolic"                 │
│                                                             │
│  TPU v4 的 MXU: 128×128 的 Systolic Array                    │
│  = 每周期 16,384 次乘加运算                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### TPU Pod 互联

```
┌─────────────────────────────────────────────────────────────┐
│                   TPU v4 Pod (4096 芯片)                     │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  TPU 的独特优势: ICI (Inter-Chip Interconnect)               │
│  所有 TPU 芯片通过 3D Torus 拓扑直连                          │
│                                                             │
│  GPU 集群:  GPU ←NVLink→ GPU ←IB→ GPU ←IB→ GPU             │
│             (节点内快，节点间慢)                               │
│                                                             │
│  TPU Pod:   TPU ←ICI→ TPU ←ICI→ TPU ←ICI→ TPU              │
│             (所有芯片之间带宽一致，无节点边界)                  │
│                                                             │
│        ┌─────────────────────────────────┐                  │
│        │        3D Torus 拓扑             │                  │
│        │                                 │                  │
│        │   ○─○─○─○─○─○─○─○              │                  │
│        │   │ │ │ │ │ │ │ │              │                  │
│        │   ○─○─○─○─○─○─○─○              │                  │
│        │   │ │ │ │ │ │ │ │   × 多层     │                  │
│        │   ○─○─○─○─○─○─○─○              │                  │
│        │   │ │ │ │ │ │ │ │              │                  │
│        │   ○─○─○─○─○─○─○─○              │                  │
│        │                                 │                  │
│        │  每个 ○ = 1 个 TPU 芯片           │                  │
│        │  每条 ─ = ICI 连接               │                  │
│        └─────────────────────────────────┘                  │
│                                                             │
│  这意味着:                                                   │
│  - 4096 芯片集群的通信效率远超等规模 GPU 集群                  │
│  - 大模型训练的并行效率更高                                    │
│  - 特别适合超大规模训练 (Google Gemini 就在 TPU 上训练)       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### JAX + TPU 编程

```python
import jax
import jax.numpy as jnp
from jax import pmap  # 并行化原语

# 查看可用 TPU 设备
print(jax.devices())  # [TpuDevice(id=0), TpuDevice(id=1), ...]

# TPU 上的矩阵运算 - 自动使用 Systolic Array
key = jax.random.PRNGKey(0)
a = jax.random.normal(key, (4096, 4096))
b = jax.random.normal(key, (4096, 4096))
c = jnp.dot(a, b)  # XLA 自动编译优化

# 多 TPU 数据并行 - 一行代码
@pmap
def train_step(params, batch):
    loss, grads = jax.value_and_grad(loss_fn)(params, batch)
    params = jax.tree.map(lambda p, g: p - 0.01 * g, params, grads)
    return params, loss

# XLA 编译优化 - 对 TPU 效果最好
@jax.jit
def forward(params, x):
    for layer in params:
        x = jnp.dot(x, layer['weights']) + layer['bias']
        x = jax.nn.relu(x)
    return x
```

### TPU 的局限性

```
TPU 的主要限制:
  
  1. 只在 Google Cloud 上可用
     不卖芯片，只能通过 GCP 使用
     → 绑定云厂商，无法自建集群
  
  2. 软件生态绑定 JAX
     PyTorch 支持 (torch-xla) 存在但不成熟
     很多库需要 JAX 版本重写
     → 迁移成本高
  
  3. 灵活性受限
     Systolic Array 对非矩阵运算效率低
     自定义算子开发困难
     → 不适合需要大量自定义计算的研究
  
  4. 调试困难
     错误信息不如 CUDA 清晰
     Profiling 工具相比 Nsight 还有差距
```

---

## 华为昇腾

### 架构概述

华为昇腾（Ascend）是国内最主要的 AI 芯片方案，基于达芬奇（Da Vinci）架构设计。

```
┌─────────────────────────────────────────────────────────────┐
│                  昇腾产品线                                   │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  训练系列:                                                   │
│    Ascend 910B  ── 主力训练芯片（对标 A100）                  │
│    Ascend 910C  ── 新一代（对标 H100，量产中）               │
│                                                             │
│  推理系列:                                                   │
│    Ascend 310   ── 边缘推理（低功耗 8W）                     │
│    Ascend 310P  ── 数据中心推理                              │
│                                                             │
│  整机系统:                                                   │
│    Atlas 800T A2  ── 8 卡训练服务器                          │
│    Atlas 900     ── 训练集群                                 │
│    CloudEngine   ── 网络交换机                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Da Vinci 架构

```
┌─────────────────────────────────────────────────────────────┐
│              Da Vinci 核心 (AI Core)                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────┐                │
│  │        Cube Unit (矩阵计算单元)          │                │
│  │    16×16 的矩阵乘法单元                  │                │
│  │    类似 Tensor Core，但架构不同           │                │
│  └─────────────────────────────────────────┘                │
│                      │                                      │
│  ┌─────────────────────────────────────────┐                │
│  │        Vector Unit (向量计算单元)         │                │
│  │    处理激活函数、Softmax 等               │                │
│  └─────────────────────────────────────────┘                │
│                      │                                      │
│  ┌─────────────────────────────────────────┐                │
│  │        Scalar Unit (标量计算单元)         │                │
│  │    控制流、地址计算                       │                │
│  └─────────────────────────────────────────┘                │
│                      │                                      │
│  ┌─────────────────────────────────────────┐                │
│  │        Memory (存储系统)                  │                │
│  │    L0 Buffer → L1 Buffer → HBM          │                │
│  └─────────────────────────────────────────┘                │
│                                                             │
│  与 NVIDIA GPU 对比:                                         │
│    Cube Unit ≈ Tensor Core (矩阵乘加)                       │
│    Vector Unit ≈ CUDA Cores (通用计算)                       │
│    AI Core ≈ SM (流处理器)                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### CANN 软件栈

```
┌─────────────────────────────────────────────────────────────┐
│                    CANN 软件栈                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  应用层:  MindSpore (华为自研) │ PyTorch (适配层)             │
│           ───────────────────────────────────               │
│  适配层:  torch_npu (PyTorch 昇腾插件)                       │
│           ───────────────────────────────────               │
│  图引擎:  GE (Graph Engine) - 计算图优化                      │
│           ───────────────────────────────────               │
│  算子库:  AICPU Ops │ AICore Ops │ 自定义 TBE 算子            │
│           ───────────────────────────────────               │
│  运行时:  ACL (Ascend Computing Language)                     │
│           ───────────────────────────────────               │
│  驱动:    Ascend HDK                                         │
│                                                             │
│  关键特性:                                                   │
│  - torch_npu: 让 PyTorch 代码在昇腾上运行，改动较小           │
│  - 算子兼容: 覆盖 PyTorch 90%+ 常用算子                     │
│  - 分布式: HCCL (Huawei Collective Communication Library)    │
│  - 工具链: msprof (性能分析)、AMCT (模型压缩)                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 昇腾实际使用

```python
# PyTorch + 昇腾 NPU
import torch
import torch_npu  # 昇腾适配层

# 设备从 "cuda" 改为 "npu"
device = torch.device("npu:0")

# 模型和数据迁移到 NPU
model = model.to(device)
input_data = input_data.to(device)

# 训练循环 - 基本和 CUDA 一样
with torch.amp.autocast(device_type="npu", dtype=torch.float16):
    output = model(input_data)
    loss = criterion(output, target)

loss.backward()
optimizer.step()

# 分布式训练 - 使用 HCCL 后端
import torch.distributed as dist
dist.init_process_group(backend="hccl")  # HCCL 替代 NCCL
```

### 昇腾的现状与挑战

```
优势:
  ✅ 国产替代的战略价值 — 不受出口管制影响
  ✅ 华为全栈整合能力 — 芯片+服务器+网络+软件
  ✅ 大厂落地案例 — 百度、科大讯飞、智谱 AI 等已采用
  ✅ 国家政策支持 — 国产化采购优先

挑战:
  ⚠️ 绝对性能仍有差距 — 910B 大致对标 A100，弱于 H100
  ⚠️ 软件生态不够成熟 — 算子覆盖率和稳定性仍在提升
  ⚠️ 社区规模小 — 遇到问题可参考资料较少
  ⚠️ 适配成本 — 部分模型需要修改代码和调优
  ⚠️ 供应链 — 先进制程芯片制造能力受限

适用场景:
  → 国内企业的合规部署
  → 对数据主权有严格要求的场景
  → 政府和国企项目
  → 对 NVIDIA 供应链风险的对冲
```

---

## Intel Gaudi

### 架构概述

Intel 通过收购 Habana Labs 获得了 Gaudi 系列 AI 加速器。

```
┌─────────────────────────────────────────────────────────────┐
│                 Gaudi 架构特点                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Gaudi 3 (2024):                                            │
│    工艺: 5nm                                                 │
│    算力: BF16 1,835 TFLOPS (vs H100 1,979 TFLOPS)          │
│    显存: 128GB HBM2e, 3.7 TB/s                              │
│    网络: 24× 200GbE (内置 RDMA)                              │
│    TDP: 900W                                                 │
│                                                             │
│  独特设计:                                                   │
│    1. 内置以太网 RDMA                                        │
│       不需要额外 IB 网卡，直接芯片间通信                      │
│       → 降低系统成本和复杂度                                  │
│                                                             │
│    2. TPC (Tensor Processing Core)                           │
│       可编程的张量处理核心，支持自定义算子                     │
│       → 比 TPU 更灵活                                        │
│                                                             │
│    3. MME (Matrix Multiplication Engine)                     │
│       专用矩阵计算引擎                                       │
│       → 类似 Tensor Core                                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Gaudi 软件生态

```
┌─────────────────────────────────────────────────────────────┐
│                Intel Gaudi 软件栈                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  应用层:  HuggingFace Optimum-Habana                         │
│           ───────────────────────────────────               │
│  框架:    PyTorch (通过 Habana bridge)                       │
│           ───────────────────────────────────               │
│  编译器:  SynapseAI Graph Compiler                           │
│           ───────────────────────────────────               │
│  库:      TPC Kernels │ Habana Collective Comms               │
│           ───────────────────────────────────               │
│  驱动:    habanalabs kernel driver                            │
│                                                             │
│  优势:                                                       │
│  - HuggingFace 深度合作，Optimum-Habana 支持主流模型         │
│  - AWS DL1/DL2q 实例可用                                    │
│  - Intel 开发者社区支持                                      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

```python
# Gaudi 上使用 HuggingFace
from optimum.habana import GaudiTrainer, GaudiTrainingArguments

training_args = GaudiTrainingArguments(
    output_dir="./output",
    use_habana=True,
    use_lazy_mode=True,  # Gaudi 的惰性执行模式
    gaudi_config_name="Habana/bert-base-uncased",
    per_device_train_batch_size=32,
    bf16=True,
)

trainer = GaudiTrainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
)
trainer.train()
```

---

## 其他新兴玩家

### 概览

```
┌─────────────────────────────────────────────────────────────┐
│              其他 AI 加速器生态                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  寒武纪 (Cambricon) MLU:                                     │
│    - 国产 AI 芯片，MLU370/MLU590                             │
│    - Cambricon Neuware 软件栈                                │
│    - 主要用于国内云厂商和安防                                 │
│                                                             │
│  Cerebras WSE (Wafer Scale Engine):                          │
│    - 整片晶圆做成一个芯片（850,000 核心）                     │
│    - 超大 SRAM (40GB on-chip)，无需 HBM                     │
│    - 适合超大模型训练，但成本极高                              │
│                                                             │
│  Graphcore IPU:                                               │
│    - 智能处理器，强调图计算                                   │
│    - 大容量 SRAM，BSP 执行模型                               │
│    - 2024 年被软银收购，前景未明                              │
│                                                             │
│  Groq LPU:                                                   │
│    - 推理专用芯片，SRAM 架构                                 │
│    - 主打极低延迟推理                                        │
│    - 无 HBM，纯 SRAM → 延迟低但容量受限                      │
│    - 适合小模型超低延迟场景                                   │
│                                                             │
│  AWS Trainium/Inferentia:                                    │
│    - AWS 自研 AI 芯片                                        │
│    - Trainium2: 训练，对标 H100                              │
│    - Inferentia2: 推理优化                                   │
│    - 只在 AWS 上可用                                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 全面对比

### 硬件规格对比

| 指标 | NVIDIA H100 | AMD MI300X | Google TPU v5p | 昇腾 910B | Intel Gaudi 3 |
|------|------------|-----------|---------------|----------|--------------|
| **架构** | Hopper | CDNA 3 | Systolic Array | Da Vinci | MME + TPC |
| **工艺** | 4nm | 5/6nm | 自研 | 7nm | 5nm |
| **显存** | 80GB HBM3 | 192GB HBM3 | 95GB HBM | 64GB HBM2e | 128GB HBM2e |
| **带宽** | 3.35 TB/s | 5.3 TB/s | ~4.8 TB/s | 1.6 TB/s | 3.7 TB/s |
| **BF16 算力** | 989 TFLOPS | 1,307 TFLOPS | 459 TFLOPS | ~320 TFLOPS | 1,835 TFLOPS |
| **互联** | NVLink 4.0 | Infinity Fabric | ICI | HCCS | 内置 RoCE |
| **软件** | CUDA | ROCm | JAX/XLA | CANN/torch_npu | SynapseAI |
| **可用性** | 全球购买/云 | 购买/云 | 仅 GCP | 国内购买 | 购买/AWS |

### 软件生态成熟度对比

```
                     CUDA 生态      ROCm 生态    JAX/TPU     CANN/昇腾    Gaudi
                     ─────────     ──────────   ────────    ─────────   ──────
PyTorch 支持          ██████████    ████████░░   ██████░░░░  ██████░░░░  ███████░░░
框架覆盖              ██████████    ████████░░   ██████████  ██████░░░░  ██████░░░░
FlashAttention       ██████████    ████████░░   ████████░░  ██████░░░░  █████░░░░░
vLLM 支持            ██████████    ████████░░   ░░░░░░░░░░  ██████░░░░  ██████░░░░
DeepSpeed 支持       ██████████    ████████░░   ░░░░░░░░░░  ████████░░  ██████░░░░
第三方库兼容          ██████████    ██████░░░░   ████░░░░░░  ████░░░░░░  ████░░░░░░
文档质量              ██████████    ██████░░░░   ████████░░  ██████░░░░  ██████░░░░
社区规模              ██████████    ██████░░░░   ████████░░  ████░░░░░░  ███░░░░░░░
调试工具              ██████████    ██████░░░░   ██████░░░░  █████░░░░░  █████░░░░░
```

### 性价比分析

```
┌─────────────────────────────────────────────────────────────┐
│               性价比分析（以 70B 模型推理为例）                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  场景: 70B FP16 推理，吞吐 1000 tokens/s                    │
│                                                             │
│  NVIDIA H100:                                               │
│    需要 2 张卡 (80GB × 2 = 160GB)                           │
│    硬件成本: ~$60K                                          │
│    功耗: 1,400W                                             │
│    软件适配: 0 天 (开箱即用)                                  │
│                                                             │
│  AMD MI300X:                                                 │
│    只需 1 张卡 (192GB)                                       │
│    硬件成本: ~$12K                                          │
│    功耗: 750W                                               │
│    软件适配: 3-7 天 (ROCm 适配)                              │
│                                                             │
│  Google TPU v5p:                                             │
│    云上按需: ~$4.2/chip/h                                   │
│    灵活但有云厂商锁定                                        │
│    软件适配: 14+ 天 (需要 JAX 重写)                          │
│                                                             │
│  结论:                                                       │
│  - 预算优先: AMD MI300X (显存大，价格低)                     │
│  - 效率优先: NVIDIA H100 (生态成熟，零适配)                  │
│  - 弹性需求: TPU (按需使用，超大规模)                        │
│  - 国产合规: 昇腾 (政策需求)                                 │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 选型建议

### 决策矩阵

```
你应该选什么？

├── 最强性能 + 最好生态 → NVIDIA H100/B200
│   适合：核心训练集群、追求最低风险
│
├── 最大显存 + 高性价比 → AMD MI300X
│   适合：推理服务、中小团队、成本敏感
│
├── 超大规模训练 → Google TPU v5p
│   适合：大模型预训练、已在 GCP 的团队
│
├── 国产化需求 → 华为昇腾 910B/910C
│   适合：国内合规部署、政企项目
│
├── 推理 + 低延迟 → Groq LPU / Intel Gaudi 3
│   适合：推理专用场景
│
└── 对冲策略 → 混合部署
    训练: NVIDIA + 部分 AMD/昇腾
    推理: AMD MI300X + 昇腾（降低成本）
    实验: TPU (GCP 免费额度)
```

### 迁移成本评估

| 从 NVIDIA 迁移到 | 代码改动量 | 适配周期 | 风险等级 |
|----------------|----------|---------|---------|
| AMD (ROCm) | 小（5-10%） | 1-2 周 | 中低 |
| 昇腾 (CANN) | 中（10-20%） | 2-4 周 | 中 |
| TPU (JAX) | 大（重写） | 1-3 月 | 高 |
| Gaudi (SynapseAI) | 中（10-15%） | 2-3 周 | 中 |

---

## 小结

```
非 NVIDIA AI 加速器的核心要点:

1. 竞争格局正在改变
   NVIDIA 仍然是 AI 芯片王者，但不再是唯一选择
   AMD、Google、华为都在快速追赶

2. 硬件差距在缩小，软件差距仍然是壁垒
   CUDA 生态的网络效应极强
   但 ROCm、CANN 的进步速度很快

3. 选型要看场景
   训练追求生态 → NVIDIA
   推理追求性价比 → AMD MI300X
   超大规模 → TPU
   国产合规 → 昇腾

4. 多元化是趋势
   头部公司都在布局多种芯片
   减少对单一供应商的依赖是明智之举

5. 关注发展
   AI 芯片是最快迭代的领域之一
   今天的结论可能 2 年后就需要更新
```

---

## 延伸阅读

### 官方资源

- [AMD Instinct MI300X](https://www.amd.com/en/products/accelerators/instinct/mi300/mi300x.html)
- [Google Cloud TPU](https://cloud.google.com/tpu/docs)
- [华为昇腾开发者](https://www.hiascend.com/)
- [Intel Gaudi](https://habana.ai/)

### 深度分析

- [SemiAnalysis: AI Chip Competitive Landscape](https://semianalysis.com/)
- [MLPerf Benchmark Results](https://mlcommons.org/benchmarks/)
- [Tom's Hardware: AI Accelerator Comparisons](https://www.tomshardware.com/)

---

*返回：[README.md](README.md) - 章节索引*

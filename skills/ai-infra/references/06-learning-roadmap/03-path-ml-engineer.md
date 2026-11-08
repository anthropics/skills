# 路径 B：AI/ML 工程师深入底层

> 从使用者到理解原理，3-4 个月深入 AI 基础设施底层。

## 目录

- [背景分析](#背景分析)
- [学习计划总览](#学习计划总览)
- [Phase 1: GPU 架构深入](#phase-1-gpu-架构深入)
- [Phase 2: 分布式训练深入](#phase-2-分布式训练深入)
- [Phase 3: 推理优化深入](#phase-3-推理优化深入)
- [Phase 4: 集群调度与生产部署](#phase-4-集群调度与生产部署)

---

## 背景分析

### 你的优势

| 优势领域 | 具体技能 |
|----------|----------|
| PyTorch/TensorFlow | 模型定义、训练、数据处理 |
| 模型训练流程 | 超参调优、评估、问题排查 |
| 模型调优经验 | 学习率调度、正则化、收敛分析 |
| 深度学习原理 | Transformer、Attention、网络结构 |

### 你需要补充

| 补充领域 | 具体内容 |
|----------|----------|
| 硬件架构细节 | GPU 内部架构、内存带宽、瓶颈分析 |
| 系统级优化 | CUDA 编程、通信优化、内存管理 |
| 生产部署经验 | K8s、高可用设计、监控运维 |

---

## 学习计划总览

```
Phase 1 ────► Phase 2 ────► Phase 3 ────► Phase 4
2-3 周        4-6 周        4-6 周        2-3 周
GPU深入      分布式深入     推理优化深入   集群+部署

总计: 12-18 周 (约 3-4 个月)
```

**学习重点**: "从使用者到理解原理"

- 你已经会用 `torchrun`，现在要理解 DDP 内部如何 overlap 通信和计算
- 你已经会用 `model.half()` 做混合精度，现在要理解 Tensor Core 如何加速 FP16 计算

---

## Phase 1: GPU 架构深入

### 目标

**2-3 周**：深入理解硬件细节和性能瓶颈

### 关键问题

1. 为什么 H100 比 A100 快？架构差异在哪？
2. 为什么有时 FP16 比 FP32 快 2x 以上？
3. 训练大模型时，瓶颈在计算还是内存？
4. NVLink 和 PCIe 对多卡训练有什么影响？

### 学习内容

| 周次 | 主题 | 内容 |
|------|------|------|
| Week 1 | 架构理解 | GPU 架构演进、SM 结构、内存带宽 vs 计算吞吐 |
| Week 2-3 | 性能分析 | Nsight Systems 使用、精度对比、带宽利用率分析 |

### 动手实践

```python
# 用 PyTorch Profiler 分析训练
import torch
from torch.profiler import profile, ProfilerActivity

model = torch.nn.Linear(4096, 4096).cuda()
x = torch.randn(64, 4096).cuda()

with profile(activities=[ProfilerActivity.CUDA]) as prof:
    for _ in range(10):
        output = model(x)
        output.sum().backward()

print(prof.key_averages().table(sort_by="cuda_time_total"))
```

### 检验标准

- [ ] 能解释 Memory Bound vs Compute Bound
- [ ] 能用 Nsight 分析性能瓶颈
- [ ] 能对比不同精度的性能差异

---

## Phase 2: 分布式训练深入

### 目标

**4-6 周**：从使用者到理解原理

### Week 1-2: DDP 源码级理解

**关键问题**:
- DDP 如何实现通信和计算重叠？
- Gradient Bucket 是什么？为什么需要？
- DDP 的 hook 机制如何工作？

**DDP 通信计算重叠原理**:

```
传统方式: Forward → Backward → AllReduce (串行)

DDP 方式: Forward → Backward (逐层) + AllReduce (并行)
  Layer N backward → trigger AllReduce(N)
  Layer N-1 backward → trigger AllReduce(N-1)
  ...
```

**关键机制**:
1. **Gradient Bucket**: 默认 25MB，bucket 满了立即触发 AllReduce
2. **Hook 机制**: 在 grad_fn 上注册 hook，梯度计算完成后触发
3. **同步点**: optimizer.step() 前等待所有 AllReduce 完成

### Week 3-4: ZeRO 深入理解

**内存分析公式** (Ψ = 模型参数量):

| 阶段 | 优化器状态 | 梯度 | 参数 | 总内存 |
|------|------------|------|------|--------|
| Baseline | 12Ψ | 2Ψ | 2Ψ | 16Ψ |
| ZeRO-1 | 12Ψ/N | 2Ψ | 2Ψ | 4Ψ + 12Ψ/N |
| ZeRO-2 | 12Ψ/N | 2Ψ/N | 2Ψ | 2Ψ + 14Ψ/N |
| ZeRO-3 | 12Ψ/N | 2Ψ/N | 2Ψ/N | 16Ψ/N |

### Week 5-6: 模型并行深入

**Transformer 张量并行切分**:

```
Self-Attention (Column Parallel):
  Q, K, V 按列切分到不同 GPU
  每个 GPU 计算部分 head

FFN (Column + Row Parallel):
  第一层 Linear: 按列切分 (Column Parallel)
  第二层 Linear: 按行切分 (Row Parallel)
```

### 动手实践

```python
# 用 DeepSpeed 训练 7B 模型
# ds_config.json
{
    "train_batch_size": 32,
    "gradient_accumulation_steps": 8,
    "fp16": {"enabled": true},
    "zero_optimization": {
        "stage": 2,
        "offload_optimizer": {"device": "cpu"}
    }
}
```

### 检验标准

- [ ] 能解释 DDP 的 Gradient Bucket 机制
- [ ] 能计算 ZeRO 各阶段的内存节省
- [ ] 能配置 DeepSpeed 训练大模型

---

## Phase 3: 推理优化深入

### 目标

**4-6 周**：理解 LLM 推理的关键优化

### Week 1-2: FlashAttention 原理

**传统 Attention 的问题**:
- O(N²) 的显存占用 (attention matrix)
- 大量 HBM 读写，Memory Bound

**FlashAttention 解决方案**:
- Tiling: 分块计算，利用 SRAM
- Recomputation: 不存储中间结果，反向时重算
- 结果: 内存 O(N)，速度提升 2-4x

### Week 3-4: PagedAttention 原理

**传统 KV Cache 问题**:
- 预分配最大长度，造成浪费
- 内存碎片化

**PagedAttention 解决方案**:
- 借鉴 OS 虚拟内存思想
- KV Cache 按页分配
- 支持 prefix sharing

### Week 5-6: 推理框架对比

| 框架 | 特点 | 适用场景 |
|------|------|----------|
| vLLM | PagedAttention, Continuous Batching | 高吞吐 LLM 服务 |
| TGI | 生产就绪, Token Streaming | HuggingFace 模型部署 |
| TensorRT-LLM | NVIDIA 官方, 极致优化 | 追求极限性能 |

### 动手实践

```python
# 对比不同框架性能
# benchmark_inference.py
from vllm import LLM, SamplingParams
import time

llm = LLM(model="meta-llama/Llama-2-7b-hf")
prompts = ["Hello, " * 10] * 100

start = time.time()
outputs = llm.generate(prompts, SamplingParams(max_tokens=100))
elapsed = time.time() - start

tokens = sum(len(o.outputs[0].token_ids) for o in outputs)
print(f"Throughput: {tokens/elapsed:.2f} tokens/s")
```

### 检验标准

- [ ] 能解释 FlashAttention 的 Tiling 策略
- [ ] 能解释 PagedAttention 的内存管理
- [ ] 能对比 vLLM/TGI 性能差异

---

## Phase 4: 集群调度与生产部署

### 目标

**2-3 周**：补充系统运维知识

### 学习内容

| 主题 | 内容 |
|------|------|
| K8s GPU 调度 | Device Plugin, MIG, 时间分片 |
| 多租户资源隔离 | ResourceQuota, LimitRange |
| 模型服务高可用 | 负载均衡, 故障转移, A/B 测试 |
| 成本优化 | Spot 实例, 自动伸缩 |

### 动手实践

```yaml
# K8s 上部署 vLLM 服务
apiVersion: apps/v1
kind: Deployment
metadata:
  name: vllm-server
spec:
  replicas: 2
  template:
    spec:
      containers:
      - name: vllm
        image: vllm/vllm-openai:latest
        args: ["--model", "meta-llama/Llama-2-7b-hf"]
        resources:
          limits:
            nvidia.com/gpu: 1
```

### 检验标准

- [ ] 能在 K8s 上部署 GPU 推理服务
- [ ] 能配置 HPA 自动扩缩容
- [ ] 能设计基本的高可用架构

---

## 学习里程碑

| 里程碑 | 时间点 | 检验内容 |
|--------|--------|----------|
| Mile 1 | 3周 | 能用 Nsight 分析性能，理解 Roofline 模型 |
| Mile 2 | 9周 | 能配置 DeepSpeed 3D 并行，分析通信瓶颈 |
| Mile 3 | 15周 | 能部署优化 vLLM 服务，做性能调优 |
| Mile 4 | 18周 | 能设计生产级推理服务架构 |

---

## 延伸阅读

- [路径A-后端工程师转型](./02-path-backend-engineer.md)
- [核心技能清单](./05-core-skills.md)
- [动手项目建议](./07-hands-on-projects.md)

---

*返回章节：[学习路线图](./README.md)*

---

## 参考资料与引用

1. **Stanford CS231n.** *Convolutional Neural Networks for Visual Recognition.*  
   https://cs231n.stanford.edu/

2. **Stanford CS224n.** *Natural Language Processing with Deep Learning.*  
   https://web.stanford.edu/class/cs224n/

3. **Chip Huyen.** *Designing Machine Learning Systems.* O'Reilly 2022.  
   https://www.oreilly.com/library/view/designing-machine-learning/9781098107956/

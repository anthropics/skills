# 性能分析工具

> 性能分析就像医生做体检——你不能凭感觉说"模型跑得慢"，需要用工具精确定位"到底慢在哪里"。

## 目录

- [性能分析概述](#性能分析概述)
- [PyTorch Profiler](#pytorch-profiler)
- [NVIDIA Nsight Systems](#nvidia-nsight-systems)
- [NVIDIA Nsight Compute](#nvidia-nsight-compute)
- [Roofline 模型分析](#roofline-模型分析)
- [性能瓶颈定位方法论](#性能瓶颈定位方法论)
- [延伸阅读](#延伸阅读)

---

## 性能分析概述

### 性能分析的层次

```
性能分析的三个层次

Layer 1: Python 级（宏观）
┌─────────────────────────────────────────┐
│ • 哪个模块/层最耗时？                     │
│ • GPU 利用率是多少？                      │
│ • CPU 和 GPU 是否有空闲等待？              │
│ 工具: PyTorch Profiler, cProfile          │
└─────────────────────────────────────────┘

Layer 2: 系统级（中观）
┌─────────────────────────────────────────┐
│ • GPU Kernel 的调度时间线                 │
│ • CPU-GPU 数据传输                        │
│ • 多 GPU 通信（NCCL）                     │
│ • 内存拷贝                                │
│ 工具: Nsight Systems, NVTX               │
└─────────────────────────────────────────┘

Layer 3: Kernel 级（微观）
┌─────────────────────────────────────────┐
│ • 单个 Kernel 的 SM 利用率               │
│ • 内存带宽利用率                          │
│ • 寄存器使用、共享内存使用                 │
│ • Warp 调度效率                           │
│ 工具: Nsight Compute                     │
└─────────────────────────────────────────┘
```

### 工具选择指南

| 你想知道什么 | 使用什么工具 | 适用阶段 |
|-------------|-------------|---------|
| 哪个层/模块最慢 | PyTorch Profiler | 开发/调优 |
| GPU 是否在空闲等待 | Nsight Systems | 调优 |
| NCCL 通信占多少时间 | Nsight Systems | 分布式调优 |
| 某个 Kernel 为什么慢 | Nsight Compute | 深度优化 |
| 是否计算受限 vs 内存受限 | Roofline Model | 分析决策 |

---

## PyTorch Profiler

### 基本使用

```python
import torch
from torch.profiler import profile, record_function, ProfilerActivity

model = MyModel().cuda()
input_data = torch.randn(32, 512, device='cuda')

# 基本 Profiling
with profile(
    activities=[
        ProfilerActivity.CPU,
        ProfilerActivity.CUDA,
    ],
    record_shapes=True,
    profile_memory=True,
    with_stack=True,
) as prof:
    with record_function("model_inference"):
        output = model(input_data)

# 打印结果
print(prof.key_averages().table(
    sort_by="cuda_time_total",
    row_limit=20,
))

# 输出示例:
# Name                  CPU total   CUDA total  Calls
# model_inference       12.5ms      8.2ms       1
# aten::linear          3.2ms       2.8ms       12
# aten::layer_norm      1.1ms       0.9ms       6
# aten::scaled_dot_...  5.1ms       4.2ms       6
```

### TensorBoard 集成

```python
from torch.profiler import schedule, tensorboard_trace_handler

# 高级 Profiling 配置
with profile(
    activities=[ProfilerActivity.CPU, ProfilerActivity.CUDA],
    schedule=schedule(
        wait=1,       # 跳过前 1 步
        warmup=1,     # 预热 1 步
        active=3,     # 采集 3 步
        repeat=2,     # 重复 2 轮
    ),
    on_trace_ready=tensorboard_trace_handler("./profiler_logs"),
    record_shapes=True,
    profile_memory=True,
    with_stack=True,
) as prof:
    for step, batch in enumerate(dataloader):
        output = model(batch)
        loss = criterion(output, target)
        loss.backward()
        optimizer.step()
        
        prof.step()  # 通知 Profiler 进入下一步

# 查看结果
# tensorboard --logdir=./profiler_logs
```

### 显存分析

```python
# 显存分析
with profile(
    activities=[ProfilerActivity.CUDA],
    profile_memory=True,
    record_shapes=True,
) as prof:
    output = model(input_data)
    loss = criterion(output, target)
    loss.backward()

# 显存快照
print(prof.key_averages().table(
    sort_by="self_cuda_memory_usage",
    row_limit=10,
))

# 更详细的显存分析
torch.cuda.memory._record_memory_history()
# ... 运行模型 ...
torch.cuda.memory._dump_snapshot("memory_snapshot.pickle")
# 使用 https://pytorch.org/memory_viz 可视化
```

---

## NVIDIA Nsight Systems

### 概述

Nsight Systems 提供系统级的 GPU 活动时间线视图，是定位 CPU-GPU 协调问题和通信瓶颈的首选工具。

### 使用方法

```bash
# 命令行采集 Profile
nsys profile \
  --trace=cuda,nvtx,osrt \
  --output=training_profile \
  --force-overwrite=true \
  python train.py

# 常用选项
nsys profile \
  --trace=cuda,nvtx,osrt,cudnn,cublas \  # 采集范围
  --cuda-memory-usage=true \              # 显存使用
  --gpu-metrics-device=all \              # GPU 指标
  --capture-range=cudaProfilerApi \       # 手动控制范围
  --output=profile_output \
  python train.py

# 使用 NVTX 标注（在代码中）
import torch.cuda.nvtx as nvtx

class ProfiledModel(torch.nn.Module):
    def forward(self, x):
        nvtx.range_push("attention")
        x = self.attention(x)
        nvtx.range_pop()
        
        nvtx.range_push("ffn")
        x = self.ffn(x)
        nvtx.range_pop()
        
        return x
```

### 分析技巧

```
Nsight Systems 时间线解读

典型的训练步骤时间线:

CPU  ─────[DataLoad]───[Forward]─────────[Backward]─────[Optim]──
GPU  ──────────────────[Kernel][Kernel]──[Kernel][Kernel][Kernel]─
NCCL ───────────────────────────[AllReduce]───────────────────────

理想状态: CPU 和 GPU 高度重叠，没有空闲 (bubble)

常见问题模式:

1. CPU 瓶颈 (CPU bound):
   CPU  ─[很长的DataLoad]────────────────[很长的DataLoad]──
   GPU  ──────────────────[少量Kernel]───────────────────
        ← GPU 大量空闲，等待 CPU 准备数据

2. GPU 瓶颈 (GPU bound):
   CPU  ─[短]─────────────────────────────[短]─────────
   GPU  ─[Kernel][Kernel][Kernel][Kernel][Kernel]──────
        ← 这是理想状态！GPU 满负荷

3. 通信瓶颈:
   CPU  ─[Forward]──[Backward]──────────────[Next Step]─
   GPU  ─[Kernel]───[Kernel]───[等待NCCL]───[Kernel]───
   NCCL ──────────────────────[AllReduce长]──────────────
        ← 通信成为瓶颈，考虑通信-计算重叠
```

---

## NVIDIA Nsight Compute

### 概述

Nsight Compute 是 Kernel 级的深度分析工具，用于分析单个 CUDA Kernel 的性能。

### 使用方法

```bash
# 采集单个 Kernel 的详细指标
ncu --set full \
    --kernel-name "volta_h884gemm" \
    --launch-count 5 \
    --output kernel_profile \
    python inference.py

# 常用选项
ncu --set full \                    # 完整指标集
    --section "SpeedOfLight" \      # 或指定特定分析节
    --section "MemoryWorkloadAnalysis" \
    --target-processes all \
    python inference.py
```

### 关键指标解读

```
Nsight Compute 关键指标

1. Speed of Light (SOL)
   ┌─────────────────────────────────────────┐
   │ Compute (SM) Throughput:  45%           │ ← SM 计算利用率
   │ Memory Throughput:        78%           │ ← 内存带宽利用率
   │                                         │
   │ 解读: Memory Throughput > Compute       │
   │       → 该 Kernel 是内存受限 (memory-bound)│
   └─────────────────────────────────────────┘

2. Memory Workload Analysis
   ┌─────────────────────────────────────────┐
   │ L1 Hit Rate: 85%                        │
   │ L2 Hit Rate: 62%                        │
   │ DRAM Throughput: 2.1 TB/s (of 3.35)     │
   │                                         │
   │ 解读: L2 命中率低 → 考虑改善数据局部性    │
   └─────────────────────────────────────────┘

3. Occupancy
   ┌─────────────────────────────────────────┐
   │ Achieved Occupancy: 62%                 │
   │ Theoretical Occupancy: 100%             │
   │ Limiter: Registers (64 per thread)      │
   │                                         │
   │ 解读: 寄存器使用过多限制了占用率          │
   │       考虑减少每线程寄存器使用            │
   └─────────────────────────────────────────┘
```

---

## Roofline 模型分析

### 什么是 Roofline 模型

```
Roofline 模型

                    性能 (FLOPS)
                         ↑
Peak Compute ──────────  │                    ___________
                         │                   /
                         │                  /
                         │                 /  ← 内存带宽斜率
                         │                /
                         │               /
                         │              /
                         │     ┌───┐  /
                         │     │ A │ /    A: 内存受限 (memory-bound)
                         │     └───┘/
                         │         /
                         │        /  ┌───┐
                         │       /   │ B │  B: 计算受限 (compute-bound)
                         │      /    └───┘
                         └──────────────────→ 计算密度 (FLOP/Byte)
                                         转折点

关键概念:
  计算密度 = 总计算量(FLOP) / 总数据搬运量(Bytes)
  转折点 = Peak_FLOPS / Peak_Bandwidth

A100 80GB 的参数:
  Peak FP16 FLOPS: 312 TFLOPS
  Peak HBM Bandwidth: 2.0 TB/s (实测 ~1.5 TB/s)
  转折点: 312 / 1.5 ≈ 208 FLOP/Byte

常见算子的计算密度:
  矩阵乘法 (大): ~200-500 → 计算受限 ✅
  LayerNorm:     ~5-10    → 内存受限
  Softmax:       ~10-20   → 内存受限
  逐元素操作:     ~1-5     → 内存受限 (最该融合的！)
```

### 计算密度分析

```python
def analyze_arithmetic_intensity(
    model_config: dict,
    batch_size: int,
    seq_len: int,
) -> dict:
    """分析模型各层的计算密度"""
    d_model = model_config["d_model"]
    d_ff = model_config.get("d_ff", 4 * d_model)
    num_heads = model_config["num_heads"]
    head_dim = d_model // num_heads
    
    analyses = {}
    
    # Linear 层 (矩阵乘法)
    # FLOP: 2 * M * N * K
    # Bytes: 2 * (M*K + K*N + M*N) (FP16)
    M, K, N = batch_size * seq_len, d_model, d_model
    flops = 2 * M * K * N
    bytes_accessed = 2 * (M*K + K*N + M*N)
    analyses["qkv_projection"] = {
        "flops": flops * 3,  # Q, K, V
        "bytes": bytes_accessed * 3,
        "intensity": flops / bytes_accessed,
        "type": "compute-bound" if flops/bytes_accessed > 100 else "memory-bound",
    }
    
    # Attention score (Q @ K^T)
    M, K, N = batch_size * num_heads * seq_len, head_dim, seq_len
    flops = 2 * M * K * N
    bytes_accessed = 2 * (M*K + K*N + M*N)
    analyses["attention_score"] = {
        "flops": flops,
        "bytes": bytes_accessed,
        "intensity": flops / bytes_accessed,
        "type": "compute-bound" if flops/bytes_accessed > 100 else "memory-bound",
    }
    
    # Softmax (逐元素)
    elements = batch_size * num_heads * seq_len * seq_len
    flops = 5 * elements  # exp, sum, div 等
    bytes_accessed = 2 * 2 * elements  # 读 + 写, FP16
    analyses["softmax"] = {
        "flops": flops,
        "bytes": bytes_accessed,
        "intensity": flops / bytes_accessed,
        "type": "memory-bound",  # 永远是内存受限
    }
    
    return analyses
```

---

## 性能瓶颈定位方法论

### 系统化排查流程

```
性能瓶颈排查流程

Step 1: 宏观定位
┌──────────────────────────────────────────┐
│ 用 PyTorch Profiler 确定:                │
│ • Forward vs Backward 的时间比           │
│ • 哪些层/模块最耗时                      │
│ • GPU 利用率（nvidia-smi）               │
└──────────┬───────────────────────────────┘
           ▼
Step 2: 分类诊断
┌────────────┬────────────┬────────────────┐
│ GPU 利用率  │ 类别       │ 方向            │
├────────────┼────────────┼────────────────┤
│ < 30%      │ CPU 瓶颈   │ DataLoader 优化 │
│ 30-70%     │ 通信/调度  │ Nsight Systems  │
│ > 70%      │ GPU 瓶颈   │ Kernel 优化     │
└────────────┴────────────┴────────────────┘

Step 3: 细节分析
┌──────────────────────────────────────────┐
│ CPU 瓶颈 → 优化 DataLoader, 预处理       │
│ 通信瓶颈 → 优化 AllReduce, 通信重叠      │
│ GPU 瓶颈 → Nsight Compute 分析 Kernel    │
│ 显存瓶颈 → 显存分析, 梯度检查点           │
└──────────────────────────────────────────┘
```

### 常见瓶颈和解决方案

| 瓶颈类型 | 症状 | 诊断方法 | 解决方案 |
|---------|------|---------|---------|
| DataLoader | GPU 利用率波动大 | Nsight Systems 看 CPU 空闲 | 增加 num_workers, pin_memory |
| 小 Kernel 多 | Kernel Launch 开销大 | Nsight Systems 看 Launch 间隔 | torch.compile, CUDA Graphs |
| 内存受限 Kernel | Compute 利用率低 | Nsight Compute SOL | 算子融合，Triton Kernel |
| AllReduce | 训练步之间有大段空闲 | Nsight Systems 看 NCCL | 计算通信重叠 |
| 显存不足 | OOM 错误 | torch.cuda.memory_summary | 梯度检查点, 混合精度 |

### 快速诊断脚本

```python
import torch
import time

def quick_diagnose(model, dataloader, num_steps=10):
    """快速性能诊断"""
    model.cuda().train()
    
    timings = {"data": [], "forward": [], "backward": [], "optim": []}
    optimizer = torch.optim.Adam(model.parameters())
    
    for i, batch in enumerate(dataloader):
        if i >= num_steps:
            break
        
        # 数据加载时间
        t0 = time.perf_counter()
        batch = {k: v.cuda() for k, v in batch.items()}
        torch.cuda.synchronize()
        timings["data"].append(time.perf_counter() - t0)
        
        # 前向传播
        t0 = time.perf_counter()
        output = model(**batch)
        loss = output.loss
        torch.cuda.synchronize()
        timings["forward"].append(time.perf_counter() - t0)
        
        # 反向传播
        t0 = time.perf_counter()
        loss.backward()
        torch.cuda.synchronize()
        timings["backward"].append(time.perf_counter() - t0)
        
        # 优化器更新
        t0 = time.perf_counter()
        optimizer.step()
        optimizer.zero_grad()
        torch.cuda.synchronize()
        timings["optim"].append(time.perf_counter() - t0)
    
    # 输出诊断报告
    print("\n=== 性能诊断报告 ===")
    total = 0
    for phase, times in timings.items():
        avg = sum(times[1:]) / len(times[1:]) * 1000  # 跳过第一步
        total += avg
        print(f"  {phase:>10}: {avg:.1f} ms ({avg/total*100 if total else 0:.0f}%)")
    
    print(f"  {'total':>10}: {total:.1f} ms")
    print(f"\n  GPU 显存: {torch.cuda.max_memory_allocated()/1e9:.1f} GB")
    
    # 瓶颈判断
    data_ratio = sum(timings["data"][1:]) / (sum(v for t in timings.values() for v in t[1:]))
    if data_ratio > 0.2:
        print("\n  ⚠️  数据加载占比过高，建议优化 DataLoader")
    elif sum(timings["forward"][1:]) > sum(timings["backward"][1:]) * 1.5:
        print("\n  ⚠️  前向传播偏慢，检查是否有未优化的算子")
    else:
        print("\n  ✅ 时间分布基本合理")
```

---

## 延伸阅读

- [PyTorch Profiler Documentation](https://pytorch.org/tutorials/recipes/recipes/profiler_recipe.html)
- [NVIDIA Nsight Systems User Guide](https://docs.nvidia.com/nsight-systems/)
- [NVIDIA Nsight Compute User Guide](https://docs.nvidia.com/nsight-compute/)
- [Roofline Model Introduction](https://docs.nersc.gov/tools/performance/roofline/)
- [PyTorch Memory Visualization](https://pytorch.org/blog/understanding-gpu-memory-1/)
- [Efficient PyTorch: A Tutorial on Optimizing PyTorch](https://github.com/pytorch/pytorch/wiki/Efficient-PyTorch)

---

*上一篇：[03-operator-optimization.md](03-operator-optimization.md)* | *下一篇：[05-training-debugging.md](05-training-debugging.md)*

[返回目录](README.md) | [返回主页](../README.md)

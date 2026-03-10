# 路径 A：后端/系统工程师转型 AI Infra

> 发挥系统基础优势，4-6 个月转型 AI 基础设施工程师。

## 目录

- [背景分析](#背景分析)
- [学习计划总览](#学习计划总览)
- [Phase 1: ML/DL 基础补课](#phase-1-mldl-基础补课)
- [Phase 2: GPU 基础 + CUDA 入门](#phase-2-gpu-基础--cuda-入门)
- [Phase 3: 集群调度（优势领域延伸）](#phase-3-集群调度优势领域延伸)
- [Phase 4: 分布式训练原理](#phase-4-分布式训练原理)
- [Phase 5: 推理服务 + MLOps](#phase-5-推理服务--mlops)
- [里程碑与检验](#里程碑与检验)

---

## 背景分析

### 你的优势

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    后端工程师的优势                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ✅ 熟悉分布式系统                                                      │
│      ├── 分布式一致性、CAP 理论                                          │
│      ├── 消息队列、RPC 框架                                              │
│      └── 微服务架构设计                                                  │
│                                                                         │
│   ✅ 了解 K8s、容器化部署                                                │
│      ├── Pod、Deployment、Service                                       │
│      ├── 资源管理和调度                                                  │
│      └── CI/CD 流程                                                     │
│                                                                         │
│   ✅ 有性能优化经验                                                      │
│      ├── 性能分析和调优方法                                              │
│      ├── 缓存、连接池等优化手段                                          │
│      └── 监控和可观测性                                                  │
│                                                                         │
│   ✅ 理解高可用、容错设计                                                │
│      ├── 故障转移、熔断降级                                              │
│      ├── 数据备份与恢复                                                  │
│      └── SRE 实践                                                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 你需要补充

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    需要补充的知识                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ❌ ML/DL 基础概念                                                      │
│      ├── 机器学习基本原理                                                │
│      ├── 深度学习网络结构                                                │
│      └── 模型训练流程                                                   │
│                                                                         │
│   ❌ GPU 架构和 CUDA                                                    │
│      ├── GPU 硬件架构                                                   │
│      ├── CUDA 编程模型                                                  │
│      └── GPU 性能优化                                                   │
│                                                                         │
│   ❌ 训练/推理流程                                                       │
│      ├── 模型训练的计算特性                                              │
│      ├── 推理服务的性能指标                                              │
│      └── 优化技术（量化、并行等）                                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 学习计划总览

```
┌─────────────────────────────────────────────────────────────────────────┐
│           后端工程师 → AI Infra 学习路径 (4-6 个月)                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Phase 1 ──► Phase 2 ──► Phase 3 ──► Phase 4 ──► Phase 5              │
│   2-3 周      2-3 周      3-4 周      4-6 周      4-6 周               │
│   ML 补课    GPU/CUDA    集群调度    分布式训练   推理+MLOps            │
│                             ▲                                           │
│                             │                                           │
│                     (你的优势领域)                                       │
│                                                                         │
│   总计: 15-22 周 (约 4-6 个月)                                          │
│   建议: 每周 10-15 小时业余学习                                          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: ML/DL 基础补课

### 目标

**2-3 周**：理解 ML 基本概念，能训练简单模型

### 学习内容

```
┌─────────────────────────────────────────────────────────────────────────┐
│   Phase 1: ML/DL 基础补课 (2-3 周)                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Week 1: 机器学习基础                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ 监督学习 vs 无监督学习                                         │   │
│   │ □ 分类 vs 回归                                                   │   │
│   │ □ 训练集、验证集、测试集                                          │   │
│   │ □ 过拟合与正则化                                                  │   │
│   │ □ 评估指标（准确率、召回率、F1）                                   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 2: 深度学习基础                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ 神经网络结构（全连接、CNN、RNN）                                │   │
│   │ □ 前向传播和反向传播                                              │   │
│   │ □ 梯度下降和优化器（SGD、Adam）                                   │   │
│   │ □ Loss 函数（交叉熵、MSE）                                       │   │
│   │ □ Batch/Epoch/Learning Rate                                      │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 3: PyTorch 入门                                                  │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ Tensor 操作                                                    │   │
│   │ □ autograd 自动微分                                              │   │
│   │ □ nn.Module 模型定义                                             │   │
│   │ □ DataLoader 数据加载                                            │   │
│   │ □ 训练循环编写                                                   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 推荐资源

| 资源 | 类型 | 时长 | 推荐理由 |
|------|------|------|----------|
| fast.ai Practical Deep Learning | 课程 | 7 周 | 实践导向，快速入门 |
| 吴恩达 Machine Learning | 课程 | 自定 | 经典入门 |
| PyTorch 官方 Tutorial | 文档 | 自定 | 权威上手 |
| 动手学深度学习 | 书籍 | 自定 | 中文友好 |

### 动手项目

```python
# 项目 1: MNIST 手写数字分类
# 目标: 理解基本的训练流程

import torch
import torch.nn as nn
import torch.optim as optim
from torchvision import datasets, transforms
from torch.utils.data import DataLoader

# 1. 数据加载
transform = transforms.Compose([
    transforms.ToTensor(),
    transforms.Normalize((0.1307,), (0.3081,))
])

train_dataset = datasets.MNIST('./data', train=True, 
                               download=True, transform=transform)
train_loader = DataLoader(train_dataset, batch_size=64, shuffle=True)

# 2. 模型定义
class SimpleNet(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 256)
        self.fc2 = nn.Linear(256, 10)
        self.relu = nn.ReLU()
    
    def forward(self, x):
        x = x.view(-1, 784)
        x = self.relu(self.fc1(x))
        x = self.fc2(x)
        return x

model = SimpleNet()

# 3. 训练循环
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(model.parameters(), lr=0.001)

for epoch in range(5):
    for batch_idx, (data, target) in enumerate(train_loader):
        optimizer.zero_grad()
        output = model(data)
        loss = criterion(output, target)
        loss.backward()
        optimizer.step()
        
        if batch_idx % 100 == 0:
            print(f'Epoch {epoch}, Batch {batch_idx}, Loss: {loss.item():.4f}')
```

### 检验标准

- [ ] 能解释什么是梯度下降
- [ ] 能区分训练/验证/测试集的作用
- [ ] 能用 PyTorch 训练 MNIST 分类器
- [ ] 能跑通 Hugging Face Transformers 推理

---

## Phase 2: GPU 基础 + CUDA 入门

### 目标

**2-3 周**：理解 GPU 架构，能写简单 CUDA 程序

### 学习内容

```
┌─────────────────────────────────────────────────────────────────────────┐
│   Phase 2: GPU 基础 + CUDA 入门 (2-3 周)                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Week 1: GPU 架构理解                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ CPU vs GPU 设计哲学                                           │   │
│   │ □ NVIDIA GPU 架构（SM、Warp、Thread）                           │   │
│   │ □ 内存层次（Global、Shared、Register）                           │   │
│   │ □ 不同 GPU 型号对比（A100/H100）                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 2: CUDA 编程基础                                                 │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ CUDA 编程模型（Grid、Block、Thread）                           │   │
│   │ □ 内存管理（cudaMalloc、cudaMemcpy）                             │   │
│   │ □ Kernel 函数编写                                                │   │
│   │ □ 同步和原子操作                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 3: 性能分析与优化                                                 │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ nvidia-smi 使用                                               │   │
│   │ □ Nsight Systems/Compute                                        │   │
│   │ □ Coalesced 内存访问                                            │   │
│   │ □ Occupancy 优化                                                │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 关键概念图解

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    CUDA 编程模型                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Grid (一次 Kernel 调用)                                               │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                                                                 │   │
│   │   Block (0,0)      Block (1,0)      Block (2,0)               │   │
│   │   ┌───────────┐   ┌───────────┐   ┌───────────┐               │   │
│   │   │ T0 T1 T2  │   │ T0 T1 T2  │   │ T0 T1 T2  │               │   │
│   │   │ T3 T4 T5  │   │ T3 T4 T5  │   │ T3 T4 T5  │               │   │
│   │   │ ...       │   │ ...       │   │ ...       │               │   │
│   │   └───────────┘   └───────────┘   └───────────┘               │   │
│   │                                                                 │   │
│   │   Block (0,1)      Block (1,1)      Block (2,1)               │   │
│   │   ┌───────────┐   ┌───────────┐   ┌───────────┐               │   │
│   │   │ T0 T1 T2  │   │ T0 T1 T2  │   │ T0 T1 T2  │               │   │
│   │   │ T3 T4 T5  │   │ T3 T4 T5  │   │ T3 T4 T5  │               │   │
│   │   │ ...       │   │ ...       │   │ ...       │               │   │
│   │   └───────────┘   └───────────┘   └───────────┘               │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   映射关系:                                                             │
│   Grid    ←→ GPU (整个设备)                                            │
│   Block   ←→ SM (流多处理器)                                           │
│   Warp    ←→ 32 个 Thread，SIMT 执行                                   │
│   Thread  ←→ CUDA Core                                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 动手项目

```c
// 项目 2: 向量加法 CUDA Kernel
// vector_add.cu

#include <stdio.h>
#include <cuda_runtime.h>

// CUDA Kernel
__global__ void vectorAdd(float *a, float *b, float *c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}

int main() {
    int n = 1000000;
    size_t size = n * sizeof(float);
    
    // Host 内存分配
    float *h_a = (float*)malloc(size);
    float *h_b = (float*)malloc(size);
    float *h_c = (float*)malloc(size);
    
    // 初始化数据
    for (int i = 0; i < n; i++) {
        h_a[i] = i;
        h_b[i] = i * 2;
    }
    
    // Device 内存分配
    float *d_a, *d_b, *d_c;
    cudaMalloc(&d_a, size);
    cudaMalloc(&d_b, size);
    cudaMalloc(&d_c, size);
    
    // 数据拷贝: Host -> Device
    cudaMemcpy(d_a, h_a, size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b, size, cudaMemcpyHostToDevice);
    
    // 启动 Kernel
    int threadsPerBlock = 256;
    int blocksPerGrid = (n + threadsPerBlock - 1) / threadsPerBlock;
    vectorAdd<<<blocksPerGrid, threadsPerBlock>>>(d_a, d_b, d_c, n);
    
    // 数据拷贝: Device -> Host
    cudaMemcpy(h_c, d_c, size, cudaMemcpyDeviceToHost);
    
    // 验证结果
    for (int i = 0; i < 10; i++) {
        printf("c[%d] = %f\n", i, h_c[i]);
    }
    
    // 释放内存
    cudaFree(d_a); cudaFree(d_b); cudaFree(d_c);
    free(h_a); free(h_b); free(h_c);
    
    return 0;
}

// 编译: nvcc -o vector_add vector_add.cu
// 运行: ./vector_add
```

### 检验标准

- [ ] 能解释 SM、Warp、Thread 的关系
- [ ] 能解释 GPU 内存层次
- [ ] 能写简单的 CUDA Kernel
- [ ] 能用 nvidia-smi 和 nsight 分析性能

---

## Phase 3: 集群调度（优势领域延伸）

### 目标

**3-4 周**：掌握 GPU 集群管理和调度（发挥你的 K8s 优势）

### 学习内容

```
┌─────────────────────────────────────────────────────────────────────────┐
│   Phase 3: 集群调度 (3-4 周) - 你的优势领域                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Week 1: GPU 资源管理                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ NVIDIA Device Plugin 原理与部署                               │   │
│   │ □ GPU 资源声明和调度                                            │   │
│   │ □ MIG (Multi-Instance GPU) 配置                                │   │
│   │ □ GPU 时间分片                                                  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 2: 批调度器                                                      │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ AI 工作负载调度挑战                                           │   │
│   │ □ Volcano 核心功能和使用                                        │   │
│   │ □ Gang Scheduling 原理                                          │   │
│   │ □ 队列和公平调度                                                │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 3-4: 多租户与成本优化                                             │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ ResourceQuota 和 LimitRange                                   │   │
│   │ □ 多租户资源隔离                                                │   │
│   │ □ Spot 实例使用                                                 │   │
│   │ □ 集群自动伸缩                                                  │   │
│   │ □ 成本监控和优化                                                │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 动手项目

```yaml
# 项目 3: K8s 上部署 GPU 训练任务
# gpu-training-job.yaml

apiVersion: v1
kind: Pod
metadata:
  name: pytorch-training
spec:
  containers:
  - name: pytorch
    image: pytorch/pytorch:2.0.0-cuda11.7-cudnn8-runtime
    command: ["python", "-c"]
    args:
    - |
      import torch
      print(f"CUDA available: {torch.cuda.is_available()}")
      print(f"Device count: {torch.cuda.device_count()}")
      print(f"Device name: {torch.cuda.get_device_name(0)}")
      
      # 简单训练测试
      x = torch.randn(1000, 1000).cuda()
      y = torch.randn(1000, 1000).cuda()
      z = torch.matmul(x, y)
      print(f"Matrix multiplication on GPU completed")
    resources:
      limits:
        nvidia.com/gpu: 1
      requests:
        nvidia.com/gpu: 1
  restartPolicy: Never
```

```yaml
# Volcano Job 示例
# volcano-pytorch-job.yaml

apiVersion: batch.volcano.sh/v1alpha1
kind: Job
metadata:
  name: pytorch-ddp-job
spec:
  minAvailable: 2
  schedulerName: volcano
  plugins:
    ssh: []
    svc: []
  tasks:
  - replicas: 2
    name: worker
    template:
      spec:
        containers:
        - name: pytorch
          image: pytorch/pytorch:2.1.0-cuda12.1-cudnn8-runtime
          command: ["torchrun"]
          args: ["--nproc_per_node=1", "train.py"]
          resources:
            limits:
              nvidia.com/gpu: 1
        restartPolicy: OnFailure
```

### 检验标准

- [ ] 能在 K8s 上部署 GPU Pod
- [ ] 能配置 ResourceQuota 和 LimitRange
- [ ] 能用 Volcano 运行分布式训练任务
- [ ] 能解释 Gang Scheduling 的作用

---

## Phase 4: 分布式训练原理

### 目标

**4-6 周**：理解分布式训练各种策略，能配置和调优

### 学习内容

```
┌─────────────────────────────────────────────────────────────────────────┐
│   Phase 4: 分布式训练原理 (4-6 周)                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Week 1-2: 数据并行                                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ 数据并行原理                                                  │   │
│   │ □ PyTorch DDP 使用和原理                                        │   │
│   │ □ AllReduce 通信                                                │   │
│   │ □ Gradient Accumulation                                         │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 3-4: ZeRO 与 FSDP                                               │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ ZeRO-1/2/3 原理                                               │   │
│   │ □ DeepSpeed 配置和使用                                          │   │
│   │ □ PyTorch FSDP 使用                                             │   │
│   │ □ 内存优化效果分析                                              │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 5-6: 模型并行与混合并行                                           │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ 张量并行原理                                                  │   │
│   │ □ 流水线并行原理                                                │   │
│   │ □ 3D 并行组合                                                   │   │
│   │ □ Megatron-LM 架构                                              │   │
│   │ □ 通信瓶颈分析                                                  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 动手项目

```python
# 项目 4: DDP 训练示例
# ddp_train.py

import torch
import torch.nn as nn
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP
from torch.utils.data.distributed import DistributedSampler
import os

def setup(rank, world_size):
    os.environ['MASTER_ADDR'] = 'localhost'
    os.environ['MASTER_PORT'] = '12355'
    dist.init_process_group("nccl", rank=rank, world_size=world_size)

def cleanup():
    dist.destroy_process_group()

def train(rank, world_size):
    setup(rank, world_size)
    
    # 创建模型并包装 DDP
    model = nn.Linear(10, 10).to(rank)
    ddp_model = DDP(model, device_ids=[rank])
    
    # 损失函数和优化器
    loss_fn = nn.MSELoss()
    optimizer = torch.optim.SGD(ddp_model.parameters(), lr=0.001)
    
    # 训练循环
    for epoch in range(10):
        # 模拟数据
        inputs = torch.randn(20, 10).to(rank)
        targets = torch.randn(20, 10).to(rank)
        
        optimizer.zero_grad()
        outputs = ddp_model(inputs)
        loss = loss_fn(outputs, targets)
        loss.backward()
        optimizer.step()
        
        if rank == 0:
            print(f"Epoch {epoch}, Loss: {loss.item():.4f}")
    
    cleanup()

if __name__ == "__main__":
    world_size = 2
    torch.multiprocessing.spawn(train, args=(world_size,), nprocs=world_size)
```

### 检验标准

- [ ] 能用 DDP 训练模型
- [ ] 能解释 ZeRO-1/2/3 的区别
- [ ] 能用 DeepSpeed/FSDP 训练大模型
- [ ] 能分析通信瓶颈

---

## Phase 5: 推理服务 + MLOps

### 目标

**4-6 周**：能部署生产级推理服务，建立 ML Pipeline

### 学习内容

```
┌─────────────────────────────────────────────────────────────────────────┐
│   Phase 5: 推理服务 + MLOps (4-6 周)                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Week 1-2: LLM 推理优化                                                │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ KV Cache 原理                                                 │   │
│   │ □ PagedAttention 原理                                           │   │
│   │ □ Continuous Batching                                           │   │
│   │ □ 量化技术 (GPTQ/AWQ)                                           │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 3-4: 推理服务框架                                                 │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ vLLM 部署和使用                                               │   │
│   │ □ TGI 部署                                                      │   │
│   │ □ Triton Inference Server                                       │   │
│   │ □ 性能压测和调优                                                │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Week 5-6: MLOps 实践                                                  │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ □ 实验跟踪 (MLflow/W&B)                                         │   │
│   │ □ 模型版本管理                                                  │   │
│   │ □ ML Pipeline (Kubeflow)                                        │   │
│   │ □ 模型监控和数据漂移                                            │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 动手项目

```python
# 项目 5: vLLM 推理服务部署
# vllm_server.py

from vllm import LLM, SamplingParams

# 加载模型
llm = LLM(
    model="meta-llama/Llama-2-7b-chat-hf",
    tensor_parallel_size=1,
    gpu_memory_utilization=0.9,
)

# 推理参数
sampling_params = SamplingParams(
    temperature=0.7,
    top_p=0.9,
    max_tokens=256,
)

# 批量推理
prompts = [
    "What is machine learning?",
    "Explain distributed training.",
]

outputs = llm.generate(prompts, sampling_params)

for output in outputs:
    print(f"Prompt: {output.prompt}")
    print(f"Generated: {output.outputs[0].text}")
    print("-" * 50)
```

```bash
# 启动 vLLM OpenAI 兼容 API 服务
python -m vllm.entrypoints.openai.api_server \
    --model meta-llama/Llama-2-7b-chat-hf \
    --port 8000 \
    --tensor-parallel-size 1
```

### 检验标准

- [ ] 能部署 vLLM 服务
- [ ] 能解释 KV Cache 和 PagedAttention
- [ ] 能用 MLflow 管理实验
- [ ] 能构建基本的 CI/CD for ML

---

## 里程碑与检验

### 学习里程碑

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    学习里程碑检查点                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Mile 1 (3周): ML 基础完成                                             │
│   □ 能训练 MNIST/CIFAR 分类器                                           │
│   □ 能跑通 HuggingFace 推理                                             │
│   □ 能解释训练流程                                                      │
│                                                                         │
│   Mile 2 (6周): GPU/CUDA 入门                                           │
│   □ 能写简单 CUDA Kernel                                                │
│   □ 能用 nsight 分析性能                                                │
│   □ 能解释 GPU 内存层次                                                 │
│                                                                         │
│   Mile 3 (10周): 集群调度掌握                                            │
│   □ 能在 K8s 部署 GPU Pod                                               │
│   □ 能配置 Volcano 任务                                                 │
│   □ 能设计多租户方案                                                    │
│                                                                         │
│   Mile 4 (16周): 分布式训练掌握                                          │
│   □ 能用 DDP/FSDP 训练                                                  │
│   □ 能配置 DeepSpeed                                                    │
│   □ 能分析通信瓶颈                                                      │
│                                                                         │
│   Mile 5 (22周): 推理+MLOps 完成                                        │
│   □ 能部署 vLLM 服务                                                    │
│   □ 能建立 ML Pipeline                                                  │
│   □ 能进行性能调优                                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 综合能力检验

完成路径 A 学习后，你应该能够：

1. **设计**: 设计 GPU 训练集群的架构方案
2. **部署**: 在 K8s 上部署分布式训练任务
3. **优化**: 分析和优化训练/推理性能
4. **运维**: 管理 ML 平台的资源和调度
5. **构建**: 构建完整的 MLOps Pipeline

---

## 延伸阅读

- [路径B-ML工程师深入](./03-path-ml-engineer.md)
- [核心技能清单](./05-core-skills.md)
- [动手项目建议](./07-hands-on-projects.md)
- [面试准备指南](./08-interview-preparation.md)

---

*返回章节：[学习路线图](./README.md)*

---

## 参考资料与引用

1. **NVIDIA.** *Deep Learning Institute (DLI) Courses.*  
   https://www.nvidia.com/en-us/training/

2. **HuggingFace.** *NLP Course.*  
   https://huggingface.co/learn/nlp-course/

3. **Kubernetes Documentation.** *AI/ML Workloads Guide.*  
   https://kubernetes.io/docs/

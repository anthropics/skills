# 路径 C：学生/新人从零开始

> 完整的 6-9 个月学习计划，从基础到入门 AI 基础设施。

## 目录

- [前置要求](#前置要求)
- [学习计划总览](#学习计划总览)
- [Month 1: 基础工具](#month-1-基础工具)
- [Month 2: ML/DL 基础](#month-2-mldl-基础)
- [Month 3: GPU 编程基础](#month-3-gpu-编程基础)
- [Month 4: 分布式训练](#month-4-分布式训练)
- [Month 5: 推理部署](#month-5-推理部署)
- [Month 6: Kubernetes + 调度](#month-6-kubernetes--调度)
- [Month 7-9: 综合项目](#month-7-9-综合项目)

---

## 前置要求

### 必须具备

- ✅ CS 基础（数据结构、算法、操作系统概念）
- ✅ Python 编程能力
- ✅ 基本的 Linux 使用经验

### 建议具备

- 📝 英语阅读能力（技术文档多为英文）
- 📝 基本的数学基础（线性代数、微积分、概率）

### 学习环境准备

| 需求 | 选项 | 说明 |
|------|------|------|
| GPU 服务器 | 云 GPU / Colab / Kaggle | 初期可用免费资源 |
| 开发环境 | VS Code + Remote SSH | 远程开发 |
| 学习时间 | 每周 30-40 小时 | 全职学习强度 |

---

## 学习计划总览

```
┌─────────────────────────────────────────────────────────────────────────┐
│           新人 → AI Infra 完整学习路径 (6-9 个月)                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Month 1      Month 2      Month 3      Month 4                       │
│   ┌──────┐    ┌──────┐    ┌──────┐    ┌──────┐                        │
│   │ 基础 │───►│ ML/DL│───►│ GPU  │───►│分布式│                        │
│   │ 工具 │    │ 基础 │    │ 编程 │    │ 训练 │                        │
│   └──────┘    └──────┘    └──────┘    └──────┘                        │
│                                          │                             │
│   Month 5      Month 6      Month 7-9    │                             │
│   ┌──────┐    ┌──────┐    ┌──────────┐  │                             │
│   │ 推理 │───►│ K8s  │───►│ 综合项目 │  │                             │
│   │ 部署 │    │ 调度 │    │ + 源码  │◄─┘                             │
│   └──────┘    └──────┘    └──────────┘                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Month 1: 基础工具

### Week 1-2: Linux 进阶 + Shell

**学习目标**: 熟练使用 Linux 命令行

| 主题 | 学习内容 |
|------|----------|
| 文件系统 | 目录结构、权限管理、软链接 |
| 进程管理 | ps、top、kill、systemd |
| 网络 | ssh、scp、curl、netstat |
| Shell 脚本 | 变量、循环、条件、函数 |

**动手练习**:
```bash
# 练习 1: 服务器监控脚本
#!/bin/bash
echo "=== 系统状态报告 ==="
echo "CPU 使用率:"
top -bn1 | grep "Cpu(s)"
echo "内存使用:"
free -h
echo "磁盘使用:"
df -h
echo "GPU 状态:"
nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv
```

### Week 3-4: Docker + Git

**学习目标**: 掌握容器化和版本控制

| 主题 | 学习内容 |
|------|----------|
| Docker 基础 | 镜像、容器、Dockerfile |
| Docker 进阶 | 多阶段构建、网络、Volume |
| Git 基础 | clone、commit、push、pull |
| Git 工作流 | 分支管理、PR、Merge |

**项目**: 用 Docker 部署一个 Python Web 服务

```dockerfile
# Dockerfile
FROM python:3.10-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY . .
CMD ["python", "app.py"]
```

### 检验标准

- [ ] 能写基本的 Shell 脚本
- [ ] 能构建和运行 Docker 容器
- [ ] 能使用 Git 进行版本控制

---

## Month 2: ML/DL 基础

### Week 1-2: 机器学习基础

**学习目标**: 理解机器学习核心概念

| 主题 | 学习内容 |
|------|----------|
| 基本概念 | 监督/无监督学习、训练/测试集 |
| 常用算法 | 线性回归、决策树、SVM |
| 模型评估 | 准确率、召回率、F1、交叉验证 |
| 过拟合 | 正则化、Dropout |

**推荐资源**: 吴恩达 Machine Learning 课程

### Week 3-4: 深度学习基础

**学习目标**: 能用 PyTorch 训练简单模型

| 主题 | 学习内容 |
|------|----------|
| 神经网络 | 全连接、激活函数、损失函数 |
| 训练过程 | 前向传播、反向传播、优化器 |
| PyTorch | Tensor、autograd、nn.Module |
| CNN 基础 | 卷积、池化、经典网络 |

**项目**: 训练 MNIST 分类器 + CIFAR 图像分类

```python
# MNIST 分类器
import torch
import torch.nn as nn
from torchvision import datasets, transforms

class SimpleNet(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 256)
        self.fc2 = nn.Linear(256, 10)
    
    def forward(self, x):
        x = x.view(-1, 784)
        x = torch.relu(self.fc1(x))
        return self.fc2(x)

# 训练代码...
```

### 检验标准

- [ ] 能解释梯度下降原理
- [ ] 能用 PyTorch 训练 CNN
- [ ] 能评估模型性能

---

## Month 3: GPU 编程基础

### Week 1-2: GPU 架构

**学习目标**: 理解 GPU 基本架构

| 主题 | 学习内容 |
|------|----------|
| CPU vs GPU | 设计哲学差异 |
| NVIDIA 架构 | SM、Warp、Thread |
| 内存层次 | Global、Shared、Register |
| 硬件规格 | 对比不同 GPU |

### Week 3-4: CUDA 入门

**学习目标**: 能写简单的 CUDA 程序

| 主题 | 学习内容 |
|------|----------|
| 编程模型 | Grid、Block、Thread |
| 内存管理 | cudaMalloc、cudaMemcpy |
| Kernel 编写 | __global__ 函数 |
| 同步 | __syncthreads__ |

**项目**: 实现向量加法和矩阵乘法的 CUDA kernel

```c
// 向量加法
__global__ void vectorAdd(float *a, float *b, float *c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        c[idx] = a[idx] + b[idx];
    }
}
```

### 检验标准

- [ ] 能解释 GPU 并行执行模型
- [ ] 能写简单的 CUDA Kernel
- [ ] 能用 nvidia-smi 监控 GPU

---

## Month 4: 分布式训练

### Week 1-2: 分布式基础

**学习目标**: 理解数据并行原理

| 主题 | 学习内容 |
|------|----------|
| 为什么分布式 | 数据量大、模型大、时间长 |
| 数据并行原理 | 模型复制、数据切分、梯度聚合 |
| AllReduce | Ring-AllReduce 算法 |
| PyTorch DDP | 基本使用 |

### Week 3-4: 实战训练

**学习目标**: 能进行多卡训练

| 主题 | 学习内容 |
|------|----------|
| DDP 配置 | 进程组、rank、world_size |
| 混合精度 | FP16、AMP |
| Gradient Accumulation | 大 batch 训练 |
| 调试技巧 | 常见问题排查 |

**项目**: 用 DDP 训练 ResNet/BERT

```python
# DDP 训练基本框架
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

dist.init_process_group("nccl")
model = DDP(model.cuda(), device_ids=[local_rank])
# 训练循环...
```

### 检验标准

- [ ] 能配置 DDP 多卡训练
- [ ] 能使用混合精度训练
- [ ] 能解释 AllReduce 过程

---

## Month 5: 推理部署

### Week 1-2: 模型部署基础

**学习目标**: 理解模型部署流程

| 主题 | 学习内容 |
|------|----------|
| 模型导出 | ONNX、TorchScript |
| 推理服务 | TorchServe、Triton |
| API 设计 | RESTful、gRPC |
| 性能指标 | 延迟、吞吐、并发 |

### Week 3-4: LLM 推理

**学习目标**: 能部署 LLM 推理服务

| 主题 | 学习内容 |
|------|----------|
| LLM 推理特点 | 自回归、KV Cache |
| vLLM 使用 | 安装、配置、API |
| 量化基础 | INT8、GPTQ |
| 性能调优 | batch size、并发 |

**项目**: 部署一个 LLM 推理服务

```python
# vLLM 服务
from vllm import LLM, SamplingParams

llm = LLM(model="meta-llama/Llama-2-7b-hf")
outputs = llm.generate(["Hello"], SamplingParams(max_tokens=100))
print(outputs[0].outputs[0].text)
```

### 检验标准

- [ ] 能导出和部署 PyTorch 模型
- [ ] 能使用 vLLM 部署 LLM
- [ ] 能进行基本的性能测试

---

## Month 6: Kubernetes + 调度

### Week 1-2: K8s 基础

**学习目标**: 掌握 K8s 核心概念

| 主题 | 学习内容 |
|------|----------|
| 核心概念 | Pod、Deployment、Service |
| 资源管理 | requests、limits |
| 配置管理 | ConfigMap、Secret |
| 存储 | PV、PVC |

### Week 3-4: GPU 调度

**学习目标**: 能在 K8s 上部署 GPU 任务

| 主题 | 学习内容 |
|------|----------|
| Device Plugin | NVIDIA k8s-device-plugin |
| GPU 资源声明 | nvidia.com/gpu |
| ResourceQuota | 资源配额管理 |
| 调试技巧 | GPU Pod 问题排查 |

**项目**: 在 K8s 上部署 GPU 训练任务

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: gpu-training
spec:
  containers:
  - name: pytorch
    image: pytorch/pytorch:latest
    resources:
      limits:
        nvidia.com/gpu: 1
```

### 检验标准

- [ ] 能创建和管理 K8s 资源
- [ ] 能部署 GPU Pod
- [ ] 能配置 ResourceQuota

---

## Month 7-9: 综合项目

### 项目选择

| 项目 | 难度 | 覆盖技能 |
|------|------|----------|
| 端到端 LLM 微调+部署 | ⭐⭐⭐ | 训练、推理、部署 |
| 分布式训练监控平台 | ⭐⭐⭐ | 分布式、监控、可视化 |
| ML Pipeline 系统 | ⭐⭐⭐ | MLOps、K8s、自动化 |

### 源码阅读建议

| 项目 | 优先级 | 学习重点 |
|------|--------|----------|
| PyTorch DDP | 高 | 分布式训练原理 |
| vLLM 核心模块 | 高 | LLM 推理优化 |
| DeepSpeed ZeRO | 中 | 内存优化策略 |

### 项目示例: LLM 微调 + 部署

```
阶段 1: 数据准备 (2天)
├── 选择数据集
└── 数据预处理

阶段 2: 模型微调 (3天)
├── 配置 LoRA
└── DeepSpeed 训练

阶段 3: 推理优化 (3天)
├── 模型量化
└── vLLM 部署

阶段 4: 生产部署 (3天)
├── K8s 部署
└── 监控告警
```

### 检验标准

- [ ] 完成一个完整的端到端项目
- [ ] 阅读至少一个核心项目的源码
- [ ] 能写技术博客总结学习成果

---

## 学习资源推荐

| 阶段 | 推荐资源 |
|------|----------|
| Month 1 | Linux 命令行大全、Docker 官方文档 |
| Month 2 | fast.ai 课程、PyTorch 官方 Tutorial |
| Month 3 | PMPP 书籍、NVIDIA CUDA Guide |
| Month 4 | PyTorch Distributed Tutorial |
| Month 5 | vLLM 文档 |
| Month 6 | Kubernetes 官方文档 |

---

## 延伸阅读

- [路径A-后端工程师转型](./02-path-backend-engineer.md)
- [核心技能清单](./05-core-skills.md)
- [推荐资源汇总](./06-recommended-resources.md)

---

*返回章节：[学习路线图](./README.md)*

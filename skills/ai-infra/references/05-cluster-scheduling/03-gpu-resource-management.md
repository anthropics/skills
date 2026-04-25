# GPU 资源管理

> 在 Kubernetes 中高效管理和分配 GPU 资源。

## 目录

- [NVIDIA Device Plugin](#nvidia-device-plugin)
- [GPU 共享方案对比](#gpu-共享方案对比)
- [MIG 多实例 GPU](#mig-多实例-gpu)
- [GPU 时间分片](#gpu-时间分片)
- [GPU 拓扑感知调度](#gpu-拓扑感知调度)

---

## NVIDIA Device Plugin

### 生活类比：GPU 管理员

想象 GPU 节点是一栋有 8 间独立办公室（GPU）的大楼。Device Plugin 就是**物业管理员**：

1. **盘点房间**：启动时检测有几间办公室、什么型号
2. **登记到系统**：向 kubelet 报告 `nvidia.com/gpu: 8`
3. **分配钥匙**：Pod 来了，给它分配具体哪间（`CUDA_VISIBLE_DEVICES=3`）
4. **回收钥匙**：Pod 退出后，房间变回可用

### 工作原理

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                 NVIDIA Device Plugin 工作原理                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐       ┌───────────────────────────────────────────────┐  │
│   │  Scheduler  │ ────▶ │ 调度决策: 哪个节点有足够的 GPU?                │  │
│   └─────────────┘       └───────────────────────────────────────────────┘  │
│         │                                                                   │
│         ▼                                                                   │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │                           Node                                       │  │
│   │  ┌───────────────────────────────────────────────────────────────┐  │  │
│   │  │           NVIDIA Device Plugin (DaemonSet)                     │  │  │
│   │  │                                                                │  │  │
│   │  │  1. 检测节点上的 GPU 数量和型号                                 │  │  │
│   │  │  2. 向 kubelet 注册 nvidia.com/gpu 资源                        │  │  │
│   │  │  3. Pod 启动时分配具体的 GPU 设备                               │  │  │
│   │  │  4. 设置 CUDA_VISIBLE_DEVICES 环境变量                         │  │  │
│   │  └───────────────────────────────────────────────────────────────┘  │  │
│   │                         │                                            │  │
│   │                         ▼                                            │  │
│   │  ┌───────────────────────────────────────────────────────────────┐  │  │
│   │  │              GPU 0    GPU 1    GPU 2    GPU 3                  │  │  │
│   │  └───────────────────────────────────────────────────────────────┘  │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 安装和验证

```bash
# 安装 NVIDIA Device Plugin（以 DaemonSet 形式部署到所有 GPU 节点）
kubectl apply -f https://raw.githubusercontent.com/NVIDIA/k8s-device-plugin/v0.14.0/nvidia-device-plugin.yml

# 验证安装（每个 GPU 节点应有一个 Running 的 Pod）
kubectl get pods -n kube-system | grep nvidia

# 查看节点 GPU 资源
kubectl get nodes -o json | jq '.items[].status.capacity | select(.["nvidia.com/gpu"])'
# 输出: "nvidia.com/gpu": "8"

# 检查 GPU 分配情况
kubectl describe node <node-name> | grep -A 5 "Allocated resources"
```

### 测试 GPU 访问

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: gpu-test
spec:
  containers:
  - name: cuda
    image: nvidia/cuda:12.0-base
    command: ["nvidia-smi"]
    resources:
      limits:
        nvidia.com/gpu: 1     # 申请 1 块 GPU
  restartPolicy: Never
```

```bash
kubectl apply -f gpu-test.yaml
kubectl logs gpu-test
# 应看到 nvidia-smi 输出，确认 GPU 可用
```

> **注意**：默认 Device Plugin 只支持**整卡分配**，不感知 GPU 拓扑。如需 MIG、时间分片或拓扑感知，需要额外配置或使用 GPU Operator。

---

## GPU 共享方案对比

在"一块 GPU 太贵、一个任务用不完"的场景下，GPU 共享是降本增效的关键。三种方案各有适用场景：

### 三种方案原理对比

```
方案 1: 独占 GPU（默认）
┌──────────────────────────────────┐
│         GPU (完整 80GB)           │
│    ┌──────────────────────────┐  │
│    │       Pod A (独占)        │  │
│    │   100% 算力, 100% 显存    │  │
│    └──────────────────────────┘  │
└──────────────────────────────────┘
类比: 一个人独占整间办公室

方案 2: MIG 硬件切分
┌──────────────────────────────────┐
│         GPU (A100 80GB)          │
│  ┌────────┐┌────────┐┌────────┐ │
│  │ MIG-0  ││ MIG-1  ││ MIG-2  │ │
│  │ Pod A  ││ Pod B  ││ Pod C  │ │
│  │ 20GB   ││ 20GB   ││ 40GB   │ │
│  └────────┘└────────┘└────────┘ │
└──────────────────────────────────┘
类比: 用实体墙把办公室隔成独立隔间
      每个隔间有自己的门锁和空调

方案 3: 时间分片
┌──────────────────────────────────┐
│         GPU (完整 80GB)           │
│  ┌──────────────────────────┐   │
│  │  t0: Pod A 运行          │   │
│  │  t1: Pod B 运行          │   │
│  │  t2: Pod C 运行          │   │
│  │  t3: Pod A 运行 ...      │   │
│  └──────────────────────────┘   │
└──────────────────────────────────┘
类比: 多人轮流使用同一间办公室（按时间段）
      东西放在桌上可能被别人看到
```

### 详细对比表

| 特性 | 独占 GPU | MIG | 时间分片 |
|------|---------|-----|---------|
| **隔离级别** | 完全隔离 | 硬件级隔离（显存+算力） | 无隔离 |
| **显存保障** | 100% 独占 | 固定分配（如 20GB/实例） | 共享，无保障 |
| **算力保障** | 100% 独占 | 固定分配（如 28 SM） | 共享，按时间轮转 |
| **性能干扰** | 无 | 极小（硬件隔离） | 有（上下文切换开销） |
| **故障隔离** | 完全 | 实例级隔离 | 无（一个 Pod OOM 可能影响其他） |
| **支持硬件** | 所有 GPU | A100/A30/H100 | 所有 GPU |
| **最小粒度** | 1 块 GPU | 1g.10gb（~1/7 卡） | 取决于 replicas 配置 |
| **适用场景** | 训练、高性能推理 | 多租户推理、开发 | 开发测试、低负载任务 |
| **配置复杂度** | 无需配置 | 需要 MIG 模式+驱动配置 | 简单（ConfigMap） |

### 如何选择？

```
你的任务需要什么？
       │
       ├── 完整算力 + 最大性能？
       │   └── ✅ 独占 GPU（训练、批量推理）
       │
       ├── 硬件级隔离 + 多租户？
       │   ├── 有 A100/H100？ → ✅ MIG
       │   └── 没有？ → 考虑多块小 GPU 替代
       │
       └── 只是开发测试 / 低负载？
           └── ✅ 时间分片（最简单、零成本）
```

---

## MIG 多实例 GPU

### MIG 原理深入

MIG（Multi-Instance GPU）是 NVIDIA 从 Ampere 架构开始引入的**硬件级 GPU 虚拟化**技术。它不是简单的软件隔离，而是在硬件层面将 GPU 的 SM（流多处理器）、显存控制器和 L2 Cache 都做了物理切分。

> **关键区别**：MIG 每个实例拥有独立的显存带宽通道。这意味着一个实例的显存密集访问不会影响另一个实例——就像每个隔间有独立的网线，不会互相抢带宽。

### MIG 配置选项 (A100 80GB)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       A100 MIG 配置选项                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Profile          切分数   每实例显存   每实例 SM   显存带宽               │
│   ──────────────  ────────  ─────────   ────────   ──────────              │
│   1g.10gb           7        10GB        14 SM      ~285 GB/s              │
│   2g.20gb           3        20GB        28 SM      ~570 GB/s              │
│   3g.40gb           2        40GB        42 SM      ~855 GB/s              │
│   7g.80gb           1        80GB        98 SM      ~2000 GB/s             │
│                                                                             │
│   混合切分示例 (常见生产配置):                                              │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │                        A100 80GB                                     │  │
│   │  ┌──────────────────────┬────────────────┬────────┬────────┐       │  │
│   │  │    3g.40gb           │   2g.20gb      │1g.10gb │1g.10gb │       │  │
│   │  │    大模型推理         │   小模型推理    │ 开发   │ 开发   │       │  │
│   │  └──────────────────────┴────────────────┴────────┴────────┘       │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Profile 选择指南

| 场景 | 推荐 Profile | 理由 |
|------|-------------|------|
| **7B LLM 推理**（FP16） | 3g.40gb | 需要 ~14GB 显存 + KV Cache 空间 |
| **1-3B 小模型推理** | 2g.20gb | 显存够用，算力适中 |
| **开发调试 / Notebook** | 1g.10gb | 最低成本，够跑小实验 |
| **Embedding 模型** | 1g.10gb | 模型小，批量处理 |
| **大模型推理（13B+）** | 7g.80gb | 需要完整显存和算力 |

> **注意**：MIG 不适合训练场景。训练需要 GPU 间高速通信（NVLink/NCCL），而 MIG 实例之间无法通过 NVLink 通信。

### 使用 MIG 资源

```yaml
# 请求特定 MIG Profile
apiVersion: v1
kind: Pod
metadata:
  name: mig-inference
spec:
  containers:
  - name: inference
    image: my-inference:latest
    resources:
      limits:
        nvidia.com/mig-3g.40gb: 1   # 请求 1 个 3g.40gb 实例
        # 其他可选:
        # nvidia.com/mig-1g.10gb: 1
        # nvidia.com/mig-2g.20gb: 1
        # nvidia.com/mig-7g.80gb: 1
```

### MIG 管理命令

```bash
# 查看当前 MIG 配置
nvidia-smi mig -lgip    # 列出可用的 GPU Instance Profile
nvidia-smi mig -lgi     # 列出已创建的 GPU Instance

# 启用 MIG 模式（需要重启 GPU）
sudo nvidia-smi -i 0 -mig 1

# 创建 MIG 实例
sudo nvidia-smi mig -i 0 -cgi 9,9,9,9,9,9,9 -C    # 7 × 1g.10gb
# 或混合配置
sudo nvidia-smi mig -i 0 -cgi 19,14,9,9 -C          # 1×3g.40gb + 1×2g.20gb + 2×1g.10gb

# 销毁所有 MIG 实例
sudo nvidia-smi mig -i 0 -dci && sudo nvidia-smi mig -i 0 -dgi
```

---

## GPU 时间分片

### 原理

时间分片利用 NVIDIA GPU 的**上下文切换**能力，让多个 CUDA 进程轮流使用同一块 GPU。操作系统级别的 GPU 调度器会按时间片分配 GPU 算力。

> **本质**：这不是"虚拟化"，而是"轮流使用"。所有进程共享同一块显存空间，没有隔离。如果一个进程分配了太多显存，其他进程会 OOM。

### 配置时间分片

```yaml
# time-slicing-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: time-slicing-config
  namespace: nvidia-device-plugin
data:
  any: |-
    version: v1
    sharing:
      timeSlicing:
        renameByDefault: false
        resources:
        - name: nvidia.com/gpu
          replicas: 4    # 每块 GPU "逻辑上"变成 4 块
```

```bash
# 应用配置
kubectl apply -f time-slicing-config.yaml

# 重启 device plugin 使配置生效
kubectl rollout restart daemonset nvidia-device-plugin -n kube-system

# 验证：节点 GPU 数量变为 4 倍
kubectl get nodes -o json | jq '.items[].status.capacity["nvidia.com/gpu"]'
# 原来 8，现在显示 32
```

> **重要风险**：时间分片后，K8s 认为节点有 32 块 GPU（实际只有 8 块）。如果 4 个 Pod 各申请 1 块 "GPU" 且每个都用满显存，就会出现显存不足。需要靠用户自律或配合 LimitRange 控制每个 Pod 的实际显存使用。

### 适用场景对比总结

| 方案 | 隔离性 | 性能开销 | 配置复杂度 | 适用场景 |
|------|--------|---------|-----------|---------|
| **独占 GPU** | 完全隔离 | 无 | 无 | 训练、高性能推理、生产关键任务 |
| **MIG** | 硬件隔离 | <5% | 中（需启用 MIG 模式） | 多租户推理、混合负载节点 |
| **时间分片** | 无隔离 | 5-15%（上下文切换） | 低（改 ConfigMap） | 开发测试、CI/CD、低负载探索 |

---

## GPU 拓扑感知调度

### 为什么拓扑很重要？

在多 GPU 节点上，并非所有 GPU 对之间的连接速度都相同：

```
典型 8-GPU 节点拓扑 (DGX A100)

     NVSwitch (全互联 600GB/s)
    ┌───┬───┬───┬───┬───┬───┬───┬───┐
    │ 0 │ 1 │ 2 │ 3 │ 4 │ 5 │ 6 │ 7 │
    └───┴───┴───┴───┴───┴───┴───┴───┘
       GPU 0-3: 同一 CPU socket (NUMA 0)
       GPU 4-7: 同一 CPU socket (NUMA 1)

跨 NUMA 通信 (GPU 0 ↔ GPU 5):
  数据路径: GPU 0 → NVSwitch → GPU 5 (直达，但 CPU 亲和性差)
  Host 内存: CPU 0 内存 → QPI → CPU 1 内存 (跨 NUMA 延迟+)
```

如果分布式训练的 2 块 GPU 分别在不同 NUMA 域，虽然 NVLink 通信不受影响，但 CPU 端的数据预处理和 Host 内存拷贝会受 NUMA 影响。

### 启用拓扑感知

使用 **GPU Feature Discovery** (GFD) + **Topology-aware Scheduling**：

```bash
# 安装 GPU Feature Discovery（自动标记节点 GPU 拓扑信息）
kubectl apply -f https://raw.githubusercontent.com/NVIDIA/gpu-feature-discovery/v0.8.0/deployments/static/gpu-feature-discovery-daemonset.yaml

# 查看自动添加的节点标签
kubectl get node <node> -o json | jq '.metadata.labels | with_entries(select(.key | startswith("nvidia.com")))'
# 输出示例:
# "nvidia.com/gpu.product": "NVIDIA-A100-SXM4-80GB"
# "nvidia.com/gpu.count": "8"
# "nvidia.com/mig.capable": "true"
# "nvidia.com/gpu.memory": "81920"
```

```yaml
# 利用拓扑信息做亲和性调度
apiVersion: v1
kind: Pod
metadata:
  name: training-pod
spec:
  nodeSelector:
    nvidia.com/gpu.product: "NVIDIA-A100-SXM4-80GB"    # 指定 GPU 型号
  containers:
  - name: trainer
    resources:
      limits:
        nvidia.com/gpu: 4    # 希望拿到同一 NUMA 域的 4 块 GPU
```

> **最佳实践**：对于需要 2-4 GPU 的训练任务，配合 NVIDIA 的 Topology-aware GPU Scheduling Plugin，可以确保分配到的 GPU 具有最优互联拓扑（NVLink 直连），而非随机分配。这在多租户共享节点时尤为重要。

---

*下一篇：[04-批调度器详解](04-batch-schedulers.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **NVIDIA.** *NVIDIA Device Plugin for Kubernetes.*  
   https://github.com/NVIDIA/k8s-device-plugin

2. **NVIDIA.** *Multi-Instance GPU (MIG) User Guide.*  
   https://docs.nvidia.com/datacenter/tesla/mig-user-guide/

3. **Kubernetes.** *Extended Resources / Device Plugins.*  
   https://kubernetes.io/docs/concepts/extend-kubernetes/compute-storage-net/device-plugins/

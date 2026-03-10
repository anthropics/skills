# Kubernetes 基础

> 掌握 K8s 核心概念，理解 AI 工作负载的配置方式。

## 目录

- [核心概念回顾](#核心概念回顾)
- [AI 工作负载配置](#ai-工作负载配置)
- [资源请求策略](#资源请求策略)
- [常用操作命令](#常用操作命令)

---

## 核心概念回顾

### 生活类比：K8s 就像一个智能物流中心

把 GPU 集群想象成一个大型物流仓储中心：

| K8s 概念 | 物流中心类比 | 核心职责 |
|----------|-------------|---------|
| **Cluster** | 整个仓储园区 | 所有资源的集合 |
| **Node** | 单栋仓库 | 实际存放货物（运行容器）的物理空间 |
| **Pod** | 一个包裹（可含多件商品） | 最小调度单元，共享网络和存储 |
| **Deployment** | "持续补货"策略 | 保持指定数量副本始终运行 |
| **Job** | "一次性配送"订单 | 跑完就结束，不需要持续运行 |
| **Scheduler** | 智能分拣系统 | 决定每个包裹放哪栋仓库 |
| **Namespace** | 不同租户的隔离仓区 | 资源和权限的隔离边界 |

### 基础对象

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Kubernetes 核心对象                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Pod: 最小调度单元                                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  Pod                                                                │   │
│   │   ┌──────────────┐  ┌──────────────┐                               │   │
│   │   │ Container 1  │  │ Container 2  │   共享网络/存储               │   │
│   │   └──────────────┘  └──────────────┘                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   工作负载类型:                                                             │
│   ─────────────                                                             │
│   • Deployment  - 无状态服务 (推理服务)                                    │
│   • StatefulSet - 有状态服务 (参数服务器)                                  │
│   • Job         - 一次性任务 (训练任务)                                    │
│   • CronJob     - 定时任务 (定期重训练)                                    │
│                                                                             │
│   资源管理:                                                                 │
│   ─────────────                                                             │
│   • Request: 调度时保证的最小资源                                           │
│   • Limit: 运行时的资源上限                                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 为什么 AI 工作负载主要用 Job 而非 Deployment？

训练任务有明确的"开始→结束"生命周期，跑完就释放 GPU。如果用 Deployment，任务结束后 Pod 仍占着 GPU 不释放——就像快递送完了还占着停车位。

| 对比项 | Job | Deployment |
|--------|-----|-----------|
| **生命周期** | 有限（跑完退出） | 无限（持续运行） |
| **失败处理** | 自动重试 `backoffLimit` 次 | 重启 Pod |
| **完成判定** | `completions` 个 Pod 成功退出 | 无"完成"概念 |
| **典型用途** | 模型训练、数据预处理、评估 | 推理服务、API 网关 |
| **GPU 释放** | 任务完成后立即释放 | 手动缩容才释放 |

> **关键洞察**：分布式训练常用 **多 Pod Job**（`parallelism=N`）或 Volcano Job，而非手动创建多个 Deployment。

### 调度相关概念

```
调度决策流程：一个 GPU Pod 如何被分配到节点？

用户提交 Pod                   Scheduler 过滤 + 打分
     │                              │
     ▼                              ▼
┌──────────┐    ┌──────────────────────────────────────────────────┐
│ Pod Spec │───▶│ 1. 过滤阶段(Filtering)                           │
│          │    │    ✗ 节点 A: 0 GPU → 淘汰                        │
│ GPU: 4   │    │    ✗ 节点 B: 2 GPU → 不够 → 淘汰                │
│ nodeSelector: │    │    ✓ 节点 C: 8 GPU, type=a100 → 候选         │
│  gpu-type:   │    │    ✓ 节点 D: 8 GPU, type=a100 → 候选         │
│   a100       │    │                                                │
│ tolerations: │    │ 2. 打分阶段(Scoring)                           │
│  nvidia-gpu  │    │    节点 C: 已用 2 GPU → 分数 80                │
└──────────┘    │    节点 D: 已用 6 GPU → 分数 40                │
                │                                                │
                │ 3. 绑定(Binding): Pod → 节点 C                  │
                └──────────────────────────────────────────────────┘
```

| 概念 | 作用 | AI 场景应用 | 类比 |
|------|------|-------------|------|
| **NodeSelector** | 选择特定标签节点 | 选择 GPU 类型（A100/H100） | 指定快递送到哪个仓库 |
| **Tolerations** | 容忍节点污点 | 允许调度到 GPU 专用节点 | 有"危险品运输许可证" |
| **Affinity** | 亲和性/反亲和性 | 分布式训练 Pod 同机/跨机 | 同一批货放在同一楼层 |
| **Topology** | 拓扑感知 | GPU 拓扑亲和（NVLink 连接） | 相邻仓位便于搬运 |
| **Priority** | 任务优先级 | 生产推理 > 训练 > 开发 | VIP 快递优先处理 |

**Taint + Toleration 模式**：GPU 节点通常设置 `nvidia.com/gpu=true:NoSchedule` 污点，防止非 GPU Pod 被调度上去浪费资源。只有显式声明 Toleration 的 Pod 才能"进入"GPU 节点——就像进入仓库的"限制区域"需要特别通行证。

---

## AI 工作负载配置

### 训练任务 Job

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: llama-training
  namespace: ml-training
spec:
  completions: 1           # 需要成功完成的 Pod 数
  parallelism: 1           # 同时运行的 Pod 数
  backoffLimit: 3          # 最多重试 3 次（GPU OOM 或节点故障）
  template:
    spec:
      restartPolicy: OnFailure     # ← 注意：Job 只允许 OnFailure 或 Never
      
      # ── 节点选择：精确指定 GPU 型号 ──
      nodeSelector:
        gpu-type: a100-80gb        # 标签选择
      
      # ── 容忍 GPU 节点污点 ──
      tolerations:
      - key: "nvidia.com/gpu"
        operator: "Exists"
        effect: "NoSchedule"
      
      containers:
      - name: trainer
        image: pytorch/pytorch:2.0.0-cuda11.8-cudnn8-runtime
        command: ["torchrun"]
        args:
        - "--nproc_per_node=8"     # 每节点 8 个进程（对应 8 GPU）
        - "train.py"
        
        # ── 资源请求 ──
        resources:
          requests:                 # 调度保证（Scheduler 据此选节点）
            cpu: "32"
            memory: "256Gi"
            nvidia.com/gpu: "8"    # GPU 必须 request = limit
          limits:                   # 运行上限
            cpu: "64"
            memory: "512Gi"
            nvidia.com/gpu: "8"    # GPU 不支持超售
        
        env:
        - name: NCCL_DEBUG
          value: "INFO"
        
        volumeMounts:
        - name: data
          mountPath: /data
        - name: shm                # 共享内存
          mountPath: /dev/shm
      
      volumes:
      - name: data
        persistentVolumeClaim:
          claimName: training-data-pvc
      - name: shm
        emptyDir:
          medium: Memory           # tmpfs，使用内存而非磁盘
          sizeLimit: 64Gi          # DataLoader 多进程通信需要大共享内存
```

> **为什么 `/dev/shm` 如此重要？** PyTorch DataLoader 的 `num_workers>0` 时，父子进程通过共享内存传递数据。K8s 默认 `/dev/shm` 只有 64MB，多 worker 大 batch 训练会直接报 `Bus Error`。这是 AI 训练上 K8s 最常踩的坑之一。

### 推理服务 Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: llm-inference
spec:
  replicas: 3                      # 3 副本保证可用性
  selector:
    matchLabels:
      app: llm-inference
  template:
    metadata:
      labels:
        app: llm-inference
    spec:
      containers:
      - name: vllm
        image: vllm/vllm-openai:latest
        args:
        - "--model=/models/llama-7b"
        - "--tensor-parallel-size=1"
        
        resources:
          limits:
            nvidia.com/gpu: 1      # 推理通常 1-2 GPU 即可
        
        ports:
        - containerPort: 8000
        
        # ── 健康检查：推理服务必须配置 ──
        readinessProbe:            # 就绪探针：未就绪不会接收流量
          httpGet:
            path: /health
            port: 8000
          initialDelaySeconds: 60  # 模型加载需要时间（7B 约 30-60s）
          periodSeconds: 10
        
        livenessProbe:             # 存活探针：服务挂了会重启
          httpGet:
            path: /health
            port: 8000
          initialDelaySeconds: 120
          periodSeconds: 30
          failureThreshold: 3      # 连续 3 次失败才重启
```

> **为什么 `initialDelaySeconds` 要设这么大？** LLM 推理服务启动时需要：加载模型权重到 GPU 显存（7B ≈ 14GB，加载耗时 ~30s）→ 预热 KV Cache → CUDA kernel 编译。如果探针过早检查，会误杀正在启动的 Pod，导致反复重启。

---

## 资源请求策略

### GPU 资源的特殊性

GPU 在 K8s 中是**扩展资源**（Extended Resource），与 CPU/内存有本质不同：

| 特性 | CPU | Memory | GPU |
|------|-----|--------|-----|
| **是否可压缩** | ✅ 可压缩（超用会限速） | ❌ 不可压缩（超用会 OOMKill） | ❌ 不可分割 |
| **request ≠ limit** | 允许超售 | 允许（但危险） | **不允许**，必须相等 |
| **最小单位** | 1m（千分之一核） | 1 字节 | **1 块 GPU**（整卡） |
| **调度含义** | 保证最低 CPU | 保证最低内存 | 独占 N 块 GPU |

> **关键规则**：`nvidia.com/gpu` 的 request 必须等于 limit，且必须是整数。不能申请 0.5 块 GPU（MIG 除外）。这意味着 GPU 天然不支持超售——一块卡分给了你，别人就用不了。

### request/limit 策略建议

```
场景 1: 训练任务（GPU 密集型）
┌──────────────────────────────────────────────────┐
│  resources:                                       │
│    requests:                                      │
│      cpu: "32"        ← 匹配 GPU 数量 (4核/GPU)  │
│      memory: "256Gi"  ← 2× GPU 显存总量           │
│      nvidia.com/gpu: "8"                          │
│    limits:                                        │
│      cpu: "64"        ← 允许突发（数据预处理）     │
│      memory: "512Gi"  ← 留余量防 OOM              │
│      nvidia.com/gpu: "8"  ← 必须 = request        │
└──────────────────────────────────────────────────┘

场景 2: 推理服务（延迟敏感型）
┌──────────────────────────────────────────────────┐
│  resources:                                       │
│    requests:                                      │
│      cpu: "4"         ← 前后处理需要 CPU           │
│      memory: "32Gi"   ← 模型权重 + KV Cache        │
│      nvidia.com/gpu: "1"                          │
│    limits:                                        │
│      cpu: "8"                                     │
│      memory: "64Gi"   ← 防止长序列 KV Cache 爆内存 │
│      nvidia.com/gpu: "1"                          │
└──────────────────────────────────────────────────┘
```

**CPU 配比经验**：训练时 DataLoader 需要大量 CPU 做数据增强和预处理。经验法则是 **每块 GPU 配 4-8 个 CPU 核**。如果 CPU 不足，GPU 会因"等数据"而空转（utilization 忽高忽低是典型症状）。

**内存配比经验**：Host 内存至少是 GPU 显存总量的 2 倍。8×A100-80GB 的节点应配 ≥1.28TB 内存。ZeRO-Offload 会将优化器状态卸载到 CPU 内存，需要更多。

---

## 常用操作命令

### 任务管理

```bash
# 提交任务
kubectl apply -f training-job.yaml

# 查看任务状态
kubectl get jobs -n ml-training
kubectl describe job llama-training -n ml-training

# 查看 Pod 日志（-f 实时跟踪）
kubectl logs -f <pod-name> -n ml-training

# 查看前一个崩溃容器的日志（排查 OOM/CUDA Error）
kubectl logs <pod-name> -n ml-training --previous

# 进入 Pod 调试
kubectl exec -it <pod-name> -n ml-training -- bash

# 在 Pod 内验证 GPU
kubectl exec -it <pod-name> -n ml-training -- nvidia-smi

# 删除任务
kubectl delete job llama-training -n ml-training
```

### 资源查看

```bash
# 查看节点 GPU 资源（总量/已分配）
kubectl get nodes -o json | jq '.items[] | {
  name: .metadata.name,
  gpu_total: .status.capacity["nvidia.com/gpu"],
  gpu_alloc: .status.allocatable["nvidia.com/gpu"]
}'

# 查看 GPU 使用情况（快速概览）
kubectl describe nodes | grep -A 5 "Allocated resources"

# 查看命名空间配额使用
kubectl describe resourcequota -n ml-training

# 查看哪些 Pod 占用了 GPU
kubectl get pods --all-namespaces -o json | jq '.items[] |
  select(.spec.containers[].resources.limits["nvidia.com/gpu"] != null) |
  {namespace: .metadata.namespace, name: .metadata.name,
   gpu: .spec.containers[].resources.limits["nvidia.com/gpu"]}'
```

### 常见问题排查

```bash
# Pod 一直 Pending？查看事件找原因
kubectl describe pod <pod-name> -n ml-training
# 常见原因:
#   - Insufficient nvidia.com/gpu → 集群无空闲 GPU
#   - 0/10 nodes are available: 1 node had taint... → 缺少 toleration
#   - exceeded quota → ResourceQuota 已满

# GPU Pod 启动后报错？
kubectl logs <pod-name> -n ml-training | grep -i "cuda\|gpu\|nccl\|error"
# 常见原因:
#   - CUDA out of memory → 显存不足，减小 batch_size
#   - NCCL error → 多机通信问题，检查网络和 NCCL 配置
#   - Bus Error → /dev/shm 太小，增大 sizeLimit
```

---

*下一篇：[03-GPU 资源管理](03-gpu-resource-management.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Kubernetes Documentation.** *Kubernetes Official Docs.*  
   https://kubernetes.io/docs/

2. **NVIDIA.** *GPU Operator for Kubernetes.*  
   https://docs.nvidia.com/datacenter/cloud-native/gpu-operator/

3. **CNCF.** *Cloud Native Computing Foundation.*  
   https://www.cncf.io/

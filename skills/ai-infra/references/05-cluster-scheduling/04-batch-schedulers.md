# 批调度器详解

> Volcano、Yunikorn、Kueue 为 AI 工作负载提供高级调度能力。

## 目录

- [Volcano](#volcano)
- [Yunikorn](#yunikorn)
- [Kueue](#kueue)
- [调度器选择](#调度器选择)

---

## Volcano

专为 AI/大数据批处理设计的 K8s 调度器。

### 核心能力

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       Volcano 核心能力                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. Gang Scheduling (组调度)                                               │
│   ─────────────────────────                                                 │
│   分布式训练必须所有 worker 同时启动                                        │
│   minAvailable: 4 → 不足 4 个资源时不启动任何 Pod                          │
│                                                                             │
│   2. Fair Share (公平共享)                                                  │
│   ─────────────────────────                                                 │
│   多团队按权重公平分配资源                                                  │
│                                                                             │
│   3. Queue Management (队列管理)                                            │
│   ─────────────────────────                                                 │
│   资源上限、优先级、借用策略                                                │
│                                                                             │
│   4. Preemption (抢占)                                                      │
│   ─────────────────────────                                                 │
│   高优先级任务可抢占低优先级                                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 安装 Volcano

```bash
# 推荐使用 Helm 安装 (生产环境)
helm repo add volcano-sh https://volcano-sh.github.io/helm-charts
helm install volcano volcano-sh/volcano -n volcano-system --create-namespace

# 或使用 kubectl 安装 (注意使用最新 release 版本)
kubectl apply -f https://raw.githubusercontent.com/volcano-sh/volcano/release-1.9/installer/volcano-development.yaml

# 验证
kubectl get pods -n volcano-system
```

### Volcano Job 示例

```yaml
apiVersion: batch.volcano.sh/v1alpha1
kind: Job
metadata:
  name: distributed-training
spec:
  minAvailable: 4  # Gang Scheduling: 至少 4 个 Pod 才启动
  schedulerName: volcano
  queue: training-queue
  
  plugins:
    svc: []  # 自动创建 headless service
    ssh: []  # 自动配置 SSH 互信
  
  tasks:
  - replicas: 4
    name: worker
    template:
      spec:
        containers:
        - name: pytorch
          image: pytorch/pytorch:2.0.0-cuda11.8-cudnn8-runtime
          command:
          - torchrun
          - --nnodes=4
          - --nproc_per_node=8
          - --rdzv_backend=c10d
          - --rdzv_endpoint=$(VC_TASK_0_HOSTS):29500
          - train.py
          resources:
            limits:
              nvidia.com/gpu: 8
        restartPolicy: OnFailure
```

### 队列管理

```yaml
# 创建队列
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: training-queue
spec:
  weight: 2  # 权重，影响资源分配比例
  capability:  # 队列资源上限
    cpu: "100"
    memory: "500Gi"
    nvidia.com/gpu: "32"
  reclaimable: true  # 允许回收空闲资源

---
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: inference-queue
spec:
  weight: 1
  capability:
    nvidia.com/gpu: "16"
```

---

## Yunikorn

Apache 孵化的批调度器，与 K8s 深度集成。

### 安装 Yunikorn

```bash
helm repo add yunikorn https://apache.github.io/yunikorn-release
helm install yunikorn yunikorn/yunikorn \
  --namespace yunikorn \
  --create-namespace
```

### 配置队列

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: yunikorn-configs
  namespace: yunikorn
data:
  queues.yaml: |
    partitions:
    - name: default
      queues:
      - name: root
        queues:
        - name: training
          resources:
            guaranteed:
              nvidia.com/gpu: "16"
            max:
              nvidia.com/gpu: "32"
        - name: inference
          resources:
            guaranteed:
              nvidia.com/gpu: "8"
            max:
              nvidia.com/gpu: "16"
```

### 使用 Yunikorn

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: training-job
  labels:
    applicationId: "training-001"
    queue: "root.training"  # 指定队列
spec:
  template:
    metadata:
      labels:
        applicationId: "training-001"
        queue: "root.training"
    spec:
      schedulerName: yunikorn
      # ...
```

---

## Kueue

Kubernetes 原生的作业队列系统，由 Kubernetes SIG Scheduling 维护，专注于**资源配额管理和作业排队**。

### 核心概念

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       Kueue 核心概念                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. ResourceFlavor (资源风味)                                              │
│   ─────────────────────────                                                 │
│   描述集群中不同类型的资源 (如 A100 vs H100, spot vs on-demand)             │
│                                                                             │
│   2. ClusterQueue (集群队列)                                                │
│   ─────────────────────────                                                 │
│   定义资源容量和配额，管理作业准入策略                                      │
│   一个 ClusterQueue 可包含多个 ResourceFlavor                               │
│                                                                             │
│   3. LocalQueue (本地队列)                                                  │
│   ─────────────────────────                                                 │
│   命名空间级别的队列，指向 ClusterQueue，供用户提交作业                     │
│                                                                             │
│   4. Workload (工作负载)                                                    │
│   ─────────────────────────                                                 │
│   Kueue 对提交的 Job/Pod 的抽象封装                                        │
│                                                                             │
│   流程: 用户提交 Job → LocalQueue → ClusterQueue → 资源检查 → 准入/排队   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 安装 Kueue

```bash
# 使用 kubectl 安装 (推荐最新稳定版)
VERSION=v0.9.1
kubectl apply --server-side -f https://github.com/kubernetes-sigs/kueue/releases/download/$VERSION/manifests.yaml

# 验证安装
kubectl get pods -n kueue-system
```

### 配置示例

```yaml
# 1. 定义 ResourceFlavor
apiVersion: kueue.x-k8s.io/v1beta1
kind: ResourceFlavor
metadata:
  name: gpu-a100
spec:
  nodeLabels:
    gpu-type: a100  # 匹配标签为 gpu-type=a100 的节点

---
apiVersion: kueue.x-k8s.io/v1beta1
kind: ResourceFlavor
metadata:
  name: gpu-h100
spec:
  nodeLabels:
    gpu-type: h100

---
# 2. 定义 ClusterQueue
apiVersion: kueue.x-k8s.io/v1beta1
kind: ClusterQueue
metadata:
  name: training-cluster-queue
spec:
  namespaceSelector: {}  # 允许所有命名空间
  preemption:
    reclaimWithinCohort: Any      # 允许回收同群组的资源
    withinClusterQueue: LowerPriority  # 队列内低优先级可被抢占
  resourceGroups:
  - coveredResources: ["cpu", "memory", "nvidia.com/gpu"]
    flavors:
    - name: gpu-a100
      resources:
      - name: "nvidia.com/gpu"
        nominalQuota: 32        # 保障配额
        borrowingLimit: 8       # 最多可借用 8 块
      - name: "cpu"
        nominalQuota: 128
      - name: "memory"
        nominalQuota: 512Gi
    - name: gpu-h100
      resources:
      - name: "nvidia.com/gpu"
        nominalQuota: 16
      - name: "cpu"
        nominalQuota: 64
      - name: "memory"
        nominalQuota: 256Gi

---
# 3. 定义 LocalQueue (命名空间级别)
apiVersion: kueue.x-k8s.io/v1beta1
kind: LocalQueue
metadata:
  name: team-a-queue
  namespace: team-a
spec:
  clusterQueue: training-cluster-queue
```

### 提交作业

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: llm-training
  namespace: team-a
  labels:
    kueue.x-k8s.io/queue-name: team-a-queue  # 指定 LocalQueue
spec:
  parallelism: 4
  completions: 4
  template:
    spec:
      containers:
      - name: pytorch
        image: pytorch/pytorch:2.1.0-cuda12.1-cudnn8-runtime
        command: ["torchrun", "--nproc_per_node=8", "train.py"]
        resources:
          requests:
            nvidia.com/gpu: 8
            cpu: 32
            memory: 128Gi
          limits:
            nvidia.com/gpu: 8
      restartPolicy: Never
```

### Kueue vs Volcano/Yunikorn 定位

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Kueue 的独特定位                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Kueue 不替换 kube-scheduler，而是作为**准入控制层**                       │
│                                                                             │
│   Job 提交 → Kueue (排队、配额检查、准入) → kube-scheduler (调度)          │
│                                                                             │
│   优势:                                                                     │
│   • 与默认 kube-scheduler 兼容，无需替换                                   │
│   • 可与 Volcano/Yunikorn 协同 (Kueue 管配额, 它们管调度)                  │
│   • K8s 官方维护，生态最好                                                 │
│   • 原生支持多种 Job 类型 (Job, PyTorchJob, RayJob 等)                     │
│   • 灵活的 ResourceFlavor 适配异构集群                                     │
│                                                                             │
│   局限:                                                                     │
│   • 不提供 Gang Scheduling (需要配合 Volcano 等)                           │
│   • 调度策略不如 Volcano 丰富                                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 调度器选择

| 特性 | Volcano | Yunikorn | Kueue |
|------|---------|----------|-------|
| **Gang Scheduling** | ✅ 原生支持 | ✅ 支持 | ❌ 需配合其他调度器 |
| **队列管理** | ✅ 强大 | ✅ 层级队列 | ✅ ClusterQueue + LocalQueue |
| **公平调度** | ✅ DRF | ✅ 多策略 | ✅ 配额 + 借用 + 抢占 |
| **多 ResourceFlavor** | ❌ | ❌ | ✅ 异构资源管理 |
| **与 kube-scheduler 关系** | 替换 | 替换 | 协同 (不替换) |
| **社区** | CNCF Sandbox | Apache 孵化 | K8s SIG Scheduling |
| **最适合** | AI 训练 | 混合负载 | 配额管理 + 异构集群 |

**建议**：
- AI 训练为主，需要 Gang Scheduling → **Volcano**
- 混合负载、与 Spark 结合 → **Yunikorn**
- 异构 GPU 集群、K8s 原生生态 → **Kueue**
- 生产推荐组合 → **Kueue (配额管理) + Volcano (调度)**

---

*下一篇：[05-资源隔离与配额](05-resource-isolation.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Volcano.** *Volcano: Cloud Native Batch System.*  
   https://volcano.sh/

2. **Kubernetes SIG Scheduling.** *Kueue: Job Queueing for Kubernetes.*  
   https://kueue.sigs.k8s.io/

3. **Run:ai.** *GPU Orchestration Platform.*  
   https://www.run.ai/

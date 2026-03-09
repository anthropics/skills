# 集群调度与资源管理详解

> GPU 资源昂贵，高效调度直接影响成本和效率。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [05-cluster-scheduling/](./05-cluster-scheduling/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | AI 工作负载的调度挑战 | [01-ai-workload-challenges.md](./05-cluster-scheduling/01-ai-workload-challenges.md) |
> | Kubernetes 基础 | [02-kubernetes-basics.md](./05-cluster-scheduling/02-kubernetes-basics.md) |
> | GPU 资源管理 | [03-gpu-resource-management.md](./05-cluster-scheduling/03-gpu-resource-management.md) |
> | 批调度器详解 | [04-batch-schedulers.md](./05-cluster-scheduling/04-batch-schedulers.md) |
> | 资源隔离与配额 | [05-resource-isolation.md](./05-cluster-scheduling/05-resource-isolation.md) |
> | 多租户管理 | [06-multi-tenancy.md](./05-cluster-scheduling/06-multi-tenancy.md) |
> | 成本优化策略 | [07-cost-optimization.md](./05-cluster-scheduling/07-cost-optimization.md) |
> | GPU 监控与可观测性 | [08-gpu-monitoring.md](./05-cluster-scheduling/08-gpu-monitoring.md) |
> | AI 存储系统 | [09-storage-systems.md](./05-cluster-scheduling/09-storage-systems.md) |
> | 网络基础设施 | [10-network-infrastructure.md](./05-cluster-scheduling/10-network-infrastructure.md) |

---

## 目录

- [AI 工作负载的调度挑战](#ai-工作负载的调度挑战)
- [Kubernetes 基础](#kubernetes-基础)
- [GPU 资源管理](#gpu-资源管理)
- [批调度器](#批调度器)
- [资源隔离与配额](#资源隔离与配额)
- [多租户管理](#多租户管理)
- [成本优化策略](#成本优化策略)
- [实战练习](#实战练习)

---

## AI 工作负载的调度挑战

### 传统工作负载 vs AI 工作负载

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  AI 工作负载的特殊性                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统 Web 服务                       AI 训练任务                        │
│   ─────────────                       ──────────                        │
│   - 长时间运行                         - 批处理，有明确结束时间           │
│   - 资源需求稳定                       - 资源需求变化大                   │
│   - 可随时弹性伸缩                     - 需要 Gang Scheduling            │
│   - CPU 密集                           - GPU 密集                        │
│   - 无状态/状态可外置                  - 有状态 (checkpoint)             │
│   - 故障重启即可                       - 需要从 checkpoint 恢复          │
│                                                                         │
│   AI 训练的调度挑战:                                                    │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ 1. Gang Scheduling                                              │   │
│   │    分布式训练需要所有 worker 同时启动，否则无法通信               │   │
│   │                                                                 │   │
│   │ 2. GPU 拓扑感知                                                  │   │
│   │    NVLink 连接的 GPU 应尽量调度到一起，通信效率高                 │   │
│   │                                                                 │   │
│   │ 3. 抢占与恢复                                                    │   │
│   │    支持优先级抢占，低优先级任务能保存进度                         │   │
│   │                                                                 │   │
│   │ 4. 资源碎片化                                                    │   │
│   │    GPU 不可切分（传统），导致碎片问题严重                         │   │
│   │                                                                 │   │
│   │ 5. 公平性                                                        │   │
│   │    多团队共享集群，需要公平分配 GPU 资源                          │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 调度架构演进

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    调度系统演进                                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统 HPC (Slurm)        Kubernetes + 扩展        云原生 AI 平台       │
│   ────────────────        ──────────────────        ────────────        │
│   - 专为批处理设计         - 通用容器编排            - AI 原生           │
│   - 资源队列               - 需要额外调度器          - 一站式平台        │
│   - 静态资源划分           - GPU 插件支持            - 自动化程度高      │
│                           - Volcano/Yunikorn                            │
│                                                                         │
│   ┌───────────────────┐   ┌───────────────────┐   ┌───────────────────┐ │
│   │      Slurm        │   │   Kubernetes      │   │   Kubeflow        │ │
│   │       +           │   │       +           │   │   Ray Cluster     │ │
│   │   PBS/Torque      │   │  Volcano/Yunikorn │   │   MLflow          │ │
│   └───────────────────┘   └───────────────────┘   └───────────────────┘ │
│                                                                         │
│   大多数公司选择: Kubernetes + 批调度器扩展                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Kubernetes 基础

### K8s 核心概念回顾

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Kubernetes 核心对象                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Pod: 最小调度单元                                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │  ┌───────────────────────────────────────────────────────┐      │   │
│   │  │ Pod                                                    │      │   │
│   │  │  ┌──────────────┐  ┌──────────────┐                   │      │   │
│   │  │  │ Container 1  │  │ Container 2  │  共享网络/存储     │      │   │
│   │  │  └──────────────┘  └──────────────┘                   │      │   │
│   │  └───────────────────────────────────────────────────────┘      │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   常用工作负载类型:                                                      │
│   - Deployment: 无状态服务 (如推理服务)                                  │
│   - StatefulSet: 有状态服务 (如参数服务器)                               │
│   - Job: 一次性任务 (如训练任务)                                         │
│   - CronJob: 定时任务 (如定期重训练)                                     │
│                                                                         │
│   资源管理:                                                              │
│   - Request: 调度时保证的最小资源                                        │
│   - Limit: 运行时的资源上限                                              │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### AI 工作负载的 K8s 配置

```yaml
# training-job.yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: llama-training
  namespace: ml-training
spec:
  completions: 1
  parallelism: 1
  backoffLimit: 3
  template:
    metadata:
      labels:
        app: llama-training
    spec:
      restartPolicy: OnFailure
      
      # 节点选择
      nodeSelector:
        gpu-type: a100-80gb
      
      # 容忍污点
      tolerations:
      - key: "nvidia.com/gpu"
        operator: "Exists"
        effect: "NoSchedule"
      
      containers:
      - name: trainer
        image: pytorch/pytorch:2.0.0-cuda11.8-cudnn8-runtime
        command: ["torchrun"]
        args:
        - "--nproc_per_node=8"
        - "train.py"
        - "--config=configs/llama-7b.yaml"
        
        resources:
          requests:
            cpu: "32"
            memory: "256Gi"
            nvidia.com/gpu: "8"
          limits:
            cpu: "64"
            memory: "512Gi"
            nvidia.com/gpu: "8"
        
        # 环境变量
        env:
        - name: NCCL_DEBUG
          value: "INFO"
        - name: CUDA_VISIBLE_DEVICES
          value: "0,1,2,3,4,5,6,7"
        
        # 挂载存储
        volumeMounts:
        - name: data
          mountPath: /data
        - name: checkpoints
          mountPath: /checkpoints
        - name: shm  # 共享内存，用于 DataLoader
          mountPath: /dev/shm
      
      volumes:
      - name: data
        persistentVolumeClaim:
          claimName: training-data-pvc
      - name: checkpoints
        persistentVolumeClaim:
          claimName: checkpoints-pvc
      - name: shm
        emptyDir:
          medium: Memory
          sizeLimit: 64Gi
```

---

## GPU 资源管理

### NVIDIA Device Plugin

```
┌─────────────────────────────────────────────────────────────────────────┐
│               NVIDIA Device Plugin 工作原理                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                      Kubernetes                                  │   │
│   │                                                                 │   │
│   │   ┌─────────────┐      ┌─────────────────────────────────────┐ │   │
│   │   │  Scheduler  │ ──→  │ 调度决策: 哪个节点有足够的 GPU?      │ │   │
│   │   └─────────────┘      └─────────────────────────────────────┘ │   │
│   │         │                                                       │   │
│   │         ▼                                                       │   │
│   │   ┌─────────────────────────────────────────────────────────┐  │   │
│   │   │                    Node                                  │  │   │
│   │   │                                                         │  │   │
│   │   │   ┌──────────────────────────────────────────────────┐ │  │   │
│   │   │   │           NVIDIA Device Plugin (DaemonSet)        │ │  │   │
│   │   │   │                                                   │ │  │   │
│   │   │   │  1. 检测节点上的 GPU 数量和型号                    │ │  │   │
│   │   │   │  2. 向 kubelet 注册 nvidia.com/gpu 资源           │ │  │   │
│   │   │   │  3. Pod 启动时分配具体的 GPU 设备                  │ │  │   │
│   │   │   │  4. 设置 CUDA_VISIBLE_DEVICES 环境变量            │ │  │   │
│   │   │   │                                                   │ │  │   │
│   │   │   └──────────────────────────────────────────────────┘ │  │   │
│   │   │                         │                               │  │   │
│   │   │                         ▼                               │  │   │
│   │   │   ┌──────────────────────────────────────────────────┐ │  │   │
│   │   │   │              GPU 0    GPU 1    GPU 2    GPU 3     │ │  │   │
│   │   │   └──────────────────────────────────────────────────┘ │  │   │
│   │   │                                                         │  │   │
│   │   └─────────────────────────────────────────────────────────┘  │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 安装 NVIDIA Device Plugin

```bash
# 安装 NVIDIA Device Plugin
kubectl create -f https://raw.githubusercontent.com/NVIDIA/k8s-device-plugin/v0.14.0/nvidia-device-plugin.yml

# 验证
kubectl get nodes -o json | jq '.items[].status.capacity'
# 应该能看到 "nvidia.com/gpu": "8"

# 检查 GPU 分配
kubectl describe node <node-name> | grep -A 5 "Allocated resources"
```

### MIG（Multi-Instance GPU）

将单个 GPU 切分为多个独立实例。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    A100 MIG 配置                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   A100 80GB 可切分方式:                                                  │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ 配置方式              │  切分数  │  每实例显存  │ 每实例 SM      │   │
│   │──────────────────────│─────────│────────────│──────────────│   │
│   │ 1g.10gb              │   7     │   10GB     │  14 SM       │   │
│   │ 2g.20gb              │   3     │   20GB     │  28 SM       │   │
│   │ 3g.40gb              │   2     │   40GB     │  42 SM       │   │
│   │ 4g.40gb              │   1     │   40GB     │  56 SM       │   │
│   │ 7g.80gb              │   1     │   80GB     │  98 SM       │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   物理视图:                                                              │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                        A100 80GB                                 │   │
│   │  ┌─────────┬─────────┬─────────┬─────────┬─────────┬─────────┐ │   │
│   │  │ 1g.10gb │ 1g.10gb │ 1g.10gb │ 1g.10gb │ 1g.10gb │ 1g.10gb │ │   │
│   │  └─────────┴─────────┴─────────┴─────────┴─────────┴─────────┘ │   │
│   │  ┌──────────────────────────────────────────────────────────┐  │   │
│   │  │                      1g.10gb                              │  │   │
│   │  └──────────────────────────────────────────────────────────┘  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   适用场景: 推理服务、开发测试、小模型训练                                │
│   不适用: 大模型训练（需要完整 GPU 互联）                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

```yaml
# MIG 资源请求
apiVersion: v1
kind: Pod
metadata:
  name: inference-pod
spec:
  containers:
  - name: inference
    image: my-inference:latest
    resources:
      limits:
        nvidia.com/mig-1g.10gb: 1  # 请求一个 1g.10gb MIG 实例
```

### GPU 时间分片

多个 Pod 共享同一个 GPU（通过时间分片）。

```yaml
# 配置时间分片
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
        failRequestsGreaterThanOne: false
        resources:
        - name: nvidia.com/gpu
          replicas: 4  # 每个 GPU 可被 4 个 Pod 共享

# 应用配置
kubectl patch daemonset nvidia-device-plugin \
  -n nvidia-device-plugin \
  --type='json' \
  -p='[{"op": "add", "path": "/spec/template/spec/containers/0/args/-", "value": "--config-file=/config/any"}]'
```

---

## 批调度器

### Volcano

专为 AI/大数据批处理设计的 K8s 调度器。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Volcano 核心能力                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. Gang Scheduling (组调度)                                           │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                                                                 │   │
│   │   分布式训练: 需要 4 个 worker 同时启动                          │   │
│   │                                                                 │   │
│   │   默认调度器:                                                    │   │
│   │   Worker 0 ✅ 启动 → Worker 1 ✅ 启动 → Worker 2 ❌ 资源不足    │   │
│   │   → Worker 0, 1 空等 → 超时失败                                 │   │
│   │                                                                 │   │
│   │   Volcano Gang Scheduling:                                      │   │
│   │   检查是否有足够资源容纳所有 4 个 worker                         │   │
│   │   → 有: 同时启动所有 worker                                     │   │
│   │   → 无: 等待，不启动任何 worker (避免死锁)                       │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   2. Fair Share Scheduling (公平共享)                                   │
│   3. Queue Management (队列管理)                                        │
│   4. Preemption (优先级抢占)                                            │
│   5. Resource Reservation (资源预留)                                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Volcano 安装与使用

```bash
# 安装 Volcano
kubectl apply -f https://raw.githubusercontent.com/volcano-sh/volcano/master/installer/volcano-development.yaml

# 验证
kubectl get pods -n volcano-system
```

```yaml
# volcano-job.yaml
apiVersion: batch.volcano.sh/v1alpha1
kind: Job
metadata:
  name: distributed-training
spec:
  minAvailable: 4  # 至少 4 个 pod 才能启动 (Gang Scheduling)
  schedulerName: volcano
  queue: training-queue  # 使用指定队列
  
  policies:
  - event: PodEvicted
    action: RestartJob
  
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

### Volcano 队列管理

```yaml
# 创建队列
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: training-queue
spec:
  weight: 2  # 队列权重，影响资源分配比例
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
    cpu: "50"
    memory: "200Gi"
    nvidia.com/gpu: "16"
```

### Yunikorn

Apache 孵化的批调度器，与 K8s 深度集成。

```yaml
# 安装 Yunikorn
helm repo add yunikorn https://apache.github.io/yunikorn-release
helm install yunikorn yunikorn/yunikorn --namespace yunikorn --create-namespace

# 配置队列
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
          properties:
            application.sort.policy: fifo
        - name: inference
          resources:
            guaranteed:
              nvidia.com/gpu: "8"
            max:
              nvidia.com/gpu: "16"
```

---

## 资源隔离与配额

### ResourceQuota

限制 namespace 级别的资源使用。

```yaml
apiVersion: v1
kind: ResourceQuota
metadata:
  name: gpu-quota
  namespace: team-a
spec:
  hard:
    requests.nvidia.com/gpu: "16"   # 最多请求 16 GPU
    limits.nvidia.com/gpu: "16"     # 最多使用 16 GPU
    requests.cpu: "100"
    requests.memory: "500Gi"
    pods: "50"  # 最多 50 个 Pod
```

### LimitRange

限制单个 Pod/Container 的资源范围。

```yaml
apiVersion: v1
kind: LimitRange
metadata:
  name: gpu-limits
  namespace: team-a
spec:
  limits:
  - type: Container
    default:
      nvidia.com/gpu: "1"
    defaultRequest:
      nvidia.com/gpu: "1"
    max:
      nvidia.com/gpu: "8"  # 单容器最多 8 GPU
    min:
      nvidia.com/gpu: "1"
  - type: Pod
    max:
      nvidia.com/gpu: "8"  # 单 Pod 最多 8 GPU
```

### Priority Class

定义任务优先级，支持抢占。

```yaml
# 高优先级（生产推理）
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: production-inference
value: 1000000
globalDefault: false
preemptionPolicy: PreemptLowerPriority
description: "Production inference workloads"

---
# 中优先级（训练任务）
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: training
value: 100000
globalDefault: false
preemptionPolicy: PreemptLowerPriority
description: "Training workloads"

---
# 低优先级（开发测试）
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: development
value: 1000
globalDefault: true
preemptionPolicy: Never  # 不抢占其他任务
description: "Development and testing"

---
# 使用优先级
apiVersion: batch/v1
kind: Job
metadata:
  name: critical-training
spec:
  template:
    spec:
      priorityClassName: training  # 指定优先级
      containers:
      - name: trainer
        # ...
```

---

## 多租户管理

### 多租户架构模式

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    多租户 GPU 集群架构                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                      平台管理层                                  │   │
│   │   - 用户认证 (OIDC/LDAP)                                        │   │
│   │   - 权限控制 (RBAC)                                             │   │
│   │   - 计量计费                                                    │   │
│   │   - 监控告警                                                    │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                 │                                       │
│           ┌─────────────────────┼─────────────────────┐                │
│           │                     │                     │                │
│           ▼                     ▼                     ▼                │
│   ┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐     │
│   │   Team A        │   │   Team B        │   │   Team C        │     │
│   │   Namespace     │   │   Namespace     │   │   Namespace     │     │
│   │                 │   │                 │   │                 │     │
│   │ ResourceQuota:  │   │ ResourceQuota:  │   │ ResourceQuota:  │     │
│   │  GPU: 32        │   │  GPU: 16        │   │  GPU: 8         │     │
│   │                 │   │                 │   │                 │     │
│   │ Queue: team-a   │   │ Queue: team-b   │   │ Queue: team-c   │     │
│   │ Weight: 4       │   │ Weight: 2       │   │ Weight: 1       │     │
│   └─────────────────┘   └─────────────────┘   └─────────────────┘     │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                    共享 GPU 集群                                 │   │
│   │   Node Pool 1: A100-80GB × 8 (训练)                             │   │
│   │   Node Pool 2: A100-40GB × 8 (训练)                             │   │
│   │   Node Pool 3: L40S × 16 (推理)                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### RBAC 配置

```yaml
# 为团队创建 Role
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  namespace: team-a
  name: ml-developer
rules:
- apiGroups: [""]
  resources: ["pods", "pods/log", "pods/exec", "services", "configmaps", "secrets"]
  verbs: ["get", "list", "watch", "create", "update", "delete"]
- apiGroups: ["batch"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "update", "delete"]
- apiGroups: ["batch.volcano.sh"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "update", "delete"]

---
# 绑定用户到 Role
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: ml-developer-binding
  namespace: team-a
subjects:
- kind: User
  name: alice@company.com
  apiGroup: rbac.authorization.k8s.io
roleRef:
  kind: Role
  name: ml-developer
  apiGroup: rbac.authorization.k8s.io
```

---

## 成本优化策略

### 资源利用率优化

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    GPU 成本优化策略                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. 提高利用率                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 使用时间分片/MIG 支持更多小任务                                 │   │
│   │ - 合理设置 request/limit，避免过度申请                           │   │
│   │ - 开发环境使用抢占式实例                                         │   │
│   │ - 实现自动扩缩容                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   2. 选择合适的 GPU                                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ 场景               │ 推荐 GPU        │ 原因                     │   │
│   │───────────────────│────────────────│─────────────────────────│   │
│   │ 大模型训练         │ H100/A100      │ 性能和带宽最优           │   │
│   │ 中小模型训练       │ A100/A10G      │ 性价比好                 │   │
│   │ 推理(吞吐优先)     │ A100/L40S      │ 高吞吐                   │   │
│   │ 推理(成本优先)     │ L4/T4          │ 成本低                   │   │
│   │ 开发测试           │ T4/MIG         │ 够用即可                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   3. 云上成本优化                                                       │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - Spot/抢占式实例: 节省 60-90%，适合容错任务                     │   │
│   │ - 预留实例: 承诺使用 1-3 年，节省 30-60%                        │   │
│   │ - 混合使用: 基础负载用预留，峰值用按需/Spot                      │   │
│   │ - 自动关机: 开发环境夜间/周末自动关闭                            │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Spot 实例使用

```yaml
# 使用 Spot 节点池的训练任务
apiVersion: batch/v1
kind: Job
metadata:
  name: training-job
spec:
  template:
    spec:
      nodeSelector:
        node-type: spot-gpu  # 调度到 Spot 节点
      
      tolerations:
      - key: "kubernetes.io/spot"
        operator: "Equal"
        value: "true"
        effect: "NoSchedule"
      
      # 配置优雅终止，保存 checkpoint
      terminationGracePeriodSeconds: 300
      
      containers:
      - name: trainer
        image: my-trainer:latest
        lifecycle:
          preStop:
            exec:
              command:
              - /bin/sh
              - -c
              - "python save_checkpoint.py && sleep 60"
```

### 集群自动伸缩

```yaml
# Cluster Autoscaler 配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: cluster-autoscaler-config
  namespace: kube-system
data:
  config: |
    {
      "nodePools": [
        {
          "name": "gpu-training-pool",
          "minSize": 0,
          "maxSize": 32,
          "instanceTypes": ["p4d.24xlarge"],
          "labels": {
            "purpose": "training"
          }
        },
        {
          "name": "gpu-inference-pool",
          "minSize": 2,
          "maxSize": 16,
          "instanceTypes": ["g5.xlarge"],
          "labels": {
            "purpose": "inference"
          }
        }
      ],
      "scaleDown": {
        "enabled": true,
        "delayAfterAdd": "10m",
        "delayAfterDelete": "10s",
        "unneededTime": "10m"
      }
    }
```

---

## 实战练习

### 练习 1：部署 NVIDIA Device Plugin

```bash
# 1. 部署 Device Plugin
kubectl apply -f https://raw.githubusercontent.com/NVIDIA/k8s-device-plugin/v0.14.0/nvidia-device-plugin.yml

# 2. 验证 GPU 被识别
kubectl get nodes -o json | jq '.items[].status.capacity | select(.["nvidia.com/gpu"])'

# 3. 运行测试 Pod
cat <<EOF | kubectl apply -f -
apiVersion: v1
kind: Pod
metadata:
  name: gpu-test
spec:
  containers:
  - name: cuda-test
    image: nvidia/cuda:12.0-base
    command: ["nvidia-smi"]
    resources:
      limits:
        nvidia.com/gpu: 1
  restartPolicy: Never
EOF

# 4. 查看输出
kubectl logs gpu-test
```

### 练习 2：配置 ResourceQuota

```yaml
# quota-demo.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: ml-team-demo

---
apiVersion: v1
kind: ResourceQuota
metadata:
  name: gpu-quota
  namespace: ml-team-demo
spec:
  hard:
    requests.nvidia.com/gpu: "4"
    limits.nvidia.com/gpu: "4"
    pods: "10"

---
# 测试超限
apiVersion: v1
kind: Pod
metadata:
  name: gpu-pod-1
  namespace: ml-team-demo
spec:
  containers:
  - name: cuda
    image: nvidia/cuda:12.0-base
    command: ["sleep", "infinity"]
    resources:
      limits:
        nvidia.com/gpu: 8  # 超过配额，会被拒绝
```

```bash
kubectl apply -f quota-demo.yaml
kubectl describe resourcequota gpu-quota -n ml-team-demo
```

### 练习 3：Volcano Gang Scheduling

```yaml
# volcano-gang-demo.yaml
apiVersion: batch.volcano.sh/v1alpha1
kind: Job
metadata:
  name: gang-demo
spec:
  minAvailable: 2  # 必须 2 个 pod 同时启动
  schedulerName: volcano
  tasks:
  - replicas: 2
    name: worker
    template:
      spec:
        containers:
        - name: test
          image: busybox
          command: ["sh", "-c", "echo 'Worker started' && sleep 60"]
          resources:
            limits:
              nvidia.com/gpu: 1
        restartPolicy: OnFailure
```

```bash
# 安装 Volcano (如果还没安装)
kubectl apply -f https://raw.githubusercontent.com/volcano-sh/volcano/master/installer/volcano-development.yaml

# 运行 Gang Scheduling 示例
kubectl apply -f volcano-gang-demo.yaml

# 观察调度行为
kubectl get pods -w
kubectl get vcjob gang-demo -o yaml
```

---

## 延伸阅读

### 官方文档

- [Kubernetes GPU Support](https://kubernetes.io/docs/tasks/manage-gpus/scheduling-gpus/)
- [NVIDIA Device Plugin](https://github.com/NVIDIA/k8s-device-plugin)
- [Volcano Documentation](https://volcano.sh/en/docs/)
- [Yunikorn Documentation](https://yunikorn.apache.org/docs/)

### 推荐博客

- [NVIDIA Blog: GPU Scheduling in Kubernetes](https://developer.nvidia.com/blog/)
- [Google Cloud: Best practices for running GPU workloads](https://cloud.google.com/architecture/best-practices-for-running-gpu-workloads-on-kubernetes)

### 必读论文

- [Gandiva: Introspective Cluster Scheduling for Deep Learning](https://www.usenix.org/conference/osdi18/presentation/xiao)
- [Tiresias: A GPU Cluster Manager for Distributed Deep Learning](https://www.usenix.org/conference/nsdi19/presentation/gu)

---

*下一篇：[06-learning-roadmap.md](06-learning-roadmap.md) - 完整学习路线图*

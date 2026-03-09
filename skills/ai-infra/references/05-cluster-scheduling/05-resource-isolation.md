# 资源隔离与配额

> 通过配额和优先级实现多租户资源公平分配。

## 目录

- [为什么需要资源隔离？](#为什么需要资源隔离)
- [ResourceQuota](#resourcequota)
- [LimitRange](#limitrange)
- [Priority Class 与抢占](#priority-class-与抢占)
- [Fair-Share 调度原理](#fair-share-调度原理)

---

## 为什么需要资源隔离？

### 生活类比：公司的会议室管理

共享 GPU 集群就像公司共用的会议室：

- **没有规则时**：强势团队占满所有会议室，其他团队永远排不上——"公地悲剧"
- **ResourceQuota**：每个部门最多预定 N 间会议室——总量限制
- **LimitRange**：单次预定不能超过 2 间——防止一人霸占
- **PriorityClass**：CEO 的会议可以"踢掉"普通会议——抢占机制
- **Fair-Share**：按部门人数比例分配——公平共享

### GPU 集群的"公地悲剧"

没有配额管理的 GPU 集群会出现什么？

```
时间线：无配额管控的 64-GPU 集群
────────────────────────────────────────────────────
Week 1: 算法组 A 提交 32-GPU 训练 → 成功
        算法组 B 提交 32-GPU 训练 → 成功
        利用率 100%，皆大欢喜

Week 2: 算法组 A 提交 48-GPU 训练 → 成功（先到先得）
        算法组 B 提交 32-GPU 训练 → Pending（只剩 16 GPU）
        B 组等了 3 天...

Week 3: A 组又提交一个 64-GPU 训练 → 独占整个集群
        B 组和 C 组全部 Pending
        → 投诉、扯皮、领导协调...
────────────────────────────────────────────────────
```

> **核心问题**：GPU 是昂贵资源（一块 H100 约 $3/小时），没有规则的共享必然导致冲突。资源隔离的目标是在**效率**（高利用率）和**公平**（每个团队都能用到）之间找平衡。

---

## ResourceQuota

### 原理

ResourceQuota 是 **Namespace 级别**的资源总量限制。一旦设置，该 Namespace 下所有 Pod 的资源请求之和不能超过配额。

> **类比**：给每个部门一张"额度卡"，花完就不能再申请，直到有任务结束释放额度。

### 配额设计策略

配额如何分配是个管理艺术，常见策略：

| 策略 | 方式 | 优点 | 缺点 |
|------|------|------|------|
| **按比例分配** | 按团队人数/预算比例 | 简单公平 | 可能浪费（小团队用不完） |
| **按需分配** | 根据历史使用量调整 | 精准 | 需要数据分析，调整滞后 |
| **超额分配** | 各团队配额之和 > 集群总量 | 高利用率 | 需要配合优先级和抢占 |
| **弹性配额** | 保证最低 + 允许借用 | 兼顾效率和公平 | 配置复杂 |

**生产推荐**：保证量占集群 60-70%，剩余 30-40% 作为弹性池。配合 Volcano Queue 的 `reclaimable: true` 实现"借用-归还"。

### 配置示例

```yaml
apiVersion: v1
kind: ResourceQuota
metadata:
  name: gpu-quota
  namespace: team-a
spec:
  hard:
    requests.nvidia.com/gpu: "16"    # 最多使用 16 块 GPU
    limits.nvidia.com/gpu: "16"      # GPU 的 request 必须 = limit
    requests.cpu: "100"              # CPU 也要限制（防止 DataLoader 抢 CPU）
    requests.memory: "500Gi"
    pods: "50"                       # 限制 Pod 总数（防止碎片化）
    persistentvolumeclaims: "20"     # 限制存储卷数量
```

> **为什么要同时限制 CPU 和 Pod 数？** 一个常见的滥用模式是：申请 1 块 GPU 但配 64 核 CPU，或者创建大量 1-GPU Pod 碎片化占满集群。限制 CPU 和 Pod 数可以防止这些"变相霸占"。

### 查看配额使用

```bash
kubectl describe resourcequota gpu-quota -n team-a

# 输出示例:
# Name:                    gpu-quota
# Namespace:               team-a
# Resource                 Used   Hard
# --------                 ----   ----
# limits.nvidia.com/gpu    8      16      ← 还可以用 8 块 GPU
# pods                     10     50
# requests.cpu             40     100
# requests.memory          200Gi  500Gi
# requests.nvidia.com/gpu  8      16
```

### 配额用满时会发生什么？

```
用户提交: 需要 8 GPU 的训练任务
配额状态: 已用 12/16 GPU
    │
    ▼
Admission Controller 检查:
  12 + 8 = 20 > 16 (配额上限)
    │
    ▼
结果: Pod 创建被拒绝（不是 Pending，是直接报错）
错误: "exceeded quota: gpu-quota, requested: requests.nvidia.com/gpu=8,
       used: requests.nvidia.com/gpu=12, limited: requests.nvidia.com/gpu=16"
```

> **重要区别**：ResourceQuota 超限是在 **Pod 创建时**拒绝，而不是调度时 Pending。这意味着 Job 的 Pod 根本不会被创建出来。

---

## LimitRange

### 原理

LimitRange 限制的是**单个 Pod/Container** 的资源范围，防止"一个任务吃掉整个团队的配额"。

> **类比**：会议室管理中，除了部门总额度，还规定"单次会议最多用 2 间"。

### 配置示例

```yaml
apiVersion: v1
kind: LimitRange
metadata:
  name: gpu-limits
  namespace: team-a
spec:
  limits:
  - type: Container
    # ⚠️ 不为 nvidia.com/gpu 设置 default/defaultRequest
    # 否则所有 Pod（包括非 GPU Pod）都会被注入 GPU 请求
    # → CPU-only Pod 因为找不到 GPU 节点而 Pending
    max:
      nvidia.com/gpu: "8"       # 单容器最多 8 GPU
      cpu: "32"
      memory: "256Gi"
    min:
      cpu: "1"                  # 至少 1 核（防止 CPU 过低导致 GPU 空等）
      memory: "4Gi"
  
  - type: Pod
    max:
      nvidia.com/gpu: "8"       # 单 Pod 最多 8 GPU（= 单节点上限）
```

### 为什么限制单任务 8 GPU？

```
集群配置: 每节点 8 GPU

单任务 ≤ 8 GPU:
  → 在一个节点内完成，不需要跨节点通信
  → 调度简单，不会"卡住"等两个空闲节点同时出现

单任务 > 8 GPU (如 16 GPU):
  → 需要跨 2 个节点，要求同时有 2 个节点各有 8 GPU 空闲
  → 调度难度指数级上升，容易永久 Pending
  → 且跨节点通信比节点内 NVLink 慢 10-50 倍
```

> **实践建议**：除非使用 Volcano/Kueue 等 Gang Scheduling 调度器，否则不建议允许单任务超过单节点 GPU 数。需要多节点训练时，应使用分布式训练框架（PyTorchJob/MPIJob）。

---

## Priority Class 与抢占

### 原理：为什么需要优先级？

GPU 集群的工作负载有天然的优先级差异：

```
优先级层次图:

  ┌──────────────────────────────────────────────────────┐
  │  Level 4: 生产推理服务 (critical)                     │  影响线上用户
  │  value: 1000000 | 抢占: 可以踢掉所有低优先级           │  不能停
  ├──────────────────────────────────────────────────────┤
  │  Level 3: 重要训练 (high-training)                    │  有 Deadline
  │  value: 500000  | 抢占: 可以踢掉开发和探索任务         │  尽快完成
  ├──────────────────────────────────────────────────────┤
  │  Level 2: 常规训练 (training)                         │  正常排队
  │  value: 100000  | 抢占: 可以踢掉开发任务               │
  ├──────────────────────────────────────────────────────┤
  │  Level 1: 开发测试 (development)                      │  可被抢占
  │  value: 1000    | 抢占: Never (不踢别人)              │  随时可中断
  └──────────────────────────────────────────────────────┘
```

### 创建优先级类

```yaml
# Level 4: 生产推理 —— 绝对不能被抢占
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: production-inference
value: 1000000
preemptionPolicy: PreemptLowerPriority
description: "Production inference services - highest priority"

---
# Level 3: 重要训练 —— Deadline 紧迫的训练
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: high-training
value: 500000
preemptionPolicy: PreemptLowerPriority
description: "High priority training with deadline"

---
# Level 2: 常规训练
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: training
value: 100000
preemptionPolicy: PreemptLowerPriority
description: "Regular training workloads"

---
# Level 1: 开发测试 —— 全局默认，可被所有人抢占
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: development
value: 1000
globalDefault: true                    # 未指定优先级的 Pod 默认使用这个
preemptionPolicy: Never                # 不抢占其他任务
description: "Development and testing - can be preempted"
```

### 抢占场景详解

```
场景: 64-GPU 集群，全部被 development 级别的开发任务占满

  时刻 T0: 集群状态
  ┌─────────────────────────────────────────────────────┐
  │  GPU 0-15:  dev-job-1 (development, 16 GPU)         │
  │  GPU 16-31: dev-job-2 (development, 16 GPU)         │
  │  GPU 32-47: dev-job-3 (development, 16 GPU)         │
  │  GPU 48-63: dev-job-4 (development, 16 GPU)         │
  │  空闲: 0 GPU                                         │
  └─────────────────────────────────────────────────────┘

  时刻 T1: 提交 production-inference (需要 8 GPU)
  ┌─────────────────────────────────────────────────────┐
  │  Scheduler 发现: 无空闲 GPU                          │
  │  抢占决策: production-inference(1000000)              │
  │           > dev-job-4(1000)                          │
  │  → 终止 dev-job-4，释放 16 GPU                       │
  │  → production-inference 获得 8 GPU                   │
  │  → 剩余 8 GPU 可供其他任务使用                        │
  └─────────────────────────────────────────────────────┘
```

> **抢占的代价**：被抢占的 Pod 会收到 SIGTERM 信号，然后被强制终止。如果训练任务没有保存 checkpoint，之前的训练进度全部丢失。这就是为什么**所有训练任务都应该实现定期 checkpoint 保存**。

### 使用优先级

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: critical-training
spec:
  template:
    spec:
      priorityClassName: high-training      # 指定优先级
      containers:
      - name: trainer
        image: pytorch/pytorch:2.0.0
        resources:
          limits:
            nvidia.com/gpu: 8
```

### 优先级设计原则

| 原则 | 说明 | 示例 |
|------|------|------|
| **层级清晰** | 不同类型工作负载对应不同层级 | 推理 > 训练 > 开发 |
| **间隔充足** | value 之间留足空间，方便插入新层级 | 1000, 100000, 500000, 1000000 |
| **最低级不抢占** | development 设 `preemptionPolicy: Never` | 防止开发任务互相踢 |
| **默认最低级** | `globalDefault: true` 设在最低级 | 忘记设优先级也不会造成问题 |
| **配合 Checkpoint** | 可被抢占的任务必须实现 checkpoint | 否则抢占 = 白跑 |

---

## Fair-Share 调度原理

### 超越简单配额：弹性共享

ResourceQuota 的问题是**刚性的**——团队 A 用不完的 GPU 也不能给团队 B 用。Fair-Share 调度解决了这个问题。

```
刚性配额 vs 弹性 Fair-Share:

场景: 集群 64 GPU, Team A 配额 32, Team B 配额 32

═══ 刚性配额 (ResourceQuota) ═══
Team A 提交 16 GPU 任务 → 使用 16，剩余 16 空闲但"锁定"
Team B 提交 48 GPU 任务 → 只能用 32，还需等待
集群利用率: (16 + 32) / 64 = 75% ← 浪费！

═══ 弹性 Fair-Share (Volcano/Kueue) ═══
Team A 提交 16 GPU 任务 → 使用 16
Team B 提交 48 GPU 任务 → 使用 48（借用 A 的空闲 16）
集群利用率: (16 + 48) / 64 = 100% ✓

当 Team A 提交新任务时:
→ Team B 的低优先级任务被"归还"释放 GPU
→ Team A 拿回自己的份额
```

### Volcano Queue 实现 Fair-Share

```yaml
# Team A: 权重 4（占总份额的 4/7 ≈ 57%）
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: team-a-queue
spec:
  weight: 4                     # 相对权重
  capability:
    nvidia.com/gpu: "32"        # 硬上限：无论如何不超过 32
  reclaimable: true             # ← 关键：允许空闲资源被其他队列借用

---
# Team B: 权重 2（占总份额的 2/7 ≈ 29%）
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: team-b-queue
spec:
  weight: 2
  capability:
    nvidia.com/gpu: "24"
  reclaimable: true

---
# Team C: 权重 1（占总份额的 1/7 ≈ 14%）
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: team-c-queue
spec:
  weight: 1
  capability:
    nvidia.com/gpu: "16"
  reclaimable: true
```

### 权重如何工作？

```
64-GPU 集群，所有队列都有任务排队时的分配:

总权重 = 4 + 2 + 1 = 7

Team A 份额: 64 × 4/7 ≈ 36 GPU
Team B 份额: 64 × 2/7 ≈ 18 GPU
Team C 份额: 64 × 1/7 ≈ 9 GPU

注意: 份额不是"保证量"，而是"竞争时的分配比例"
  - 只有 Team A 有任务时 → Team A 可以用满 64 GPU
  - 三个团队都排满队时 → 按 4:2:1 分配
  - Team C 空闲时 → 9 GPU 按比例分给 A 和 B
```

> **Fair-Share 的数学本质**：Max-Min Fairness 算法。先满足需求最小的队列，剩余资源再按权重分。这保证了"小团队至少能拿到自己的份额，大团队在有空闲时可以多用"。

### Kueue（K8s 原生方案）

对于不想引入 Volcano 的团队，**Kueue**（独立的 Kubernetes SIG 项目，需单独安装）提供了 Job 排队和 Fair-Share 方案：

```yaml
# ClusterQueue: 定义资源池
apiVersion: kueue.x-k8s.io/v1beta1
kind: ClusterQueue
metadata:
  name: gpu-cluster-queue
spec:
  resourceGroups:
  - coveredResources: ["nvidia.com/gpu", "cpu", "memory"]
    flavors:
    - name: a100-80gb
      resources:
      - name: "nvidia.com/gpu"
        nominalQuota: 64          # 集群总 GPU
        borrowingLimit: 0         # 顶层不允许借用

---
# LocalQueue: 团队级队列（绑定到 Namespace）
apiVersion: kueue.x-k8s.io/v1beta1
kind: LocalQueue
metadata:
  name: team-a-queue
  namespace: team-a
spec:
  clusterQueue: gpu-cluster-queue
```

---

*下一篇：[06-多租户管理](06-multi-tenancy.md)*

*返回目录：[README](README.md)*

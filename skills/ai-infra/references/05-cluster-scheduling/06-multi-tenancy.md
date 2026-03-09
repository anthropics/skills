# 多租户管理

> 在共享 GPU 集群上实现多团队安全高效协作。

## 目录

- [为什么需要多租户？](#为什么需要多租户)
- [多租户架构模式](#多租户架构模式)
- [RBAC 权限配置](#rbac-权限配置)
- [租户隔离实践](#租户隔离实践)
- [计量计费与成本分摊](#计量计费与成本分摊)

---

## 为什么需要多租户？

### 生活类比：合租公寓

GPU 集群的多租户管理就像管理一栋合租公寓：

| 合租公寓 | GPU 集群 | 要解决的问题 |
|---------|---------|-------------|
| 每户有独立房间 | 每个团队有独立 Namespace | **隔离**：互不干扰 |
| 每户有用电额度 | 每个团队有 GPU 配额 | **公平**：防止霸占 |
| 每户门卡不通用 | 每个团队有独立 RBAC 权限 | **安全**：防止越权 |
| 公共区域共享 | 共享存储/网络/GPU 节点 | **效率**：共享基础设施 |
| 物业统一管理 | 平台团队管控 | **治理**：统一运维 |
| 按使用量分摊水电费 | 按 GPU 时计费 | **成本**：谁用谁付 |

### 共享 vs 独占：成本对比

```
方案 A: 每个团队独立集群
──────────────────────────────────
Team A: 32 GPU 独占集群  → 利用率 30%  → 实际使用 ~10 GPU
Team B: 16 GPU 独占集群  → 利用率 25%  → 实际使用 ~4 GPU
Team C:  8 GPU 独占集群  → 利用率 20%  → 实际使用 ~2 GPU
总计: 56 GPU, 实际使用 16 GPU, 利用率 29%
月成本: 56 × $2/hr × 720hr = $80,640

方案 B: 共享集群 + 多租户
──────────────────────────────────
共享集群: 32 GPU (满足 16 GPU 峰值需求 + 余量)
弹性调度 + 分时复用 → 利用率 70%
月成本: 32 × $2/hr × 720hr = $46,080

节省: $34,560/月 (43%)
```

> **核心价值**：多租户不只是"省钱"，更重要的是通过弹性共享让每个团队都能在需要时获得超出自己"配额"的资源——前提是其他团队暂时用不完。

---

## 多租户架构模式

### 整体架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      多租户 GPU 集群架构                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                      平台管理层                                      │   │
│   │   用户认证 (OIDC/LDAP) │ RBAC 权限 │ 计量计费 │ 监控告警            │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                 │                                           │
│           ┌─────────────────────┼─────────────────────┐                    │
│           ▼                     ▼                     ▼                    │
│   ┌─────────────────┐   ┌─────────────────┐   ┌─────────────────┐         │
│   │   Team A        │   │   Team B        │   │   Team C        │         │
│   │   Namespace     │   │   Namespace     │   │   Namespace     │         │
│   │                 │   │                 │   │                 │         │
│   │ Quota: 32 GPU   │   │ Quota: 16 GPU   │   │ Quota: 8 GPU    │         │
│   │ Queue: team-a   │   │ Queue: team-b   │   │ Queue: team-c   │         │
│   │ Weight: 4       │   │ Weight: 2       │   │ Weight: 1       │         │
│   └─────────────────┘   └─────────────────┘   └─────────────────┘         │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                    共享 GPU 集群                                     │   │
│   │   Node Pool 1: A100-80GB × 8 (训练)                                 │   │
│   │   Node Pool 2: L40S × 16 (推理)                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 三层隔离模型

多租户架构需要在三个层面做隔离：

```
第 1 层: 逻辑隔离 (Namespace)
┌──────────────────────────────────┐
│  Namespace = 租户边界             │
│  • 资源配额 (ResourceQuota)       │
│  • 单任务限制 (LimitRange)        │
│  • 调度队列 (Queue)               │
│  • RBAC 权限 (Role/RoleBinding)   │
└──────────────────────────────────┘
      ↓ 解决: 谁能用多少资源

第 2 层: 网络隔离 (NetworkPolicy)
┌──────────────────────────────────┐
│  • 禁止跨 Namespace 访问          │
│  • 白名单允许特定通信             │
│  • 保护模型和数据不被窥探         │
└──────────────────────────────────┘
      ↓ 解决: 数据安全

第 3 层: 节点隔离 (可选)
┌──────────────────────────────────┐
│  • 专属节点池 (Taint/Toleration)  │
│  • 安全敏感团队独占物理节点       │
│  • 高性能团队独占 NVLink 互联     │
└──────────────────────────────────┘
      ↓ 解决: 强隔离需求
```

> **设计原则**：大多数团队只需要第 1 层（逻辑隔离），开销最低、灵活性最高。只有对安全性或性能有特殊要求时，才逐步叠加第 2、3 层。过度隔离 = 独占集群，失去了共享的价值。

---

## RBAC 权限配置

### 权限设计原则

GPU 集群的 RBAC 需要比普通 K8s 集群更精细：

```
角色层次:

Platform Admin (集群管理员)
├── 管理所有 Namespace
├── 创建/删除 GPU 节点
├── 调整 ResourceQuota
└── 查看所有团队资源使用

Team Admin (团队管理员)
├── 管理本团队 Namespace 内所有资源
├── 创建/删除 Job、Pod
├── 管理团队内 Secret/ConfigMap
└── 查看配额使用情况

ML Developer (算法工程师)
├── 创建/删除/查看 Job 和 Pod
├── 查看日志和 exec 进 Pod
├── 使用已有的 Secret/ConfigMap
└── 不能修改配额和权限

Viewer (只读用户)
├── 查看 Pod 状态和日志
└── 不能创建或修改任何资源
```

### 创建团队 Role

```yaml
# ML Developer: 算法工程师日常所需的最小权限
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  namespace: team-a
  name: ml-developer
rules:
# Pod 操作（训练/推理的核心）
- apiGroups: [""]
  resources: ["pods", "pods/log", "pods/exec"]
  verbs: ["get", "list", "watch", "create", "delete"]

# 服务和配置
- apiGroups: [""]
  resources: ["services", "configmaps", "secrets"]
  verbs: ["get", "list", "watch", "create", "update", "delete"]

# K8s 原生 Job
- apiGroups: ["batch"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "delete"]

# Volcano Job（分布式训练）
- apiGroups: ["batch.volcano.sh"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "delete"]

# PyTorchJob（Kubeflow 训练算子）
- apiGroups: ["kubeflow.org"]
  resources: ["pytorchjobs"]
  verbs: ["get", "list", "watch", "create", "delete"]

# 只读: 查看配额（知道还剩多少资源）
- apiGroups: [""]
  resources: ["resourcequotas"]
  verbs: ["get", "list"]

# PVC: 管理训练数据和模型存储
- apiGroups: [""]
  resources: ["persistentvolumeclaims"]
  verbs: ["get", "list", "watch", "create", "delete"]
```

> **最小权限原则**：算法工程师不需要 `update` Pod（不应修改运行中的训练任务），不能修改 ResourceQuota（这是管理员的事），不能访问其他 Namespace。

### 绑定用户

```yaml
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: team-a-developers
  namespace: team-a
subjects:
# 绑定个人用户
- kind: User
  name: alice@company.com
  apiGroup: rbac.authorization.k8s.io
- kind: User
  name: bob@company.com
  apiGroup: rbac.authorization.k8s.io
# 绑定用户组（推荐：与 LDAP/AD 同步）
- kind: Group
  name: team-a-group
  apiGroup: rbac.authorization.k8s.io
roleRef:
  kind: Role
  name: ml-developer
  apiGroup: rbac.authorization.k8s.io
```

> **生产建议**：优先使用 Group 绑定而非逐个绑定用户。当团队人员变动时，只需修改 LDAP/AD 组成员，无需更新 K8s RBAC。

---

## 租户隔离实践

### 完整租户配置（一键创建）

以下是创建一个新租户所需的完整配置，逐一解释每项的设计理由：

```yaml
# ═══ 1. Namespace: 租户的"领地" ═══
apiVersion: v1
kind: Namespace
metadata:
  name: team-a
  labels:
    team: team-a                      # 用于 NetworkPolicy 的选择器
    cost-center: "CC-12345"           # 用于成本分摊
  annotations:
    team-lead: "alice@company.com"    # 便于运维联系
    budget-gpu-hours: "5000"          # 月度 GPU 时预算

---
# ═══ 2. ResourceQuota: 资源总量限制 ═══
apiVersion: v1
kind: ResourceQuota
metadata:
  name: team-a-quota
  namespace: team-a
spec:
  hard:
    requests.nvidia.com/gpu: "32"     # GPU 上限
    limits.nvidia.com/gpu: "32"
    requests.cpu: "200"               # CPU 上限（约 6 核/GPU）
    requests.memory: "1Ti"            # 内存上限
    pods: "100"                       # Pod 上限
    persistentvolumeclaims: "30"      # 存储卷上限

---
# ═══ 3. LimitRange: 单任务限制 ═══
apiVersion: v1
kind: LimitRange
metadata:
  name: team-a-limits
  namespace: team-a
spec:
  limits:
  - type: Container
    max:
      nvidia.com/gpu: "8"             # 单容器最多 8 GPU
  - type: Pod
    max:
      nvidia.com/gpu: "8"             # 单 Pod 最多 8 GPU

---
# ═══ 4. 调度队列 (Volcano): 弹性 Fair-Share ═══
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: team-a-queue
spec:
  weight: 4                           # 权重 4（竞争时按比例分配）
  capability:
    nvidia.com/gpu: "32"              # 硬上限
  reclaimable: true                   # 空闲资源可被其他队列借用

---
# ═══ 5. NetworkPolicy: 网络隔离 ═══
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: team-a-isolation
  namespace: team-a
spec:
  podSelector: {}                     # 应用到所有 Pod
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          team: team-a                # 只允许同团队 Pod 互访
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          team: team-a                # 同团队内部通信
  - to:                               # 允许访问外部（下载数据/模型）
    - ipBlock:
        cidr: 0.0.0.0/0
  - to:                               # 允许 DNS 解析
    - namespaceSelector:
        matchLabels:
          kubernetes.io/metadata.name: kube-system
    ports:
    - protocol: UDP
      port: 53
```

> **NetworkPolicy 注意事项**：必须显式允许 DNS（kube-system:53），否则 Pod 无法解析域名。这是网络隔离配置中最常遗漏的一项。

### 租户 Checklist

| 配置项 | 作用 | 必要性 | 不配置的后果 |
|--------|------|--------|-------------|
| **Namespace** | 资源隔离边界 | ✅ 必须 | 所有团队混在 default 中 |
| **ResourceQuota** | GPU/CPU 总量限制 | ✅ 必须 | 一个团队耗尽集群资源 |
| **LimitRange** | 单任务资源限制 | ✅ 推荐 | 一个大任务吃掉整个配额 |
| **RBAC** | 权限控制 | ✅ 必须 | 任何人可操作任何团队的资源 |
| **Queue** | 调度队列 + Fair-Share | ✅ 推荐 | 无弹性共享，GPU 空置率高 |
| **NetworkPolicy** | 网络隔离 | ⚠️ 安全敏感时必须 | 模型/数据可被其他团队访问 |
| **Labels/Annotations** | 计费标记 | ⚠️ 需要成本分摊时 | 无法追踪各团队开销 |

---

## 计量计费与成本分摊

### 为什么需要成本分摊？

没有成本意识的团队会把共享集群当"免费自助餐"。成本分摊让每个团队感知到自己的开销，自然会优化资源使用。

### GPU 时计费模型

```
计费公式:

  团队月度费用 = Σ (任务 GPU 数 × 任务运行小时 × GPU 单价)

示例:
  Team A 本月任务:
  ┌──────────────────────────────────────────────────────┐
  │  训练任务 1:  8 GPU × 72 小时  = 576 GPU·时          │
  │  训练任务 2:  4 GPU × 24 小时  = 96 GPU·时           │
  │  推理服务:    2 GPU × 720 小时 = 1440 GPU·时          │
  │  开发调试:    1 GPU × 100 小时 = 100 GPU·时           │
  ├──────────────────────────────────────────────────────┤
  │  总计: 2212 GPU·时 × $2/GPU·时 = $4,424              │
  └──────────────────────────────────────────────────────┘
```

### 采集数据源

```
数据采集架构:

Pod 资源使用 ──────────────┐
(cAdvisor/kubelet metrics)  │
                            ▼
GPU 利用率 ─────────────→ Prometheus ───→ 计费系统
(DCGM Exporter)             │               │
                            ▼               ▼
Namespace/Label ─────────→ Grafana       月度报告
(K8s metadata)              (可视化)     (按团队汇总)
```

关键 Prometheus 指标：

```promql
# 每个 Namespace 的 GPU 使用量（块数 × 时间）
sum by (namespace) (
  count by (namespace, pod) (
    DCGM_FI_DEV_GPU_UTIL{pod!=""}
  )
) * 30   # 30 秒采集间隔 → 换算小时

# 更精确: 按实际 GPU 利用率加权
sum by (namespace) (
  avg_over_time(DCGM_FI_DEV_GPU_UTIL[1h]) / 100
  * on(pod, namespace) group_left
  kube_pod_container_resource_limits{resource="nvidia_com_gpu"}
)
```

### 成本优化激励

好的计费模型不只是"收钱"，还要激励团队优化资源使用：

| 激励措施 | 原理 | 效果 |
|---------|------|------|
| **闲时折扣** | 凌晨/周末使用打 5 折 | 引导非紧急任务错峰运行 |
| **低优先级折扣** | development 级别打 3 折 | 鼓励设置低优先级 |
| **利用率奖励** | GPU 利用率 >80% 的任务打 8 折 | 鼓励优化代码效率 |
| **超额惩罚** | 超出配额的借用资源 1.5 倍价格 | 控制过度借用 |
| **Spot 折扣** | 使用可抢占资源打 2 折 | 鼓励容错设计 |

---

*下一篇：[07-成本优化策略](07-cost-optimization.md)*

*返回目录：[README](README.md)*

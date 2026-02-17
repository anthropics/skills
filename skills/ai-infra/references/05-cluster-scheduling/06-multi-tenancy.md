# 多租户管理

> 在共享 GPU 集群上实现多团队安全高效协作。

## 目录

- [多租户架构模式](#多租户架构模式)
- [RBAC 权限配置](#rbac-权限配置)
- [租户隔离实践](#租户隔离实践)

---

## 多租户架构模式

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

---

## RBAC 权限配置

### 创建团队 Role

```yaml
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  namespace: team-a
  name: ml-developer
rules:
# Pod 操作
- apiGroups: [""]
  resources: ["pods", "pods/log", "pods/exec"]
  verbs: ["get", "list", "watch", "create", "delete"]

# 服务和配置
- apiGroups: [""]
  resources: ["services", "configmaps", "secrets"]
  verbs: ["get", "list", "watch", "create", "update", "delete"]

# Job 操作
- apiGroups: ["batch"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "delete"]

# Volcano Job
- apiGroups: ["batch.volcano.sh"]
  resources: ["jobs"]
  verbs: ["get", "list", "watch", "create", "delete"]

# 只读: 查看配额使用
- apiGroups: [""]
  resources: ["resourcequotas"]
  verbs: ["get", "list"]
```

### 绑定用户

```yaml
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: team-a-developers
  namespace: team-a
subjects:
- kind: User
  name: alice@company.com
  apiGroup: rbac.authorization.k8s.io
- kind: User
  name: bob@company.com
  apiGroup: rbac.authorization.k8s.io
- kind: Group
  name: team-a-group
  apiGroup: rbac.authorization.k8s.io
roleRef:
  kind: Role
  name: ml-developer
  apiGroup: rbac.authorization.k8s.io
```

---

## 租户隔离实践

### 完整租户配置

```yaml
# 1. 创建命名空间
apiVersion: v1
kind: Namespace
metadata:
  name: team-a
  labels:
    team: team-a

---
# 2. 配置资源配额
apiVersion: v1
kind: ResourceQuota
metadata:
  name: team-a-quota
  namespace: team-a
spec:
  hard:
    requests.nvidia.com/gpu: "32"
    limits.nvidia.com/gpu: "32"
    requests.cpu: "200"
    requests.memory: "1Ti"
    pods: "100"

---
# 3. 配置 LimitRange
apiVersion: v1
kind: LimitRange
metadata:
  name: team-a-limits
  namespace: team-a
spec:
  limits:
  - type: Container
    max:
      nvidia.com/gpu: "8"
  - type: Pod
    max:
      nvidia.com/gpu: "8"

---
# 4. 创建调度队列 (Volcano)
apiVersion: scheduling.volcano.sh/v1beta1
kind: Queue
metadata:
  name: team-a-queue
spec:
  weight: 4
  capability:
    nvidia.com/gpu: "32"
  reclaimable: true

---
# 5. 网络隔离 (可选)
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: team-a-isolation
  namespace: team-a
spec:
  podSelector: {}
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - namespaceSelector:
        matchLabels:
          team: team-a
  egress:
  - to:
    - namespaceSelector:
        matchLabels:
          team: team-a
  - to:  # 允许访问外部
    - ipBlock:
        cidr: 0.0.0.0/0
```

### 租户 Checklist

| 配置项 | 作用 | 必要性 |
|--------|------|--------|
| Namespace | 资源隔离边界 | ✅ 必须 |
| ResourceQuota | GPU/CPU 配额 | ✅ 必须 |
| LimitRange | 单任务资源限制 | ✅ 推荐 |
| RBAC | 权限控制 | ✅ 必须 |
| Queue | 调度队列 | ✅ 推荐 |
| NetworkPolicy | 网络隔离 | ⚠️ 可选 |

---

*下一篇：[07-成本优化策略](07-cost-optimization.md)*

*返回目录：[README](README.md)*

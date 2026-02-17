# 资源隔离与配额

> 通过配额和优先级实现多租户资源公平分配。

## 目录

- [ResourceQuota](#resourcequota)
- [LimitRange](#limitrange)
- [Priority Class](#priority-class)

---

## ResourceQuota

限制 namespace 级别的资源使用。

### 配置示例

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

### 查看配额使用

```bash
kubectl describe resourcequota gpu-quota -n team-a

# 输出示例:
# Name:                    gpu-quota
# Namespace:               team-a
# Resource                 Used   Hard
# --------                 ----   ----
# limits.nvidia.com/gpu    8      16
# pods                     10     50
# requests.nvidia.com/gpu  8      16
```

---

## LimitRange

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
    # 注意: 不为 nvidia.com/gpu 设置 default/defaultRequest
    # 否则非 GPU Pod 也会被注入 GPU 请求导致无法调度
    max:
      nvidia.com/gpu: "8"  # 单容器最多 8 GPU
  - type: Pod
    max:
      nvidia.com/gpu: "8"  # 单 Pod 最多 8 GPU
```

---

## Priority Class

定义任务优先级，支持抢占。

### 创建优先级类

```yaml
# 高优先级 - 生产推理
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: production-inference
value: 1000000
preemptionPolicy: PreemptLowerPriority
description: "Production inference - can preempt lower priority"

---
# 中优先级 - 训练任务
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: training
value: 100000
preemptionPolicy: PreemptLowerPriority
description: "Training workloads"

---
# 低优先级 - 开发测试
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: development
value: 1000
globalDefault: true
preemptionPolicy: Never  # 不抢占其他任务
description: "Development and testing"
```

### 使用优先级

```yaml
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
        image: pytorch/pytorch:2.0.0
        resources:
          limits:
            nvidia.com/gpu: 8
```

### 优先级策略建议

| 优先级 | 值 | 场景 | 抢占策略 |
|--------|------|------|----------|
| **critical** | 1000000 | 生产推理 | 抢占所有 |
| **training** | 100000 | 训练任务 | 抢占开发 |
| **development** | 1000 | 开发测试 | 不抢占 |

---

*下一篇：[06-多租户管理](06-multi-tenancy.md)*

*返回目录：[README](README.md)*

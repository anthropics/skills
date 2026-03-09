# 成本优化策略

> GPU 资源昂贵，合理优化可大幅降低成本。

## 目录

- [成本分析框架](#成本分析框架)
- [利用率优化](#利用率优化)
- [Spot 实例使用](#spot-实例使用)
- [集群自动伸缩](#集群自动伸缩)
- [GPU 选型与 Right-Sizing](#gpu-选型与-right-sizing)
- [成本监控体系](#成本监控体系)

---

## 成本分析框架

### 生活类比：开车出行的成本优化

GPU 成本优化就像优化出行开支：

| 出行优化 | GPU 成本优化 | 核心思路 |
|---------|-------------|---------|
| 别空车跑（载客率） | 提高 GPU 利用率 | 让每块 GPU 都在干活 |
| 顺风车拼车 | GPU 共享（MIG/时间分片） | 一卡多用 |
| 错峰出行省过路费 | 低优先级 + Spot 实例 | 不着急的任务用便宜资源 |
| 不开大卡车买菜 | Right-Sizing（合适型号） | 别用 H100 跑小模型 |
| 停车要熄火 | 自动缩容 | 不用时释放 |
| 长期月租 vs 按次付费 | 预留实例 vs 按需 | 稳定负载用长期合约 |

### GPU 成本的"真相"

```
一块 A100 80GB 的成本构成:

  ┌─────────────────────────────────────────────────────────────┐
  │  云上按需价格: ~$2/小时                                      │
  │                                                              │
  │  一个月(720h)不停运行: $1,440                                │
  │  一年: $17,280                                               │
  │                                                              │
  │  但实际利用率是关键:                                          │
  │  ┌─────────────────────────────────────────────────────┐    │
  │  │  利用率 30%:  有效成本 = $2/0.3 = $6.67/有效GPU时   │    │
  │  │  利用率 70%:  有效成本 = $2/0.7 = $2.86/有效GPU时   │    │
  │  │  利用率 90%:  有效成本 = $2/0.9 = $2.22/有效GPU时   │    │
  │  └─────────────────────────────────────────────────────┘    │
  │                                                              │
  │  利用率从 30% 提升到 70%，相当于成本降低 57%!                 │
  └─────────────────────────────────────────────────────────────┘
```

> **核心洞察**：GPU 成本优化的第一优先级永远是**提高利用率**。一块空闲的 GPU 每小时烧的钱和一块满载的一样多。

---

## 利用率优化

### GPU 利用率的三个维度

"利用率"不只是一个数字。要同时看三个维度：

```
维度 1: 分配率 (Allocation Rate)
═══════════════════════════════
  已分配 GPU 数 / 总 GPU 数
  例: 64 GPU 集群，分配出去 48 块 → 75%
  问题: 分配了不代表在用（Pod 可能在 Sleep）

维度 2: GPU 计算利用率 (SM Utilization)
═══════════════════════════════════════
  nvidia-smi 显示的 GPU-Util
  例: 训练时通常 80-95%，推理空闲时 5-10%
  问题: 不反映显存使用情况

维度 3: 显存利用率 (Memory Utilization)
═══════════════════════════════════════
  已用显存 / 总显存
  例: 7B 推理服务常态 30% 显存利用率
  问题: 显存占着但 GPU 计算空闲

真正的"浪费":
┌──────────────────────────────────────────────────────────────┐
│  分配了但未使用: Pod 运行中但 GPU-Util ≈ 0%                   │
│  → 原因: 等数据、等网络、代码 Bug、任务结束但 Pod 未退出      │
│                                                               │
│  显存占满但计算低: 加载了模型但几乎没有请求                     │
│  → 原因: 推理服务空闲期、过度预留                              │
│                                                               │
│  未分配: GPU 空闲无 Pod 使用                                   │
│  → 原因: 配额碎片化、调度约束过严、节点 Taint                  │
└──────────────────────────────────────────────────────────────┘
```

### 提高利用率的具体手段

| 手段 | 适用场景 | 效果 | 实施难度 |
|------|---------|------|---------|
| **GPU 共享（MIG/时间分片）** | 小模型推理、开发测试 | 利用率 ↑↑ | 中 |
| **弹性配额 + Fair-Share** | 多团队共享 | 减少空闲 GPU | 中 |
| **自动缩容** | 推理服务低峰 | 释放闲置节点 | 中 |
| **Bin-Packing 调度** | 碎片化严重时 | 整理碎片 | 低 |
| **任务超时清理** | 僵尸 Pod/Job | 回收被遗忘的 GPU | 低 |
| **利用率监控 + 告警** | 所有场景 | 发现问题 | 低 |

### 僵尸任务清理

训练集群最常见的浪费是"忘记删除的任务"：

```yaml
# 自动清理已完成的 Job（保留 1 小时后删除）
apiVersion: batch/v1
kind: Job
metadata:
  name: auto-cleanup-training
spec:
  ttlSecondsAfterFinished: 3600      # Job 完成 1 小时后自动删除
  template:
    spec:
      containers:
      - name: trainer
        image: my-trainer:latest
        resources:
          limits:
            nvidia.com/gpu: 8
      restartPolicy: Never

---
# 设置活跃截止时间（防止训练死循环/挂起）
apiVersion: batch/v1
kind: Job
metadata:
  name: bounded-training
spec:
  activeDeadlineSeconds: 259200       # 最多运行 3 天（72 小时）
  template:
    spec:
      containers:
      - name: trainer
        image: my-trainer:latest
        resources:
          limits:
            nvidia.com/gpu: 8
      restartPolicy: Never
```

> **生产建议**：为所有训练 Job 设置 `activeDeadlineSeconds` 和 `ttlSecondsAfterFinished`。曾见过因为训练脚本 Bug 导致 Pod 空跑 2 周、浪费上万美元的案例。

---

## Spot 实例使用

### Spot/抢占式实例原理

云厂商的 GPU 实例有闲置时，以 **60-90% 折扣**出售，但随时可能被回收（通常提前 2 分钟通知）。

```
成本对比（A100 单卡/小时, 参考价）:

  按需实例 (On-Demand):   $2.00/hr   ████████████████████  100%
  1年预留 (Reserved):     $1.20/hr   ████████████           60%
  3年预留:                $0.80/hr   ████████               40%
  Spot 实例:             $0.40/hr    ████                   20%

  Spot 节省了 80%! 但代价是随时可能被中断。
```

### 配置 Spot 节点训练任务

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: training-on-spot
spec:
  backoffLimit: 5                    # Spot 中断后允许重试 5 次
  template:
    spec:
      # 调度到 Spot 节点
      nodeSelector:
        node-type: spot-gpu
      
      tolerations:
      - key: "kubernetes.io/spot"
        operator: "Equal"
        value: "true"
        effect: "NoSchedule"
      
      # ── 优雅终止：Spot 回收时的求生时间 ──
      terminationGracePeriodSeconds: 120    # 2 分钟（匹配云厂商通知时间）
      
      containers:
      - name: trainer
        image: my-trainer:latest
        
        # ── 被抢占时的应急处理 ──
        lifecycle:
          preStop:                   # 收到 SIGTERM 后执行
            exec:
              command:
              - /bin/sh
              - -c
              - |
                echo "Spot preemption detected, saving checkpoint..."
                python save_checkpoint.py --emergency
                echo "Checkpoint saved, ready to terminate"
        
        resources:
          limits:
            nvidia.com/gpu: 8
        
        # 训练脚本需要支持:
        # 1. 启动时检查并恢复最新 checkpoint
        # 2. 定期保存 checkpoint（建议每 30 分钟）
        # 3. 收到 SIGTERM 时立即保存
        
        volumeMounts:
        - name: checkpoints
          mountPath: /checkpoints    # checkpoint 存到持久化存储
      
      volumes:
      - name: checkpoints
        persistentVolumeClaim:
          claimName: training-checkpoints-pvc    # 必须是网络存储，非本地盘
      
      restartPolicy: OnFailure
```

### Spot 中断处理流程

```
正常训练中...
      │
      ▼
云平台发送中断通知 (HTTP metadata endpoint)
      │
      ▼
Node Termination Handler 检测到信号
      │
      ├── 1. 标记节点为 Unschedulable
      ├── 2. 给 Pod 发送 SIGTERM
      │       │
      │       ▼
      │   preStop Hook 触发
      │       │
      │       ├── 保存紧急 checkpoint
      │       └── 等待保存完成
      │
      ├── 3. terminationGracePeriod 到期
      │       └── 强制 Kill
      │
      └── 4. Pod 在新的 Spot 节点上重启
              │
              ▼
          加载最近的 checkpoint，继续训练
```

### Spot 适用性决策

| 场景 | 是否适合 Spot | 原因 | 注意事项 |
|------|---------------|------|---------|
| **大模型训练** | ✅ 适合 | 可从 checkpoint 恢复 | checkpoint 频率要高 |
| **超参数搜索** | ✅ 非常适合 | 单次试验失败无所谓 | 结果存到远程存储 |
| **数据预处理** | ✅ 非常适合 | 幂等操作，重跑即可 | 使用断点续传 |
| **生产推理** | ❌ 不推荐 | 需要持续可用 | 用 On-Demand + Reserved |
| **模型评估** | ✅ 适合 | 可重跑 | 保存中间结果 |
| **开发测试** | ✅ 非常适合 | 成本敏感，可容忍中断 | Notebook 需要自动保存 |

### 混合实例策略

```
最优成本策略: 三层混合

┌──────────────────────────────────────────────────────────────┐
│  Layer 1: 预留实例 (Reserved) ── 30% 集群容量                │
│  用途: 生产推理服务 + 长期基础负载                            │
│  特点: 最便宜的"保底"，保证随时可用                          │
├──────────────────────────────────────────────────────────────┤
│  Layer 2: 按需实例 (On-Demand) ── 20% 集群容量               │
│  用途: 重要训练任务 + 突发高优先级需求                        │
│  特点: 随时可用，无中断风险                                   │
├──────────────────────────────────────────────────────────────┤
│  Layer 3: Spot 实例 ── 50% 集群容量                          │
│  用途: 常规训练 + 开发测试 + 超参搜索                         │
│  特点: 成本最低，但需要容错设计                               │
└──────────────────────────────────────────────────────────────┘

成本估算 (64 GPU 规模，A100):
  全部 On-Demand: 64 × $2 × 720h = $92,160/月
  混合策略:
    Reserved(20):  20 × $1.2 × 720h = $17,280
    On-Demand(12): 12 × $2.0 × 720h = $17,280
    Spot(32):      32 × $0.4 × 720h = $9,216
    总计: $43,776/月 (节省 52%)
```

---

## 集群自动伸缩

### 两层伸缩架构

```
Layer 1: Pod 级伸缩 (HPA / KEDA)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  推理请求量 ↑ → Pod 数量 ↑ → 需要更多 GPU
  推理请求量 ↓ → Pod 数量 ↓ → 释放 GPU

Layer 2: 节点级伸缩 (Cluster Autoscaler)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  有 GPU Pod 在 Pending → 自动添加 GPU 节点
  GPU 节点空闲超时 → 自动移除节点

  联动流程:
  请求量 ↑ → HPA 增加 Pod → Pod Pending（无可用GPU）
                                    ↓
                          Cluster Autoscaler 检测到
                                    ↓
                          添加新 GPU 节点（~5-10 分钟）
                                    ↓
                          Pod 调度到新节点 → 开始服务
```

### Cluster Autoscaler 配置

```yaml
# 集群自动伸缩配置
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
          "minSize": 0,                     # 训练池可缩到 0（没任务时不花钱）
          "maxSize": 32,
          "instanceTypes": ["p4d.24xlarge"],
          "labels": {"purpose": "training"},
          "taints": [{"key": "nvidia.com/gpu", "effect": "NoSchedule"}]
        },
        {
          "name": "gpu-inference-pool",
          "minSize": 2,                     # 推理池保持最少 2 节点（冷启动太慢）
          "maxSize": 16,
          "instanceTypes": ["g5.xlarge"],
          "labels": {"purpose": "inference"}
        }
      ],
      "scaleDown": {
        "enabled": true,
        "delayAfterAdd": "10m",             # 新节点至少保留 10 分钟
        "unneededTime": "10m",              # 空闲 10 分钟后开始缩容
        "utilizationThreshold": 0.5         # GPU 利用率 < 50% 视为空闲
      }
    }
```

> **训练池 minSize=0 的考量**：GPU 节点每小时几十美元，训练任务是间歇性的。没任务时缩到 0 可以大幅降本。代价是冷启动需要 5-10 分钟（节点启动 + GPU 驱动加载 + 容器拉取）。对训练任务来说，这几分钟延迟通常可接受。

### 推理服务 HPA

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: inference-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: llm-inference
  minReplicas: 2                           # 最少 2 副本（高可用）
  maxReplicas: 10                          # 最多 10 副本
  
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60       # 扩容等 1 分钟稳定
      policies:
      - type: Pods
        value: 2                           # 每次最多加 2 个 Pod
        periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300      # 缩容等 5 分钟稳定（防震荡）
      policies:
      - type: Pods
        value: 1                           # 每次最多减 1 个 Pod
        periodSeconds: 120
  
  metrics:
  # 指标 1: GPU 利用率（需要 DCGM Exporter + Prometheus Adapter）
  - type: Pods
    pods:
      metric:
        name: DCGM_FI_DEV_GPU_UTIL
      target:
        type: AverageValue
        averageValue: "70"                 # GPU 利用率 > 70% 扩容
  
  # 指标 2: 请求队列长度
  - type: Pods
    pods:
      metric:
        name: pending_requests
      target:
        type: AverageValue
        averageValue: "10"                 # 积压 > 10 请求时扩容
```

> **缩容策略要保守**：LLM 推理服务启动慢（加载模型需要 1-2 分钟），如果缩容太激进，流量回升时来不及扩容，导致延迟飙升。`stabilizationWindowSeconds: 300` 确保"稳定空闲 5 分钟"才缩容。

---

## GPU 选型与 Right-Sizing

### Right-Sizing 原则

> **Right-Sizing**：不是选最贵的，也不是选最便宜的，而是选"刚好够用"的。

### 按场景选择

| 场景 | 推荐 GPU | 显存 | 按需单价 | 性价比 |
|------|----------|------|---------|--------|
| **LLM 训练 (>70B)** | H100 SXM | 80GB | ~$3.5/hr | ⭐⭐ |
| **LLM 训练 (7-70B)** | A100 80GB | 80GB | ~$2.0/hr | ⭐⭐⭐ |
| **LLM 微调 (LoRA/QLoRA)** | A100 40GB / L40S | 40-48GB | ~$1.5/hr | ⭐⭐⭐⭐ |
| **LLM 推理 (7-13B)** | A10G / L40S | 24-48GB | ~$1.0/hr | ⭐⭐⭐⭐ |
| **LLM 推理 (量化)** | L4 / T4 | 16-24GB | ~$0.5/hr | ⭐⭐⭐⭐⭐ |
| **小模型 / 开发** | T4 / L4 / MIG | 16-24GB | ~$0.5/hr | ⭐⭐⭐⭐⭐ |

### 常见的 Right-Sizing 错误

```
错误 1: 用 H100 跑 7B 推理
─────────────────────────────
  H100 80GB 推理 7B: GPU-Util ~20%, 显存用 30%
  → 有效成本: $3.5/0.2 = $17.5/有效GPU时
  正确选择: A10G 24GB → $1.0/hr, GPU-Util ~60%
  → 有效成本: $1.0/0.6 = $1.67/有效GPU时
  省了 10 倍!

错误 2: 用 T4 训练 7B 模型
─────────────────────────────
  T4 16GB 显存放不下 7B FP16 (需要 ~14GB 参数 + 优化器)
  强行 gradient checkpointing + 超小 batch → 训练速度极慢
  T4 训练 100 天 vs A100 训练 3 天
  T4 成本: $0.5 × 2400h = $1,200
  A100 成本: $2.0 × 72h = $144
  "便宜"的 GPU 反而贵了 8 倍!

错误 3: 长期用按需实例跑推理服务
─────────────────────────────────
  24/7 推理服务用 On-Demand: $2.0 × 8760h = $17,520/年
  改用 1 年预留实例: $1.2 × 8760h = $10,512/年
  省 $7,008/年/卡
```

### 成本估算工具

```python
def estimate_gpu_cost(
    model_params_b: float,      # 模型参数量 (B)
    training_tokens_b: float,   # 训练 token 数 (B)
    gpu_type: str = "A100-80GB"
) -> dict:
    """估算 GPU 训练成本"""
    
    # GPU 单价 ($/小时, 按需)
    gpu_prices = {
        "H100": 3.5, "A100-80GB": 2.0,
        "A100-40GB": 1.5, "A10G": 1.0, "L4": 0.5, "T4": 0.5
    }
    
    # GPU 性能 (TFLOPS, FP16/BF16)
    gpu_tflops = {
        "H100": 1000, "A100-80GB": 312, "A100-40GB": 312,
        "A10G": 125, "L4": 120, "T4": 65
    }
    
    # 总 FLOPS = 6 × 参数量 × token 数 (Chinchilla 公式)
    total_flops = 6 * model_params_b * 1e9 * training_tokens_b * 1e9
    
    # 训练时间 (小时), 假设 MFU = 40% (典型实际利用效率)
    mfu = 0.4
    hours = total_flops / (gpu_tflops[gpu_type] * 1e12 * 3600 * mfu)
    
    # 成本
    cost = hours * gpu_prices[gpu_type]
    
    return {
        "gpu_type": gpu_type,
        "gpu_hours": round(hours, 1),
        "estimated_cost": round(cost, 0),
        "equivalent_gpus_30days": round(hours / 720, 1),  # 等价多少 GPU 跑满一个月
    }

# ── 示例 ──
for gpu in ["H100", "A100-80GB", "A10G"]:
    r = estimate_gpu_cost(7, 100, gpu)
    print(f"{gpu}: {r['gpu_hours']} GPU·hrs, ${r['estimated_cost']}, "
          f"≈ {r['equivalent_gpus_30days']} GPUs × 30 days")

# 输出:
# H100:      1167 GPU·hrs,  $4083, ≈ 1.6 GPUs × 30 days
# A100-80GB: 3738 GPU·hrs,  $7476, ≈ 5.2 GPUs × 30 days
# A10G:      9333 GPU·hrs,  $9333, ≈ 13.0 GPUs × 30 days
# → H100 单价最贵，但总成本最低（性能好所以用时短）
```

---

## 成本监控体系

### 监控仪表盘设计

```
GPU 成本监控 Dashboard 四象限:

┌──────────────────────────┬──────────────────────────┐
│  1. 集群总览              │  2. 团队排行              │
│  ─────────────           │  ─────────────           │
│  总 GPU: 64              │  Team A: $4,200 (48%)    │
│  已分配: 48 (75%)        │  Team B: $2,100 (24%)    │
│  实际利用: 56% avg       │  Team C: $1,400 (16%)    │
│  本月成本: $8,750        │  Team D: $1,050 (12%)    │
│  预算: $12,000           │                          │
│  趋势: ↑12% vs 上月     │  [按 GPU 时/成本/利用率]  │
├──────────────────────────┼──────────────────────────┤
│  3. 浪费检测              │  4. 优化建议              │
│  ─────────────           │  ─────────────           │
│  GPU-Util <10% 的 Pod:   │  ⚠️ 3 个 Job 超时 48h    │
│    pod-dev-alice (3天)   │  ⚠️ Team C 利用率仅 15%   │
│    pod-test-bob (1天)    │  💡 推理服务建议用 MIG     │
│  估计浪费: $420/月       │  💡 开发环境建议用 Spot    │
└──────────────────────────┴──────────────────────────┘
```

### 关键监控指标

```promql
# ── Prometheus 查询 ──

# 1. 集群 GPU 分配率
sum(kube_pod_container_resource_requests{resource="nvidia_com_gpu"})
/ sum(kube_node_status_capacity{resource="nvidia_com_gpu"}) * 100

# 2. 各 Namespace 的 GPU 计算利用率
avg by (namespace) (
  DCGM_FI_DEV_GPU_UTIL{pod!=""}
  * on(pod, namespace) group_left
  kube_pod_labels
)

# 3. 低利用率 Pod（GPU-Util < 10% 持续超过 1 小时）
avg_over_time(DCGM_FI_DEV_GPU_UTIL[1h]) < 10
  and on(pod) kube_pod_status_phase{phase="Running"}

# 4. 显存浪费（分配了但用不到 50%）
DCGM_FI_DEV_MEM_COPY_UTIL < 50
  and on(pod) kube_pod_container_resource_limits{resource="nvidia_com_gpu"} > 0

# 5. 本月累计 GPU 时（按 Namespace）
sum by (namespace) (
  avg_over_time(
    kube_pod_container_resource_requests{resource="nvidia_com_gpu"}[30d]
  ) * 24 * 30
)
```

### 告警规则

```yaml
# Prometheus AlertManager 规则
groups:
- name: gpu-cost-alerts
  rules:
  # 告警 1: GPU 空闲超过 2 小时
  - alert: GPUIdleTooLong
    expr: |
      avg_over_time(DCGM_FI_DEV_GPU_UTIL[2h]) < 5
      and on(pod) kube_pod_status_phase{phase="Running"}
    for: 30m
    labels:
      severity: warning
    annotations:
      summary: "Pod {{ $labels.pod }} GPU 空闲超过 2 小时"
      description: "GPU 利用率持续低于 5%，建议检查任务状态或释放 GPU"
  
  # 告警 2: 团队 GPU 预算即将耗尽
  - alert: GPUBudgetNearLimit
    expr: |
      gpu_team_monthly_cost / gpu_team_monthly_budget > 0.8
    for: 1h
    labels:
      severity: warning
    annotations:
      summary: "团队 {{ $labels.team }} GPU 预算已使用 80%"

  # 告警 3: 训练 Job 运行超过预期
  - alert: TrainingJobTooLong
    expr: |
      (time() - kube_job_status_start_time) / 3600 > 72
      and kube_job_status_active > 0
    labels:
      severity: warning
    annotations:
      summary: "训练 Job {{ $labels.job_name }} 已运行超过 72 小时"
```

---

## 成本优化 Checklist

| 类别 | 优化项 | 预期节省 | 优先级 |
|------|--------|---------|--------|
| **利用率** | 定期审查 GPU 利用率，清理僵尸任务 | 10-30% | ⭐⭐⭐⭐⭐ |
| **利用率** | 配置 `activeDeadlineSeconds` 防止任务无限运行 | 5-15% | ⭐⭐⭐⭐⭐ |
| **利用率** | 推理服务使用 MIG/时间分片 | 20-60% | ⭐⭐⭐⭐ |
| **实例** | 训练任务使用 Spot 实例 | 60-80% | ⭐⭐⭐⭐ |
| **实例** | 稳定推理用预留实例 | 30-60% | ⭐⭐⭐⭐ |
| **伸缩** | 训练节点池 minSize=0 自动缩容 | 20-50% | ⭐⭐⭐⭐ |
| **伸缩** | 推理服务配置 HPA | 15-30% | ⭐⭐⭐ |
| **选型** | Right-Sizing GPU 型号 | 30-80% | ⭐⭐⭐⭐ |
| **调度** | 开发环境夜间/周末自动关机 | 60-70% | ⭐⭐⭐ |
| **监控** | 建立成本仪表盘和告警 | 间接（发现问题） | ⭐⭐⭐⭐ |

---

*返回目录：[README](README.md)*

*上一篇：[06-多租户管理](06-multi-tenancy.md)*

*下一章：[06-学习路线图](../06-learning-roadmap/README.md)*

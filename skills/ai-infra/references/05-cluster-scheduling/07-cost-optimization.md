# 成本优化策略

> GPU 资源昂贵，合理优化可大幅降低成本。

## 目录

- [利用率优化](#利用率优化)
- [Spot 实例使用](#spot-实例使用)
- [集群自动伸缩](#集群自动伸缩)
- [GPU 选型建议](#gpu-选型建议)

---

## 利用率优化

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       GPU 成本优化策略                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 提高利用率                                                             │
│   ─────────────                                                             │
│   • 使用时间分片/MIG 支持更多小任务                                         │
│   • 合理设置 request/limit，避免过度申请                                    │
│   • 开发环境使用抢占式实例                                                  │
│   • 实现自动扩缩容                                                          │
│                                                                             │
│   2. 选择合适的 GPU                                                         │
│   ─────────────────                                                         │
│   场景              推荐 GPU       原因                                     │
│   ───────────────  ───────────   ────────────                              │
│   大模型训练        H100/A100     性能和带宽最优                            │
│   中小模型训练      A100/A10G     性价比好                                  │
│   推理(吞吐优先)    A100/L40S     高吞吐                                    │
│   推理(成本优先)    L4/T4         成本低                                    │
│   开发测试          T4/MIG        够用即可                                  │
│                                                                             │
│   3. 云上成本优化                                                           │
│   ─────────────────                                                         │
│   • Spot/抢占式实例: 节省 60-90%，适合容错任务                             │
│   • 预留实例: 承诺 1-3 年，节省 30-60%                                     │
│   • 混合策略: 基础负载用预留，峰值用 Spot                                  │
│   • 自动关机: 开发环境夜间/周末关闭                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Spot 实例使用

### 配置 Spot 节点训练任务

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: training-on-spot
spec:
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
      
      # 配置优雅终止，保存 checkpoint
      terminationGracePeriodSeconds: 300
      
      containers:
      - name: trainer
        image: my-trainer:latest
        
        # 被抢占时保存进度
        lifecycle:
          preStop:
            exec:
              command:
              - /bin/sh
              - -c
              - "python save_checkpoint.py && sleep 60"
        
        resources:
          limits:
            nvidia.com/gpu: 8
      
      restartPolicy: OnFailure
```

### Spot 使用建议

| 场景 | 是否适合 Spot | 原因 |
|------|---------------|------|
| 大模型训练 | ✅ 适合 | 可从 checkpoint 恢复 |
| 超参数搜索 | ✅ 非常适合 | 可容忍部分失败 |
| 生产推理 | ❌ 不推荐 | 需要稳定性 |
| 开发测试 | ✅ 非常适合 | 成本敏感 |

---

## 集群自动伸缩

### Cluster Autoscaler 配置

```yaml
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
          "labels": {"purpose": "training"}
        },
        {
          "name": "gpu-inference-pool",
          "minSize": 2,
          "maxSize": 16,
          "instanceTypes": ["g5.xlarge"],
          "labels": {"purpose": "inference"}
        }
      ],
      "scaleDown": {
        "enabled": true,
        "delayAfterAdd": "10m",
        "unneededTime": "10m"
      }
    }
```

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
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Pods
    pods:
      metric:
        name: requests_per_second
      target:
        type: AverageValue
        averageValue: "100"
```

---

## GPU 选型建议

### 按场景选择

| 场景 | 推荐 GPU | 显存 | 性价比 |
|------|----------|------|--------|
| **LLM 训练 (>70B)** | H100 SXM | 80GB | ⭐⭐ |
| **LLM 训练 (7-70B)** | A100 80GB | 80GB | ⭐⭐⭐ |
| **LLM 微调** | A100 40GB | 40GB | ⭐⭐⭐⭐ |
| **LLM 推理** | A10G/L40S | 24-48GB | ⭐⭐⭐⭐ |
| **小模型/开发** | T4/L4 | 16-24GB | ⭐⭐⭐⭐⭐ |

### 成本估算公式

```python
def estimate_gpu_cost(
    model_params_b: float,  # 模型参数量 (B)
    training_tokens_b: float,  # 训练 token 数 (B)
    gpu_type: str = "A100-80GB"
) -> dict:
    """估算 GPU 训练成本"""
    
    # GPU 单价 ($/小时)
    gpu_prices = {
        "H100": 3.5,
        "A100-80GB": 2.0,
        "A100-40GB": 1.5,
        "A10G": 1.0,
    }
    
    # FLOPS (每 token)
    flops_per_token = 6 * model_params_b * 1e9
    
    # 总 FLOPS
    total_flops = flops_per_token * training_tokens_b * 1e9
    
    # GPU 性能 (TFLOPS FP16)
    gpu_tflops = {"H100": 1000, "A100-80GB": 312, "A100-40GB": 312, "A10G": 125}
    
    # 训练时间 (小时), 假设 40% 利用率
    hours = total_flops / (gpu_tflops[gpu_type] * 1e12 * 3600 * 0.4)
    
    # 成本
    cost = hours * gpu_prices[gpu_type]
    
    return {
        "gpu_hours": hours,
        "estimated_cost": cost,
        "gpu_type": gpu_type
    }

# 示例: 7B 模型训练 100B tokens
result = estimate_gpu_cost(7, 100, "A100-80GB")
print(f"Estimated: {result['gpu_hours']:.0f} GPU hours, ${result['estimated_cost']:.0f}")
```

---

## 成本优化 Checklist

- [ ] 开发环境使用 Spot/抢占式实例
- [ ] 训练任务实现 checkpoint 自动保存/恢复
- [ ] 配置集群自动伸缩，闲时缩容
- [ ] 推理服务配置 HPA
- [ ] 开发环境配置自动关机
- [ ] 定期审查 GPU 利用率
- [ ] 使用合适大小的 GPU 类型

---

*返回目录：[README](README.md)*

*上一篇：[06-多租户管理](06-multi-tenancy.md)*

*下一章：[06-学习路线图](../06-learning-roadmap/README.md)*

# 部署架构模式

> 从单实例到大规模部署的架构设计。

## 架构模式

### 1. 单实例

```
┌─────────────────────────────────────┐
│           单实例部署                 │
├─────────────────────────────────────┤
│                                     │
│   Client → [LLM Server] → Response  │
│                                     │
│   适用: 开发测试、低流量             │
│                                     │
└─────────────────────────────────────┘
```

### 2. 多副本负载均衡

```
┌─────────────────────────────────────────────────────────┐
│                  负载均衡架构                            │
├─────────────────────────────────────────────────────────┤
│                                                         │
│                   ┌──────────────┐                      │
│   Client ───────→ │ Load Balancer │                     │
│                   └───────┬──────┘                      │
│                           │                             │
│           ┌───────────────┼───────────────┐             │
│           ▼               ▼               ▼             │
│     ┌─────────┐     ┌─────────┐     ┌─────────┐        │
│     │ Server 1│     │ Server 2│     │ Server 3│        │
│     │  (GPU)  │     │  (GPU)  │     │  (GPU)  │        │
│     └─────────┘     └─────────┘     └─────────┘        │
│                                                         │
│   策略: Round-robin / Least-connections                 │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 3. Prefill-Decode 分离

```
┌─────────────────────────────────────────────────────────┐
│               Prefill-Decode 分离架构                    │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   Prefill (计算密集):                                    │
│   处理 prompt，生成初始 KV Cache                         │
│   ┌─────────────────────────────┐                       │
│   │   Prefill Workers (高算力)   │                       │
│   └─────────────┬───────────────┘                       │
│                 │ KV Cache 传输                          │
│                 ▼                                        │
│   ┌─────────────────────────────┐                       │
│   │   Decode Workers (高带宽)    │                       │
│   └─────────────────────────────┘                       │
│   Decode (带宽密集):                                     │
│   逐 token 生成                                          │
│                                                         │
│   优势: 专用优化，资源利用率高                            │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

## Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: llm-server
spec:
  replicas: 3
  selector:
    matchLabels:
      app: llm-server
  template:
    metadata:
      labels:
        app: llm-server
    spec:
      containers:
      - name: vllm
        image: vllm/vllm-openai:latest
        resources:
          limits:
            nvidia.com/gpu: 1
        ports:
        - containerPort: 8000
---
apiVersion: v1
kind: Service
metadata:
  name: llm-service
spec:
  type: LoadBalancer
  selector:
    app: llm-server
  ports:
  - port: 8000
```

## 弹性伸缩

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: llm-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: llm-server
  minReplicas: 1
  maxReplicas: 10
  metrics:
  - type: Pods
    pods:
      metric:
        name: gpu_utilization  # 需要通过 DCGM Exporter + Prometheus Adapter 提供
      target:
        type: AverageValue
        averageValue: "80"
```

---

*下一篇：[10-performance-tuning.md](10-performance-tuning.md) - 性能调优*

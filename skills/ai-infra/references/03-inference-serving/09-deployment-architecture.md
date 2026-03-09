# 部署架构模式

> 从单实例到大规模部署 — 理解每种架构的适用场景和设计原理。

## 架构演进

```
  类比: 餐厅从路边摊发展到连锁餐饮

  阶段 1: 单实例   = 路边摊 (一个人干所有事)
  阶段 2: 多副本   = 开了 3 家分店 (每家一样，看谁不忙去谁那)
  阶段 3: PD 分离  = 前厨 + 后厨分工 (备菜和炒菜分开)
  阶段 4: 弹性伸缩 = 加盟模式 (旺季多开店，淡季关几家)
```

## 1. 单实例部署

```
  ┌─────────────────────────────────────────────────────┐
  │  Client → [LLM Server (1 GPU)] → Response           │
  │                                                     │
  │  适用: 开发测试、个人项目、低流量 (<10 QPS)          │
  │  优点: 最简单，一台机器搞定                          │
  │  缺点: 无冗余，挂了就全挂; 性能有上限               │
  └─────────────────────────────────────────────────────┘
```

## 2. 多副本负载均衡

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                                                                  │
  │                   ┌──────────────┐                               │
  │   Client ───────→ │ Load Balancer │                              │
  │                   └───────┬──────┘                               │
  │                           │                                      │
  │           ┌───────────────┼───────────────┐                      │
  │           ▼               ▼               ▼                      │
  │     ┌─────────┐     ┌─────────┐     ┌─────────┐                 │
  │     │ Server 1│     │ Server 2│     │ Server 3│                 │
  │     │ (1 GPU) │     │ (1 GPU) │     │ (1 GPU) │                 │
  │     └─────────┘     └─────────┘     └─────────┘                 │
  │                                                                  │
  │  负载均衡策略选择:                                                │
  │                                                                  │
  │  Round-Robin (轮询):                                             │
  │    请求 1→S1, 请求 2→S2, 请求 3→S3, 请求 4→S1...               │
  │    简单但不智能: S1 在处理长请求时，短请求还是会发给它            │
  │                                                                  │
  │  Least-Connections (最少连接):                                   │
  │    谁手上请求少就给谁                                            │
  │    更智能，但没考虑请求复杂度                                     │
  │                                                                  │
  │  Least-Load (最小负载, 推荐):                                    │
  │    看 GPU 利用率 / 请求队列长度                                   │
  │    最适合 LLM 场景 (不同请求生成长度差异大)                      │
  │                                                                  │
  │  适用: 中等流量 (10-100 QPS)                                     │
  │  优点: 水平扩展，有冗余                                          │
  │  缺点: 每个副本都加载完整模型，显存利用率不高                    │
  └──────────────────────────────────────────────────────────────────┘
```

## 3. Prefill-Decode 分离架构

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  核心洞察: Prefill 和 Decode 的计算特征完全不同!                  │
  │                                                                  │
  │  Prefill (处理 prompt):                                          │
  │    • Compute-bound (大量并行矩阵乘)                              │
  │    • 需要大算力，一次性完成                                      │
  │    • 时间: 几十到几百 ms                                         │
  │    → 适合: 高算力 GPU (如 H100)                                  │
  │                                                                  │
  │  Decode (逐 token 生成):                                         │
  │    • Memory-bound (每步只读权重，算很少)                         │
  │    • 需要高显存带宽，持续输出                                    │
  │    • 时间: 每 token 几到几十 ms                                  │
  │    → 适合: 高带宽 GPU 或更多实例                                 │
  │                                                                  │
  │  混在一起的问题:                                                 │
  │    Prefill 的长 prompt 占用大量算力                               │
  │    → 正在 Decode 的请求被卡住 (TTFT 抖动)                        │
  │    → 用户体验: 有时候秒回，有时候等很久                          │
  │                                                                  │
  ├──────────────────────────────────────────────────────────────────┤
  │                                                                  │
  │  Prefill-Decode 分离:                                             │
  │                                                                  │
  │  Client                                                          │
  │    │                                                             │
  │    ▼                                                             │
  │  ┌──────────┐     ┌──────────────────────────┐                  │
  │  │ Router   │────→│ Prefill Workers (高算力)  │                  │
  │  └──────────┘     │ 处理 prompt, 生成 KV Cache│                  │
  │                   └────────────┬─────────────┘                  │
  │                                │ 传输 KV Cache                   │
  │                                ▼                                 │
  │                   ┌──────────────────────────┐                  │
  │                   │ Decode Workers (高带宽)   │                  │
  │                   │ 用 KV Cache 逐 token 生成 │                  │
  │                   └──────────────────────────┘                  │
  │                                                                  │
  │  优势:                                                           │
  │  • Prefill 不会阻塞 Decode → TTFT 更稳定                        │
  │  • 两种 Worker 可以独立扩缩容                                    │
  │  • 硬件可以针对性选择                                            │
  │                                                                  │
  │  挑战:                                                           │
  │  • KV Cache 传输开销 (几十 MB 到几 GB)                           │
  │  • 需要高速网络 (NVLink / InfiniBand)                             │
  │  • 调度更复杂                                                    │
  │                                                                  │
  │  代表: Splitwise (微软)、DistServe (PKU)、Mooncake (月之暗面)     │
  └──────────────────────────────────────────────────────────────────┘
```

## 4. Kubernetes 部署

```yaml
# 基础部署: 3 副本 vLLM
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
        args: ["--model", "meta-llama/Llama-2-7b-hf", "--port", "8000"]
        resources:
          limits:
            nvidia.com/gpu: 1   # 每个 Pod 1 张 GPU
        ports:
        - containerPort: 8000
        # 健康检查: 确保模型已加载完毕
        readinessProbe:
          httpGet:
            path: /health
            port: 8000
          initialDelaySeconds: 120  # 模型加载需要时间!
          periodSeconds: 10
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

## 5. 弹性伸缩

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  LLM 弹性伸缩的特殊性:                                          │
  │                                                                  │
  │  传统 Web 服务: 新 Pod 秒级启动                                  │
  │  LLM 服务: 新 Pod 需要几分钟 (加载模型到 GPU 显存)              │
  │  → 不能等到流量暴涨才扩容! 需要预测性扩缩容                     │
  │                                                                  │
  │  扩容指标选择:                                                   │
  │  • GPU 利用率 > 80% → 扩容 (最常用)                             │
  │  • 请求队列长度 > 阈值 → 扩容                                   │
  │  • TTFT P99 > SLA → 扩容 (面向用户体验)                         │
  │                                                                  │
  │  缩容注意:                                                       │
  │  • 必须等 Pod 上所有请求处理完再关闭 (graceful shutdown)         │
  │  • 缩容冷却时间要长 (避免频繁扩缩)                              │
  └──────────────────────────────────────────────────────────────────┘
```

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
        name: gpu_utilization  # 通过 DCGM Exporter + Prometheus Adapter
      target:
        type: AverageValue
        averageValue: "80"
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60   # 1 分钟稳定期
    scaleDown:
      stabilizationWindowSeconds: 300  # 5 分钟冷却 (避免频繁缩容)
```

---

*下一篇：[10-performance-tuning.md](10-performance-tuning.md) - 性能调优*

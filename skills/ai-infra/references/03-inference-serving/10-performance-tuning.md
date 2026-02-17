# 性能调优

> 关键指标、调优 Checklist 和监控。

## 关键指标

### LLM 推理指标

| 指标 | 全称 | 含义 | 目标 |
|------|------|------|------|
| **TTFT** | Time To First Token | 首 token 延迟 | < 500ms |
| **TPS** | Tokens Per Second | 生成速度 | > 30 |
| **Throughput** | 吞吐量 | 并发处理能力 | 最大化 |
| **Latency P99** | 99 分位延迟 | 长尾延迟 | 可控 |

### 计算公式

```python
def calculate_metrics(results):
    """计算推理性能指标"""
    ttft_list = [r['time_to_first_token'] for r in results]
    total_tokens = sum(r['output_tokens'] for r in results)
    total_time = sum(r['total_time'] for r in results)
    
    metrics = {
        'ttft_avg': sum(ttft_list) / len(ttft_list),
        'ttft_p99': np.percentile(ttft_list, 99),
        'tps': total_tokens / total_time,
        'throughput': len(results) / total_time,
    }
    return metrics
```

## 调优 Checklist

### 1. 模型优化

- [ ] 使用量化 (INT8/INT4)
- [ ] 使用 FlashAttention
- [ ] 选择合适的模型大小

### 2. 服务配置

- [ ] 启用 Continuous Batching
- [ ] 配置 PagedAttention
- [ ] 调整最大并发数
- [ ] 设置合适的超时时间

### 3. 系统优化

- [ ] GPU 驱动更新
- [ ] CUDA/cuDNN 版本匹配
- [ ] 禁用 ECC (可选)
- [ ] 调整 GPU 频率

### 4. 部署优化

- [ ] 负载均衡策略
- [ ] 预热模型
- [ ] 健康检查配置

## 监控与可观测性

### Prometheus 指标

```python
from prometheus_client import Histogram, Counter, Gauge

# 延迟分布
latency_histogram = Histogram(
    'llm_inference_latency_seconds',
    'Inference latency',
    buckets=[0.1, 0.5, 1.0, 2.0, 5.0, 10.0]
)

# 吞吐量
requests_counter = Counter(
    'llm_requests_total',
    'Total requests'
)

# GPU 利用率
gpu_utilization = Gauge(
    'gpu_utilization_percent',
    'GPU utilization'
)
```

### Grafana Dashboard

关键面板：
- TTFT 分布直方图
- TPS 时间序列
- GPU 利用率
- 请求队列长度
- 错误率

## 性能对比

```python
def benchmark_inference(model, prompts, num_runs=100):
    """基准测试"""
    results = []
    
    for _ in range(num_runs):
        start = time.time()
        output = model.generate(prompts)
        end = time.time()
        
        results.append({
            'latency': end - start,
            'tokens': len(output.tokens),
        })
    
    print(f"平均延迟: {np.mean([r['latency'] for r in results]):.3f}s")
    print(f"P99 延迟: {np.percentile([r['latency'] for r in results], 99):.3f}s")
    print(f"吞吐量: {sum(r['tokens'] for r in results) / sum(r['latency'] for r in results):.1f} tokens/s")
```

---

*返回：[README.md](README.md) - 章节索引*

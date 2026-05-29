# 性能调优

> 关键指标、调优方法论和实战 Checklist。

## 关键指标 — 先搞清楚"快"是什么

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  LLM 推理的四大核心指标:                                         │
  │                                                                  │
  │  TTFT (Time To First Token) — 首 token 延迟                      │
  │    = 用户发送请求到看到第一个字的时间                             │
  │    类比: 下单到上第一道菜的等待时间                               │
  │    目标: < 500ms (用户能感知的等待极限)                           │
  │    影响因素: Prefill 速度、请求排队时间                           │
  │                                                                  │
  │  TPOT (Time Per Output Token) — 每 token 生成时间                │
  │    = 生成一个 token 需要的时间                                    │
  │    类比: 每道菜的出餐间隔                                        │
  │    目标: < 30ms (对应 >33 token/s，接近人阅读速度)               │
  │    影响因素: Decode 速度、batch 大小                              │
  │                                                                  │
  │  Throughput — 吞吐量 (token/s 或 request/s)                       │
  │    = 系统每秒总共生成多少 token                                   │
  │    类比: 餐厅每小时翻桌次数                                      │
  │    → TPOT 是单个请求的，Throughput 是整个系统的                   │
  │    → 提高 batch size 会提高 Throughput 但可能增加 TPOT            │
  │                                                                  │
  │  Latency P99 — 99 分位延迟                                       │
  │    = 99% 的请求在这个时间内完成                                   │
  │    类比: "最慢的那 1% 的顾客要等多久"                            │
  │    → 比平均延迟更重要! 用户记住的是最差体验                      │
  │                                                                  │
  │  ── 指标之间的取舍 ──                                            │
  │                                                                  │
  │  TTFT ←──── 矛盾 ────→ Throughput                                │
  │  (想要低延迟)         (想要高吞吐)                                │
  │                                                                  │
  │  小 batch → TTFT 低，但 Throughput 也低 (GPU 浪费)               │
  │  大 batch → Throughput 高，但 TTFT 高 (排队等待)                 │
  │  → 找平衡点是调优的核心!                                         │
  └──────────────────────────────────────────────────────────────────┘
```

## 调优方法论 — 按层次排查

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  性能调优金字塔 (从底到顶):                                      │
  │                                                                  │
  │          ┌─────────┐                                             │
  │          │ 部署架构 │  ← 弹性伸缩、Prefill-Decode 分离          │
  │        ┌─┴─────────┴─┐                                          │
  │        │  服务配置    │  ← Batch 策略、并发限制、超时             │
  │      ┌─┴─────────────┴─┐                                        │
  │      │   模型优化       │  ← 量化、FlashAttention、GQA           │
  │    ┌─┴─────────────────┴─┐                                      │
  │    │    系统优化           │  ← 驱动、CUDA 版本、GPU 频率        │
  │    └─────────────────────┘                                       │
  │                                                                  │
  │  原则: 先调底层再调上层 (地基不稳上面白搭)                       │
  └──────────────────────────────────────────────────────────────────┘
```

## 调优 Checklist

### 层 1: 系统优化

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  [ ] GPU 驱动更新到最新稳定版                                    │
  │      nvidia-smi 查看当前版本                                     │
  │                                                                  │
  │  [ ] CUDA / cuDNN 版本匹配                                      │
  │      PyTorch 2.x 推荐 CUDA 12.x                                │
  │      版本不匹配 → FlashAttention 可能无法启用                   │
  │                                                                  │
  │  [ ] GPU 持久模式 (减少首次调用延迟)                             │
  │      nvidia-smi -pm 1                                           │
  │                                                                  │
  │  [ ] 禁用 ECC (可选, 增加 ~6% 可用显存)                         │
  │      nvidia-smi --ecc-config=0  (重启后生效)                    │
  │      注意: 牺牲纠错能力，生产环境慎用                            │
  │                                                                  │
  │  [ ] 锁定 GPU 频率 (避免动态降频影响延迟)                       │
  │      nvidia-smi -lgc MIN,MAX                                    │
  └──────────────────────────────────────────────────────────────────┘
```

### 层 2: 模型优化

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  [ ] 量化: 根据精度要求选择                                      │
  │      精度优先 → FP16 / INT8                                     │
  │      速度优先 → INT4 (AWQ/GPTQ)                                 │
  │      效果: 显存减半+速度翻倍 (INT4)                              │
  │                                                                  │
  │  [ ] FlashAttention: 确认已启用                                  │
  │      PyTorch 2.0+ 默认启用                                      │
  │      手动检查: torch.backends.cuda.flash_sdp_enabled()          │
  │      效果: Attention 速度 2-4x                                   │
  │                                                                  │
  │  [ ] 模型选择: 不要盲目追大                                      │
  │      任务简单 → 用 1-3B 模型 (量化后消费级显卡能跑)              │
  │      任务复杂 → 用 7-13B 模型                                    │
  │      真正需要 → 才用 70B+ 模型                                   │
  └──────────────────────────────────────────────────────────────────┘
```

### 层 3: 服务配置

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  [ ] Continuous Batching: 必须启用 (vLLM/SGLang 默认启用)        │
  │      效果: 吞吐量提升 2-5x                                      │
  │                                                                  │
  │  [ ] max_num_seqs: 最大并发请求数                                │
  │      太小 → GPU 利用率低                                         │
  │      太大 → KV Cache 显存不够 → OOM                              │
  │      经验: 从 32 开始，逐步增大到显存用尽的 90%                  │
  │                                                                  │
  │  [ ] gpu_memory_utilization: KV Cache 显存占比                   │
  │      vLLM 默认 0.9 (90% 显存给 KV Cache)                       │
  │      如果 OOM → 降到 0.85                                       │
  │                                                                  │
  │  [ ] max_model_len: 最大序列长度                                 │
  │      设得越短 → 单个请求 KV Cache 越小 → 能服务更多并发          │
  │      按实际需求设置，不要无脑设最大值                             │
  │                                                                  │
  │  [ ] 请求超时: 避免慢请求拖累整体                                │
  │      设置合理的 max_tokens 限制                                  │
  └──────────────────────────────────────────────────────────────────┘
```

### 层 4: 部署架构

```
  ┌──────────────────────────────────────────────────────────────────┐
  │  [ ] 模型预热: 启动后先发几个请求"热身"                          │
  │      首次推理需要编译 CUDA kernel → 比后续慢很多                 │
  │      → readinessProbe 要设够长的 initialDelaySeconds             │
  │                                                                  │
  │  [ ] 负载均衡: 按 GPU 负载分配 (非 Round-Robin)                  │
  │      LLM 请求长度差异大 → 轮询可能导致某台过载                   │
  │                                                                  │
  │  [ ] 弹性伸缩: 基于 GPU 利用率                                   │
  │      扩容阈值: 80%                                               │
  │      缩容冷却: 至少 5 分钟 (模型加载很慢)                        │
  │                                                                  │
  │  [ ] 健康检查: 不仅检查端口，还要检查推理能力                    │
  │      发送一个简单的推理请求，验证模型正常工作                     │
  └──────────────────────────────────────────────────────────────────┘
```

## 监控与可观测性

```python
from prometheus_client import Histogram, Counter, Gauge

# 核心指标暴露给 Prometheus
ttft_histogram = Histogram(
    'llm_ttft_seconds', 'Time to first token',
    buckets=[0.1, 0.2, 0.5, 1.0, 2.0, 5.0]  # 关注亚秒级
)

tpot_histogram = Histogram(
    'llm_tpot_seconds', 'Time per output token',
    buckets=[0.01, 0.02, 0.03, 0.05, 0.1]
)

throughput_gauge = Gauge(
    'llm_throughput_tokens_per_second', 'System throughput'
)

queue_length = Gauge(
    'llm_request_queue_length', 'Pending requests'
)

# Grafana 关键面板:
# 1. TTFT 分布直方图 (关注 P50/P99)
# 2. Throughput 时间序列 (token/s)
# 3. GPU 利用率 + 显存使用率
# 4. 请求队列长度 (排队过长 = 需要扩容)
# 5. 错误率 (OOM/超时)
```

## 性能基准测试

```python
import time
import numpy as np

def benchmark_llm(model, prompts, num_runs=100):
    """全面的 LLM 推理性能基准测试"""
    results = []

    for prompt in prompts[:num_runs]:
        # 记录各阶段时间
        start = time.perf_counter()
        output = model.generate(prompt, max_tokens=100, stream=True)

        first_token_time = None
        token_times = []

        for token in output:
            now = time.perf_counter()
            if first_token_time is None:
                first_token_time = now - start  # TTFT
            else:
                token_times.append(now - prev_time)  # 每个 token 的生成时间
            prev_time = now

        results.append({
            'ttft': first_token_time,
            'tpot': np.mean(token_times) if token_times else 0,
            'total_tokens': len(token_times) + 1,
            'total_time': time.perf_counter() - start,
        })

    # 汇总
    print(f"TTFT  P50: {np.percentile([r['ttft'] for r in results], 50)*1000:.0f}ms")
    print(f"TTFT  P99: {np.percentile([r['ttft'] for r in results], 99)*1000:.0f}ms")
    print(f"TPOT  avg: {np.mean([r['tpot'] for r in results])*1000:.1f}ms")
    print(f"Throughput: {sum(r['total_tokens'] for r in results) / sum(r['total_time'] for r in results):.0f} tok/s")
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **NVIDIA.** *Deep Learning Performance Guide.* — GPU 推理性能调优  
   https://docs.nvidia.com/deeplearning/performance/

2. **vLLM Documentation.** *Performance Tuning.*  
   https://docs.vllm.ai/en/latest/

3. **Aminabadi, R. Y., et al. (2022).** *DeepSpeed-Inference: Enabling Efficient Inference of Transformer Models at Unprecedented Scale.*  
   https://arxiv.org/abs/2207.00032

4. **NVIDIA.** *Nsight Systems Profiler.* — GPU 性能分析工具  
   https://developer.nvidia.com/nsight-systems

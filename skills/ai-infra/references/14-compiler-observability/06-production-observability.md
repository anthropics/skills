# 生产可观测性

> 可观测性就像飞机驾驶舱的仪表盘——你不能"盲飞"，需要实时知道引擎转速、油量、高度和航向。

## 目录

- [可观测性概述](#可观测性概述)
- [推理服务监控指标](#推理服务监控指标)
- [SLO 设计](#slo-设计)
- [监控技术栈](#监控技术栈)
- [告警策略](#告警策略)
- [全链路追踪](#全链路追踪)
- [生产可观测性最佳实践](#生产可观测性最佳实践)
- [延伸阅读](#延伸阅读)

---

## 可观测性概述

### 可观测性三支柱

```
可观测性三支柱 (Three Pillars)

┌─────────────────────────────────────────────────┐
│                 可观测性                          │
├──────────────┬──────────────┬───────────────────┤
│   Metrics    │    Logs      │    Traces          │
│   (指标)     │   (日志)     │   (链路追踪)       │
├──────────────┼──────────────┼───────────────────┤
│ • 数值型     │ • 事件型     │ • 请求生命周期      │
│ • 可聚合     │ • 详细上下文 │ • 跨服务关联        │
│ • 时序数据   │ • 排错用     │ • 延迟分解          │
│              │              │                    │
│ Prometheus   │ ELK/Loki    │ Jaeger/Zipkin      │
│ Grafana      │ Fluentd     │ OpenTelemetry      │
├──────────────┼──────────────┼───────────────────┤
│ "多快/多少"  │ "发生了什么" │ "为什么慢"          │
└──────────────┴──────────────┴───────────────────┘
```

### AI 推理服务的特殊性

```
AI 推理服务 vs 传统 Web 服务的监控差异

传统 Web 服务:                    AI 推理服务:
├── 请求延迟均匀                 ├── 延迟高度可变（取决于输入长度）
├── 资源消耗稳定                 ├── GPU 显存动态变化
├── 无状态                       ├── KV Cache 有状态
├── 水平扩展简单                 ├── GPU 资源稀缺、扩展受限
├── 错误明确                     ├── "质量退化"难以检测
└── CPU/内存为主                 └── GPU 利用率是核心指标

AI 推理特有的监控需求:
  • Token 级延迟（TTFT, TPOT, TPS）
  • KV Cache 利用率
  • 批处理效率
  • 模型质量指标（在线）
  • GPU 温度和功耗
```

---

## 推理服务监控指标

### 关键指标定义

```
AI 推理服务核心指标

┌── 延迟指标 ──────────────────────────────────────────────┐
│                                                          │
│ TTFT (Time To First Token)                               │
│   首 token 响应时间 = 预处理 + Prefill                    │
│   用户感知: "模型开始回答有多快"                           │
│                                                          │
│ TPOT (Time Per Output Token)                             │
│   每个输出 token 的生成时间                               │
│   用户感知: "打字速度有多快"                              │
│                                                          │
│ E2E Latency (端到端延迟)                                  │
│   从请求到完成的总时间                                     │
│   E2E = TTFT + TPOT × output_tokens                     │
│                                                          │
│ TPS (Tokens Per Second)                                   │
│   每秒生成的 token 数（吞吐量指标）                        │
│                                                          │
└──────────────────────────────────────────────────────────┘

┌── 资源指标 ──────────────────────────────────────────────┐
│                                                          │
│ GPU 利用率 (SM Utilization)                              │
│ GPU 显存使用率                                            │
│ KV Cache 利用率（当前 / 最大）                            │
│ 批大小（当前 inflight batch size）                        │
│ 请求队列深度                                              │
│ GPU 温度和功耗                                            │
│                                                          │
└──────────────────────────────────────────────────────────┘

┌── 业务指标 ──────────────────────────────────────────────┐
│                                                          │
│ 请求成功率                                                │
│ 请求吞吐量 (RPS)                                         │
│ 令牌吞吐量 (Tokens/sec)                                  │
│ 上下文长度分布                                            │
│ 拒绝率（队列满/显存不足）                                 │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

### Prometheus 指标暴露

```python
from prometheus_client import Histogram, Gauge, Counter, start_http_server

# 定义指标
TTFT_HISTOGRAM = Histogram(
    'llm_ttft_seconds',
    'Time to first token',
    buckets=[0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0],
    labelnames=['model', 'endpoint'],
)

TPOT_HISTOGRAM = Histogram(
    'llm_tpot_seconds',
    'Time per output token',
    buckets=[0.01, 0.02, 0.05, 0.1, 0.2, 0.5],
    labelnames=['model'],
)

E2E_LATENCY = Histogram(
    'llm_e2e_latency_seconds',
    'End-to-end request latency',
    buckets=[0.5, 1, 2, 5, 10, 30, 60],
    labelnames=['model', 'endpoint'],
)

TOKENS_GENERATED = Counter(
    'llm_tokens_generated_total',
    'Total tokens generated',
    labelnames=['model'],
)

GPU_UTILIZATION = Gauge(
    'gpu_utilization_percent',
    'GPU SM utilization',
    labelnames=['gpu_id'],
)

KV_CACHE_UTILIZATION = Gauge(
    'llm_kv_cache_utilization',
    'KV cache utilization ratio',
    labelnames=['model'],
)

QUEUE_DEPTH = Gauge(
    'llm_request_queue_depth',
    'Number of pending requests',
    labelnames=['model'],
)

REQUEST_ERRORS = Counter(
    'llm_request_errors_total',
    'Total request errors',
    labelnames=['model', 'error_type'],
)

# 在推理服务中使用
class InferenceMetrics:
    """推理指标采集器"""
    
    def record_request(self, model: str, ttft: float, tpot: float,
                       e2e: float, output_tokens: int, endpoint: str = "chat"):
        TTFT_HISTOGRAM.labels(model=model, endpoint=endpoint).observe(ttft)
        TPOT_HISTOGRAM.labels(model=model).observe(tpot)
        E2E_LATENCY.labels(model=model, endpoint=endpoint).observe(e2e)
        TOKENS_GENERATED.labels(model=model).inc(output_tokens)
    
    def update_gpu_metrics(self):
        """更新 GPU 指标（定期调用）"""
        import pynvml
        pynvml.nvmlInit()
        for i in range(pynvml.nvmlDeviceGetCount()):
            handle = pynvml.nvmlDeviceGetHandleByIndex(i)
            util = pynvml.nvmlDeviceGetUtilizationRates(handle)
            GPU_UTILIZATION.labels(gpu_id=str(i)).set(util.gpu)
```

---

## SLO 设计

### SLO 定义框架

```
AI 推理服务 SLO 设计

┌── Tier 1: 核心 SLO ─────────────────────────────────────┐
│                                                          │
│ SLO-1: TTFT P99 < 2s                                    │
│   含义: 99% 的请求在 2 秒内开始输出                       │
│   监控: Prometheus histogram_quantile(0.99, ...)         │
│                                                          │
│ SLO-2: 可用性 > 99.9%                                    │
│   含义: 每月最多 43 分钟不可用                            │
│   计算: 成功请求数 / 总请求数                             │
│                                                          │
│ SLO-3: 错误率 < 0.1%                                     │
│   含义: 每 1000 个请求最多 1 个错误                       │
│   包括: 500 错误、超时、OOM                               │
│                                                          │
└──────────────────────────────────────────────────────────┘

┌── Tier 2: 体验 SLO ─────────────────────────────────────┐
│                                                          │
│ SLO-4: TPOT P95 < 50ms                                   │
│   含义: 95% 的 token 生成速度 > 20 TPS                   │
│   影响: 用户感知的"打字速度"                              │
│                                                          │
│ SLO-5: E2E P95 < 30s（标准请求）                          │
│   含义: 95% 的请求在 30 秒内完成                          │
│                                                          │
└──────────────────────────────────────────────────────────┘

┌── Tier 3: 资源 SLO ─────────────────────────────────────┐
│                                                          │
│ SLO-6: GPU 利用率 > 60%                                  │
│   含义: GPU 不应大量空闲（成本效率）                      │
│                                                          │
│ SLO-7: 排队时间 P95 < 5s                                 │
│   含义: 请求不应长时间等待                                │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

### Error Budget 管理

```python
class ErrorBudgetTracker:
    """错误预算追踪器"""
    
    def __init__(self, slo_target: float = 0.999, window_days: int = 30):
        self.slo_target = slo_target
        self.window_days = window_days
        self.total_requests = 0
        self.failed_requests = 0
    
    def record(self, success: bool):
        self.total_requests += 1
        if not success:
            self.failed_requests += 1
    
    @property
    def current_sli(self) -> float:
        """当前服务水平指标"""
        if self.total_requests == 0:
            return 1.0
        return 1.0 - (self.failed_requests / self.total_requests)
    
    @property
    def error_budget_remaining(self) -> float:
        """剩余错误预算百分比"""
        allowed_errors = self.total_requests * (1 - self.slo_target)
        if allowed_errors == 0:
            return 1.0
        return max(0, 1.0 - (self.failed_requests / allowed_errors))
    
    def should_freeze_changes(self) -> bool:
        """错误预算耗尽时应冻结变更"""
        return self.error_budget_remaining < 0.1  # 剩余不到 10%
```

---

## 监控技术栈

### 推荐架构

```
AI 推理服务监控架构

┌──────────────────────────────────────────────────────────┐
│                     Grafana Dashboard                     │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐              │
│  │ 延迟面板  │  │ GPU 面板  │  │ 告警面板  │              │
│  └──────────┘  └──────────┘  └──────────┘              │
└─────────┬──────────────┬──────────────┬─────────────────┘
          │              │              │
    ┌─────▼────┐   ┌─────▼────┐  ┌─────▼────┐
    │Prometheus │   │  Loki    │  │ Jaeger   │
    │ (Metrics) │   │ (Logs)   │  │ (Traces) │
    └─────┬────┘   └─────┬────┘  └─────┬────┘
          │              │              │
    ┌─────▼──────────────▼──────────────▼────┐
    │          OpenTelemetry Collector         │
    └─────────────────┬──────────────────────┘
                      │
    ┌─────────────────▼──────────────────────┐
    │          推理服务 (vLLM / TGI)           │
    │  ┌──────┐  ┌──────┐  ┌──────┐         │
    │  │GPU 0 │  │GPU 1 │  │GPU 2 │  ...    │
    │  └──────┘  └──────┘  └──────┘         │
    └────────────────────────────────────────┘
```

### Grafana Dashboard 设计

```
推理服务 Dashboard 关键面板

Row 1: 概览
┌──────────────┬──────────────┬──────────────┬──────────────┐
│  请求吞吐量   │  平均延迟     │  错误率       │  GPU 利用率   │
│  120 req/s   │  1.2s        │  0.05%       │  78%         │
│  ▲ 15%       │  ▼ 8%        │  → 稳定      │  → 稳定      │
└──────────────┴──────────────┴──────────────┴──────────────┘

Row 2: 延迟详情
┌─────────────────────────────┬─────────────────────────────┐
│  TTFT 分布 (P50/P95/P99)    │  TPOT 分布                  │
│  ▁▂▃▅▇█▇▅▃▂▁               │  ▁▂▃▅▇█▇▅▃▂▁               │
│  P50: 0.3s P99: 1.8s       │  P50: 25ms P99: 45ms        │
└─────────────────────────────┴─────────────────────────────┘

Row 3: 资源
┌─────────────────────────────┬─────────────────────────────┐
│  GPU 显存使用                │  KV Cache 使用率             │
│  ████████░░ 72 GB / 80 GB   │  ████████░░ 78%             │
│  各 GPU 单独折线             │  随时间变化趋势              │
└─────────────────────────────┴─────────────────────────────┘

Row 4: 队列与批处理
┌─────────────────────────────┬─────────────────────────────┐
│  请求队列深度                │  当前批大小                  │
│  █▂▁▁▁▂█▂▁                  │  ▃▅▇█▇▅▃▅▇                  │
│  峰值: 42, 当前: 3          │  平均: 28, 最大: 64          │
└─────────────────────────────┴─────────────────────────────┘
```

---

## 告警策略

### 告警规则设计

```yaml
# Prometheus 告警规则示例

groups:
  - name: llm-inference-alerts
    rules:
      # 核心告警：TTFT 超标
      - alert: HighTTFT
        expr: histogram_quantile(0.99, rate(llm_ttft_seconds_bucket[5m])) > 2
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "TTFT P99 超过 2 秒"
          description: "模型 {{ $labels.model }} 的 TTFT P99 为 {{ $value }}s"
      
      # 核心告警：错误率过高
      - alert: HighErrorRate
        expr: rate(llm_request_errors_total[5m]) / rate(llm_e2e_latency_seconds_count[5m]) > 0.01
        for: 3m
        labels:
          severity: critical
        annotations:
          summary: "推理错误率超过 1%"
      
      # 资源告警：GPU 显存高
      - alert: HighGPUMemory
        expr: gpu_memory_used_bytes / gpu_memory_total_bytes > 0.95
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "GPU {{ $labels.gpu_id }} 显存使用率超过 95%"
      
      # 资源告警：队列堆积
      - alert: HighQueueDepth
        expr: llm_request_queue_depth > 100
        for: 3m
        labels:
          severity: warning
        annotations:
          summary: "请求队列深度超过 100"
      
      # GPU 告警：温度过高
      - alert: GPUHighTemperature
        expr: gpu_temperature_celsius > 85
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "GPU {{ $labels.gpu_id }} 温度过高: {{ $value }}°C"
```

### 告警分级

```
告警分级策略

P0 (Critical) - 立即响应:
  ├── 服务不可用（所有请求失败）
  ├── GPU 硬件故障
  └── 数据平面错误率 > 5%

P1 (High) - 15 分钟内响应:
  ├── SLO 违规（TTFT/可用性）
  ├── GPU OOM 频繁
  └── 错误率 > 1%

P2 (Medium) - 1 小时内响应:
  ├── 延迟 P95 超标
  ├── GPU 利用率异常（过低或过高）
  └── 队列持续堆积

P3 (Low) - 工作时间处理:
  ├── 单个请求超时
  ├── 非核心指标异常
  └── 容量规划预警
```

---

## 全链路追踪

### OpenTelemetry 集成

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.jaeger.thrift import JaegerExporter

# 初始化追踪
provider = TracerProvider()
exporter = JaegerExporter(agent_host_name="jaeger", agent_port=6831)
provider.add_span_processor(BatchSpanProcessor(exporter))
trace.set_tracer_provider(provider)

tracer = trace.get_tracer("llm-inference-service")

class TracedInferenceService:
    """带链路追踪的推理服务"""
    
    def generate(self, prompt: str, params: dict) -> str:
        with tracer.start_as_current_span("generate") as span:
            span.set_attribute("prompt_length", len(prompt))
            span.set_attribute("model", params.get("model", ""))
            span.set_attribute("max_tokens", params.get("max_tokens", 0))
            
            # 分词
            with tracer.start_as_current_span("tokenize"):
                input_ids = self.tokenizer.encode(prompt)
                span.set_attribute("input_tokens", len(input_ids))
            
            # 排队等待
            with tracer.start_as_current_span("queue_wait"):
                batch_slot = self.scheduler.acquire()
            
            # Prefill
            with tracer.start_as_current_span("prefill"):
                kv_cache = self.model.prefill(input_ids)
            
            # Decode
            with tracer.start_as_current_span("decode") as decode_span:
                output_ids = self.model.decode(kv_cache, params)
                decode_span.set_attribute("output_tokens", len(output_ids))
            
            # 后处理
            with tracer.start_as_current_span("detokenize"):
                result = self.tokenizer.decode(output_ids)
            
            return result
```

### 追踪分析

```
全链路追踪示例

请求 ID: abc-123
总耗时: 3.2s

├── generate ──────────────────────────────── 3200ms
│   ├── tokenize ──────────── 5ms
│   ├── queue_wait ────────── 200ms     ← 排队等待
│   ├── prefill ───────────── 800ms     ← Prefill（输入 2K tokens）
│   ├── decode ────────────── 2100ms    ← 生成 42 tokens
│   │   ├── step_1 ──── 50ms
│   │   ├── step_2 ──── 50ms
│   │   ├── ...
│   │   └── step_42 ─── 50ms
│   └── detokenize ────────── 3ms

分析:
  TTFT = tokenize + queue_wait + prefill = 1005ms
  TPOT = decode / output_tokens = 50ms/token
  TPS = 1000 / 50 = 20 tokens/sec
```

---

## 生产可观测性最佳实践

```
AI 推理服务可观测性检查清单

□ 指标 (Metrics)
  □ TTFT / TPOT / E2E 延迟直方图
  □ 请求吞吐量和错误率
  □ GPU 利用率、显存、温度
  □ KV Cache 使用率
  □ 队列深度和批大小
  □ 按模型/端点分标签

□ 日志 (Logs)
  □ 结构化日志（JSON 格式）
  □ 请求级日志（输入长度、输出长度、延迟）
  □ 错误日志（堆栈、GPU 状态）
  □ 审计日志（安全相关）
  □ 日志级别可动态调整

□ 追踪 (Traces)
  □ 请求全链路追踪
  □ Prefill / Decode 分段
  □ 队列等待时间
  □ 跨服务调用追踪

□ 告警
  □ SLO 违规告警
  □ 资源饱和告警
  □ 异常检测告警
  □ 告警收敛和降噪
  □ 值班和升级策略

□ 仪表板
  □ 实时概览 Dashboard
  □ 按模型的详细 Dashboard
  □ GPU 集群资源 Dashboard
  □ 成本追踪 Dashboard
```

---

## 参考资料与引用

1. Beyer, B., et al. (2016). *Site Reliability Engineering* - Chapter 4: Service Level Objectives. Google. https://sre.google/sre-book/service-level-objectives/
2. OpenTelemetry Documentation - Observability Framework. https://opentelemetry.io/docs/
3. Prometheus Monitoring - Best Practices. https://prometheus.io/docs/practices/
4. vLLM Metrics Guide - Inference Monitoring. https://docs.vllm.ai/en/latest/serving/metrics.html
5. Grafana Dashboard Best Practices. https://grafana.com/docs/grafana/latest/best-practices/
6. The Art of SLOs - Google SRE. https://sre.google/resources/practices-and-processes/art-of-slos/

---

*上一篇：[05-training-debugging.md](05-training-debugging.md)*

[返回目录](README.md) | [返回主页](../README.md)

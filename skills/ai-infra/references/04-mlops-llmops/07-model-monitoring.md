# 模型监控与可观测性

> 模型上线只是开始，持续监控才能保证模型在生产中持续发挥价值。

## 目录

- [监控三大维度](#监控三大维度)
- [数据漂移检测](#数据漂移检测)
- [模型性能监控](#模型性能监控)
- [Prometheus + Grafana](#prometheus--grafana)
- [实战练习](#实战练习)

---

## 监控三大维度

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       ML 监控三大维度                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 系统监控 (System Metrics)                                              │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ • 延迟 (P50/P95/P99)          • GPU 利用率 / 显存使用                │   │
│   │ • 吞吐量 (QPS)                • 错误率 / 队列长度                    │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. 数据监控 (Data Drift)                                                  │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ • 输入数据分布变化            • 特征缺失率                          │   │
│   │ • 异常值检测                  • Schema 变更                         │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. 模型监控 (Model Performance)                                           │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ • 预测分布变化 (Concept Drift) • 业务指标 (CTR, 转化率)            │   │
│   │ • 预测置信度分布              • 对比基准模型                        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 关键指标

| 维度 | 指标 | 告警阈值示例 |
|------|------|--------------|
| **系统** | P99 延迟 | > 200ms |
| **系统** | 错误率 | > 1% |
| **数据** | 数据漂移分数 | > 0.1 |
| **数据** | 缺失率 | > 5% |
| **模型** | 预测精度 | < 0.85 |
| **模型** | 置信度均值 | < 0.7 |

---

## 数据漂移检测

### 什么是数据漂移

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          数据漂移类型                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Data Drift (数据漂移)                                                     │
│   ─────────────────────                                                     │
│   输入特征分布变化，但特征与标签关系不变                                    │
│                                                                             │
│   训练时: age ~ N(30, 10)                                                   │
│   生产中: age ~ N(45, 15)  ← 用户群体变化                                  │
│                                                                             │
│   Concept Drift (概念漂移)                                                  │
│   ──────────────────────                                                    │
│   特征与标签的关系发生变化                                                  │
│                                                                             │
│   训练时: 高价格 → 高品质                                                  │
│   生产中: 高价格 → 不一定 (市场变化)                                       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 使用 Evidently 检测漂移

```python
from evidently import Report
from evidently.metric_preset import DataDriftPreset, DataQualityPreset

# 创建漂移检测报告
report = Report(metrics=[
    DataDriftPreset(),
    DataQualityPreset()
])

# 对比参考数据 (训练时) 和当前数据 (生产中)
report.run(
    reference_data=reference_df,
    current_data=production_df
)

# 保存 HTML 报告
report.save_html("drift_report.html")

# 程序化检查
result = report.as_dict()
if result['metrics'][0]['result']['dataset_drift']:
    alert("⚠️ Data drift detected!")
    trigger_retraining()
```

### 持续监控 Pipeline

```python
# drift_monitor.py
from evidently import Report
from evidently.metrics import DataDriftPreset
import schedule
import time

def check_drift():
    """定期检测数据漂移"""
    # 获取最近的生产数据
    current_data = fetch_recent_production_data(hours=24)
    reference_data = load_reference_data()
    
    # 运行检测
    report = Report(metrics=[DataDriftPreset()])
    report.run(reference_data=reference_data, current_data=current_data)
    
    result = report.as_dict()
    drift_score = result['metrics'][0]['result']['share_of_drifted_columns']
    
    # 记录指标
    log_metric("drift_score", drift_score)
    
    # 告警
    if drift_score > 0.3:  # 超过30%的特征漂移
        send_alert(
            title="Data Drift Alert",
            message=f"Drift score: {drift_score:.2%}",
            severity="high"
        )

# 每小时检查一次
schedule.every(1).hours.do(check_drift)

while True:
    schedule.run_pending()
    time.sleep(60)
```

---

## 模型性能监控

### 实时指标收集

```python
from prometheus_client import Counter, Histogram, Gauge, start_http_server
import time

# 定义指标
PREDICTION_LATENCY = Histogram(
    'model_prediction_latency_seconds',
    'Prediction latency',
    buckets=[0.01, 0.05, 0.1, 0.5, 1.0]
)

PREDICTION_COUNT = Counter(
    'model_prediction_total',
    'Total predictions',
    ['model_version', 'status']
)

PREDICTION_CONFIDENCE = Histogram(
    'model_prediction_confidence',
    'Confidence distribution',
    buckets=[0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
)

# 使用指标
@PREDICTION_LATENCY.time()
def predict(input_data):
    """带监控的预测函数"""
    try:
        output = model(input_data)
        
        PREDICTION_COUNT.labels(
            model_version="v1.0",
            status="success"
        ).inc()
        
        PREDICTION_CONFIDENCE.observe(output.confidence)
        
        return output
    except Exception as e:
        PREDICTION_COUNT.labels(
            model_version="v1.0",
            status="error"
        ).inc()
        raise

# 启动指标服务器
start_http_server(8000)
```

### 业务指标追踪

```python
# 追踪模型的业务影响
class BusinessMetrics:
    def __init__(self):
        self.predictions = []
        self.outcomes = []
    
    def log_prediction(self, prediction_id: str, prediction: dict):
        """记录预测"""
        self.predictions.append({
            "id": prediction_id,
            "prediction": prediction,
            "timestamp": time.time()
        })
    
    def log_outcome(self, prediction_id: str, actual_outcome: dict):
        """记录实际结果 (可能延迟)"""
        self.outcomes.append({
            "id": prediction_id,
            "outcome": actual_outcome,
            "timestamp": time.time()
        })
    
    def calculate_metrics(self) -> dict:
        """计算业务指标"""
        # 匹配预测和结果
        matched = self._match_predictions_outcomes()
        
        return {
            "accuracy": self._calc_accuracy(matched),
            "precision": self._calc_precision(matched),
            "recall": self._calc_recall(matched),
            "business_impact": self._calc_business_impact(matched)
        }
```

---

## Prometheus + Grafana

### Prometheus 配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'model-service'
    static_configs:
      - targets: ['model-service:8000']
    
  - job_name: 'gpu-metrics'
    static_configs:
      - targets: ['dcgm-exporter:9400']
```

### Grafana Dashboard 示例

```json
{
  "panels": [
    {
      "title": "Prediction Latency P99",
      "type": "graph",
      "targets": [{
        "expr": "histogram_quantile(0.99, model_prediction_latency_seconds_bucket)"
      }]
    },
    {
      "title": "Predictions per Second",
      "type": "graph",
      "targets": [{
        "expr": "rate(model_prediction_total[5m])"
      }]
    },
    {
      "title": "Error Rate",
      "type": "stat",
      "targets": [{
        "expr": "sum(rate(model_prediction_total{status='error'}[5m])) / sum(rate(model_prediction_total[5m]))"
      }]
    },
    {
      "title": "Confidence Distribution",
      "type": "heatmap",
      "targets": [{
        "expr": "model_prediction_confidence_bucket"
      }]
    }
  ]
}
```

### 告警规则

```yaml
# alerting_rules.yml
groups:
  - name: model-alerts
    rules:
      - alert: HighLatency
        expr: histogram_quantile(0.99, model_prediction_latency_seconds_bucket) > 0.2
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Model latency too high"
      
      - alert: HighErrorRate
        expr: |
          sum(rate(model_prediction_total{status="error"}[5m])) 
          / sum(rate(model_prediction_total[5m])) > 0.01
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Model error rate > 1%"
      
      - alert: LowConfidence
        expr: avg(model_prediction_confidence) < 0.7
        for: 15m
        labels:
          severity: warning
        annotations:
          summary: "Average prediction confidence dropping"
```

---

## 实战练习

### 练习：完整监控系统

```python
# monitoring_system.py
from dataclasses import dataclass
from datetime import datetime, timedelta
import pandas as pd

@dataclass
class MonitoringConfig:
    drift_threshold: float = 0.3
    latency_p99_threshold_ms: float = 200
    error_rate_threshold: float = 0.01
    confidence_threshold: float = 0.7
    check_interval_minutes: int = 60

class ModelMonitor:
    def __init__(self, config: MonitoringConfig):
        self.config = config
        self.alerts = []
    
    def check_all(self):
        """运行所有检查"""
        self.check_data_drift()
        self.check_latency()
        self.check_error_rate()
        self.check_confidence()
        
        return self.alerts
    
    def check_data_drift(self):
        drift_score = calculate_drift_score()
        if drift_score > self.config.drift_threshold:
            self.alerts.append({
                "type": "DATA_DRIFT",
                "severity": "high",
                "value": drift_score,
                "threshold": self.config.drift_threshold
            })
    
    def check_latency(self):
        p99_latency = get_p99_latency()
        if p99_latency > self.config.latency_p99_threshold_ms:
            self.alerts.append({
                "type": "HIGH_LATENCY",
                "severity": "warning",
                "value": p99_latency,
                "threshold": self.config.latency_p99_threshold_ms
            })
    
    def should_retrain(self) -> bool:
        """判断是否需要重训练"""
        high_severity_alerts = [a for a in self.alerts if a["severity"] == "high"]
        return len(high_severity_alerts) > 0

# 使用
monitor = ModelMonitor(MonitoringConfig())
alerts = monitor.check_all()

if monitor.should_retrain():
    trigger_retraining_pipeline()
```

---

*下一篇：[08-LLMOps](08-llmops.md)*

*返回目录：[README](README.md)*

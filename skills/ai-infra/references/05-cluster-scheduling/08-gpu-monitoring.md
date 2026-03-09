# GPU 监控与可观测性

> 看不到的资源无法优化，GPU 监控是集群运维的基石。

## 目录

- [为什么需要 GPU 监控](#为什么需要-gpu-监控)
- [DCGM Exporter](#dcgm-exporter)
- [Prometheus 集成](#prometheus-集成)
- [Grafana 看板](#grafana-看板)
- [告警配置](#告警配置)
- [完整部署方案](#完整部署方案)

---

## 为什么需要 GPU 监控

### 核心指标

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       GPU 监控核心指标                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. GPU 利用率 (GPU Utilization)                                          │
│      SM 占用率，反映计算密集度                                              │
│      理想值: 训练 >80%, 推理 >60%                                          │
│                                                                             │
│   2. 显存使用 (GPU Memory Usage)                                           │
│      已用/总量，OOM 前的关键指标                                            │
│      告警阈值: >90% 预警                                                   │
│                                                                             │
│   3. GPU 温度 (GPU Temperature)                                            │
│      过热会导致降频 (Thermal Throttling)                                    │
│      阈值: >83°C 警告, >90°C 危险                                         │
│                                                                             │
│   4. 功耗 (Power Usage)                                                    │
│      实际功耗/TDP，反映负载水平                                             │
│      异常低功耗 = GPU 空闲浪费                                              │
│                                                                             │
│   5. GPU 时钟频率 (SM Clock)                                               │
│      降频说明散热或功耗限制                                                 │
│                                                                             │
│   6. NVLink/PCIe 带宽 (Interconnect Bandwidth)                             │
│      分布式训练通信瓶颈诊断                                                 │
│                                                                             │
│   7. Tensor Core 利用率                                                     │
│      Tensor Core 活跃比例，评估混合精度效率                                 │
│                                                                             │
│   8. ECC 错误 (Memory Errors)                                              │
│      可纠正/不可纠正错误计数，硬件健康指标                                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## DCGM Exporter

NVIDIA DCGM (Data Center GPU Manager) Exporter 将 GPU 指标暴露为 Prometheus 格式。

### 架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    GPU 监控架构                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────┐    ┌──────────────┐    ┌─────────────┐    ┌──────────────┐  │
│   │  GPU     │───▶│ DCGM Exporter│───▶│ Prometheus  │───▶│  Grafana     │  │
│   │ (NVML)  │    │ (DaemonSet)  │    │ (scrape)    │    │ (Dashboard)  │  │
│   └─────────┘    └──────────────┘    └──────┬──────┘    └──────────────┘  │
│                                              │                              │
│                                     ┌────────▼────────┐                    │
│                                     │  Alertmanager   │                    │
│                                     │  (告警通知)     │                    │
│                                     └─────────────────┘                    │
│                                                                             │
│   可选扩展:                                                                 │
│   ┌──────────────┐                                                         │
│   │ Prometheus   │  将 GPU 指标注册为 K8s custom metrics                   │
│   │ Adapter      │  供 HPA 使用 (基于 GPU 利用率自动扩缩)                  │
│   └──────────────┘                                                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 部署 DCGM Exporter

```bash
# 方式 1: Helm 安装 (推荐)
helm repo add gpu-helm-charts https://nvidia.github.io/dcgm-exporter/helm-charts
helm install dcgm-exporter gpu-helm-charts/dcgm-exporter \
  --namespace monitoring \
  --create-namespace \
  --set serviceMonitor.enabled=true  # 如果使用 Prometheus Operator

# 方式 2: 直接部署 DaemonSet
kubectl apply -f https://raw.githubusercontent.com/NVIDIA/dcgm-exporter/main/deployment/dcgm-exporter.yaml
```

```yaml
# 自定义 DaemonSet 配置
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: dcgm-exporter
  namespace: monitoring
spec:
  selector:
    matchLabels:
      app: dcgm-exporter
  template:
    metadata:
      labels:
        app: dcgm-exporter
    spec:
      nodeSelector:
        nvidia.com/gpu.present: "true"  # 仅部署到 GPU 节点
      containers:
      - name: dcgm-exporter
        image: nvcr.io/nvidia/k8s/dcgm-exporter:3.3.5-3.4.1-ubuntu22.04
        ports:
        - name: metrics
          containerPort: 9400
        env:
        - name: DCGM_EXPORTER_KUBERNETES
          value: "true"
        - name: DCGM_EXPORTER_LISTEN
          value: ":9400"
        securityContext:
          runAsNonRoot: false
          runAsUser: 0
        volumeMounts:
        - name: device-plugin
          mountPath: /var/lib/kubelet/pod-resources
      volumes:
      - name: device-plugin
        hostPath:
          path: /var/lib/kubelet/pod-resources

---
apiVersion: v1
kind: Service
metadata:
  name: dcgm-exporter
  namespace: monitoring
  labels:
    app: dcgm-exporter
spec:
  ports:
  - name: metrics
    port: 9400
    targetPort: 9400
  selector:
    app: dcgm-exporter
```

### 自定义指标

```csv
# custom-metrics.csv - 选择需要采集的指标
# 格式: DCGM_FIELD_ID, Prometheus 指标类型, 帮助信息

# 基础指标
DCGM_FI_DEV_GPU_UTIL,       gauge, GPU utilization (%)
DCGM_FI_DEV_MEM_COPY_UTIL,  gauge, Memory utilization (%)
DCGM_FI_DEV_FB_USED,        gauge, Framebuffer memory used (MiB)
DCGM_FI_DEV_FB_FREE,        gauge, Framebuffer memory free (MiB)

# 温度与功耗
DCGM_FI_DEV_GPU_TEMP,       gauge, GPU temperature (C)
DCGM_FI_DEV_POWER_USAGE,    gauge, Power usage (W)
DCGM_FI_DEV_TOTAL_ENERGY_CONSUMPTION, counter, Total energy consumption (mJ)

# 时钟频率
DCGM_FI_DEV_SM_CLOCK,       gauge, SM clock frequency (MHz)
DCGM_FI_DEV_MEM_CLOCK,      gauge, Memory clock frequency (MHz)

# Tensor Core
DCGM_FI_PROF_PIPE_TENSOR_ACTIVE, gauge, Tensor Core utilization (ratio)

# NVLink
DCGM_FI_DEV_NVLINK_BANDWIDTH_TOTAL, counter, NVLink bandwidth total (bytes)

# ECC 错误
DCGM_FI_DEV_ECC_SBE_AGG_TOTAL, counter, Single-bit ECC errors
DCGM_FI_DEV_ECC_DBE_AGG_TOTAL, counter, Double-bit ECC errors

# PCIe
DCGM_FI_DEV_PCIE_TX_THROUGHPUT, counter, PCIe TX throughput (bytes)
DCGM_FI_DEV_PCIE_RX_THROUGHPUT, counter, PCIe RX throughput (bytes)
```

```bash
# 挂载自定义指标配置
helm install dcgm-exporter gpu-helm-charts/dcgm-exporter \
  --set arguments[0]="--collectors=/etc/dcgm-exporter/custom-metrics.csv" \
  --set-file extraConfigMap.custom-metrics\.csv=./custom-metrics.csv
```

---

## Prometheus 集成

### ServiceMonitor 配置

```yaml
# 如果使用 Prometheus Operator
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: dcgm-exporter
  namespace: monitoring
spec:
  selector:
    matchLabels:
      app: dcgm-exporter
  endpoints:
  - port: metrics
    interval: 15s
    path: /metrics
```

### 常用 PromQL 查询

```promql
# 1. 集群 GPU 总利用率
avg(DCGM_FI_DEV_GPU_UTIL)

# 2. 每个节点的 GPU 利用率
avg by (Hostname) (DCGM_FI_DEV_GPU_UTIL)

# 3. GPU 显存使用率
DCGM_FI_DEV_FB_USED / (DCGM_FI_DEV_FB_USED + DCGM_FI_DEV_FB_FREE) * 100

# 4. 显存即将耗尽的 GPU (>90%)
(DCGM_FI_DEV_FB_USED / (DCGM_FI_DEV_FB_USED + DCGM_FI_DEV_FB_FREE)) > 0.9

# 5. GPU 温度过高 (>83°C)
DCGM_FI_DEV_GPU_TEMP > 83

# 6. 空闲 GPU (利用率 < 5% 持续 30 分钟)
avg_over_time(DCGM_FI_DEV_GPU_UTIL[30m]) < 5

# 7. Tensor Core 利用率
avg by (gpu, Hostname) (DCGM_FI_PROF_PIPE_TENSOR_ACTIVE) * 100

# 8. 按命名空间的 GPU 使用量
count by (namespace) (kube_pod_container_resource_limits{resource="nvidia_com_gpu"})

# 9. GPU 功耗
avg by (Hostname, gpu) (DCGM_FI_DEV_POWER_USAGE)

# 10. ECC 错误率 (硬件健康)
rate(DCGM_FI_DEV_ECC_DBE_AGG_TOTAL[1h]) > 0
```

### Prometheus Adapter (用于 HPA)

```yaml
# prometheus-adapter-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: prometheus-adapter-config
  namespace: monitoring
data:
  config.yaml: |
    rules:
    - seriesQuery: 'DCGM_FI_DEV_GPU_UTIL{namespace!="",pod!=""}'
      resources:
        overrides:
          namespace: {resource: "namespace"}
          pod: {resource: "pod"}
      name:
        matches: "DCGM_FI_DEV_GPU_UTIL"
        as: "gpu_utilization"
      metricsQuery: 'avg(DCGM_FI_DEV_GPU_UTIL{<<.LabelMatchers>>}) by (<<.GroupBy>>)'
```

```yaml
# 基于 GPU 利用率的 HPA
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: llm-inference-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: llm-inference
  minReplicas: 1
  maxReplicas: 8
  metrics:
  - type: Pods
    pods:
      metric:
        name: gpu_utilization
      target:
        type: AverageValue
        averageValue: "80"
```

---

## Grafana 看板

### 推荐看板

| 看板 | Grafana ID | 用途 |
|------|------------|------|
| NVIDIA DCGM Exporter | 12239 | 官方 DCGM 看板 |
| GPU Cluster Overview | 自定义 | 集群级别 GPU 总览 |
| GPU Node Detail | 自定义 | 单节点 GPU 详情 |
| Training Job Monitor | 自定义 | 训练任务监控 |

### 导入官方看板

```bash
# 在 Grafana UI 中:
# 1. 左侧菜单 → Dashboards → Import
# 2. 输入 ID: 12239
# 3. 选择 Prometheus 数据源
# 4. Import
```

### 自定义集群总览面板

关键面板配置：

```
GPU 集群总览看板布局:

┌─────────────────────────────────────────────────────────────────────┐
│ Row 1: 集群概览                                                     │
│ ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────┐          │
│ │ GPU 总数   │ │ 已分配    │ │ 空闲      │ │ 平均利用率 │          │
│ │   Stat    │ │   Stat    │ │   Stat    │ │   Gauge   │          │
│ └───────────┘ └───────────┘ └───────────┘ └───────────┘          │
├─────────────────────────────────────────────────────────────────────┤
│ Row 2: 利用率趋势                                                   │
│ ┌─────────────────────────────────────────────────────────────┐    │
│ │ GPU Utilization by Node (Time Series)                        │    │
│ │  — node-1: ████████████████████░░░░  80%                    │    │
│ │  — node-2: ██████████████░░░░░░░░░░  60%                    │    │
│ │  — node-3: ████████░░░░░░░░░░░░░░░░  35%                    │    │
│ └─────────────────────────────────────────────────────────────┘    │
├─────────────────────────────────────────────────────────────────────┤
│ Row 3: 显存与温度                                                   │
│ ┌──────────────────────────┐ ┌──────────────────────────────┐     │
│ │ Memory Usage (Bar Gauge) │ │ Temperature Heatmap           │     │
│ │ GPU0 ████████████░ 85%   │ │  ┌──┬──┬──┬──┬──┬──┬──┬──┐  │     │
│ │ GPU1 ██████░░░░░░░ 50%   │ │  │72│75│83│68│70│71│85│73│  │     │
│ │ GPU2 ██████████░░░ 78%   │ │  └──┴──┴──┴──┴──┴──┴──┴──┘  │     │
│ └──────────────────────────┘ └──────────────────────────────┘     │
├─────────────────────────────────────────────────────────────────────┤
│ Row 4: 功耗与错误                                                   │
│ ┌──────────────────────────┐ ┌──────────────────────────────┐     │
│ │ Power Usage (Time Series)│ │ ECC Errors (Table)           │     │
│ └──────────────────────────┘ └──────────────────────────────┘     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 告警配置

### Prometheus 告警规则

```yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: gpu-alerts
  namespace: monitoring
spec:
  groups:
  - name: gpu.rules
    rules:
    # GPU 温度过高
    - alert: GPUTemperatureHigh
      expr: DCGM_FI_DEV_GPU_TEMP > 83
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "GPU 温度过高: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "GPU 温度 {{ $value }}°C，超过 83°C 阈值"
    
    # GPU 温度危险
    - alert: GPUTemperatureCritical
      expr: DCGM_FI_DEV_GPU_TEMP > 90
      for: 2m
      labels:
        severity: critical
      annotations:
        summary: "GPU 温度危险: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "GPU 温度 {{ $value }}°C，即将触发 Thermal Throttling"
    
    # 显存即将耗尽
    - alert: GPUMemoryAlmostFull
      expr: (DCGM_FI_DEV_FB_USED / (DCGM_FI_DEV_FB_USED + DCGM_FI_DEV_FB_FREE)) > 0.95
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "GPU 显存即将耗尽: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "显存使用率 {{ $value | humanizePercentage }}"
    
    # GPU 空闲浪费
    - alert: GPUIdleWaste
      expr: avg_over_time(DCGM_FI_DEV_GPU_UTIL[30m]) < 5 and ON(namespace, pod) kube_pod_info
      for: 30m
      labels:
        severity: info
      annotations:
        summary: "GPU 空闲浪费: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "GPU 利用率持续低于 5%，持续 30 分钟"
    
    # ECC 双位错误 (硬件故障)
    - alert: GPUECCDoublebitError
      expr: rate(DCGM_FI_DEV_ECC_DBE_AGG_TOTAL[1h]) > 0
      for: 1m
      labels:
        severity: critical
      annotations:
        summary: "GPU ECC 双位错误: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "检测到不可纠正的 ECC 错误，建议更换 GPU"
    
    # GPU 降频
    - alert: GPUThrottling
      expr: DCGM_FI_DEV_SM_CLOCK < (DCGM_FI_DEV_SM_CLOCK offset 10m) * 0.8
      for: 10m
      labels:
        severity: warning
      annotations:
        summary: "GPU 降频: {{ $labels.Hostname }} GPU {{ $labels.gpu }}"
        description: "SM 时钟降低超过 20%，可能因温度或功耗限制"
```

---

## 完整部署方案

### 使用 NVIDIA GPU Operator (推荐)

GPU Operator 包含 Device Plugin、DCGM Exporter、驱动管理等全套组件：

```bash
# 1. 添加 NVIDIA Helm 仓库
helm repo add nvidia https://helm.ngc.nvidia.com/nvidia
helm repo update

# 2. 安装 GPU Operator (包含 DCGM Exporter)
helm install gpu-operator nvidia/gpu-operator \
  --namespace gpu-operator \
  --create-namespace \
  --set dcgmExporter.serviceMonitor.enabled=true \
  --set dcgmExporter.config.name=custom-metrics \
  --set toolkit.enabled=true

# 3. 安装 kube-prometheus-stack (Prometheus + Grafana)
helm repo add prometheus-community https://prometheus-community.github.io/helm-charts
helm install kube-prometheus prometheus-community/kube-prometheus-stack \
  --namespace monitoring \
  --create-namespace \
  --set grafana.adminPassword=admin123

# 4. 安装 Prometheus Adapter (用于 HPA)
helm install prometheus-adapter prometheus-community/prometheus-adapter \
  --namespace monitoring \
  --set prometheus.url=http://kube-prometheus-prometheus.monitoring.svc \
  --set prometheus.port=9090

# 验证
kubectl get pods -n gpu-operator
kubectl get servicemonitor -n gpu-operator
```

### 验证指标采集

```bash
# 直接访问 DCGM Exporter 指标
kubectl port-forward svc/dcgm-exporter -n gpu-operator 9400:9400
curl localhost:9400/metrics | grep DCGM_FI_DEV_GPU_UTIL

# 通过 Prometheus 查询
kubectl port-forward svc/kube-prometheus-prometheus -n monitoring 9090:9090
# 浏览器打开 http://localhost:9090
# 查询: DCGM_FI_DEV_GPU_UTIL

# 访问 Grafana
kubectl port-forward svc/kube-prometheus-grafana -n monitoring 3000:80
# 浏览器打开 http://localhost:3000
# 导入 Dashboard ID: 12239
```

---

## 📚 延伸阅读

- [NVIDIA DCGM Documentation](https://docs.nvidia.com/datacenter/dcgm/latest/)
- [DCGM Exporter GitHub](https://github.com/NVIDIA/dcgm-exporter)
- [NVIDIA GPU Operator](https://docs.nvidia.com/datacenter/cloud-native/gpu-operator/)
- [Prometheus Adapter for Kubernetes Metrics APIs](https://github.com/kubernetes-sigs/prometheus-adapter)

---

*返回目录：[README](README.md)*

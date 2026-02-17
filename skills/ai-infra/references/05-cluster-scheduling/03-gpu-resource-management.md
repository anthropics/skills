# GPU 资源管理

> 在 Kubernetes 中高效管理和分配 GPU 资源。

## 目录

- [NVIDIA Device Plugin](#nvidia-device-plugin)
- [MIG 多实例 GPU](#mig-多实例-gpu)
- [GPU 时间分片](#gpu-时间分片)

---

## NVIDIA Device Plugin

### 工作原理

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                 NVIDIA Device Plugin 工作原理                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐       ┌───────────────────────────────────────────────┐  │
│   │  Scheduler  │ ────▶ │ 调度决策: 哪个节点有足够的 GPU?                │  │
│   └─────────────┘       └───────────────────────────────────────────────┘  │
│         │                                                                   │
│         ▼                                                                   │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │                           Node                                       │  │
│   │  ┌───────────────────────────────────────────────────────────────┐  │  │
│   │  │           NVIDIA Device Plugin (DaemonSet)                     │  │  │
│   │  │                                                                │  │  │
│   │  │  1. 检测节点上的 GPU 数量和型号                                 │  │  │
│   │  │  2. 向 kubelet 注册 nvidia.com/gpu 资源                        │  │  │
│   │  │  3. Pod 启动时分配具体的 GPU 设备                               │  │  │
│   │  │  4. 设置 CUDA_VISIBLE_DEVICES 环境变量                         │  │  │
│   │  └───────────────────────────────────────────────────────────────┘  │  │
│   │                         │                                            │  │
│   │                         ▼                                            │  │
│   │  ┌───────────────────────────────────────────────────────────────┐  │  │
│   │  │              GPU 0    GPU 1    GPU 2    GPU 3                  │  │  │
│   │  └───────────────────────────────────────────────────────────────┘  │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 安装和验证

```bash
# 安装 NVIDIA Device Plugin
kubectl apply -f https://raw.githubusercontent.com/NVIDIA/k8s-device-plugin/v0.14.0/nvidia-device-plugin.yml

# 验证安装
kubectl get pods -n kube-system | grep nvidia

# 查看节点 GPU 资源
kubectl get nodes -o json | jq '.items[].status.capacity | select(.["nvidia.com/gpu"])'
# 输出: "nvidia.com/gpu": "8"

# 检查 GPU 分配
kubectl describe node <node-name> | grep -A 5 "Allocated resources"
```

### 测试 GPU 访问

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: gpu-test
spec:
  containers:
  - name: cuda
    image: nvidia/cuda:12.0-base
    command: ["nvidia-smi"]
    resources:
      limits:
        nvidia.com/gpu: 1
  restartPolicy: Never
```

```bash
kubectl apply -f gpu-test.yaml
kubectl logs gpu-test
```

---

## MIG 多实例 GPU

将单个 GPU 切分为多个独立实例。

### MIG 配置选项 (A100 80GB)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       A100 MIG 配置选项                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   配置方式           切分数    每实例显存    每实例 SM                       │
│   ──────────────    ────────  ──────────   ─────────                       │
│   1g.10gb             7         10GB        14 SM                          │
│   2g.20gb             3         20GB        28 SM                          │
│   3g.40gb             2         40GB        42 SM                          │
│   7g.80gb             1         80GB        98 SM                          │
│                                                                             │
│   物理视图 (7 × 1g.10gb):                                                  │
│   ┌─────────────────────────────────────────────────────────────────────┐  │
│   │                        A100 80GB                                     │  │
│   │  ┌────────┬────────┬────────┬────────┬────────┬────────┬────────┐  │  │
│   │  │ MIG 0  │ MIG 1  │ MIG 2  │ MIG 3  │ MIG 4  │ MIG 5  │ MIG 6  │  │  │
│   │  │ 10GB   │ 10GB   │ 10GB   │ 10GB   │ 10GB   │ 10GB   │ 10GB   │  │  │
│   │  └────────┴────────┴────────┴────────┴────────┴────────┴────────┘  │  │
│   └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│   适用: 推理服务、开发测试、小模型训练                                      │
│   不适用: 大模型训练（需要完整 GPU 互联）                                   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 使用 MIG 资源

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: mig-inference
spec:
  containers:
  - name: inference
    image: my-inference:latest
    resources:
      limits:
        nvidia.com/mig-1g.10gb: 1  # 请求 1 个 MIG 实例
```

---

## GPU 时间分片

多个 Pod 共享同一个 GPU（通过时间分片）。

### 配置时间分片

```yaml
# time-slicing-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: time-slicing-config
  namespace: nvidia-device-plugin
data:
  any: |-
    version: v1
    sharing:
      timeSlicing:
        renameByDefault: false
        resources:
        - name: nvidia.com/gpu
          replicas: 4  # 每个 GPU 可被 4 个 Pod 共享
```

```bash
# 应用配置
kubectl apply -f time-slicing-config.yaml

# 重启 device plugin
kubectl rollout restart daemonset nvidia-device-plugin -n kube-system
```

### 适用场景对比

| 方案 | 隔离性 | 适用场景 |
|------|--------|----------|
| **独占 GPU** | 完全隔离 | 训练、高性能推理 |
| **MIG** | 硬件隔离 | 多租户推理 |
| **时间分片** | 无隔离 | 开发测试、低负载 |

---

*下一篇：[04-批调度器详解](04-batch-schedulers.md)*

*返回目录：[README](README.md)*

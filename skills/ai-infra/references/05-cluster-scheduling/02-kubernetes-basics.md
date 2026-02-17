# Kubernetes 基础

> 掌握 K8s 核心概念，理解 AI 工作负载的配置方式。

## 目录

- [核心概念回顾](#核心概念回顾)
- [AI 工作负载配置](#ai-工作负载配置)
- [常用操作命令](#常用操作命令)

---

## 核心概念回顾

### 基础对象

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Kubernetes 核心对象                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Pod: 最小调度单元                                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  Pod                                                                │   │
│   │   ┌──────────────┐  ┌──────────────┐                               │   │
│   │   │ Container 1  │  │ Container 2  │   共享网络/存储               │   │
│   │   └──────────────┘  └──────────────┘                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   工作负载类型:                                                             │
│   ─────────────                                                             │
│   • Deployment  - 无状态服务 (推理服务)                                    │
│   • StatefulSet - 有状态服务 (参数服务器)                                  │
│   • Job         - 一次性任务 (训练任务)                                    │
│   • CronJob     - 定时任务 (定期重训练)                                    │
│                                                                             │
│   资源管理:                                                                 │
│   ─────────────                                                             │
│   • Request: 调度时保证的最小资源                                           │
│   • Limit: 运行时的资源上限                                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 调度相关概念

| 概念 | 作用 | AI 场景应用 |
|------|------|-------------|
| **NodeSelector** | 选择特定节点 | 选择 GPU 类型 |
| **Tolerations** | 容忍节点污点 | 允许调度到 GPU 节点 |
| **Affinity** | 亲和性/反亲和性 | 同节点/跨节点调度 |
| **Priority** | 任务优先级 | 抢占低优先级任务 |

---

## AI 工作负载配置

### 训练任务 Job

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: llama-training
  namespace: ml-training
spec:
  completions: 1
  parallelism: 1
  backoffLimit: 3
  template:
    spec:
      restartPolicy: OnFailure
      
      # 节点选择
      nodeSelector:
        gpu-type: a100-80gb
      
      # 容忍 GPU 节点污点
      tolerations:
      - key: "nvidia.com/gpu"
        operator: "Exists"
        effect: "NoSchedule"
      
      containers:
      - name: trainer
        image: pytorch/pytorch:2.0.0-cuda11.8-cudnn8-runtime
        command: ["torchrun"]
        args:
        - "--nproc_per_node=8"
        - "train.py"
        
        resources:
          requests:
            cpu: "32"
            memory: "256Gi"
            nvidia.com/gpu: "8"
          limits:
            cpu: "64"
            memory: "512Gi"
            nvidia.com/gpu: "8"
        
        env:
        - name: NCCL_DEBUG
          value: "INFO"
        
        volumeMounts:
        - name: data
          mountPath: /data
        - name: shm  # 共享内存，DataLoader 需要
          mountPath: /dev/shm
      
      volumes:
      - name: data
        persistentVolumeClaim:
          claimName: training-data-pvc
      - name: shm
        emptyDir:
          medium: Memory
          sizeLimit: 64Gi
```

### 推理服务 Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: llm-inference
spec:
  replicas: 3
  selector:
    matchLabels:
      app: llm-inference
  template:
    metadata:
      labels:
        app: llm-inference
    spec:
      containers:
      - name: vllm
        image: vllm/vllm-openai:latest
        args:
        - "--model=/models/llama-7b"
        - "--tensor-parallel-size=1"
        
        resources:
          limits:
            nvidia.com/gpu: 1
        
        ports:
        - containerPort: 8000
        
        readinessProbe:
          httpGet:
            path: /health
            port: 8000
          initialDelaySeconds: 60
          periodSeconds: 10
```

---

## 常用操作命令

### 任务管理

```bash
# 提交任务
kubectl apply -f training-job.yaml

# 查看任务状态
kubectl get jobs -n ml-training
kubectl describe job llama-training -n ml-training

# 查看 Pod 日志
kubectl logs -f <pod-name> -n ml-training

# 进入 Pod 调试
kubectl exec -it <pod-name> -n ml-training -- bash

# 删除任务
kubectl delete job llama-training -n ml-training
```

### 资源查看

```bash
# 查看节点 GPU 资源
kubectl get nodes -o json | jq '.items[] | {name: .metadata.name, gpu: .status.capacity["nvidia.com/gpu"]}'

# 查看 GPU 使用情况
kubectl describe nodes | grep -A 5 "Allocated resources"

# 查看命名空间配额使用
kubectl describe resourcequota -n ml-training
```

---

*下一篇：[03-GPU 资源管理](03-gpu-resource-management.md)*

*返回目录：[README](README.md)*

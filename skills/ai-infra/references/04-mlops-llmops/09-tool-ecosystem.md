# MLOps 工具生态

> 了解 MLOps 工具全景，为团队选择合适的工具组合。

## 目录

- [工具全景图](#工具全景图)
- [分领域工具详解](#分领域工具详解)
- [工具选型指南](#工具选型指南)
- [推荐工具组合](#推荐工具组合)

---

## 工具全景图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      MLOps 工具生态全景                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   实验跟踪           模型注册            特征存储                            │
│   ─────────          ─────────           ─────────                          │
│   • MLflow           • MLflow Registry   • Feast                            │
│   • W&B              • HuggingFace Hub   • Tecton                           │
│   • Comet            • Vertex AI         • Databricks FS                    │
│   • Neptune          • SageMaker         • AWS Feature Store                │
│   • Aim              • Azure ML          • Hopsworks                        │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   Pipeline/编排      模型服务            监控告警                           │
│   ─────────────      ─────────           ─────────                          │
│   • Kubeflow         • vLLM              • Evidently                        │
│   • Airflow          • TGI               • Whylogs                          │
│   • Prefect          • Triton            • Prometheus                       │
│   • Dagster          • BentoML           • Grafana                          │
│   • Argo Workflows   • Ray Serve         • Arize                            │
│                      • TorchServe        • Fiddler                          │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   数据版本           LLMOps              平台                               │
│   ─────────          ─────────           ─────────                          │
│   • DVC              • LangSmith         • Databricks                       │
│   • LakeFS           • Langfuse          • Vertex AI                        │
│   • Delta Lake       • Humanloop         • SageMaker                        │
│   • Pachyderm        • PromptLayer       • Azure ML                         │
│                      • Helicone          • MLflow                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 分领域工具详解

### 实验跟踪工具对比

| 工具 | 部署方式 | 特点 | 适合场景 |
|------|----------|------|----------|
| **MLflow** | 自托管/云 | 开源、全面、sklearn 集成好 | 企业、私有部署 |
| **W&B** | SaaS | UI 最佳、可视化强、HF 集成 | 快速实验、深度学习 |
| **Comet** | SaaS/自托管 | 协作功能强 | 团队协作 |
| **Neptune** | SaaS | 元数据管理强 | 大规模实验 |
| **Aim** | 自托管 | 轻量、快速 | 个人/小团队 |

### Pipeline 工具对比

| 工具 | 特点 | 适合场景 |
|------|------|----------|
| **Kubeflow** | K8s 原生、ML 专用 | K8s 环境、ML Pipeline |
| **Airflow** | 成熟稳定、DAG 编排 | 数据工程、ETL |
| **Prefect** | Python 原生、易用 | Python 团队 |
| **Dagster** | 数据感知、测试友好 | 数据密集型 |

### 模型服务工具对比

| 工具 | 特点 | 适合场景 |
|------|------|----------|
| **vLLM** | LLM 专用、高性能 | LLM 推理服务 |
| **TGI** | HuggingFace 出品 | HF 模型部署 |
| **Triton** | NVIDIA、多框架 | 企业级、异构模型 |
| **BentoML** | 简单易用、打包方便 | 快速部署 |
| **Ray Serve** | 分布式、灵活 | 大规模、复杂服务 |

### 监控工具对比

| 工具 | 特点 | 适合场景 |
|------|------|----------|
| **Evidently** | 开源、漂移检测 | 数据/模型监控 |
| **Whylogs** | 轻量、数据 profiling | 数据质量监控 |
| **Arize** | SaaS、全面 | 企业级监控 |
| **Prometheus+Grafana** | 通用、成熟 | 系统指标监控 |

---

## 工具选型指南

### 选型考虑因素

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         工具选型考虑因素                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 团队规模和能力                                                         │
│   ─────────────────────                                                     │
│   • 小团队: 选择易上手、维护少的工具 (W&B, Prefect)                         │
│   • 大团队: 可考虑功能全面、需要维护的工具 (MLflow, Kubeflow)               │
│                                                                             │
│   2. 基础设施                                                               │
│   ─────────────────────                                                     │
│   • 有 K8s: Kubeflow, Argo, Volcano                                        │
│   • 无 K8s: Prefect, Dagster                                               │
│   • 云服务: 云厂商托管服务                                                  │
│                                                                             │
│   3. 合规和安全                                                             │
│   ─────────────────────                                                     │
│   • 数据敏感: 自托管 (MLflow, Feast)                                       │
│   • 合规要求高: 企业级平台 (Databricks, Vertex AI)                         │
│                                                                             │
│   4. 预算                                                                   │
│   ─────────────────────                                                     │
│   • 预算有限: 开源工具 (MLflow + Prefect + Evidently)                      │
│   • 预算充足: SaaS 或企业平台                                               │
│                                                                             │
│   5. 技术栈                                                                 │
│   ─────────────────────                                                     │
│   • HuggingFace 生态: W&B, TGI, HF Hub                                     │
│   • PyTorch 生态: MLflow, TorchServe                                       │
│   • TensorFlow 生态: Vertex AI, TensorFlow Serving                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 决策流程图

```
开始选型
    │
    ├─▶ Q1: 是否需要自托管？
    │       │
    │       ├─ 是 ─▶ 考虑开源工具
    │       │        (MLflow, Kubeflow, Feast)
    │       │
    │       └─ 否 ─▶ 考虑 SaaS/托管服务
    │                (W&B, Databricks, Vertex AI)
    │
    ├─▶ Q2: 是否有 Kubernetes？
    │       │
    │       ├─ 是 ─▶ Kubeflow, Argo, KServe
    │       │
    │       └─ 否 ─▶ Prefect, Dagster, BentoML
    │
    ├─▶ Q3: 主要是 LLM 应用？
    │       │
    │       ├─ 是 ─▶ LangSmith, vLLM, TGI
    │       │
    │       └─ 否 ─▶ 传统 MLOps 工具
    │
    └─▶ 根据团队能力和预算最终确定
```

---

## 推荐工具组合

### 场景 1: 初创团队 / 快速验证

```
┌─────────────────────────────────────────────────────────────────────────────┐
│   初创团队推荐组合 (低成本、快速上手)                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   实验跟踪: W&B (免费额度)                                                  │
│   Pipeline: Prefect (Python 原生)                                          │
│   模型注册: HuggingFace Hub                                                 │
│   模型服务: BentoML 或 vLLM                                                 │
│   监控: Evidently (开源)                                                    │
│                                                                             │
│   特点: 快速上手、维护成本低、免费或低成本                                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 场景 2: 企业级 / 私有部署

```
┌─────────────────────────────────────────────────────────────────────────────┐
│   企业级推荐组合 (安全合规、可控)                                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   实验跟踪: MLflow (自托管)                                                 │
│   Pipeline: Kubeflow Pipelines                                              │
│   模型注册: MLflow Model Registry                                           │
│   特征存储: Feast (自托管)                                                  │
│   模型服务: Triton Inference Server                                         │
│   监控: Prometheus + Grafana + Evidently                                   │
│                                                                             │
│   特点: 完全可控、满足合规、需要运维投入                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 场景 3: LLM 应用

```
┌─────────────────────────────────────────────────────────────────────────────┐
│   LLM 应用推荐组合                                                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Prompt 管理: LangSmith                                                    │
│   实验跟踪: W&B                                                             │
│   向量数据库: Pinecone / Milvus / Chroma                                    │
│   模型服务: vLLM / TGI                                                      │
│   监控: Langfuse (LLM 专用)                                                 │
│   评估: RAGAS                                                               │
│                                                                             │
│   特点: LLM 专用工具、Prompt/RAG 管理                                       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 场景 4: 云原生 / Kubernetes

```
┌─────────────────────────────────────────────────────────────────────────────┐
│   云原生推荐组合                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   实验跟踪: MLflow (K8s 部署)                                               │
│   Pipeline: Kubeflow Pipelines / Argo Workflows                             │
│   模型注册: MLflow Registry                                                 │
│   模型服务: KServe / Seldon                                                 │
│   GPU 调度: Volcano                                                         │
│   监控: Prometheus + Grafana                                                │
│                                                                             │
│   特点: K8s 原生、云厂商无关、可扩展                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 快速对比表

| 场景 | 实验跟踪 | Pipeline | 服务 | 监控 |
|------|----------|----------|------|------|
| **初创** | W&B | Prefect | BentoML | Evidently |
| **企业** | MLflow | Kubeflow | Triton | Prometheus |
| **LLM** | W&B | Prefect | vLLM | Langfuse |
| **K8s** | MLflow | Kubeflow | KServe | Prometheus |

---

## 延伸阅读

### 工具官方文档

- [MLflow](https://mlflow.org/docs/)
- [Weights & Biases](https://docs.wandb.ai/)
- [Kubeflow](https://www.kubeflow.org/docs/)
- [LangSmith](https://docs.smith.langchain.com/)
- [Evidently](https://docs.evidentlyai.com/)

### 学习资源

- [MLOps Community](https://mlops.community/)
- [Made With ML](https://madewithml.com/)
- [Full Stack Deep Learning](https://fullstackdeeplearning.com/)

---

*返回目录：[README](README.md)*

*上一篇：[08-LLMOps](08-llmops.md)*

*下一章：[05-集群调度](../05-cluster-scheduling/README.md)*

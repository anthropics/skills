# MLOps / LLMOps 详解

> 从实验到生产的桥梁，决定 AI 项目能否持续迭代。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [04-mlops-llmops/](./04-mlops-llmops/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 什么是 MLOps | [01-what-is-mlops.md](./04-mlops-llmops/01-what-is-mlops.md) |
> | MLOps 成熟度模型 | [02-maturity-model.md](./04-mlops-llmops/02-maturity-model.md) |
> | 实验跟踪 | [03-experiment-tracking.md](./04-mlops-llmops/03-experiment-tracking.md) |
> | 模型版本管理 | [04-model-registry.md](./04-mlops-llmops/04-model-registry.md) |
> | 特征工程平台 | [05-feature-store.md](./04-mlops-llmops/05-feature-store.md) |
> | CI/CD for ML | [06-cicd-for-ml.md](./04-mlops-llmops/06-cicd-for-ml.md) |
> | 模型监控与可观测性 | [07-model-monitoring.md](./04-mlops-llmops/07-model-monitoring.md) |
> | LLMOps 特殊考量 | [08-llmops.md](./04-mlops-llmops/08-llmops.md) |
> | 工具生态 | [09-tool-ecosystem.md](./04-mlops-llmops/09-tool-ecosystem.md) |
> | 数据管理与质量 | [10-data-management.md](./04-mlops-llmops/10-data-management.md) |
> | AI Safety 与 Guardrails | [11-ai-safety-guardrails.md](./04-mlops-llmops/11-ai-safety-guardrails.md) |

---

## 目录

- [什么是 MLOps](#什么是-mlops)
- [MLOps 成熟度模型](#mlops-成熟度模型)
- [实验跟踪](#实验跟踪)
- [模型版本管理](#模型版本管理)
- [特征工程平台](#特征工程平台)
- [CI/CD for ML](#cicd-for-ml)
- [模型监控与可观测性](#模型监控与可观测性)
- [LLMOps 特殊考量](#llmops-特殊考量)
- [工具生态](#工具生态)
- [实战练习](#实战练习)

---

## 什么是 MLOps

### 定义

MLOps = Machine Learning + DevOps + Data Engineering

将软件工程的最佳实践应用于 ML 系统，实现模型的**持续开发、部署和维护**。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       MLOps 生命周期                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐ │
│   │  数据   │ → │  实验   │ → │  训练   │ → │  部署   │ → │  监控   │ │
│   │  准备   │   │  跟踪   │   │  管道   │   │  服务   │   │  反馈   │ │
│   └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘ │
│        │             │             │             │             │       │
│        └─────────────┴─────────────┴─────────────┴─────────────┘       │
│                               │                                         │
│                               ▼                                         │
│                        持续迭代闭环                                      │
│                                                                         │
│   关键能力:                                                              │
│   - 可复现性: 任何实验都能精确复现                                        │
│   - 自动化: 从数据到部署全流程自动化                                      │
│   - 可观测性: 实时监控模型性能                                           │
│   - 治理: 版本控制、审计追踪、合规                                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### MLOps vs DevOps

| 维度 | DevOps | MLOps |
|------|--------|-------|
| **输入** | 代码 | 代码 + 数据 + 模型 |
| **测试** | 单元测试、集成测试 | + 数据验证、模型验证 |
| **构建产物** | 应用程序 | 模型文件 + 服务代码 |
| **部署** | 滚动更新 | A/B 测试、金丝雀发布 |
| **监控** | 系统指标 | + 模型指标、数据漂移 |
| **反馈循环** | Bug 修复 | 模型重训练 |

---

## MLOps 成熟度模型

### Google 的 MLOps 成熟度等级

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     MLOps 成熟度等级                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Level 0: 手工流程                                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 手动训练、手动部署                                             │   │
│   │ - Jupyter Notebook 实验                                         │   │
│   │ - 无版本控制                                                     │   │
│   │ - 模型上线周期: 数月                                             │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Level 1: ML 流水线自动化                                              │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 训练流水线自动化                                               │   │
│   │ - 实验跟踪、模型版本管理                                         │   │
│   │ - 持续训练 (CT)                                                  │   │
│   │ - 模型上线周期: 数周                                             │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Level 2: CI/CD for ML                                                 │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 代码、数据、模型全部版本控制                                    │   │
│   │ - 自动化测试 (数据验证、模型验证)                                 │   │
│   │ - 自动化部署、A/B 测试                                           │   │
│   │ - 模型监控、自动重训练                                           │   │
│   │ - 模型上线周期: 数天                                             │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 实验跟踪

### 为什么需要实验跟踪

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       实验跟踪解决的痛点                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   没有实验跟踪:                                                          │
│   ├── "上周那个效果好的模型用的什么超参数？"                              │
│   ├── "这个模型是用哪个版本的数据训练的？"                                │
│   ├── "为什么 A 同学的实验结果和 B 不一样？"                              │
│   └── "哪个实验的效果最好？"                                             │
│                                                                         │
│   有了实验跟踪:                                                          │
│   ├── 每次实验的超参数、指标、代码版本、数据版本全部记录                   │
│   ├── 可视化对比不同实验                                                 │
│   ├── 一键复现任何历史实验                                               │
│   └── 团队协作、知识沉淀                                                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### MLflow

开源的 ML 生命周期管理平台。

```python
import mlflow
import mlflow.pytorch

# 设置实验
mlflow.set_experiment("llama-finetuning")

# 开始记录
with mlflow.start_run(run_name="lr_sweep_001"):
    # 记录参数
    mlflow.log_param("learning_rate", 1e-5)
    mlflow.log_param("batch_size", 32)
    mlflow.log_param("epochs", 3)
    mlflow.log_param("model", "llama-2-7b")
    mlflow.log_param("dataset", "alpaca-cleaned")
    
    # 训练循环
    for epoch in range(3):
        train_loss = train_one_epoch(model, train_loader)
        val_loss, val_acc = evaluate(model, val_loader)
        
        # 记录指标
        mlflow.log_metrics({
            "train_loss": train_loss,
            "val_loss": val_loss,
            "val_accuracy": val_acc
        }, step=epoch)
    
    # 保存模型
    mlflow.pytorch.log_model(model, "model")
    
    # 记录额外文件
    mlflow.log_artifact("config.yaml")
    
    # 添加标签
    mlflow.set_tag("status", "completed")
    mlflow.set_tag("gpu", "A100-80GB")

# 查询历史实验
runs = mlflow.search_runs(
    experiment_names=["llama-finetuning"],
    filter_string="metrics.val_accuracy > 0.9",
    order_by=["metrics.val_accuracy DESC"]
)
print(runs[["params.learning_rate", "metrics.val_accuracy"]])
```

### Weights & Biases (W&B)

更现代化的实验跟踪平台，可视化能力强。

```python
import wandb

# 初始化
wandb.init(
    project="llm-training",
    name="llama-7b-sft",
    config={
        "learning_rate": 1e-5,
        "batch_size": 32,
        "model": "llama-2-7b",
        "dataset": "alpaca",
    }
)

# 训练循环
for step, batch in enumerate(dataloader):
    loss = train_step(model, batch)
    
    # 记录指标
    wandb.log({
        "train/loss": loss,
        "train/learning_rate": scheduler.get_last_lr()[0],
    }, step=step)
    
    # 记录样本生成结果
    if step % 100 == 0:
        samples = generate_samples(model, prompts)
        wandb.log({
            "samples": wandb.Table(
                columns=["prompt", "generation"],
                data=list(zip(prompts, samples))
            )
        })

# 保存模型 artifact
artifact = wandb.Artifact("model", type="model")
artifact.add_dir("checkpoints/")
wandb.log_artifact(artifact)

wandb.finish()
```

### 实验跟踪最佳实践

| 实践 | 说明 |
|------|------|
| **记录一切** | 超参数、随机种子、环境变量、依赖版本 |
| **语义化命名** | 运行名称包含关键信息，如 `lr1e-5_bs32_epoch3` |
| **使用标签** | 标记实验状态、GPU 类型、数据版本 |
| **定期清理** | 删除失败/无用的实验，保持整洁 |
| **团队规范** | 统一命名规范、指标定义 |

---

## 模型版本管理

### Model Registry

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Model Registry 核心功能                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                      Model Registry                              │   │
│   │                                                                 │   │
│   │   Model: llama-chat                                             │   │
│   │   ├── Version 1.0.0 (Staging)                                   │   │
│   │   │   ├── Artifacts: model.safetensors, config.json             │   │
│   │   │   ├── Metrics: accuracy=0.85, latency=50ms                  │   │
│   │   │   ├── Source Run: run_abc123                                │   │
│   │   │   └── Tags: ["sft", "alpaca-data"]                          │   │
│   │   │                                                             │   │
│   │   ├── Version 2.0.0 (Production) ⭐                              │   │
│   │   │   ├── Artifacts: model.safetensors, config.json             │   │
│   │   │   ├── Metrics: accuracy=0.92, latency=45ms                  │   │
│   │   │   ├── Source Run: run_xyz789                                │   │
│   │   │   └── Tags: ["dpo", "ultrachat-data"]                       │   │
│   │   │                                                             │   │
│   │   └── Version 2.1.0 (Archived)                                  │   │
│   │       └── ...                                                   │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   核心能力:                                                              │
│   - 模型版本化存储                                                       │
│   - 阶段管理 (Staging → Production → Archived)                          │
│   - 血缘追踪 (Lineage): 模型来自哪个实验、哪份数据                        │
│   - 访问控制和审计                                                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### MLflow Model Registry 使用

```python
import mlflow
from mlflow.tracking import MlflowClient

client = MlflowClient()

# 注册模型
model_uri = f"runs:/{run_id}/model"
mlflow.register_model(model_uri, "llama-chat")

# 获取模型版本（使用 Alias API，MLflow 2.9+）
client.set_registered_model_alias("llama-chat", "production", "2")
model_version = client.get_model_version_by_alias("llama-chat", "production")

# 设置别名（推荐，MLflow 2.9+ Alias API）
client.set_registered_model_alias(
    name="llama-chat",
    alias="production",
    version="2",
)

# 加载生产模型
model = mlflow.pytorch.load_model("models:/llama-chat/Production")
```

### Hugging Face Hub

LLM 时代最流行的模型托管平台。

```python
from huggingface_hub import HfApi, login

# 登录
login(token="hf_xxx")

api = HfApi()

# 上传模型
api.upload_folder(
    folder_path="./my-model",
    repo_id="myorg/llama-finetuned",
    repo_type="model",
    commit_message="Upload finetuned model v1.0"
)

# 创建模型卡片 (README.md)
model_card = """
---
license: apache-2.0
tags:
  - llama
  - fine-tuned
  - chat
datasets:
  - alpaca
metrics:
  - accuracy
---

# Llama Finetuned

This model was fine-tuned on Alpaca dataset.

## Training
- Base model: meta-llama/Llama-2-7b
- Dataset: alpaca
- Epochs: 3
- Learning rate: 1e-5

## Evaluation
| Metric | Score |
|--------|-------|
| MMLU   | 0.52  |
| HellaSwag | 0.78 |
"""

# 下载模型
from transformers import AutoModelForCausalLM
model = AutoModelForCausalLM.from_pretrained("myorg/llama-finetuned")
```

---

## 特征工程平台

### Feature Store 概念

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       Feature Store 架构                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                        数据源                                    │   │
│   │   DB │ Event Stream │ Files │ APIs │ Logs                       │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│                               ▼                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                    Feature Engineering                           │   │
│   │              (Spark / Flink / SQL / Python)                      │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│                               ▼                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                      Feature Store                               │   │
│   │   ┌─────────────────────┐   ┌─────────────────────┐             │   │
│   │   │   Offline Store     │   │   Online Store      │             │   │
│   │   │   (历史特征)         │   │   (实时特征)         │             │   │
│   │   │   Parquet/Delta     │   │   Redis/DynamoDB    │             │   │
│   │   └─────────────────────┘   └─────────────────────┘             │   │
│   │                                                                 │   │
│   │   + Feature Registry (元数据、血缘、文档)                         │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│           ┌───────────────────┴───────────────────┐                    │
│           │                                       │                    │
│           ▼                                       ▼                    │
│   ┌─────────────────┐                   ┌─────────────────┐           │
│   │    Training     │                   │    Serving      │           │
│   │  (批量读取)      │                   │  (实时读取)      │           │
│   └─────────────────┘                   └─────────────────┘           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Feast 示例

```python
from feast import FeatureStore, Entity, Field, FeatureView, FileSource
from feast.types import Float32, Int64
from datetime import timedelta

# 定义数据源
user_features_source = FileSource(
    path="data/user_features.parquet",
    timestamp_field="event_timestamp",
)

# 定义实体
user = Entity(name="user_id", value_type=Int64)

# 定义特征视图
user_features_view = FeatureView(
    name="user_features",
    entities=["user_id"],
    ttl=timedelta(days=1),
    schema=[
        Field(name="total_purchases", dtype=Int64),
        Field(name="avg_purchase_value", dtype=Float32),
        Field(name="days_since_last_purchase", dtype=Int64),
    ],
    source=user_features_source,
)

# 注册特征
store = FeatureStore(repo_path=".")
store.apply([user, user_features_view])

# 训练时: 获取历史特征
training_df = store.get_historical_features(
    entity_df=entity_df,  # 包含 user_id 和 event_timestamp
    features=["user_features:total_purchases", "user_features:avg_purchase_value"]
).to_df()

# 推理时: 获取实时特征
online_features = store.get_online_features(
    features=["user_features:total_purchases"],
    entity_rows=[{"user_id": 123}]
).to_dict()
```

---

## CI/CD for ML

### ML Pipeline 架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        ML CI/CD Pipeline                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │                      触发器                                    │     │
│   │  - Git Push (代码变更)                                         │     │
│   │  - 定时触发 (每日重训)                                          │     │
│   │  - 数据更新 (新数据到达)                                        │     │
│   │  - 模型漂移告警                                                 │     │
│   └───────────────────────────────┬───────────────────────────────┘     │
│                                   │                                     │
│                                   ▼                                     │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │                    CI: 持续集成                                │     │
│   │                                                               │     │
│   │   1. 代码检查                                                  │     │
│   │      - Linting (flake8, black)                                │     │
│   │      - Type checking (mypy)                                   │     │
│   │      - 单元测试                                                │     │
│   │                                                               │     │
│   │   2. 数据验证                                                  │     │
│   │      - Schema 验证                                            │     │
│   │      - 统计特性检查                                            │     │
│   │      - 数据质量检查                                            │     │
│   │                                                               │     │
│   │   3. 模型验证                                                  │     │
│   │      - 小规模训练测试                                          │     │
│   │      - 基准性能检查                                            │     │
│   │                                                               │     │
│   └───────────────────────────────┬───────────────────────────────┘     │
│                                   │                                     │
│                                   ▼                                     │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │                    CT: 持续训练                                │     │
│   │                                                               │     │
│   │   1. 数据准备                                                  │     │
│   │   2. 特征工程                                                  │     │
│   │   3. 模型训练                                                  │     │
│   │   4. 模型评估                                                  │     │
│   │   5. 模型注册                                                  │     │
│   │                                                               │     │
│   └───────────────────────────────┬───────────────────────────────┘     │
│                                   │                                     │
│                                   ▼                                     │
│   ┌───────────────────────────────────────────────────────────────┐     │
│   │                    CD: 持续部署                                │     │
│   │                                                               │     │
│   │   1. 模型打包 (Docker/TorchServe)                              │     │
│   │   2. 金丝雀部署 (5% 流量)                                      │     │
│   │   3. A/B 测试                                                 │     │
│   │   4. 逐步放量 → 全量发布                                       │     │
│   │   5. 回滚机制                                                  │     │
│   │                                                               │     │
│   └───────────────────────────────────────────────────────────────┘     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### GitHub Actions for ML

```yaml
# .github/workflows/ml-pipeline.yml
name: ML Pipeline

on:
  push:
    branches: [main]
  schedule:
    - cron: '0 0 * * *'  # 每日重训
  workflow_dispatch:  # 手动触发

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.10'
      
      - name: Install dependencies
        run: pip install -r requirements.txt
      
      - name: Run tests
        run: pytest tests/
      
      - name: Data validation
        run: python scripts/validate_data.py

  train:
    needs: test
    runs-on: [self-hosted, gpu]
    steps:
      - uses: actions/checkout@v3
      
      - name: Train model
        run: |
          python train.py \
            --config configs/production.yaml \
            --output models/
        env:
          WANDB_API_KEY: ${{ secrets.WANDB_API_KEY }}
      
      - name: Evaluate model
        run: python evaluate.py --model models/latest
      
      - name: Register model
        if: ${{ success() }}
        run: |
          python scripts/register_model.py \
            --model models/latest \
            --stage staging

  deploy:
    needs: train
    runs-on: ubuntu-latest
    steps:
      - name: Deploy to staging
        run: |
          kubectl apply -f k8s/staging/
      
      - name: Run integration tests
        run: python tests/integration_test.py
      
      - name: Promote to production
        if: ${{ success() }}
        run: |
          kubectl apply -f k8s/production/
```

### Kubeflow Pipelines

```python
from kfp import dsl
from kfp.dsl import component, pipeline

@component(base_image="python:3.10")
def preprocess_data(input_path: str, output_path: str):
    import pandas as pd
    # 数据预处理逻辑
    df = pd.read_parquet(input_path)
    df_processed = preprocess(df)
    df_processed.to_parquet(output_path)

@component(base_image="pytorch/pytorch:2.0.0-cuda11.7-cudnn8-runtime")
def train_model(
    data_path: str,
    model_path: str,
    learning_rate: float,
    epochs: int
):
    import torch
    # 训练逻辑
    model = train(data_path, lr=learning_rate, epochs=epochs)
    torch.save(model.state_dict(), model_path)

@component
def evaluate_model(model_path: str, test_data_path: str) -> float:
    # 评估逻辑
    accuracy = evaluate(model_path, test_data_path)
    return accuracy

@pipeline(name="ml-training-pipeline")
def training_pipeline(
    input_data: str,
    learning_rate: float = 1e-5,
    epochs: int = 3
):
    preprocess_task = preprocess_data(
        input_path=input_data,
        output_path="/data/processed"
    )
    
    train_task = train_model(
        data_path=preprocess_task.outputs["output_path"],
        model_path="/models/latest",
        learning_rate=learning_rate,
        epochs=epochs
    ).set_gpu_limit(1)
    
    evaluate_task = evaluate_model(
        model_path=train_task.outputs["model_path"],
        test_data_path="/data/test"
    )
    
    # 条件部署
    with dsl.Condition(evaluate_task.output > 0.9):
        deploy_model(model_path=train_task.outputs["model_path"])
```

---

## 模型监控与可观测性

### 监控维度

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       ML 监控三大维度                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. 系统监控 (System Metrics)                                          │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 延迟 (P50/P95/P99)                                            │   │
│   │ - 吞吐量 (QPS)                                                  │   │
│   │ - GPU 利用率 / 显存使用                                          │   │
│   │ - 错误率                                                        │   │
│   │ - 队列长度                                                      │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   2. 数据监控 (Data Drift)                                              │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 输入数据分布变化                                               │   │
│   │ - 特征缺失率                                                    │   │
│   │ - 异常值检测                                                    │   │
│   │ - Schema 变更                                                   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   3. 模型监控 (Model Performance)                                       │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ - 预测分布变化 (Concept Drift)                                  │   │
│   │ - 业务指标 (CTR, 转化率)                                        │   │
│   │ - 预测置信度分布                                                │   │
│   │ - 对比基准模型                                                  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 数据漂移检测

```python
from evidently import Report
from evidently.metrics import (
    DataDriftPreset,
    DataQualityPreset,
    TargetDriftPreset
)

# 创建漂移检测报告
report = Report(metrics=[
    DataDriftPreset(),
    DataQualityPreset(),
    TargetDriftPreset()
])

# 对比参考数据和当前数据
report.run(
    reference_data=reference_df,  # 训练时的数据分布
    current_data=production_df    # 生产中的实时数据
)

# 保存报告
report.save_html("drift_report.html")

# 获取漂移指标
result = report.as_dict()
if result['metrics'][0]['result']['dataset_drift']:
    alert("Data drift detected!")
```

### Prometheus + Grafana 监控

```python
from prometheus_client import Counter, Histogram, Gauge, start_http_server

# 定义指标
PREDICTION_LATENCY = Histogram(
    'model_prediction_latency_seconds',
    'Time spent processing prediction',
    buckets=[0.01, 0.05, 0.1, 0.5, 1.0, 5.0]
)

PREDICTION_COUNT = Counter(
    'model_prediction_total',
    'Total number of predictions',
    ['model_version', 'status']
)

PREDICTION_CONFIDENCE = Histogram(
    'model_prediction_confidence',
    'Confidence score distribution',
    buckets=[0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
)

GPU_MEMORY_USAGE = Gauge(
    'gpu_memory_usage_bytes',
    'GPU memory usage in bytes'
)

# 使用
@PREDICTION_LATENCY.time()
def predict(input_data):
    output = model(input_data)
    
    PREDICTION_COUNT.labels(
        model_version="v1.0",
        status="success"
    ).inc()
    
    PREDICTION_CONFIDENCE.observe(output.confidence)
    
    return output

# 启动指标服务器
start_http_server(8000)
```

---

## LLMOps 特殊考量

### LLMOps vs 传统 MLOps

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    LLMOps 特殊挑战                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统 MLOps                        LLMOps                             │
│   ──────────                        ──────                             │
│   模型小，训练快                      模型大，训练慢、成本高               │
│   数据标注相对便宜                    标注困难，RLHF 成本高                │
│   明确的评估指标                      评估复杂（安全性、幻觉、对齐）        │
│   输入输出固定格式                    自然语言输入，输出不确定             │
│   模型即产品                          Prompt + 模型 + RAG = 产品         │
│                                                                         │
│   LLMOps 新增关注点:                                                    │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ 1. Prompt 管理                                                  │   │
│   │    - Prompt 版本控制                                            │   │
│   │    - A/B 测试不同 prompt                                        │   │
│   │    - Prompt 模板库                                              │   │
│   │                                                                 │   │
│   │ 2. RAG 管理                                                     │   │
│   │    - 向量数据库索引更新                                          │   │
│   │    - 检索质量监控                                                │   │
│   │    - 知识库版本管理                                              │   │
│   │                                                                 │   │
│   │ 3. 安全与对齐                                                    │   │
│   │    - 内容审核 (Content Moderation)                              │   │
│   │    - 越狱检测 (Jailbreak Detection)                             │   │
│   │    - 幻觉检测 (Hallucination Detection)                         │   │
│   │                                                                 │   │
│   │ 4. 成本管理                                                      │   │
│   │    - Token 使用量监控                                           │   │
│   │    - 缓存策略（Semantic Cache）                                  │   │
│   │    - 模型路由（小模型优先）                                       │   │
│   │                                                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Prompt 管理

```python
# 使用 LangSmith 进行 Prompt 管理
from langsmith import Client
from langchain import hub

client = Client()

# 上传 prompt 到 hub
prompt_template = """
You are a helpful assistant. Answer the following question:

Question: {question}

Please provide a clear and concise answer.
"""

# 创建 prompt
prompt = hub.push(
    "my-org/qa-prompt:v1.0",
    prompt_template,
    tags=["production", "qa"]
)

# 拉取特定版本
prompt = hub.pull("my-org/qa-prompt:v1.0")

# A/B 测试不同 prompt
import random

prompts = {
    "v1": hub.pull("my-org/qa-prompt:v1.0"),
    "v2": hub.pull("my-org/qa-prompt:v2.0"),
}

def get_prompt():
    version = "v1" if random.random() < 0.5 else "v2"
    return prompts[version], version
```

### LLM 评估

```python
# 使用 RAGAS 评估 RAG 系统
from ragas import evaluate
from ragas.metrics import (
    faithfulness,
    answer_relevancy,
    context_precision,
    context_recall
)

# 准备评估数据
eval_data = {
    "question": ["What is AI?", ...],
    "answer": ["AI is...", ...],
    "contexts": [["context1", "context2"], ...],
    "ground_truth": ["AI stands for...", ...]
}

# 运行评估
result = evaluate(
    eval_data,
    metrics=[
        faithfulness,        # 答案是否基于上下文
        answer_relevancy,    # 答案是否相关
        context_precision,   # 检索精度
        context_recall       # 检索召回
    ]
)

print(result)
# {'faithfulness': 0.85, 'answer_relevancy': 0.92, ...}
```

### 成本优化

```python
# 语义缓存
from langchain.cache import RedisSemanticCache
from langchain.globals import set_llm_cache
import redis

# 设置语义缓存
set_llm_cache(RedisSemanticCache(
    redis_url="redis://localhost:6379",
    embedding=embeddings,
    score_threshold=0.95  # 相似度阈值
))

# 模型路由 (小模型优先)
from langchain.chains.router import MultiPromptChain

def route_model(query):
    # 简单问题用小模型
    if is_simple_query(query):
        return small_model
    # 复杂问题用大模型
    return large_model

# Token 使用监控
from langchain.callbacks import get_openai_callback

with get_openai_callback() as cb:
    response = llm(query)
    print(f"Tokens used: {cb.total_tokens}")
    print(f"Cost: ${cb.total_cost:.4f}")
```

---

## 工具生态

### MLOps 工具全景

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      MLOps 工具生态                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   实验跟踪        │  模型注册        │  特征存储                         │
│   - MLflow       │  - MLflow        │  - Feast                         │
│   - W&B          │  - HF Hub        │  - Tecton                        │
│   - Comet        │  - Vertex AI     │  - Databricks FS                 │
│   - Neptune      │  - SageMaker     │  - AWS Feature Store             │
│                  │                  │                                   │
│   ──────────────────────────────────────────────────────────────────   │
│                                                                         │
│   Pipeline       │  Serving         │  监控                            │
│   - Kubeflow     │  - vLLM          │  - Evidently                     │
│   - Airflow      │  - TGI           │  - Whylogs                       │
│   - Prefect      │  - Triton        │  - Prometheus                    │
│   - Dagster      │  - BentoML       │  - Arize                         │
│                  │  - Ray Serve     │  - Fiddler                       │
│                  │                  │                                   │
│   ──────────────────────────────────────────────────────────────────   │
│                                                                         │
│   LLMOps 专用    │  平台            │                                   │
│   - LangSmith    │  - Databricks    │                                   │
│   - Weights &    │  - Vertex AI     │                                   │
│     Biases       │  - SageMaker     │                                   │
│   - Humanloop    │  - Azure ML      │                                   │
│   - PromptLayer  │  - MLflow        │                                   │
│                  │                  │                                   │
└─────────────────────────────────────────────────────────────────────────┘
```

### 工具选择建议

| 场景 | 推荐工具 | 理由 |
|------|----------|------|
| **初创团队** | MLflow + W&B | 开源 + 免费额度 |
| **企业级** | Databricks / Vertex AI | 全托管，合规 |
| **LLM 应用** | LangSmith + W&B | LLM 专门优化 |
| **Kubernetes** | Kubeflow + MLflow | 云原生 |
| **快速实验** | W&B | 可视化最佳 |

---

## 实战练习

### 练习 1：MLflow 实验跟踪

```python
# mlflow_demo.py
import mlflow
import torch
from transformers import AutoModelForSequenceClassification, Trainer

mlflow.set_tracking_uri("http://localhost:5000")
mlflow.set_experiment("text-classification")

with mlflow.start_run():
    # 记录参数
    mlflow.log_params({
        "model": "bert-base-uncased",
        "learning_rate": 2e-5,
        "batch_size": 16,
        "epochs": 3
    })
    
    # 训练
    model = AutoModelForSequenceClassification.from_pretrained("bert-base-uncased")
    trainer = Trainer(model=model, ...)
    trainer.train()
    
    # 记录指标
    eval_results = trainer.evaluate()
    mlflow.log_metrics(eval_results)
    
    # 保存模型
    mlflow.pytorch.log_model(model, "model")

# 启动 MLflow UI: mlflow ui --port 5000
```

### 练习 2：数据漂移检测

```python
# drift_detection.py
from evidently.report import Report
from evidently.metric_preset import DataDriftPreset
import pandas as pd

# 模拟参考数据和生产数据
reference_data = pd.DataFrame({
    "feature_1": np.random.normal(0, 1, 1000),
    "feature_2": np.random.normal(5, 2, 1000),
})

# 模拟漂移
production_data = pd.DataFrame({
    "feature_1": np.random.normal(0.5, 1, 1000),  # 均值偏移
    "feature_2": np.random.normal(5, 3, 1000),    # 方差变大
})

# 生成报告
report = Report(metrics=[DataDriftPreset()])
report.run(reference_data=reference_data, current_data=production_data)
report.save_html("drift_report.html")

# 检查是否需要告警
result = report.as_dict()
if result['metrics'][0]['result']['dataset_drift']:
    print("⚠️ Data drift detected! Consider retraining.")
```

### 练习 3：简单 ML Pipeline

```python
# simple_pipeline.py
from prefect import flow, task
import mlflow

@task
def load_data():
    # 加载数据
    return train_data, test_data

@task
def train_model(train_data, config):
    with mlflow.start_run():
        mlflow.log_params(config)
        model = train(train_data, **config)
        mlflow.pytorch.log_model(model, "model")
    return model

@task
def evaluate_model(model, test_data):
    metrics = evaluate(model, test_data)
    mlflow.log_metrics(metrics)
    return metrics

@task
def deploy_if_better(model, metrics, threshold=0.9):
    if metrics['accuracy'] > threshold:
        deploy_model(model)
        return True
    return False

@flow
def ml_pipeline(config):
    train_data, test_data = load_data()
    model = train_model(train_data, config)
    metrics = evaluate_model(model, test_data)
    deployed = deploy_if_better(model, metrics)
    return deployed

# 运行 pipeline
ml_pipeline(config={"lr": 1e-5, "epochs": 3})
```

---

## 延伸阅读

### 推荐书籍

- *Designing Machine Learning Systems* - Chip Huyen
- *Machine Learning Engineering* - Andriy Burkov
- *Building Machine Learning Pipelines* - O'Reilly

### 推荐课程

- [Full Stack Deep Learning](https://fullstackdeeplearning.com/)
- [Made With ML](https://madewithml.com/)
- [MLOps Zoomcamp](https://github.com/DataTalksClub/mlops-zoomcamp)

### 官方文档

- [MLflow Documentation](https://mlflow.org/docs/latest/)
- [Kubeflow Documentation](https://www.kubeflow.org/docs/)
- [Weights & Biases Docs](https://docs.wandb.ai/)
- [LangSmith Documentation](https://docs.smith.langchain.com/)

---

*下一篇：[05-cluster-scheduling.md](05-cluster-scheduling.md) - 集群调度详解*

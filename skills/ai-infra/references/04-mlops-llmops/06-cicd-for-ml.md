# CI/CD for ML

> 将软件工程的持续集成/持续部署实践应用于机器学习系统。

## 目录

- [ML Pipeline 架构](#ml-pipeline-架构)
- [CI: 持续集成](#ci-持续集成)
- [CT: 持续训练](#ct-持续训练)
- [CD: 持续部署](#cd-持续部署)
- [GitHub Actions 实战](#github-actions-实战)
- [Kubeflow Pipelines](#kubeflow-pipelines)

---

## ML Pipeline 架构

### 整体架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        ML CI/CD Pipeline 架构                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   触发器                                                                    │
│   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐               │
│   │ Git Push │   │ Schedule │   │   Data   │   │  Drift   │               │
│   │  代码变更 │   │ 定时任务 │   │  Update  │   │  Alert   │               │
│   └─────┬────┘   └─────┬────┘   └─────┬────┘   └─────┬────┘               │
│         └──────────────┴──────────────┴──────────────┘                     │
│                                │                                           │
│   ┌────────────────────────────┼────────────────────────────┐              │
│   │                            ▼                            │              │
│   │   ┌────────────────────────────────────────────────┐    │              │
│   │   │              CI: 持续集成                       │    │              │
│   │   │  代码检查 → 数据验证 → 模型验证 → 集成测试     │    │              │
│   │   └────────────────────────┬───────────────────────┘    │              │
│   │                            │                            │              │
│   │                            ▼                            │              │
│   │   ┌────────────────────────────────────────────────┐    │              │
│   │   │              CT: 持续训练                       │    │              │
│   │   │  数据准备 → 特征工程 → 训练 → 评估 → 注册      │    │              │
│   │   └────────────────────────┬───────────────────────┘    │              │
│   │                            │                            │              │
│   │                            ▼                            │              │
│   │   ┌────────────────────────────────────────────────┐    │              │
│   │   │              CD: 持续部署                       │    │              │
│   │   │  打包 → 金丝雀 → A/B测试 → 全量 → 监控        │    │              │
│   │   └────────────────────────────────────────────────┘    │              │
│   │                                                         │              │
│   └─────────────────────────────────────────────────────────┘              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## CI: 持续集成

### ML 特有的测试

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           CI 三层测试                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 代码测试                                                               │
│   ─────────────                                                             │
│   • Linting (black, flake8)                                                │
│   • Type checking (mypy)                                                   │
│   • Unit tests (pytest)                                                    │
│                                                                             │
│   2. 数据测试                                                               │
│   ─────────────                                                             │
│   • Schema 验证 (字段类型、必填项)                                          │
│   • 统计检查 (分布、异常值)                                                 │
│   • 数据质量 (缺失率、重复率)                                               │
│                                                                             │
│   3. 模型测试                                                               │
│   ─────────────                                                             │
│   • 小规模训练测试 (能跑通)                                                 │
│   • 性能基准 (不低于阈值)                                                   │
│   • 推理测试 (输入输出正确)                                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 数据验证示例

```python
# scripts/validate_data.py
import pandas as pd
import pandera as pa
from pandera import Column, Check

# 定义数据 Schema
schema = pa.DataFrameSchema({
    "user_id": Column(int, Check.greater_than(0)),
    "age": Column(int, Check.in_range(0, 120)),
    "feature_1": Column(float, nullable=False),
    "label": Column(int, Check.isin([0, 1])),
})

def validate_training_data(path: str):
    df = pd.read_parquet(path)
    
    # Schema 验证
    schema.validate(df)
    
    # 统计检查
    assert df["label"].mean() > 0.01, "正样本比例过低"
    assert df.duplicated().mean() < 0.01, "重复率过高"
    
    print("✅ 数据验证通过")

if __name__ == "__main__":
    validate_training_data("data/train.parquet")
```

### 模型验证示例

```python
# scripts/validate_model.py
import torch

def validate_model_quick(config_path: str):
    """快速模型验证 - 小规模训练测试"""
    config = load_config(config_path)
    
    # 使用小数据集
    config["max_samples"] = 100
    config["max_steps"] = 10
    
    # 训练
    model = train(config)
    
    # 验证推理
    sample_input = get_sample_input()
    output = model(sample_input)
    
    assert output.shape == expected_shape, "输出形状错误"
    assert not torch.isnan(output).any(), "输出包含 NaN"
    
    print("✅ 模型验证通过")
```

---

## CT: 持续训练

### 训练触发条件

| 触发器 | 场景 | 示例 |
|--------|------|------|
| **定时** | 定期更新 | 每日凌晨重训 |
| **数据更新** | 新数据到达 | 增量数据触发 |
| **代码变更** | 模型改进 | PR 合并后 |
| **漂移告警** | 性能下降 | 检测到数据漂移 |
| **手动** | 紧急修复 | 手动触发 |

### 训练 Pipeline

```python
# training_pipeline.py
from prefect import flow, task

@task
def prepare_data(config):
    """数据准备"""
    df = load_data(config["data_path"])
    df = preprocess(df)
    return train_test_split(df)

@task
def train_model(train_data, config):
    """模型训练"""
    model = create_model(config)
    
    with mlflow.start_run():
        mlflow.log_params(config)
        model.fit(train_data)
        metrics = evaluate(model)
        mlflow.log_metrics(metrics)
        mlflow.pytorch.log_model(model, "model")
    
    return model, metrics

@task
def register_if_better(model, metrics, threshold):
    """条件注册"""
    if metrics["accuracy"] > threshold:
        mlflow.register_model(
            f"runs:/{mlflow.active_run().info.run_id}/model",
            "production-model"
        )
        return True
    return False

@flow
def training_pipeline(config):
    train_data, test_data = prepare_data(config)
    model, metrics = train_model(train_data, config)
    registered = register_if_better(model, metrics, config["threshold"])
    return registered
```

---

## CD: 持续部署

### 部署策略

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          部署策略对比                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 金丝雀部署 (Canary)                                                    │
│   ────────────────────────                                                  │
│   [Old: 95%] ─────────────────────────────▶ User                           │
│   [New: 5%]  ────▶                                                         │
│                                                                             │
│   • 小流量验证新模型                                                        │
│   • 监控指标，问题快速回滚                                                  │
│                                                                             │
│   2. A/B 测试                                                               │
│   ────────────────────────                                                  │
│   User Group A ──▶ [Model A]                                               │
│   User Group B ──▶ [Model B]                                               │
│                                                                             │
│   • 用户分组，对比效果                                                      │
│   • 统计显著性验证                                                          │
│                                                                             │
│   3. Shadow Mode                                                            │
│   ────────────────────────                                                  │
│   Request ──▶ [Production Model] ──▶ Response                              │
│           └─▶ [Shadow Model]    ──▶ (Log only)                             │
│                                                                             │
│   • 新模型不影响用户                                                        │
│   • 对比预测结果                                                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## GitHub Actions 实战

### 完整 ML CI/CD 配置

```yaml
# .github/workflows/ml-pipeline.yml
name: ML Pipeline

on:
  push:
    branches: [main]
  schedule:
    - cron: '0 2 * * *'  # 每日凌晨2点
  workflow_dispatch:

jobs:
  # ========== CI ==========
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-python@v4
        with:
          python-version: '3.10'
      
      - name: Install dependencies
        run: pip install -r requirements.txt
      
      - name: Lint
        run: black --check . && flake8 .
      
      - name: Unit tests
        run: pytest tests/unit -v
      
      - name: Data validation
        run: python scripts/validate_data.py
      
      - name: Model validation
        run: python scripts/validate_model.py

  # ========== CT ==========
  train:
    needs: test
    runs-on: [self-hosted, gpu]
    if: github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v3
      
      - name: Train
        run: python train.py --config configs/prod.yaml
        env:
          MLFLOW_TRACKING_URI: ${{ secrets.MLFLOW_URI }}
      
      - name: Evaluate
        run: python evaluate.py
      
      - name: Register model
        run: python scripts/register_model.py --stage staging

  # ========== CD ==========
  deploy-staging:
    needs: train
    runs-on: ubuntu-latest
    environment: staging
    steps:
      - name: Deploy to staging
        run: kubectl apply -f k8s/staging/
      
      - name: Integration tests
        run: pytest tests/integration -v

  deploy-production:
    needs: deploy-staging
    runs-on: ubuntu-latest
    environment: production
    steps:
      - name: Canary deploy (5%)
        run: kubectl apply -f k8s/canary/
      
      - name: Wait and monitor
        run: |
          sleep 600
          python scripts/check_canary_metrics.py
      
      - name: Full rollout
        run: kubectl apply -f k8s/production/
```

---

## Kubeflow Pipelines

### Pipeline 定义

```python
# kubeflow_pipeline.py
from kfp import dsl
from kfp.dsl import component, pipeline

@component(base_image="python:3.10")
def preprocess(input_path: str, output_path: str):
    import pandas as pd
    df = pd.read_parquet(input_path)
    df_processed = preprocess_func(df)
    df_processed.to_parquet(output_path)

@component(base_image="pytorch/pytorch:2.0.0-cuda11.7-cudnn8-runtime")
def train(data_path: str, model_path: str, lr: float, epochs: int):
    model = create_model()
    model = train_model(model, data_path, lr=lr, epochs=epochs)
    save_model(model, model_path)

@component
def evaluate(model_path: str, test_path: str) -> float:
    return evaluate_model(model_path, test_path)

@pipeline(name="ml-training")
def training_pipeline(input_data: str, lr: float = 1e-5, epochs: int = 3):
    preprocess_task = preprocess(
        input_path=input_data,
        output_path="/data/processed"
    )
    
    train_task = train(
        data_path=preprocess_task.outputs["output_path"],
        model_path="/models/latest",
        lr=lr,
        epochs=epochs
    ).set_gpu_limit(1)
    
    eval_task = evaluate(
        model_path=train_task.outputs["model_path"],
        test_path="/data/test"
    )
    
    # 条件部署
    with dsl.Condition(eval_task.output > 0.9):
        deploy(model_path=train_task.outputs["model_path"])

# 编译并提交
from kfp import compiler
compiler.Compiler().compile(training_pipeline, "pipeline.yaml")
```

---

## 最佳实践清单

| 阶段 | 检查项 |
|------|--------|
| **CI** | 代码 lint ✓, 单元测试 ✓, 数据验证 ✓, 模型验证 ✓ |
| **CT** | 版本记录 ✓, 指标跟踪 ✓, 模型注册 ✓ |
| **CD** | 金丝雀验证 ✓, 监控告警 ✓, 回滚机制 ✓ |

---

*下一篇：[07-模型监控](07-model-monitoring.md)*

*返回目录：[README](README.md)*

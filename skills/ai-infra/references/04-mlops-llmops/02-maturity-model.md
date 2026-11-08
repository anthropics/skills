# MLOps 成熟度模型

> 评估和提升 MLOps 能力的系统化框架，指引团队的进化路径。

## 目录

- [Google MLOps 成熟度等级](#google-mlops-成熟度等级)
- [Level 0: 手工流程](#level-0-手工流程)
- [Level 1: ML Pipeline 自动化](#level-1-ml-pipeline-自动化)
- [Level 2: CI/CD for ML](#level-2-cicd-for-ml)
- [成熟度评估方法](#成熟度评估方法)
- [提升策略](#提升策略)

---

## Google MLOps 成熟度等级

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      MLOps 成熟度三等级                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Level 2: CI/CD for ML ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 🏆      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  • 代码、数据、模型全部版本控制                                      │   │
│   │  • 自动化测试（代码+数据+模型）                                      │   │
│   │  • CI/CD Pipeline + 模型监控 + 自动重训练                           │   │
│   │  • 模型上线周期: 数天                                                │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Level 1: ML Pipeline ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 🥈      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  • 训练流程自动化                                                    │   │
│   │  • 实验跟踪和模型版本管理                                            │   │
│   │  • 持续训练 (CT)，模型上线周期: 数周                                │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Level 0: Manual ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 🥉      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  • 手动训练、手动部署、Jupyter 实验                                  │   │
│   │  • 缺乏版本控制，模型上线周期: 数月                                  │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 各等级关键指标

| 指标 | Level 0 | Level 1 | Level 2 |
|------|---------|---------|---------|
| **模型上线周期** | 数月 | 数周 | 数天 |
| **实验可复现性** | ❌ 困难 | ✅ 可复现 | ✅ 一键复现 |
| **部署自动化** | ❌ 手动 | ⚠️ 半自动 | ✅ 全自动 |
| **监控告警** | ❌ 无 | ⚠️ 基础 | ✅ 完善 |

---

## Level 0: 手工流程

### 典型特征

```python
# Level 0 反面示例 - 充满硬编码
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
import pickle

# 硬编码路径，无版本控制
df = pd.read_csv("/home/alice/data/train_final_FINAL.csv")

# 魔法数字，无记录
model = RandomForestClassifier(n_estimators=100, max_depth=10)
model.fit(X_train, y_train)

# 手动保存，文件名混乱
pickle.dump(model, open("model_good_v2.pkl", "wb"))
# 部署? 手动: scp model.pkl user@server:/models/
```

### 常见问题

- 😰 "上周效果好的模型用的什么参数？找不到了..."
- 😰 "这个模型是用哪版数据训练的？"
- 😰 "在我的机器上能跑啊..."

---

## Level 1: ML Pipeline 自动化

### 自动化训练流水线

```python
# Level 1: 自动化训练 + 实验跟踪
import mlflow
from prefect import flow, task

@task
def train_model(train_data, config: dict):
    """带实验跟踪的训练"""
    with mlflow.start_run():
        mlflow.log_params(config)
        
        model = create_model(config)
        model.fit(train_data)
        
        metrics = evaluate(model, val_data)
        mlflow.log_metrics(metrics)
        mlflow.sklearn.log_model(model, "model")
        
        return model, metrics

@task
def register_model(model, metrics, threshold=0.8):
    if metrics["accuracy"] > threshold:
        mlflow.register_model(
            f"runs:/{mlflow.active_run().info.run_id}/model",
            "production-model"
        )

@flow
def training_pipeline(config):
    data = load_data(config["data_path"])
    model, metrics = train_model(data, config)
    register_model(model, metrics)

# 可定时触发或事件触发
```

### 关键能力

- ✅ 训练流程可重复执行
- ✅ 实验参数和结果被追踪
- ✅ 模型版本化管理
- ⚠️ 部署仍需手动或半自动

---

## Level 2: CI/CD for ML

### 完整自动化流水线

```yaml
# .github/workflows/ml-cicd.yml
name: ML CI/CD Pipeline

on:
  push:
    branches: [main]
  schedule:
    - cron: '0 2 * * *'

jobs:
  # CI: 代码+数据+模型测试
  test:
    runs-on: ubuntu-latest
    steps:
      - name: Code quality
        run: |
          black --check . && flake8 . && pytest tests/
      - name: Data validation
        run: python scripts/validate_data.py
      - name: Model validation
        run: python scripts/validate_model.py

  # CT: 持续训练
  train:
    needs: test
    runs-on: [self-hosted, gpu]
    steps:
      - name: Train
        run: python train.py --config configs/prod.yaml
      - name: Register
        run: python scripts/register_model.py --stage staging

  # CD: 持续部署
  deploy:
    needs: train
    steps:
      - name: Canary deploy (5%)
        run: kubectl apply -f k8s/canary/
      - name: Monitor metrics
        run: python scripts/check_canary.py
      - name: Promote to production
        run: kubectl apply -f k8s/production/
```

### 监控与反馈闭环

```python
# 自动漂移检测和重训练触发
from evidently import Report
from evidently.metric_preset import DataDriftPreset

def check_and_trigger_retrain():
    """检测漂移并触发重训练"""
    report = Report(metrics=[DataDriftPreset()])
    report.run(reference_data=ref_df, current_data=prod_df)
    
    result = report.as_dict()
    if result['metrics'][0]['result']['dataset_drift']:
        trigger_retraining_pipeline()
        alert("Data drift detected, retraining triggered!")
```

---

## 成熟度评估方法

### 评估维度清单

| 维度 | Level 0 | Level 1 | Level 2 |
|------|---------|---------|---------|
| **数据管理** | 手动，无版本 | DVC/Delta，基础验证 | 自动管道，完整治理 |
| **实验管理** | Notebook | MLflow/W&B | 自动化实验，HPO |
| **模型管理** | 文件系统 | Model Registry | 血缘追踪，生命周期 |
| **部署** | 手动 | 脚本化 | CI/CD Pipeline |
| **测试** | 无测试 | 代码测试 | 全面测试 |
| **监控** | 无 | 基础系统监控 | 漂移检测，自动重训 |

### 快速评估脚本

```python
def assess_maturity(answers: dict) -> int:
    """评估 MLOps 成熟度等级"""
    score = 0
    
    # Level 1 能力
    if answers.get("experiment_tracking"): score += 1
    if answers.get("model_versioning"): score += 1
    if answers.get("automated_training"): score += 1
    
    # Level 2 能力
    if answers.get("automated_testing"): score += 1
    if answers.get("cicd_pipeline"): score += 1
    if answers.get("model_monitoring"): score += 1
    if answers.get("auto_retraining"): score += 1
    
    if score >= 5: return 2
    elif score >= 2: return 1
    else: return 0
```

---

## 提升策略

### Level 0 → Level 1

1. **引入实验跟踪** (1-2周)
   ```bash
   pip install mlflow
   mlflow ui --port 5000
   ```

2. **代码版本控制** - 将 Notebook 转为脚本

3. **建立 Model Registry**

### Level 1 → Level 2

1. **建立 CI/CD Pipeline** (2-4周)
2. **实现模型监控** - Evidently/WhyLogs
3. **自动化重训练触发**

### 渐进式投入建议

| 阶段 | 时间 | 重点投入 |
|------|------|----------|
| 快速见效 | 1-2周 | 实验跟踪 (MLflow/W&B) |
| 基础建设 | 2-4周 | Model Registry + 数据版本 |
| 自动化 | 4-8周 | CI/CD Pipeline |
| 完善 | 持续 | 监控告警 + 自动重训练 |

---

## 延伸阅读

- [Google MLOps Whitepaper](https://cloud.google.com/resources/mlops-whitepaper)
- [MLOps Maturity Model](https://ml-ops.org/content/mlops-principles)

---

*下一篇：[03-实验跟踪](03-experiment-tracking.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Microsoft.** *MLOps maturity model.*  
   https://learn.microsoft.com/en-us/azure/architecture/ai-ml/guide/mlops-maturity-model

2. **Google.** *MLOps Levels 0-2.*  
   https://cloud.google.com/architecture/mlops-continuous-delivery-and-automation-pipelines-in-machine-learning

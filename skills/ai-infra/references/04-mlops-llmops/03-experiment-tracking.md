# 实验跟踪

> 让每次实验都可追溯、可复现、可比较，是 MLOps 的基础能力。

## 目录

- [为什么需要实验跟踪](#为什么需要实验跟踪)
- [核心概念](#核心概念)
- [MLflow 详解](#mlflow-详解)
- [Weights & Biases](#weights--biases)
- [最佳实践](#最佳实践)
- [实战练习](#实战练习)

---

## 为什么需要实验跟踪

### 没有实验跟踪的痛点

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        实验跟踪解决的痛点                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│   😰 "上周那个效果好的模型用的什么超参数？"                                  │
│   😰 "这个模型是用哪个版本的数据训练的？"                                    │
│   😰 "为什么 A 同学和 B 同学的实验结果不一样？"                              │
│   😰 "哪个实验的效果最好？要翻100个 Notebook..."                            │
│                                                                             │
│   有了实验跟踪:                                                             │
│   ✅ 每次实验的超参数、指标、代码版本、数据版本全部记录                      │
│   ✅ 可视化对比不同实验                                                     │
│   ✅ 一键复现任何历史实验                                                   │
│   ✅ 团队协作、知识沉淀                                                     │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 核心概念

### 实验跟踪的组成

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        实验跟踪核心组件                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Experiment (实验)                                                         │
│   └── Run (运行)                                                            │
│       ├── Parameters (参数)    - 输入配置，如 learning_rate, batch_size    │
│       ├── Metrics (指标)       - 输出结果，如 accuracy, loss               │
│       ├── Artifacts (产物)     - 文件，如 model.pkl, config.yaml           │
│       ├── Tags (标签)          - 元信息，如 status, gpu_type               │
│       └── Source (来源)        - 代码版本、环境信息                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 需要记录什么

| 类别 | 内容 | 重要性 |
|------|------|--------|
| **参数** | 超参数、随机种子、配置 | ⭐⭐⭐ |
| **指标** | 训练/验证 loss, accuracy | ⭐⭐⭐ |
| **数据** | 数据版本、数据量、分布 | ⭐⭐⭐ |
| **模型** | 模型权重、架构描述 | ⭐⭐⭐ |
| **环境** | 依赖版本、GPU 型号 | ⭐⭐ |
| **代码** | Git commit, 代码diff | ⭐⭐ |

---

## MLflow 详解

### 基础使用

```python
import mlflow

# 设置实验名称
mlflow.set_experiment("llama-finetuning")

# 开始一次运行
with mlflow.start_run(run_name="lr_sweep_001"):
    # 1. 记录参数
    mlflow.log_params({
        "learning_rate": 1e-5,
        "batch_size": 32,
        "epochs": 3,
        "model": "llama-2-7b",
        "dataset": "alpaca-cleaned"
    })
    
    # 2. 训练循环中记录指标
    for epoch in range(3):
        train_loss = train_one_epoch(model, train_loader)
        val_loss, val_acc = evaluate(model, val_loader)
        
        mlflow.log_metrics({
            "train_loss": train_loss,
            "val_loss": val_loss,
            "val_accuracy": val_acc
        }, step=epoch)
    
    # 3. 保存模型
    mlflow.pytorch.log_model(model, "model")
    
    # 4. 保存额外文件
    mlflow.log_artifact("config.yaml")
    
    # 5. 添加标签
    mlflow.set_tag("status", "completed")
    mlflow.set_tag("gpu", "A100-80GB")
```

### 查询历史实验

```python
# 查询和比较实验
runs = mlflow.search_runs(
    experiment_names=["llama-finetuning"],
    filter_string="metrics.val_accuracy > 0.9",
    order_by=["metrics.val_accuracy DESC"]
)

# 显示最佳实验
print(runs[["params.learning_rate", "metrics.val_accuracy"]].head())

# 加载最佳模型
best_run_id = runs.iloc[0]["run_id"]
model = mlflow.pytorch.load_model(f"runs:/{best_run_id}/model")
```

### 启动 MLflow UI

```bash
# 启动本地 UI
mlflow ui --port 5000

# 使用远程 Tracking Server
mlflow.set_tracking_uri("http://mlflow-server:5000")
```

---

## Weights & Biases

### 基础使用

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
    
    # 记录生成样本 (W&B 强项: 丰富的可视化)
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

### W&B 特色功能

```python
# 1. 超参数扫描
sweep_config = {
    "method": "bayes",
    "metric": {"name": "val_loss", "goal": "minimize"},
    "parameters": {
        "learning_rate": {"min": 1e-6, "max": 1e-4, "distribution": "log_uniform_values"},
        "batch_size": {"values": [16, 32, 64]},
    }
}
sweep_id = wandb.sweep(sweep_config, project="my-project")
wandb.agent(sweep_id, function=train, count=20)

# 2. 实验比较
# 在 W&B 界面可以选择多个 run 进行可视化对比

# 3. 报告生成
# 支持生成可分享的实验报告
```

---

## 最佳实践

### 实验命名规范

```python
# ✅ 好的命名: 包含关键信息
run_name = f"llama7b_lr{lr}_bs{bs}_ep{epochs}_{datetime.now():%m%d_%H%M}"
# 示例: "llama7b_lr1e-5_bs32_ep3_0215_1430"

# ❌ 避免的命名
run_name = "test"
run_name = "experiment_1"
run_name = "final_final_v2"
```

### 记录 Checklist

```python
def log_experiment(config, model, metrics):
    """实验记录最佳实践"""
    with mlflow.start_run():
        # 1. 记录所有配置
        mlflow.log_params(config)
        
        # 2. 记录环境信息
        mlflow.log_param("python_version", sys.version)
        mlflow.log_param("torch_version", torch.__version__)
        mlflow.log_param("cuda_version", torch.version.cuda)
        mlflow.log_param("gpu_name", torch.cuda.get_device_name())
        
        # 3. 记录代码版本
        mlflow.log_param("git_commit", get_git_commit())
        
        # 4. 记录数据信息
        mlflow.log_param("data_version", config["data_version"])
        mlflow.log_param("train_size", len(train_dataset))
        
        # 5. 记录所有指标
        mlflow.log_metrics(metrics)
        
        # 6. 保存产物
        mlflow.log_artifact("config.yaml")
        mlflow.pytorch.log_model(model, "model")
        
        # 7. 添加有意义的标签
        mlflow.set_tag("status", "completed")
        mlflow.set_tag("team", "nlp")
```

### 团队协作规范

| 实践 | 说明 |
|------|------|
| **统一命名** | 实验名、指标名、参数名团队统一 |
| **完整记录** | 参数、指标、环境、随机种子 |
| **及时清理** | 删除失败/无用实验 |
| **添加标签** | 标记实验状态、GPU 类型、数据版本 |
| **写注释** | 在 run 添加说明，记录实验目的 |

---

## 实战练习

### 练习 1：MLflow 快速开始

```python
# mlflow_quickstart.py
import mlflow
import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.datasets import make_classification
from sklearn.model_selection import train_test_split

# 生成数据
X, y = make_classification(n_samples=1000, n_features=20)
X_train, X_test, y_train, y_test = train_test_split(X, y)

# 设置实验
mlflow.set_experiment("sklearn-quickstart")

# 超参数搜索
for C in [0.1, 1.0, 10.0]:
    with mlflow.start_run(run_name=f"C={C}"):
        # 记录参数
        mlflow.log_param("C", C)
        mlflow.log_param("solver", "lbfgs")
        
        # 训练
        model = LogisticRegression(C=C, solver="lbfgs")
        model.fit(X_train, y_train)
        
        # 记录指标
        train_acc = model.score(X_train, y_train)
        test_acc = model.score(X_test, y_test)
        
        mlflow.log_metrics({
            "train_accuracy": train_acc,
            "test_accuracy": test_acc
        })
        
        # 保存模型
        mlflow.sklearn.log_model(model, "model")
        
        print(f"C={C}: train_acc={train_acc:.4f}, test_acc={test_acc:.4f}")

# 启动 UI: mlflow ui --port 5000
```

### 练习 2：HuggingFace + W&B 集成

```python
# hf_wandb_training.py
import wandb
from transformers import (
    AutoModelForSequenceClassification,
    AutoTokenizer,
    Trainer,
    TrainingArguments
)

# W&B 自动集成
training_args = TrainingArguments(
    output_dir="./results",
    num_train_epochs=3,
    per_device_train_batch_size=16,
    evaluation_strategy="epoch",
    report_to="wandb",  # 自动集成 W&B
    run_name="bert-classification"
)

trainer = Trainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
    eval_dataset=eval_dataset,
)

trainer.train()
wandb.finish()
```

---

## 工具选择建议

| 场景 | 推荐工具 | 理由 |
|------|----------|------|
| **初创/小团队** | MLflow | 开源免费，自托管 |
| **快速实验** | W&B | UI 最佳，免费额度 |
| **企业级** | MLflow + 远程存储 | 可控，合规 |
| **深度学习** | W&B | 可视化强，HF 集成 |
| **传统 ML** | MLflow | sklearn 集成好 |

---

*下一篇：[04-模型版本管理](04-model-registry.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **MLflow Documentation.** *MLflow Tracking.*  
   https://mlflow.org/docs/latest/tracking.html

2. **Weights & Biases.** *W&B Experiment Tracking.*  
   https://wandb.ai/site/experiment-tracking

3. **Neptune.ai.** *Experiment Tracking for ML.*  
   https://neptune.ai/

# 什么是 MLOps

> MLOps = Machine Learning + DevOps + Data Engineering，将软件工程最佳实践应用于 ML 系统。

## 目录

- [MLOps 定义](#mlops-定义)
- [MLOps 的价值](#mlops-的价值)
- [MLOps 生命周期](#mlops-生命周期)
- [MLOps vs DevOps](#mlops-vs-devops)
- [MLOps 核心原则](#mlops-核心原则)
- [MLOps 技术债务](#mlops-技术债务)
- [实战练习](#实战练习)

---

## MLOps 定义

### 什么是 MLOps

MLOps 是一套将机器学习模型从实验环境可靠地部署到生产环境，并持续维护的实践、流程和工具集。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         MLOps = ML + DevOps + DataOps                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                        Machine Learning                              │   │
│   │   • 模型开发          • 特征工程                                     │   │
│   │   • 算法选择          • 超参数调优                                   │   │
│   │   • 模型评估          • 实验管理                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                         │
│                                    ▼                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                           MLOps                                      │   │
│   │   • 自动化训练流水线    • 模型版本管理                                │   │
│   │   • 持续集成/持续部署   • 模型监控与告警                              │   │
│   │   • A/B 测试           • 自动重训练                                  │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                    ▲                                         │
│                    ┌───────────────┴───────────────┐                        │
│                    │                               │                        │
│   ┌────────────────────────┐       ┌────────────────────────┐               │
│   │       DevOps           │       │       DataOps          │               │
│   │   • CI/CD              │       │   • 数据管道           │               │
│   │   • 基础设施即代码     │       │   • 数据质量           │               │
│   │   • 监控告警           │       │   • 数据版本管理       │               │
│   └────────────────────────┘       └────────────────────────┘               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 为什么需要 MLOps

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        没有 MLOps 的痛点                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   实验阶段                                                                  │
│   ─────────                                                                 │
│   😰 "上周那个效果好的模型用的什么超参数？找不到了..."                       │
│   😰 "这个模型是用哪个版本的数据训练的？"                                    │
│   😰 "为什么 A 同学的实验结果和 B 不一样？"                                  │
│                                                                             │
│   部署阶段                                                                  │
│   ─────────                                                                 │
│   😰 "模型怎么上线？手动拷贝到服务器？"                                      │
│   😰 "模型更新了怎么回滚？"                                                  │
│   😰 "怎么知道模型在生产中的效果？"                                          │
│                                                                             │
│   运维阶段                                                                  │
│   ─────────                                                                 │
│   😰 "模型效果突然变差了，什么原因？"                                        │
│   😰 "数据分布变了，需要重新训练，流程太长了..."                             │
│   😰 "半年后要复现这个实验，环境已经变了..."                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 业界现状

根据多项调查，ML 项目的现实情况：

| 统计数据 | 数值 | 来源 |
|----------|------|------|
| ML 项目无法进入生产 | 87% | VentureBeat |
| 从实验到生产的时间 | > 3 个月 | Algorithmia |
| 数据科学家花在数据准备的时间 | 45% | CrowdFlower |
| 模型首次部署后无人监控 | 60% | MLOps Community |

---

## MLOps 的价值

### 核心价值

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          MLOps 带来的核心价值                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  🔄 可复现性 (Reproducibility)                                       │   │
│   │                                                                     │   │
│   │  任何实验都能精确复现:                                               │   │
│   │  • 代码版本 (Git commit)                                            │   │
│   │  • 数据版本 (DVC/Delta Lake)                                        │   │
│   │  • 环境版本 (Docker/Conda)                                          │   │
│   │  • 超参数配置                                                        │   │
│   │  • 随机种子                                                          │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  ⚡ 效率 (Efficiency)                                                │   │
│   │                                                                     │   │
│   │  从数据到部署全流程自动化:                                           │   │
│   │  • 减少手动操作错误                                                  │   │
│   │  • 加速迭代周期                                                      │   │
│   │  • 团队可以专注于模型优化                                            │   │
│   │                                                                     │   │
│   │  传统方式: 数月上线     →     MLOps 方式: 数天上线                   │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  👁️ 可观测性 (Observability)                                        │   │
│   │                                                                     │   │
│   │  实时了解模型健康状态:                                               │   │
│   │  • 性能指标监控                                                      │   │
│   │  • 数据漂移检测                                                      │   │
│   │  • 异常告警                                                          │   │
│   │  • 快速定位问题                                                      │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  📜 治理 (Governance)                                                │   │
│   │                                                                     │   │
│   │  满足合规和审计需求:                                                 │   │
│   │  • 完整的审计追踪                                                    │   │
│   │  • 模型血缘关系                                                      │   │
│   │  • 访问控制                                                          │   │
│   │  • 合规报告                                                          │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 业务价值量化

```python
# MLOps ROI 计算示例
class MLOpsROI:
    def __init__(self):
        # 时间节省
        self.time_savings = {
            "experiment_setup": 0.8,      # 从 5 小时降到 1 小时
            "deployment_time": 0.9,       # 从 2 周降到 2 天
            "debugging_time": 0.6,        # 从 10 小时降到 4 小时
            "retraining_time": 0.7,       # 从 3 天降到 1 天
        }
        
        # 质量提升
        self.quality_improvements = {
            "deployment_failures": -0.5,   # 减少 50%
            "model_incidents": -0.4,       # 减少 40%
            "rollback_time": -0.8,         # 减少 80%
        }
        
        # 速度提升
        self.velocity_improvements = {
            "model_iteration_speed": 3.0,  # 3x 更快迭代
            "time_to_production": 4.0,     # 4x 更快上线
        }
    
    def calculate_annual_savings(
        self,
        team_size: int = 10,
        hourly_rate: float = 50,
        models_per_year: int = 20
    ) -> dict:
        """计算年度节省"""
        # 时间节省 (小时)
        hours_saved = (
            self.time_savings["experiment_setup"] * 5 * 100 +  # 100 次实验
            self.time_savings["deployment_time"] * 80 * models_per_year +
            self.time_savings["debugging_time"] * 10 * 50  # 50 次调试
        ) * team_size
        
        money_saved = hours_saved * hourly_rate
        
        return {
            "hours_saved_annually": hours_saved,
            "money_saved_annually": money_saved,
            "models_shipped_increase": self.velocity_improvements["time_to_production"]
        }

# 计算 ROI
roi = MLOpsROI()
savings = roi.calculate_annual_savings(team_size=10)
print(f"Annual hours saved: {savings['hours_saved_annually']}")
print(f"Annual cost savings: ${savings['money_saved_annually']:,.0f}")
```

---

## MLOps 生命周期

### 完整生命周期

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          MLOps 完整生命周期                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐      │
│   │  数据   │ → │  实验   │ → │  训练   │ → │  验证   │ → │  部署   │      │
│   │  准备   │   │  开发   │   │  管道   │   │  测试   │   │  服务   │      │
│   └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘   └────┬────┘      │
│        │             │             │             │             │            │
│        ▼             ▼             ▼             ▼             ▼            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                                                                     │   │
│   │   数据收集    特征工程    自动化训练   模型评估    金丝雀发布        │   │
│   │   数据验证    实验跟踪    超参调优     A/B 测试    滚动更新         │   │
│   │   数据版本    模型开发    分布式训练   性能测试    蓝绿部署         │   │
│   │                                                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│                         ┌──────────────────┐                               │
│                         │                  │                               │
│                         ▼                  │                               │
│                    ┌─────────┐             │                               │
│                    │  监控   │             │                               │
│                    │  反馈   │ ────────────┘                               │
│                    └─────────┘                                              │
│                         │                                                   │
│                         ▼                                                   │
│              性能监控 · 漂移检测 · 告警 · 自动重训练                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 各阶段详解

#### 1. 数据准备阶段

```python
# 数据验证示例 - 使用 Great Expectations
import great_expectations as ge

# 创建数据上下文
context = ge.get_context()

# 定义数据期望
expectations = {
    "user_features": [
        {"expectation_type": "expect_column_to_exist", "kwargs": {"column": "user_id"}},
        {"expectation_type": "expect_column_values_to_not_be_null", "kwargs": {"column": "user_id"}},
        {"expectation_type": "expect_column_values_to_be_between", 
         "kwargs": {"column": "age", "min_value": 0, "max_value": 120}},
    ]
}

# 运行验证
validator = context.get_validator(
    batch_request=batch_request,
    expectation_suite_name="user_features_suite"
)
results = validator.validate()

if not results.success:
    raise ValueError(f"Data validation failed: {results}")
```

#### 2. 实验开发阶段

```python
# 实验跟踪示例 - 使用 MLflow
import mlflow

mlflow.set_experiment("recommendation-system")

with mlflow.start_run(run_name="experiment_v1"):
    # 记录超参数
    mlflow.log_params({
        "learning_rate": 0.001,
        "batch_size": 256,
        "embedding_dim": 128,
        "num_epochs": 10
    })
    
    # 记录数据信息
    mlflow.log_param("data_version", "v2.3.1")
    mlflow.log_param("data_size", len(train_df))
    
    # 训练并记录指标
    for epoch in range(10):
        train_loss = train_epoch(model, train_loader)
        val_metrics = evaluate(model, val_loader)
        
        mlflow.log_metrics({
            "train_loss": train_loss,
            "val_auc": val_metrics["auc"],
            "val_accuracy": val_metrics["accuracy"]
        }, step=epoch)
    
    # 保存模型
    mlflow.pytorch.log_model(model, "model")
```

#### 3. 部署服务阶段

```yaml
# Kubernetes 部署示例
apiVersion: apps/v1
kind: Deployment
metadata:
  name: recommendation-model
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  template:
    spec:
      containers:
      - name: model-server
        image: myregistry/recommendation-model:v2.0
        resources:
          requests:
            memory: "4Gi"
            cpu: "2"
          limits:
            nvidia.com/gpu: 1
        env:
        - name: MODEL_VERSION
          value: "v2.0"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
```

---

## MLOps vs DevOps

### 关键差异对比

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         MLOps vs DevOps 对比                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   维度            DevOps                      MLOps                         │
│   ────            ──────                      ─────                         │
│                                                                             │
│   输入            代码                        代码 + 数据 + 模型            │
│                   ▪ 源代码                    ▪ 源代码                      │
│                                               ▪ 训练数据                    │
│                                               ▪ 模型权重                    │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   测试            功能测试                    功能 + 数据 + 模型测试        │
│                   ▪ 单元测试                  ▪ 单元测试                    │
│                   ▪ 集成测试                  ▪ 数据验证                    │
│                   ▪ E2E 测试                  ▪ 模型性能验证                │
│                                               ▪ 公平性测试                  │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   构建产物        应用程序                    模型文件 + 服务代码           │
│                   ▪ Docker 镜像               ▪ 模型权重文件                │
│                   ▪ 可执行文件                ▪ 推理服务镜像                │
│                                               ▪ 配置文件                    │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   部署策略        标准部署                    ML 特定部署                   │
│                   ▪ 滚动更新                  ▪ A/B 测试                    │
│                   ▪ 蓝绿部署                  ▪ Shadow Mode                 │
│                                               ▪ 金丝雀 + 指标验证           │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   监控            系统指标                    系统 + 模型指标               │
│                   ▪ CPU/内存/网络             ▪ 系统指标                    │
│                   ▪ 请求延迟                  ▪ 模型精度/召回               │
│                   ▪ 错误率                    ▪ 数据漂移                    │
│                                               ▪ 概念漂移                    │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   反馈循环        Bug 修复                    模型重训练                    │
│                   ▪ 代码修改                  ▪ 数据更新                    │
│                   ▪ 快速迭代                  ▪ 模型更新                    │
│                                               ▪ 触发条件复杂                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 数据是关键差异

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ML 系统的独特挑战 - 数据依赖                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统软件                         ML 系统                                  │
│   ─────────                        ───────                                  │
│                                                                             │
│   ┌─────────┐                      ┌─────────┐                              │
│   │  Code   │ ────▶ Output         │  Code   │                              │
│   └─────────┘                      └────┬────┘                              │
│                                         │                                   │
│   确定性:                               ▼                                   │
│   相同输入 → 相同输出             ┌─────────┐                              │
│                                   │  Data   │ ────▶ Model ────▶ Output     │
│                                   └─────────┘                              │
│                                                                             │
│                                   不确定性:                                 │
│                                   • 数据变化 → 模型行为变化                │
│                                   • 隐式依赖难以追踪                        │
│                                   • 反馈循环带来的漂移                      │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   Hidden Technical Debt in ML Systems (Google, 2015):                       │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                        ML Code (5%)                                  │   │
│   ├─────────────────────────────────────────────────────────────────────┤   │
│   │  Configuration │ Data Collection │ Feature Extraction │ ...         │   │
│   │  Data Verification │ Machine Resource Management │ Serving │ ...    │   │
│   │  Monitoring │ Process Management Tools │ ...                        │   │
│   │                                                                     │   │
│   │                    "Other Stuff" (95%)                              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## MLOps 核心原则

### 六大核心原则

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          MLOps 六大核心原则                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 版本控制一切 (Version Everything)                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   代码: Git                                                          │   │
│   │   数据: DVC, Delta Lake, LakeFS                                      │   │
│   │   模型: MLflow, W&B, HuggingFace Hub                                │   │
│   │   配置: Hydra, OmegaConf                                            │   │
│   │   环境: Docker, Conda                                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. 自动化流水线 (Automate Pipelines)                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   数据管道: Airflow, Prefect, Dagster                               │   │
│   │   训练管道: Kubeflow Pipelines, MLflow Pipelines                    │   │
│   │   部署管道: GitHub Actions, GitLab CI, Argo CD                      │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. 持续测试 (Continuous Testing)                                          │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   代码测试: pytest, unittest                                        │   │
│   │   数据测试: Great Expectations, Deequ                               │   │
│   │   模型测试: 性能基准、公平性测试、对抗测试                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   4. 实验跟踪 (Experiment Tracking)                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   记录: 参数、指标、模型、数据、环境                                 │   │
│   │   比较: 不同实验的可视化对比                                         │   │
│   │   复现: 任何实验可一键复现                                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   5. 模型监控 (Model Monitoring)                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   性能监控: 精度、延迟、吞吐量                                       │   │
│   │   漂移监控: 数据漂移、概念漂移                                       │   │
│   │   告警: 自动告警和问题定位                                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   6. 可复现性 (Reproducibility)                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   环境: Docker 镜像、依赖锁定                                        │   │
│   │   随机性: 固定随机种子                                               │   │
│   │   血缘: 模型到数据的完整追溯                                         │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 实现原则的代码示例

```python
# 综合示例：体现 MLOps 核心原则
import mlflow
import hashlib
import subprocess
from datetime import datetime

class MLOpsProject:
    """体现 MLOps 核心原则的项目结构"""
    
    def __init__(self, project_name: str):
        self.project_name = project_name
        
    def version_everything(self) -> dict:
        """原则1: 版本控制一切"""
        versions = {
            "code_version": subprocess.check_output(
                ["git", "rev-parse", "HEAD"]
            ).decode().strip(),
            "data_version": self._get_data_hash("data/train.parquet"),
            "env_version": self._get_env_hash(),
            "timestamp": datetime.now().isoformat()
        }
        return versions
    
    def _get_data_hash(self, path: str) -> str:
        """计算数据文件哈希"""
        with open(path, 'rb') as f:
            return hashlib.md5(f.read()).hexdigest()[:8]
    
    def _get_env_hash(self) -> str:
        """计算环境哈希"""
        with open("requirements.txt", 'r') as f:
            return hashlib.md5(f.read().encode()).hexdigest()[:8]
    
    def track_experiment(self, config: dict):
        """原则4: 实验跟踪"""
        versions = self.version_everything()
        
        with mlflow.start_run():
            # 记录版本信息
            mlflow.log_params(versions)
            
            # 记录配置
            mlflow.log_params(config)
            
            # 训练并记录
            model, metrics = self.train(config)
            mlflow.log_metrics(metrics)
            
            # 保存模型
            mlflow.pytorch.log_model(model, "model")
            
    def train(self, config: dict):
        """训练逻辑"""
        # 设置随机种子保证可复现性
        import torch
        import numpy as np
        import random
        
        seed = config.get("seed", 42)
        torch.manual_seed(seed)
        np.random.seed(seed)
        random.seed(seed)
        
        # ... 训练逻辑 ...
        
        return model, metrics
```

---

## MLOps 技术债务

### ML 系统的技术债务

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       ML 系统特有的技术债务                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 数据依赖债务                                                           │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 不稳定的数据依赖                                                 │   │
│   │   • 未声明的数据消费者                                               │   │
│   │   • 数据 Schema 变更                                                 │   │
│   │   • 训练-服务数据偏差 (Training-Serving Skew)                       │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. 实验债务                                                               │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 无法复现的实验                                                   │   │
│   │   • 遗失的超参数配置                                                 │   │
│   │   • 混乱的实验记录                                                   │   │
│   │   • 代码和模型版本不匹配                                             │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. 配置债务                                                               │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 硬编码的参数                                                     │   │
│   │   • 配置散落各处                                                     │   │
│   │   • 环境相关的配置泄露                                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   4. 反馈循环债务                                                           │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 模型影响自身训练数据                                             │   │
│   │   • 隐式的反馈循环                                                   │   │
│   │   • 慢反馈循环导致的问题积累                                         │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 解决技术债务的策略

```python
# 解决技术债务的代码示例

# 1. 使用配置管理解决配置债务
from dataclasses import dataclass
from omegaconf import OmegaConf

@dataclass
class TrainingConfig:
    """类型安全的配置"""
    learning_rate: float = 1e-4
    batch_size: int = 32
    num_epochs: int = 10
    model_name: str = "bert-base"
    seed: int = 42
    
# 从 YAML 加载
config = OmegaConf.structured(TrainingConfig)
config = OmegaConf.merge(config, OmegaConf.load("config.yaml"))

# 2. 使用数据契约解决数据依赖债务
from pandera import DataFrameSchema, Column, Check

user_schema = DataFrameSchema({
    "user_id": Column(int, Check.greater_than(0)),
    "age": Column(int, Check.in_range(0, 120)),
    "country": Column(str, Check.isin(["US", "UK", "CN", "JP"])),
})

# 验证数据
validated_df = user_schema.validate(df)

# 3. 记录数据血缘解决实验债务
class DataLineage:
    def __init__(self):
        self.lineage = {}
    
    def track(self, output_name: str, inputs: list, transformation: str):
        self.lineage[output_name] = {
            "inputs": inputs,
            "transformation": transformation,
            "timestamp": datetime.now().isoformat()
        }
    
    def get_lineage(self, name: str) -> dict:
        return self.lineage.get(name, {})
```

---

## 实战练习

### 练习 1：建立 MLOps 清单

创建一个团队 MLOps 检查清单：

```markdown
# MLOps 健康检查清单

## 版本控制
- [ ] 代码使用 Git 版本控制
- [ ] 数据有版本追踪机制
- [ ] 模型有版本和血缘信息
- [ ] 环境依赖被锁定

## 实验管理
- [ ] 所有实验都被跟踪记录
- [ ] 可以复现任何历史实验
- [ ] 实验结果可以比较

## 自动化
- [ ] 训练流程自动化
- [ ] 部署流程自动化
- [ ] 测试自动化

## 监控
- [ ] 模型性能被监控
- [ ] 数据质量被监控
- [ ] 有告警机制

## 文档
- [ ] 模型文档完整
- [ ] API 文档完整
- [ ] 运维手册完整
```

### 练习 2：评估团队 MLOps 成熟度

```python
# mlops_assessment.py
def assess_mlops_maturity(answers: dict) -> dict:
    """评估 MLOps 成熟度"""
    
    scores = {
        "level_0": 0,  # 手工流程
        "level_1": 0,  # 自动化训练
        "level_2": 0,  # CI/CD for ML
    }
    
    # Level 0 评估
    if answers.get("manual_training", True):
        scores["level_0"] += 1
    if answers.get("jupyter_experiments", True):
        scores["level_0"] += 1
    if not answers.get("version_control", False):
        scores["level_0"] += 1
        
    # Level 1 评估
    if answers.get("automated_training", False):
        scores["level_1"] += 1
    if answers.get("experiment_tracking", False):
        scores["level_1"] += 1
    if answers.get("model_registry", False):
        scores["level_1"] += 1
        
    # Level 2 评估
    if answers.get("automated_testing", False):
        scores["level_2"] += 1
    if answers.get("automated_deployment", False):
        scores["level_2"] += 1
    if answers.get("model_monitoring", False):
        scores["level_2"] += 1
    if answers.get("auto_retraining", False):
        scores["level_2"] += 1
    
    # 确定当前等级
    if scores["level_2"] >= 3:
        current_level = 2
    elif scores["level_1"] >= 2:
        current_level = 1
    else:
        current_level = 0
    
    return {
        "current_level": current_level,
        "scores": scores,
        "recommendations": get_recommendations(current_level)
    }

def get_recommendations(level: int) -> list:
    """获取提升建议"""
    recommendations = {
        0: [
            "开始使用 Git 进行代码版本控制",
            "引入 MLflow 或 W&B 进行实验跟踪",
            "将 Notebook 转换为可复现的脚本"
        ],
        1: [
            "建立自动化测试流程",
            "实现 CI/CD Pipeline",
            "引入模型监控"
        ],
        2: [
            "优化监控告警体系",
            "实现自动化重训练",
            "完善文档和治理"
        ]
    }
    return recommendations.get(level, [])
```

---

## 延伸阅读

### 经典论文

- [Hidden Technical Debt in Machine Learning Systems](https://papers.nips.cc/paper/5656-hidden-technical-debt-in-machine-learning-systems) - Google, 2015
- [Challenges in Deploying Machine Learning](https://arxiv.org/abs/2011.09926) - 2020

### 推荐资源

- [Google MLOps Whitepaper](https://cloud.google.com/resources/mlops-whitepaper)
- [MLOps Principles](https://ml-ops.org/content/mlops-principles)
- [Made With ML](https://madewithml.com/)

---

*下一篇：[02-成熟度模型](02-maturity-model.md)*

*返回目录：[README](README.md)*

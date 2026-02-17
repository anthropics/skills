# 模型版本管理

> Model Registry 是模型的"仓库"，管理模型从开发到生产的全生命周期。

## 目录

- [为什么需要 Model Registry](#为什么需要-model-registry)
- [核心概念](#核心概念)
- [MLflow Model Registry](#mlflow-model-registry)
- [HuggingFace Hub](#huggingface-hub)
- [最佳实践](#最佳实践)

---

## 为什么需要 Model Registry

### 模型管理的挑战

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     没有 Model Registry 的混乱                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   文件系统:                                                                 │
│   /models/                                                                  │
│   ├── model.pkl                # 哪个版本？                                │
│   ├── model_v2.pkl             # v2 是什么？                               │
│   ├── model_good.pkl           # "good" 是谁定义的？                       │
│   ├── model_final.pkl          # 真的是 final 吗？                         │
│   ├── model_final_v2.pkl       # ...                                       │
│   ├── model_final_FINAL.pkl    # 😱                                        │
│   └── model_alice_0215.pkl     # Alice 的实验？                            │
│                                                                             │
│   常见问题:                                                                 │
│   • 哪个模型在生产环境？                                                    │
│   • 这个模型是用什么数据训练的？                                            │
│   • 如何快速回滚到上个版本？                                                │
│   • 谁在什么时候修改了模型？                                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 核心概念

### Model Registry 架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      Model Registry 核心功能                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                      Model Registry                                  │   │
│   │                                                                     │   │
│   │   Model: llama-chat                                                 │   │
│   │   ├── Version 1.0 (Archived)                                        │   │
│   │   │   ├── Artifacts: model.safetensors                              │   │
│   │   │   ├── Metrics: accuracy=0.82                                    │   │
│   │   │   └── Source: run_abc123                                        │   │
│   │   │                                                                 │   │
│   │   ├── Version 2.0 (Staging)                                         │   │
│   │   │   ├── Artifacts: model.safetensors                              │   │
│   │   │   ├── Metrics: accuracy=0.88                                    │   │
│   │   │   └── Source: run_def456                                        │   │
│   │   │                                                                 │   │
│   │   └── Version 3.0 (Production) ⭐                                   │   │
│   │       ├── Artifacts: model.safetensors                              │   │
│   │       ├── Metrics: accuracy=0.92                                    │   │
│   │       └── Source: run_xyz789                                        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   核心能力:                                                                 │
│   • 版本化存储                • 阶段管理 (Staging → Production)            │
│   • 血缘追踪 (Lineage)       • 访问控制和审计                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 模型生命周期

```
实验 → 注册 → Staging → Production → Archived
 │       │        │          │           │
 └─────────────────────────────────────────┘
              血缘追踪
```

---

## MLflow Model Registry

### 注册模型

```python
import mlflow
from mlflow.tracking import MlflowClient

client = MlflowClient()

# 方式1: 从 Run 注册
with mlflow.start_run() as run:
    # 训练并保存模型
    mlflow.pytorch.log_model(model, "model")
    
    # 注册到 Registry
    model_uri = f"runs:/{run.info.run_id}/model"
    mlflow.register_model(model_uri, "llama-chat")

# 方式2: 直接从 URI 注册
mlflow.register_model(
    model_uri="runs:/abc123/model",
    name="llama-chat"
)
```

### 阶段管理 (Alias-based，MLflow 2.9+)

```python
# 使用 Model Aliases (推荐，替代已废弃的 Stage API)
# 设置别名
client.set_registered_model_alias("llama-chat", "champion", 3)
client.set_registered_model_alias("llama-chat", "challenger", 4)

# 通过别名加载模型
model = mlflow.pytorch.load_model("models:/llama-chat@champion")

# 删除别名
client.delete_registered_model_alias("llama-chat", "challenger")

# 加载特定版本
model = mlflow.pytorch.load_model("models:/llama-chat/3")
```

### 添加描述和标签

```python
# 更新模型版本描述
client.update_model_version(
    name="llama-chat",
    version="3",
    description="Fine-tuned on DPO with ultrachat dataset"
)

# 设置标签
client.set_model_version_tag(
    name="llama-chat",
    version="3",
    key="validation_status",
    value="approved"
)
```

---

## HuggingFace Hub

### 上传模型

```python
from huggingface_hub import HfApi, login

# 登录
login(token="hf_xxx")

api = HfApi()

# 上传文件夹
api.upload_folder(
    folder_path="./my-model",
    repo_id="myorg/llama-finetuned",
    repo_type="model",
    commit_message="Upload finetuned model v1.0"
)

# 使用 transformers 直接上传
model.push_to_hub("myorg/llama-finetuned")
tokenizer.push_to_hub("myorg/llama-finetuned")
```

### Model Card

```markdown
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

## Training
- Base model: meta-llama/Llama-2-7b
- Dataset: alpaca
- Learning rate: 1e-5

## Evaluation
| Metric | Score |
|--------|-------|
| MMLU   | 0.52  |
```

### 下载和使用

```python
from transformers import AutoModelForCausalLM, AutoTokenizer

# 下载模型
model = AutoModelForCausalLM.from_pretrained(
    "myorg/llama-finetuned",
    revision="v1.0"  # 指定版本
)
tokenizer = AutoTokenizer.from_pretrained("myorg/llama-finetuned")
```

---

## 最佳实践

### 版本命名规范

```
模型名称: {用途}-{基座模型}-{版本}
示例: chat-llama2-7b-v1.0

版本号: 语义化版本 (SemVer)
- MAJOR: 架构变化
- MINOR: 训练改进
- PATCH: Bug 修复
```

### 模型元数据模板

```python
model_metadata = {
    # 基本信息
    "name": "chat-llama2-7b",
    "version": "1.0.0",
    "description": "Chat model fine-tuned on DPO",
    
    # 训练信息
    "base_model": "meta-llama/Llama-2-7b",
    "training_data": "ultrachat",
    "training_date": "2024-02-15",
    
    # 性能指标
    "metrics": {
        "mmlu": 0.52,
        "hellaswag": 0.78,
        "latency_ms": 45
    },
    
    # 血缘
    "source_run_id": "abc123",
    "git_commit": "def456",
    "data_version": "v2.0"
}
```

### 审批流程

```python
def promote_model(model_name: str, version: str):
    """模型上线审批流程"""
    client = MlflowClient()
    
    # 1. 检查必要标签
    tags = client.get_model_version(model_name, version).tags
    required_tags = ["validation_status", "reviewed_by"]
    
    for tag in required_tags:
        if tag not in tags:
            raise ValueError(f"Missing required tag: {tag}")
    
    # 2. 检查审批状态
    if tags.get("validation_status") != "approved":
        raise ValueError("Model not approved")
    
    # 3. 转换到生产
    client.transition_model_version_stage(
        name=model_name,
        version=version,
        stage="Production",
        archive_existing_versions=True
    )
    
    # 4. 记录审计日志
    log_audit(f"Model {model_name} v{version} promoted to Production")
```

---

## 工具对比

| 特性 | MLflow Registry | HuggingFace Hub |
|------|-----------------|-----------------|
| **部署方式** | 自托管/云 | SaaS |
| **集成** | MLflow 生态 | transformers 生态 |
| **版本管理** | 阶段+版本号 | Git-based |
| **访问控制** | 需配置 | 内置 |
| **社区** | 企业级 | 开源社区 |
| **最适合** | 企业私有模型 | 开源模型分享 |

---

*下一篇：[05-特征工程平台](05-feature-store.md)*

*返回目录：[README](README.md)*

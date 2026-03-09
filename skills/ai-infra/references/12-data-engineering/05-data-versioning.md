# 数据版本管理

> 代码有 Git，数据也需要版本管理——可复现的训练实验，始于可追溯的数据集。

## 目录

- [为什么需要数据版本管理](#为什么需要数据版本管理)
- [DVC (Data Version Control)](#dvc-data-version-control)
- [LakeFS](#lakefs)
- [数据血缘追踪](#数据血缘追踪)
- [可复现训练](#可复现训练)
- [延伸阅读](#延伸阅读)

---

## 为什么需要数据版本管理

```
没有数据版本管理时:
  "上周的模型效果更好？用的什么数据？" → 不知道
  "数据集被谁改过？改了什么？" → 无法追溯
  "能复现3个月前的训练结果吗？" → 做不到

有了数据版本管理:
  ✓ 每次数据变更有记录（谁/什么时候/改了什么）
  ✓ 任何历史版本可回溯
  ✓ 训练实验与数据版本绑定
  ✓ 多团队协作不冲突
```

---

## DVC (Data Version Control)

```bash
# DVC — 数据版本管理（Git for Data）

# 安装
pip install dvc dvc-s3

# 初始化（在 Git 仓库中）
dvc init

# 配置远程存储
dvc remote add -d myremote s3://my-bucket/dvc-cache

# 追踪数据集
dvc add training_data/
# 生成: training_data.dvc (元数据文件, 加入 Git)
# 实际数据上传到 S3

# 版本管理
git add training_data.dvc .gitignore
git commit -m "Add training data v1"
git tag data-v1

# 更新数据集
# (修改 training_data/ 中的内容)
dvc add training_data/
git add training_data.dvc
git commit -m "Update training data v2 - add code data"
git tag data-v2

# 切换版本
git checkout data-v1
dvc checkout  # 下载 v1 的数据

# 查看数据变更
dvc diff data-v1 data-v2
```

### DVC 管线 (Pipeline)

```yaml
# dvc.yaml — 定义数据处理管线
stages:
  download:
    cmd: python scripts/download_data.py
    outs:
      - data/raw/
  
  clean:
    cmd: python scripts/clean_data.py
    deps:
      - data/raw/
      - scripts/clean_data.py
    outs:
      - data/cleaned/
  
  dedup:
    cmd: python scripts/dedup_data.py
    deps:
      - data/cleaned/
    outs:
      - data/deduped/
  
  tokenize:
    cmd: python scripts/tokenize_data.py
    deps:
      - data/deduped/
    params:
      - tokenizer_name
      - max_length
    outs:
      - data/tokenized/
    metrics:
      - metrics/data_stats.json
```

```bash
# 运行管线
dvc repro

# 查看管线 DAG
dvc dag
```

---

## LakeFS

```
LakeFS — Git-like 数据湖版本管理:

  与 DVC 的区别:
    DVC: 文件级版本管理，与 Git 配合
    LakeFS: 数据湖级版本管理，Git 接口操作对象存储

  核心概念:
    Repository: 对应一个数据湖
    Branch: 数据的分支（如 main, staging, dev）
    Commit: 数据的快照
    Merge: 合并数据变更

  适用: 大规模数据湖管理，PB 级数据
```

```bash
# LakeFS 基本操作

# 创建仓库
lakectl repo create lakefs://ai-training s3://ai-data-lake

# 创建分支
lakectl branch create lakefs://ai-training/experiment-v2 \
    --source lakefs://ai-training/main

# 上传数据
lakectl fs upload lakefs://ai-training/experiment-v2/data/ \
    --source /local/new_data/

# 提交
lakectl commit lakefs://ai-training/experiment-v2 \
    -m "Add new training data from Common Crawl 2024-01"

# 合并到 main
lakectl merge lakefs://ai-training/experiment-v2 \
    lakefs://ai-training/main

# 数据快照（用于训练）
lakectl commit lakefs://ai-training/main \
    -m "Training data snapshot for run-2024-01-15"
```

---

## 数据血缘追踪

```
数据血缘 (Data Lineage):

  追踪数据从源头到最终使用的完整路径

  原始数据 (Common Crawl Jan 2024)
       │
       ▼ [清洗脚本 v2.1, 参数: min_length=100]
  清洗后数据 (350 GB)
       │
       ▼ [去重: MinHash, threshold=0.8]
  去重后数据 (280 GB)
       │
       ▼ [Tokenizer: Llama 3 BPE, max_len=8192]
  训练数据 (150 GB tokenized)
       │
       ▼ [训练: Llama 7B, lr=2e-5, batch=256]
  模型 checkpoint step-50000

  价值:
    ✓ 模型效果不好 → 追溯到数据问题
    ✓ 数据合规审计 → 追踪数据来源
    ✓ 复现训练 → 完整的管线记录
```

---

## 可复现训练

```python
"""训练可复现性配置"""

class ReproducibleTrainingConfig:
    """确保训练可复现的配置"""
    
    def __init__(self):
        self.data = {
            "dataset_version": "data-v2.3",       # DVC tag
            "dataset_commit": "abc123...",          # Git commit
            "data_hash": "sha256:def456...",        # 数据哈希
            "preprocessing_script": "clean_v2.1.py",
            "tokenizer": "meta-llama/Llama-3.1-8B",
        }
        self.training = {
            "seed": 42,
            "model": "meta-llama/Llama-3.1-8B",
            "learning_rate": 2e-5,
            "batch_size": 256,
            "max_steps": 100000,
            "framework": "transformers==4.40.0",
            "deepspeed_config": "ds_config_z3.json",
        }
        self.environment = {
            "cuda_version": "12.4",
            "torch_version": "2.3.0",
            "nccl_version": "2.21.5",
            "gpu_type": "H100",
            "num_gpus": 64,
        }
    
    def save(self, path: str):
        """保存训练配置（与 Git 版本绑定）"""
        import json
        with open(path, 'w') as f:
            json.dump({
                "data": self.data,
                "training": self.training,
                "environment": self.environment,
            }, f, indent=2)
```

---

## 延伸阅读

- [DVC Documentation](https://dvc.org/doc)
- [LakeFS Documentation](https://docs.lakefs.io/)
- [MLflow Data Tracking](https://mlflow.org/docs/latest/tracking.html)
- [Weights & Biases Artifacts](https://docs.wandb.ai/guides/artifacts)

---

*上一篇：[04-synthetic-data.md](04-synthetic-data.md)* | *下一篇：[06-data-compliance.md](06-data-compliance.md)*

*返回：[README.md](README.md) - 章节索引*

# 模型仓库

> 模型仓库是 AI 团队的"模型图书馆"——管理模型的版本、分发、缓存和访问控制，是 AI 工程化的关键基础设施。

## 目录

- [为什么需要模型仓库](#为什么需要模型仓库)
- [HuggingFace Hub 架构](#huggingface-hub-架构)
- [Model Registry 设计](#model-registry-设计)
- [模型分发与缓存](#模型分发与缓存)
- [大模型存储策略](#大模型存储策略)
- [自建模型仓库方案](#自建模型仓库方案)
- [延伸阅读](#延伸阅读)

---

## 为什么需要模型仓库

### 生活类比：软件应用商店

```
模型仓库 = AI 世界的 App Store:

  没有模型仓库:
    "模型在哪个服务器上？" → 到处找
    "这个模型是哪个版本？" → 不确定
    "我能用这个模型吗？" → 不知道许可证
    "怎么下载 405B 的模型？" → 800GB 下不动

  有了模型仓库:
    ✓ 统一的模型目录和搜索
    ✓ 版本管理（每次训练/微调产出新版本）
    ✓ 模型卡片（参数、性能、许可证、用法）
    ✓ 高效分发（断点续传、CDN 加速、P2P）
    ✓ 访问控制（谁能看、谁能用、谁能改）
```

### 模型仓库的核心功能

```
┌─────────────────────────────────────────────────────────────────┐
│                 模型仓库核心功能                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 模型存储与版本管理                                            │
│     Git LFS + 大文件存储                                        │
│     版本标签 (v1.0, v1.1-sft, v2.0-rlhf)                       │
│     分支管理 (main, dev, experiment-lora)                        │
│                                                                 │
│  2. 模型元数据                                                   │
│     Model Card: 模型描述、训练细节、评估结果                     │
│     Config: 模型架构配置 (config.json)                           │
│     许可证: Apache 2.0, Llama License, etc.                     │
│                                                                 │
│  3. 模型分发                                                     │
│     HTTP 下载 + CDN 加速                                        │
│     断点续传                                                     │
│     分片下载（大模型拆分为多个文件）                             │
│     P2P 分发（集群内共享）                                       │
│                                                                 │
│  4. 模型推理 API                                                 │
│     Inference API / Endpoints                                   │
│     模型即服务 (Model as a Service)                               │
│                                                                 │
│  5. 社区协作                                                     │
│     模型讨论、Pull Request                                      │
│     数据集关联、Space 应用                                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## HuggingFace Hub 架构

### 核心组件

```
HuggingFace Hub 架构:

  ┌──────────────────────────────────────────────────┐
  │                   Web Frontend                    │
  │            (模型搜索/浏览/Model Card)              │
  └───────────────────┬──────────────────────────────┘
                      │
  ┌───────────────────▼──────────────────────────────┐
  │                    API Layer                       │
  │     (REST API + huggingface_hub Python SDK)       │
  └───────────────────┬──────────────────────────────┘
                      │
        ┌─────────────┼─────────────┐
        │             │             │
  ┌─────▼─────┐ ┌─────▼─────┐ ┌─────▼─────┐
  │ Git Server │ │ LFS Store │ │ Metadata  │
  │ (元数据,   │ │ (大文件,  │ │ (搜索,    │
  │  config,   │ │  权重,    │ │  标签,    │
  │  tokenizer)│ │  safetensor│ │  统计)   │
  └───────────┘ └───────────┘ └───────────┘

  文件存储格式:
    模型权重: safetensors (推荐) / pytorch_bin
    配置: config.json, tokenizer.json
    文档: README.md (Model Card)
    量化: GGUF, GPTQ, AWQ 格式
```

### 使用 HuggingFace Hub

```python
"""HuggingFace Hub 常用操作"""
from huggingface_hub import (
    HfApi, hf_hub_download, snapshot_download,
    login, create_repo, upload_folder,
)

# 1. 下载模型（带缓存）
model_path = snapshot_download(
    repo_id="meta-llama/Llama-3.1-70B-Instruct",
    cache_dir="/nvme/hf-cache",
    # 只下载 safetensors 格式
    allow_patterns=["*.safetensors", "*.json", "tokenizer*"],
    # 排除不需要的文件
    ignore_patterns=["*.bin", "*.h5"],
)

# 2. 下载单个文件
file_path = hf_hub_download(
    repo_id="meta-llama/Llama-3.1-70B-Instruct",
    filename="config.json",
    cache_dir="/nvme/hf-cache",
)

# 3. 上传微调后的模型
api = HfApi()
login(token="hf_xxx")

# 创建仓库
create_repo("my-org/llama-3.1-70b-sft-v1", private=True)

# 上传模型文件
upload_folder(
    folder_path="/output/sft-model",
    repo_id="my-org/llama-3.1-70b-sft-v1",
    commit_message="Upload SFT model v1",
)

# 4. 管理缓存
from huggingface_hub import scan_cache_dir
cache_info = scan_cache_dir("/nvme/hf-cache")
print(f"缓存大小: {cache_info.size_on_disk_str}")
print(f"缓存仓库数: {len(cache_info.repos)}")
```

---

## Model Registry 设计

### 企业级 Model Registry

```
┌─────────────────────────────────────────────────────────────────┐
│              企业级 Model Registry 架构                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  与 HuggingFace Hub 的区别:                                      │
│    HF Hub: 公共社区平台，适合开源分享                            │
│    Model Registry: 企业内部平台，强调管控和审计                  │
│                                                                 │
│  核心功能:                                                       │
│    ┌──────────────────────────────────────────────┐              │
│    │  模型生命周期管理                             │              │
│    │                                              │              │
│    │  开发 → 测试 → 预发布 → 生产 → 归档           │              │
│    │   ▲      ▲       ▲       ▲      ▲            │              │
│    │   │      │       │       │      │            │              │
│    │  代码    单元    集成    金丝雀  版本           │              │
│    │  审查    测试    测试    发布    管理           │              │
│    └──────────────────────────────────────────────┘              │
│                                                                 │
│  关键能力:                                                       │
│    版本管理: 语义化版本号 + 训练谱系追踪                         │
│    访问控制: RBAC（谁能训练、谁能部署、谁能查看）                │
│    审计日志: 所有操作可追溯                                      │
│    合规检查: 自动安全评估、偏见检测                               │
│    A/B 测试: 多版本并行部署对比                                  │
│                                                                 │
│  实现方案:                                                       │
│    MLflow Model Registry (开源)                                  │
│    Weights & Biases Model Registry                               │
│    AWS SageMaker Model Registry                                  │
│    自建 (API + 对象存储 + 数据库)                                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### MLflow Model Registry 使用

```python
"""MLflow Model Registry 使用示例"""
import mlflow
from mlflow.tracking import MlflowClient

# 配置
mlflow.set_tracking_uri("http://mlflow-server:5000")
client = MlflowClient()

# 1. 注册模型
with mlflow.start_run():
    # 记录训练参数
    mlflow.log_params({
        "model": "llama-3.1-70b",
        "method": "sft",
        "lr": 2e-5,
        "epochs": 3,
    })
    
    # 记录评估指标
    mlflow.log_metrics({
        "mmlu": 0.82,
        "humaneval": 0.45,
        "truthfulqa": 0.71,
    })
    
    # 注册模型
    mlflow.pytorch.log_model(
        model,
        artifact_path="model",
        registered_model_name="llama-3.1-70b-sft",
    )

# 2. 模型版本管理
# 将模型推进到 Staging
client.transition_model_version_stage(
    name="llama-3.1-70b-sft",
    version=3,
    stage="Staging",
)

# 推进到 Production
client.transition_model_version_stage(
    name="llama-3.1-70b-sft",
    version=3,
    stage="Production",
)

# 3. 加载生产模型
model_uri = "models:/llama-3.1-70b-sft/Production"
model = mlflow.pytorch.load_model(model_uri)
```

---

## 模型分发与缓存

### 大模型分发挑战

```
分发 405B 模型到 100 个推理节点:

  问题:
    模型大小: ~800 GB (FP16)
    100 节点同时下载: 800 GB × 100 = 80 TB 网络流量
    单节点下载速度: ~1 GB/s → 需要 ~13 分钟
    所有节点同时下: 网络拥塞，实际可能需要 1 小时+

  解决方案:
  ┌──────────────────────────────────────────────┐
  │  方案 1: CDN / 分布式缓存                     │
  │    源站 → CDN 节点 → 本地节点                 │
  │    首次慢，后续从 CDN 缓存取                  │
  │                                              │
  │  方案 2: P2P 分发 (BitTorrent-like)           │
  │    种子节点下载 → 边下边传给其他节点           │
  │    理论速度: O(log N)                         │
  │    100 节点: 7 轮传播即可全部完成              │
  │                                              │
  │  方案 3: 共享存储预加载                        │
  │    模型放在共享 Lustre/GPFS 上                 │
  │    所有节点直接读取（mmap）                    │
  │    需要足够的存储带宽                          │
  │                                              │
  │  方案 4: 本地 NVMe 缓存                       │
  │    首次下载到本地 NVMe                         │
  │    后续从本地加载（6-14 GB/s）                 │
  │    模型更新时增量同步                          │
  └──────────────────────────────────────────────┘
```

### 缓存策略

```python
"""模型缓存管理"""
import os
import hashlib
from pathlib import Path

class ModelCacheManager:
    """本地模型缓存管理器"""
    
    def __init__(self, cache_dir: str = "/nvme/model-cache", max_size_gb: int = 500):
        self.cache_dir = Path(cache_dir)
        self.max_size_gb = max_size_gb
        self.cache_dir.mkdir(parents=True, exist_ok=True)
    
    def get_model_path(self, model_id: str, version: str = "latest") -> Path:
        """获取模型本地缓存路径"""
        cache_key = hashlib.md5(f"{model_id}:{version}".encode()).hexdigest()[:12]
        return self.cache_dir / cache_key
    
    def is_cached(self, model_id: str, version: str = "latest") -> bool:
        """检查模型是否已缓存"""
        path = self.get_model_path(model_id, version)
        return path.exists() and any(path.iterdir())
    
    def get_cache_size_gb(self) -> float:
        """获取当前缓存大小"""
        total = sum(f.stat().st_size for f in self.cache_dir.rglob('*') if f.is_file())
        return total / (1024 ** 3)
    
    def evict_lru(self):
        """LRU 清理策略"""
        if self.get_cache_size_gb() <= self.max_size_gb:
            return
        
        # 按最后访问时间排序
        cached_models = sorted(
            self.cache_dir.iterdir(),
            key=lambda p: p.stat().st_atime,
        )
        
        # 删除最旧的，直到空间足够
        while self.get_cache_size_gb() > self.max_size_gb * 0.8:
            if not cached_models:
                break
            oldest = cached_models.pop(0)
            import shutil
            shutil.rmtree(oldest)
            print(f"Evicted: {oldest.name}")
```

---

## 大模型存储策略

### 模型文件格式

| 格式 | 特点 | 适用场景 |
|------|------|---------|
| **safetensors** | 安全、快速加载、支持 mmap | 推荐默认格式 |
| **pytorch_bin** | PyTorch 原生，pickle 序列化 | 传统兼容 |
| **GGUF** | llama.cpp 专用，含量化信息 | 端侧/CPU 推理 |
| **GPTQ/AWQ** | 量化格式 | GPU 量化推理 |
| **ONNX** | 跨框架通用 | 跨平台部署 |

### safetensors 优势

```python
"""safetensors vs pytorch_bin 对比"""
from safetensors.torch import save_file, load_file
import torch
import time

# safetensors 优势:
# 1. 安全: 不使用 pickle，避免代码注入攻击
# 2. 快速: 支持 mmap，零拷贝加载
# 3. 并行: 支持多线程加载

# 保存
tensors = {"weight": torch.randn(4096, 4096)}
save_file(tensors, "model.safetensors")

# 加载（零拷贝 mmap）
start = time.time()
loaded = load_file("model.safetensors", device="cpu")
print(f"safetensors 加载: {time.time() - start:.3f}s")

# 对比 pytorch_bin
start = time.time()
loaded = torch.load("model.bin", map_location="cpu")
print(f"pytorch_bin 加载: {time.time() - start:.3f}s")

# 大模型加载性能差异:
# 70B 模型 (140 GB):
#   safetensors (mmap): ~5 秒
#   pytorch_bin: ~60 秒
# 速度提升 10x+
```

---

## 自建模型仓库方案

```
自建模型仓库方案 (适合企业内部):

  最小可行方案:
    存储: MinIO (S3 兼容对象存储)
    元数据: PostgreSQL (模型信息、版本、标签)
    API: FastAPI (RESTful 接口)
    UI: 简单 Web 前端
    认证: LDAP/OAuth2

  进阶方案:
    + MLflow Model Registry (模型生命周期管理)
    + 模型评估自动化 (CI/CD 管线)
    + 模型安全扫描 (漏洞、偏见检测)
    + P2P 分发 (Dragonfly / Kraken)
    + 分布式缓存 (Redis / Alluxio)

  关键设计点:
    1. 大文件存储: 对象存储 + 分片上传
    2. 版本管理: 语义化版本号 + Git 标签
    3. 缓存策略: 多级缓存 (本地NVMe → 分布式缓存 → 对象存储)
    4. 权限管理: RBAC (角色级别控制)
    5. 审计追踪: 所有操作记录日志
```

---

## 延伸阅读

- [HuggingFace Hub Documentation](https://huggingface.co/docs/hub)
- [MLflow Model Registry](https://mlflow.org/docs/latest/model-registry.html)
- [safetensors](https://huggingface.co/docs/safetensors)
- [GGUF Format Specification](https://github.com/ggerganov/ggml/blob/master/docs/gguf.md)

---

*上一篇：[04-object-storage.md](04-object-storage.md)* | *下一篇：[06-storage-architecture.md](06-storage-architecture.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **HuggingFace.** *Hugging Face Hub Documentation.*  
   https://huggingface.co/docs/hub/

2. **MLflow.** *MLflow Model Registry.*  
   https://mlflow.org/docs/latest/model-registry.html

3. **DVC.** *Data Version Control.*  
   https://dvc.org/

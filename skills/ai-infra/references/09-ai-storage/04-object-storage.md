# 对象存储与数据湖

> 对象存储是 AI 数据的"无限仓库"——PB 级训练数据、模型归档、Checkpoint 冷存储的最佳选择。

## 目录

- [对象存储基础](#对象存储基础)
- [主流对象存储方案](#主流对象存储方案)
- [对象存储在 AI 中的角色](#对象存储在-ai-中的角色)
- [MinIO 自建方案](#minio-自建方案)
- [数据湖架构](#数据湖架构)
- [训练数据管理](#训练数据管理)
- [分层存储策略](#分层存储策略)
- [延伸阅读](#延伸阅读)

---

## 对象存储基础

### 生活类比：快递仓库 vs 书房

```
文件系统 = 你的书房:
  按目录层级整理: 书架 → 分类 → 书
  可以随时翻开某一页
  快速存取，但空间有限

对象存储 = 大型快递仓库:
  每个包裹有唯一编号（Key）
  存进去、取出来、扔掉——就这三个操作
  不能"翻开包裹看第3页"
  空间几乎无限，成本极低

  AI 场景:
    训练数据归档 → 快递仓库存原材料
    Checkpoint 冷存储 → 仓库存旧生产记录
    模型分发 → 从仓库发货到各门店
```

### 对象存储 vs 文件系统

| 特性 | 对象存储 (S3) | 文件系统 (POSIX) |
|------|-------------|-----------------|
| **接口** | RESTful API (PUT/GET/DELETE) | open/read/write/seek |
| **命名空间** | 扁平 (bucket/key) | 层级 (目录树) |
| **随机访问** | 不支持 (需 Range GET) | 完全支持 (seek) |
| **延迟** | ~10-50 ms | ~10 μs - 1 ms |
| **吞吐** | 高 (多连接并行) | 极高 (RDMA) |
| **扩展性** | 无限 | 有限 (取决于集群) |
| **成本** | 极低 ($0.023/GB/月) | 较高 |
| **一致性** | 最终一致/强一致 | 强一致 |
| **适合场景** | 大文件存取、归档 | 随机访问、训练时读取 |

---

## 主流对象存储方案

### 方案对比

| 方案 | 类型 | 兼容性 | 适用场景 | 特点 |
|------|------|--------|---------|------|
| **AWS S3** | 云服务 | S3 原生 | 云上 AI | 生态最完善，全球可达 |
| **GCS** | 云服务 | S3 兼容 | GCP 用户 | 与 TPU/Vertex AI 集成好 |
| **Azure Blob** | 云服务 | 部分 S3 兼容 | Azure 用户 | 与 Azure ML 集成 |
| **MinIO** | 自建 | S3 完全兼容 | 私有化部署 | 高性能，K8s 原生 |
| **Ceph RGW** | 自建 | S3 兼容 | 已有 Ceph | 统一存储平台 |
| **腾讯云 COS** | 云服务 | S3 兼容 | 国内用户 | 国内访问快 |
| **阿里云 OSS** | 云服务 | S3 兼容 | 国内用户 | 国内生态完善 |

---

## 对象存储在 AI 中的角色

```
┌─────────────────────────────────────────────────────────────────┐
│              对象存储在 AI 工作流中的角色                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 训练数据长期存储                                             │
│     原始数据: 文本/图片/音频/视频 → PB 级                        │
│     处理后数据: tokenized/特征提取后 → TB 级                     │
│     成本: $0.023/GB/月 (S3 Standard)                             │
│                                                                 │
│  2. Checkpoint 归档                                              │
│     热 CP: 本地 NVMe / 并行 FS → 保留最近几个                   │
│     冷 CP: 对象存储 (S3 Standard) → 保留里程碑                  │
│     冰 CP: 归档存储 (S3 Glacier) → 合规保留                     │
│                                                                 │
│  3. 模型分发                                                     │
│     训练完成 → 上传模型到 S3                                    │
│     推理服务 → 从 S3 下载模型到本地                              │
│     CDN 加速 → 全球分发模型文件                                  │
│                                                                 │
│  4. 实验 Artifact 管理                                           │
│     MLflow/W&B → 实验结果存储到 S3                               │
│     模型比较 → 从 S3 拉取不同版本模型                            │
│                                                                 │
│  关键原则:                                                       │
│    对象存储用于存放，不用于直接训练读取                           │
│    训练时: S3 → 预加载到并行 FS / 本地 NVMe → GPU                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## MinIO 自建方案

### 架构与部署

```bash
# MinIO 分布式部署（AI 训练集群推荐配置）

# 1. 使用 Docker Compose 部署 4 节点集群
# docker-compose.yml 核心配置:
# services:
#   minio1:
#     image: quay.io/minio/minio
#     command: server http://minio{1...4}/data{1...4} --console-address ":9001"
#     volumes:
#       - /data1:/data1
#       - /data2:/data2
#       - /data3:/data3
#       - /data4:/data4

# 2. Kubernetes 部署（推荐）
# 使用 MinIO Operator
kubectl apply -f https://github.com/minio/operator/releases/latest/download/operator.yaml

# 3. 配置客户端
mc alias set ai-storage http://minio:9000 $ACCESS_KEY $SECRET_KEY

# 4. 创建训练数据 bucket
mc mb ai-storage/training-data
mc mb ai-storage/checkpoints
mc mb ai-storage/models

# 5. 上传训练数据
mc cp --recursive /local/dataset/ ai-storage/training-data/

# 6. 配置生命周期（自动归档旧 Checkpoint）
mc ilm rule add ai-storage/checkpoints \
    --transition-days 7 --storage-class GLACIER

# MinIO 性能:
# 单节点 NVMe: ~10 GB/s
# 4 节点集群: ~40 GB/s
# 适合中大规模 AI 集群的自建对象存储
```

### Python S3 操作

```python
"""AI 训练中常用的 S3 操作"""
import boto3
from botocore.config import Config
import os

# 配置高并发客户端
s3_client = boto3.client(
    's3',
    endpoint_url='http://minio:9000',  # 自建 MinIO
    config=Config(
        max_pool_connections=50,
        retries={'max_attempts': 3},
    ),
)

def upload_checkpoint(local_path: str, bucket: str, step: int):
    """上传 Checkpoint 到 S3"""
    key = f"checkpoints/step_{step}/checkpoint.pt"
    
    # 大文件使用分片上传
    from boto3.s3.transfer import TransferConfig
    config = TransferConfig(
        multipart_threshold=100 * 1024 * 1024,  # 100 MB
        max_concurrency=10,
        multipart_chunksize=100 * 1024 * 1024,
    )
    
    s3_client.upload_file(local_path, bucket, key, Config=config)
    print(f"Uploaded checkpoint step {step} to s3://{bucket}/{key}")

def download_model(bucket: str, model_name: str, local_dir: str):
    """下载模型（多线程加速）"""
    import concurrent.futures
    
    # 列出模型文件
    paginator = s3_client.get_paginator('list_objects_v2')
    prefix = f"models/{model_name}/"
    
    files = []
    for page in paginator.paginate(Bucket=bucket, Prefix=prefix):
        for obj in page.get('Contents', []):
            files.append(obj['Key'])
    
    def download_file(key):
        local_path = os.path.join(local_dir, os.path.basename(key))
        s3_client.download_file(bucket, key, local_path)
        return key
    
    # 并行下载
    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as executor:
        futures = [executor.submit(download_file, f) for f in files]
        for future in concurrent.futures.as_completed(futures):
            print(f"  Downloaded: {future.result()}")
```

---

## 数据湖架构

### 为什么 AI 需要数据湖

```
数据湖: 统一管理结构化和非结构化数据的平台

  传统方式:
    训练数据散落在: S3 + NFS + HDFS + 本地磁盘
    问题: 不知道数据在哪、版本是哪个、谁修改过

  数据湖方式:
    所有数据统一管理: 元数据目录 + 版本控制 + 血缘追踪
    ┌──────────────────────────────────────────┐
    │              数据湖平台                    │
    │  ┌────────┐ ┌────────┐ ┌────────┐       │
    │  │元数据   │ │版本控制│ │血缘追踪│        │
    │  │目录     │ │       │ │       │        │
    │  └────┬───┘ └────┬───┘ └────┬───┘       │
    │       └──────────┼──────────┘            │
    │                  │                       │
    │  ┌───────────────▼───────────────┐       │
    │  │        对象存储 (S3/MinIO)     │       │
    │  │  训练数据 / 评估数据 / 模型    │       │
    │  └───────────────────────────────┘       │
    └──────────────────────────────────────────┘
```

### 主流数据湖方案

| 方案 | 特点 | AI 适用性 | 生态 |
|------|------|----------|------|
| **Delta Lake** | Spark 生态，ACID 事务，时间旅行 | 结构化训练数据 | Databricks |
| **Apache Iceberg** | 开放标准，多引擎支持，分区演化 | 大规模数据管理 | Netflix/Apple |
| **Apache Hudi** | 增量处理，CDC 支持 | 实时数据管线 | Uber |
| **LakeFS** | Git-like 数据版本管理 | 训练数据版本控制 | 开源 |

---

## 训练数据管理

### 数据组织最佳实践

```
AI 训练数据的 S3 组织结构:

  s3://ai-data/
  ├── raw/                          # 原始数据（只读归档）
  │   ├── text/
  │   │   ├── common-crawl/
  │   │   ├── wikipedia/
  │   │   └── books/
  │   ├── images/
  │   └── code/
  │
  ├── processed/                    # 预处理后数据
  │   ├── v1/                       # 版本管理
  │   │   ├── train/
  │   │   ├── val/
  │   │   └── metadata.json
  │   └── v2/
  │
  ├── tokenized/                    # Tokenized 数据（训练直接用）
  │   ├── llama-7b-v2/
  │   │   ├── train-00000.bin
  │   │   ├── train-00001.bin
  │   │   └── ...
  │   └── config.json
  │
  └── evaluations/                  # 评估数据集
      ├── mmlu/
      ├── humaneval/
      └── truthfulqa/

  命名规范:
    日期前缀: 2024-01-15/raw-data.tar
    版本号: v1, v2, v3
    分片编号: train-00000.bin (5位数字，零填充)
```

---

## 分层存储策略

```
AI 数据的温度分层:

  ┌─────────────────────────────────────────────────────┐
  │              存储温度分层                              │
  ├─────────────┬──────────────┬─────────┬──────────────┤
  │  温度        │ 存储介质     │ 成本/TB  │ 数据类型     │
  ├─────────────┼──────────────┼─────────┼──────────────┤
  │  🔴 热       │ NVMe SSD     │ $30/月  │ 当前训练数据  │
  │             │ (本地)       │         │ 活跃 CP      │
  ├─────────────┼──────────────┼─────────┼──────────────┤
  │  🟡 温       │ 并行 FS      │ $20/月  │ 近期数据     │
  │             │ Lustre/GPFS  │         │ 近期 CP      │
  ├─────────────┼──────────────┼─────────┼──────────────┤
  │  🔵 冷       │ 对象存储     │ $3/月   │ 归档数据     │
  │             │ S3 Standard  │         │ 旧 CP        │
  ├─────────────┼──────────────┼─────────┼──────────────┤
  │  ⚪ 冰       │ 归档存储     │ $0.4/月 │ 合规保留     │
  │             │ S3 Glacier   │         │ 历史全量     │
  └─────────────┴──────────────┴─────────┴──────────────┘

  自动分层策略:
    访问频率 > 1次/天 → 热
    访问频率 > 1次/周 → 温
    访问频率 > 1次/月 → 冷
    访问频率 < 1次/月 → 冰

  数据流向:
    新训练数据: 热 → 温 → 冷 (训练完成后自动降温)
    Checkpoint: 热(NVMe) → 温(并行FS) → 冷(S3) → 冰(Glacier)
    模型权重: 冷(S3) → 热(NVMe) (部署时升温)
```

---

## 延伸阅读

- [AWS S3 Best Practices](https://docs.aws.amazon.com/AmazonS3/latest/userguide/optimizing-performance.html)
- [MinIO Documentation](https://min.io/docs/)
- [Delta Lake Documentation](https://docs.delta.io/)
- [Apache Iceberg](https://iceberg.apache.org/docs/)
- [LakeFS for ML](https://docs.lakefs.io/)

---

*上一篇：[03-checkpoint-storage.md](03-checkpoint-storage.md)* | *下一篇：[05-model-repository.md](05-model-repository.md)*

*返回：[README.md](README.md) - 章节索引*

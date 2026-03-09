# AI 存储基础设施

> 数据是 AI 的燃料，存储是 AI 的油箱——没有高效的存储系统，再强的 GPU 也只能空转。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [09-ai-storage/](./09-ai-storage/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | AI 存储基础 | [01-storage-fundamentals.md](./09-ai-storage/01-storage-fundamentals.md) |
> | 分布式文件系统 | [02-distributed-filesystems.md](./09-ai-storage/02-distributed-filesystems.md) |
> | Checkpoint 存储 | [03-checkpoint-storage.md](./09-ai-storage/03-checkpoint-storage.md) |
> | 对象存储与数据湖 | [04-object-storage.md](./09-ai-storage/04-object-storage.md) |
> | 模型仓库 | [05-model-repository.md](./09-ai-storage/05-model-repository.md) |
> | 存储架构设计 | [06-storage-architecture.md](./09-ai-storage/06-storage-architecture.md) |

---

## 目录

- [为什么存储是 AI 基建的核心瓶颈](#为什么存储是-ai-基建的核心瓶颈)
- [AI 存储的三大挑战](#ai-存储的三大挑战)
- [存储技术栈概览](#存储技术栈概览)

---

## 为什么存储是 AI 基建的核心瓶颈

### 生活类比：高速公路与停车场

```
想象 GPU 集群是一座巨大的工厂:

  GPU = 生产线上的工人
  存储 = 原材料仓库 + 成品仓库

  如果仓库的门太小（带宽不足）:
    → 工人站在生产线前等原材料         （GPU idle，等数据加载）
    → 成品堆不下影响生产               （Checkpoint 写不出去阻塞训练）
    → 仓库找不到东西                   （数据管理混乱）

  AI 训练对存储的需求是"暴风雨式"的:
    - 256 张 GPU 同时读训练数据 → 需要 256 GB/s 读带宽
    - 每 30 分钟写一次 Checkpoint → 280 GB 突发写入
    - 模型重启时集群同时加载 → 4.5 TB 瞬时读取
```

---

## AI 存储的三大挑战

```
┌─────────────────────────────────────────────────────────────┐
│                AI 存储的三大核心挑战                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  挑战 1: 规模                                                │
│    训练数据: TB → PB 级                                     │
│    Checkpoint: 每次 GB → TB 级                              │
│    模型权重: 数百 GB（405B 模型约 800GB FP16）                │
│                                                             │
│  挑战 2: 性能                                                │
│    吞吐: 数百 GB/s 并发读写                                  │
│    延迟: Checkpoint 必须快速完成避免阻塞训练                  │
│    IOPS: 大量小文件的数据预处理需要高 IOPS                   │
│                                                             │
│  挑战 3: 可靠性                                              │
│    训练天/周/月不间断运行                                    │
│    Checkpoint 是唯一的进度保存，不能丢失                     │
│    硬件故障概率随规模增大                                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 存储技术栈概览

```
┌─────────────────────────────────────────────────────────────────┐
│                   AI 存储技术栈                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  应用层       模型仓库 (HuggingFace Hub / Model Registry)       │
│               数据管理 (DVC / LakeFS)                            │
│                                                                 │
│  缓存层       本地 NVMe SSD (6-14 GB/s)                          │
│               分布式缓存 (Alluxio / JuiceFS Cache)               │
│                                                                 │
│  并行 FS      Lustre / GPFS / BeeGFS / JuiceFS / CephFS         │
│               (10-100+ GB/s 聚合带宽)                            │
│                                                                 │
│  对象存储      S3 / MinIO / GCS / OSS / COS                     │
│               (PB 级，低成本，高延迟)                             │
│                                                                 │
│  数据湖        Delta Lake / Apache Iceberg / Apache Hudi         │
│               (结构化数据管理)                                    │
│                                                                 │
│  硬件层       NVMe SSD / HDD / 持久内存 (CXL)                    │
│               RAID / JBOF / 全闪存阵列                           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

*上一篇：[08-cost-optimization.md](08-cost-optimization.md)* | *下一篇：[10-ai-networking.md](10-ai-networking.md)*

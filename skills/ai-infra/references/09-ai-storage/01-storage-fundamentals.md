# AI 存储基础

> 理解 AI 工作负载的存储需求，是设计高效存储架构的第一步——不同的 AI 阶段对存储的要求截然不同。

## 目录

- [存储在 AI 工作负载中的角色](#存储在-ai-工作负载中的角色)
- [AI 不同阶段的存储需求](#ai-不同阶段的存储需求)
- [存储性能三要素：IOPS vs 吞吐 vs 延迟](#存储性能三要素iops-vs-吞吐-vs-延迟)
- [存储介质对比](#存储介质对比)
- [存储协议与接口](#存储协议与接口)
- [AI 存储的独特挑战](#ai-存储的独特挑战)
- [存储容量规划](#存储容量规划)
- [延伸阅读](#延伸阅读)

---

## 存储在 AI 工作负载中的角色

### 生活类比：餐厅的后厨系统

```
AI 训练就像一家超级忙碌的餐厅:

  GPU         = 厨师（做菜的核心力量）
  训练数据     = 食材仓库（原材料来源）
  Checkpoint  = 菜谱进度本（保存到哪一步了）
  模型权重     = 最终的成品菜品
  存储系统     = 整个后厨管理系统

  如果后厨系统出问题:
    ✗ 食材供应不上 → 厨师空等        （GPU idle，等数据加载）
    ✗ 菜谱进度保存太慢 → 耽误出菜     （Checkpoint 阻塞训练）
    ✗ 仓库太乱找不到食材 → 混乱       （数据管理混乱）
    ✗ 仓库容量不够 → 无法采购新食材   （存储空间不足）

  好的后厨系统:
    ✓ 食材预备到位 → 厨师持续工作     （数据预取）
    ✓ 进度快速记录 → 不影响出菜       （异步 Checkpoint）
    ✓ 分区管理有序 → 随时取用         （分层存储）
```

### AI 训练的数据流

```
┌─────────────────────────────────────────────────────────────────┐
│                   AI 训练的数据流全景                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐  │
│  │ 原始数据  │───▶│ 预处理    │───▶│ 训练数据  │───▶│ GPU 训练  │  │
│  │ (PB级)   │    │ (清洗/    │    │ (格式化)  │    │          │  │
│  │          │    │  tokenize)│    │          │    │          │  │
│  └──────────┘    └──────────┘    └──────────┘    └─────┬────┘  │
│       ▲                                                │       │
│       │                                                ▼       │
│  ┌──────────┐                                   ┌──────────┐  │
│  │ 数据归档  │                                    │Checkpoint│  │
│  │ (冷存储)  │◀──────────────────────────────────│ (周期保存)│  │
│  └──────────┘                                    └─────┬────┘  │
│                                                        │       │
│                                                        ▼       │
│                                                  ┌──────────┐  │
│                                                  │ 模型权重  │  │
│                                                  │ (最终产物)│  │
│                                                  └──────────┘  │
│                                                                 │
│  每个阶段对存储的需求完全不同！                                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## AI 不同阶段的存储需求

### 预训练（Pre-training）

```
┌─────────────────────────────────────────────────────────────────┐
│                   预训练阶段存储需求                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  训练数据:                                                       │
│    数据量: 1-15 TB（tokenized），原始数据可达 PB 级              │
│    IO 模式: 大块顺序读取（每 batch 读取 MB 级别数据块）          │
│    读取带宽: 每 GPU 需要 200 MB/s - 1 GB/s                      │
│    256 GPU 集群总计: 50-256 GB/s 读取带宽                        │
│                                                                 │
│  Checkpoint:                                                    │
│    单次大小: 模型大小 × 2-8（包含优化器状态）                    │
│      - 7B 模型: 14-56 GB/次                                     │
│      - 70B 模型: 140-560 GB/次                                  │
│      - 405B 模型: 810 GB - 3.2 TB/次                            │
│    频率: 每 15-60 分钟一次                                       │
│    IO 模式: 突发写入（所有 GPU 同时写）                          │
│    性能要求: 在训练 step 间隙完成写入（几秒到几十秒）            │
│                                                                 │
│  模型权重:                                                       │
│    大小: 参数量 × 精度字节数                                    │
│    加载: 启动/恢复时一次性加载                                   │
│    IO 模式: 大块顺序读取                                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 微调（Fine-tuning）

```
微调阶段的存储特点:

  数据量较小:
    SFT 数据: 几 MB - 几 GB
    RLHF 偏好数据: 几 MB - 几百 MB
    存储压力远小于预训练

  但仍需要:
    ✓ 基础模型权重的快速加载（数百 GB）
    ✓ LoRA 适配器的频繁保存（几十 MB - 几百 MB/次）
    ✓ 多实验并行时的存储隔离
    ✓ 实验结果的版本管理

  存储策略:
    基础模型: 共享只读存储（避免多份拷贝）
    微调数据: 本地 NVMe 或小型 NFS
    Checkpoint: 本地 NVMe，定期同步到共享存储
    实验管理: MLflow/W&B 记录每次实验的 artifact 路径
```

### 推理（Inference）

```
推理阶段的存储需求:

  模型加载:
    冷启动: 将模型从存储加载到 GPU
    - 70B FP16 模型 ≈ 140 GB → 单 GPU 加载需 15-30 秒（NVMe）
    - 多节点加载: 32 节点 × 140 GB = 4.5 TB 突发读取
    热更新: 不停服切换模型版本

  KV Cache:
    长上下文推理会消耗大量显存
    可能需要将 KV Cache 卸载到主存/SSD
    要求极低延迟（< 1ms）

  日志和监控:
    请求日志: 追加写入，中等吞吐
    性能指标: 结构化数据，定期写入
    审计日志: 合规要求，不可篡改
```

### 数据预处理

```
数据预处理的存储挑战:

  IO 模式: 随机读写为主
  ┌─────────────────────────────────────────────┐
  │                                             │
  │  原始文本/图片/音频                           │
  │       │                                     │
  │       ▼                                     │
  │  [清洗/过滤]  ← 随机读取大量小文件           │
  │       │                                     │
  │       ▼                                     │
  │  [Tokenization / 特征提取]                   │
  │       │                                     │
  │       ▼                                     │
  │  [去重 (MinHash)]  ← 全量数据扫描+比对      │
  │       │                                     │
  │       ▼                                     │
  │  [打包为训练格式]  ← 顺序写入大文件          │
  │       │                                     │
  │       ▼                                     │
  │  训练就绪数据集                               │
  │                                             │
  │  关键需求: 高 IOPS（大量小文件操作）          │
  │           中等吞吐（数据扫描）               │
  │           大容量（中间产物可能占 2-3x 空间）  │
  └─────────────────────────────────────────────┘
```

---

## 存储性能三要素：IOPS vs 吞吐 vs 延迟

### 三要素解析

```
┌─────────────────────────────────────────────────────────────────┐
│           存储性能三要素：三个不同的维度                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  类比: 快递公司的三个维度                                        │
│                                                                 │
│  IOPS = 每天能处理多少个包裹                                     │
│    → 10 万个小包裹 vs 100 个大包裹                               │
│    → 数据预处理（大量小文件操作）需要高 IOPS                    │
│                                                                 │
│  吞吐 = 每天能运输多少吨货物                                     │
│    → 关注总运载量                                               │
│    → 训练数据加载、Checkpoint 写入需要高吞吐                    │
│                                                                 │
│  延迟 = 从下单到收货要多久                                       │
│    → 关注单次请求的响应速度                                     │
│    → KV Cache 卸载、实时推理需要低延迟                           │
│                                                                 │
│  关键认知: 三者往往不能同时达到最优！                             │
│    高 IOPS 的 NVMe ≠ 高吞吐的并行 FS                            │
│    低延迟的本地存储 ≠ 大容量的对象存储                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 具体数值参考

| 存储类型 | 顺序读吞吐 | 随机 IOPS | 读延迟 | 容量 | 成本/TB/月 |
|---------|-----------|----------|--------|------|-----------|
| **本地 NVMe SSD** | 6-14 GB/s | 1M+ | ~10 μs | 1-30 TB | ~$30 |
| **SATA SSD** | 500 MB/s | 100K | ~100 μs | 1-8 TB | ~$15 |
| **HDD** | 200 MB/s | ~200 | ~5 ms | 4-20 TB | ~$5 |
| **Lustre** | 10-300+ GB/s* | 取决于MDS | ~100 μs | PB 级 | ~$20 |
| **GPFS** | 10-100+ GB/s* | 高 | ~100 μs | PB 级 | ~$25 |
| **JuiceFS** | 取决于后端* | 中等 | ~1 ms | 无限(对象存储) | ~$8 |
| **NFS** | 1-10 GB/s | 中等 | ~200 μs | TB 级 | ~$10 |
| **S3/对象存储** | 1-50 GB/s* | N/A | ~10 ms | 无限 | ~$3 |

> *聚合带宽，取决于集群规模和配置

### Python 性能测试工具

```python
#!/usr/bin/env python3
"""简单的存储性能基准测试工具"""
import os
import time
import tempfile
import numpy as np

def test_sequential_write(path: str, size_gb: float = 1.0) -> dict:
    """测试顺序写入吞吐"""
    block_size = 1024 * 1024  # 1 MB blocks
    total_bytes = int(size_gb * 1024 * 1024 * 1024)
    num_blocks = total_bytes // block_size
    data = np.random.bytes(block_size)
    
    filepath = os.path.join(path, "bench_seq_write.tmp")
    start = time.perf_counter()
    
    with open(filepath, 'wb') as f:
        for _ in range(num_blocks):
            f.write(data)
        f.flush()
        os.fsync(f.fileno())
    
    elapsed = time.perf_counter() - start
    throughput_gbs = size_gb / elapsed
    
    os.remove(filepath)
    return {
        "test": "sequential_write",
        "size_gb": size_gb,
        "elapsed_s": round(elapsed, 3),
        "throughput_gb_s": round(throughput_gbs, 3),
    }

def test_sequential_read(path: str, size_gb: float = 1.0) -> dict:
    """测试顺序读取吞吐"""
    block_size = 1024 * 1024
    total_bytes = int(size_gb * 1024 * 1024 * 1024)
    num_blocks = total_bytes // block_size
    data = np.random.bytes(block_size)
    
    filepath = os.path.join(path, "bench_seq_read.tmp")
    with open(filepath, 'wb') as f:
        for _ in range(num_blocks):
            f.write(data)
    
    # 清除页面缓存（需要 root）
    # os.system("sync && echo 3 > /proc/sys/vm/drop_caches")
    
    start = time.perf_counter()
    with open(filepath, 'rb') as f:
        while f.read(block_size):
            pass
    elapsed = time.perf_counter() - start
    
    os.remove(filepath)
    return {
        "test": "sequential_read",
        "size_gb": size_gb,
        "elapsed_s": round(elapsed, 3),
        "throughput_gb_s": round(size_gb / elapsed, 3),
    }

def test_random_iops(path: str, num_ops: int = 10000, block_size: int = 4096) -> dict:
    """测试随机 IOPS（4K 随机读写）"""
    file_size = 256 * 1024 * 1024  # 256 MB 测试文件
    filepath = os.path.join(path, "bench_random.tmp")
    
    # 创建测试文件
    data = np.random.bytes(file_size)
    with open(filepath, 'wb') as f:
        f.write(data)
    
    # 随机读测试
    positions = np.random.randint(0, file_size - block_size, size=num_ops)
    block = bytearray(block_size)
    
    start = time.perf_counter()
    with open(filepath, 'rb') as f:
        for pos in positions:
            f.seek(int(pos))
            f.readinto(block)
    elapsed = time.perf_counter() - start
    
    os.remove(filepath)
    return {
        "test": "random_read_iops",
        "num_ops": num_ops,
        "block_size": block_size,
        "elapsed_s": round(elapsed, 3),
        "iops": round(num_ops / elapsed),
    }

if __name__ == "__main__":
    test_path = tempfile.gettempdir()
    print(f"测试路径: {test_path}")
    print()
    
    # 运行测试
    for test_fn in [test_sequential_write, test_sequential_read, test_random_iops]:
        result = test_fn(test_path)
        print(f"  {result['test']}:")
        for k, v in result.items():
            if k != 'test':
                print(f"    {k}: {v}")
        print()
```

---

## 存储介质对比

### 存储介质技术树

```
┌─────────────────────────────────────────────────────────────────┐
│                   存储介质技术树                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  速度快 ◀──────────────────────────────────────▶ 容量大/便宜     │
│                                                                 │
│  GPU HBM          寄存器级速度，但容量有限                       │
│  │  3 TB/s        80-192 GB/卡                                  │
│  │                                                              │
│  CPU DRAM          主内存                                        │
│  │  ~100 GB/s     256 GB - 2 TB/节点                            │
│  │                                                              │
│  NVMe SSD          最快的持久化存储                               │
│  │  6-14 GB/s     1-30 TB/节点                                  │
│  │                                                              │
│  SATA SSD          性价比持久化存储                               │
│  │  500 MB/s      1-8 TB                                        │
│  │                                                              │
│  HDD               大容量冷存储                                  │
│  │  200 MB/s      4-20 TB                                       │
│  │                                                              │
│  磁带               极端冷存储                                    │
│     ~300 MB/s     12-45 TB/卷                                   │
│                                                                 │
│  AI 存储最佳实践:                                                │
│    热数据 → NVMe SSD（Checkpoint 缓存、活跃训练数据）            │
│    温数据 → 并行 FS（共享训练数据、近期 Checkpoint）              │
│    冷数据 → 对象存储 / HDD（归档 Checkpoint、历史数据）          │
│    冰数据 → 磁带 / Glacier（合规保留、灾备）                     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### NVMe SSD 深入

```
NVMe SSD 在 AI 中的关键角色:

  为什么 NVMe 对 AI 训练至关重要？

  1. Checkpoint 缓存:
     GPU → NVMe (6 GB/s) → 后台同步到共享存储 (1 GB/s)
     → 训练几乎不暂停

  2. 数据缓存:
     热数据从共享存储预取到本地 NVMe
     → 消除网络 IO 瓶颈

  3. KV Cache 卸载:
     推理时将不活跃的 KV Cache 卸载到 NVMe
     → 支持更长的上下文长度

  关键规格:
  ┌──────────────┬──────────────┬──────────────┐
  │ 规格         │ 消费级       │ 企业级        │
  ├──────────────┼──────────────┼──────────────┤
  │ 接口         │ PCIe Gen4 x4 │ PCIe Gen5 x4 │
  │ 顺序读       │ ~7 GB/s     │ ~14 GB/s     │
  │ 顺序写       │ ~5 GB/s     │ ~12 GB/s     │
  │ 随机 IOPS    │ ~1M         │ ~2M          │
  │ 持久性       │ 600 TBW     │ 10+ DWPD     │
  │ 延迟         │ ~80 μs      │ ~10 μs       │
  │ 容量         │ 1-4 TB      │ 1-30 TB      │
  │ 价格/TB      │ ~$80        │ ~$200-500    │
  └──────────────┴──────────────┴──────────────┘

  AI 服务器推荐:
    训练节点: 2-4 块企业级 NVMe（4-15 TB 总容量）
    推理节点: 1-2 块 NVMe（足够放模型和 KV Cache 卸载）
```

---

## 存储协议与接口

### 主要存储协议

```
┌─────────────────────────────────────────────────────────────────┐
│                   存储协议对比                                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  本地存储协议:                                                   │
│    NVMe    最快的本地 SSD 协议，直连 PCIe 总线                   │
│    SATA    传统硬盘协议，带宽受限                                │
│    SAS     企业级硬盘协议，支持双端口                             │
│                                                                 │
│  网络存储协议:                                                   │
│    NFS     网络文件系统，简单通用，适合小规模                    │
│    SMB     Windows 文件共享，AI 场景少用                         │
│    POSIX   标准文件接口，Lustre/GPFS/JuiceFS 支持               │
│    S3 API  对象存储标准接口，RESTful                             │
│                                                                 │
│  高性能网络存储:                                                 │
│    NVMe-oF   NVMe over Fabrics，远程 NVMe 访问                   │
│              延迟仅比本地 NVMe 高 ~10 μs                         │
│    GPUDirect Storage  GPU 直接访问存储，绕过 CPU                 │
│              减少 50%+ 的 IO 延迟                                │
│    RDMA      远程直接内存访问，绕过操作系统内核                   │
│              InfiniBand / RoCE v2                                │
│                                                                 │
│  AI 推荐:                                                        │
│    训练集群: POSIX (Lustre/GPFS) + NVMe 本地缓存                │
│    云上环境: S3 API + JuiceFS FUSE 桥接                          │
│    高性能: GPUDirect Storage + NVMe-oF                           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## AI 存储的独特挑战

### 挑战 1：Checkpoint 风暴

```
Checkpoint 风暴 — AI 存储最大的 IO 挑战:

  场景: 256 GPU 训练 70B 模型

  模型参数: 70B × 2 bytes (BF16) = 140 GB
  优化器状态: 140 GB × 2 (Adam: m + v) = 280 GB
  梯度: 140 GB
  总 Checkpoint 大小: ~560 GB

  所有 GPU 同时写入:
    ┌──────────────────────────────────┐
    │  GPU 0 ─────┐                   │
    │  GPU 1 ─────┤                   │
    │  GPU 2 ─────┤                   │
    │  ...        ├──▶ 共享存储系统    │
    │  GPU 254 ───┤   (560 GB 突发)   │
    │  GPU 255 ───┘                   │
    │                                 │
    │  要求: 在 30 秒内完成            │
    │  → 需要 560/30 ≈ 18.7 GB/s     │
    │     持续写入带宽                 │
    └──────────────────────────────────┘

  解决方案梯度:
    Level 1: 异步 Checkpoint（后台写入，不阻塞训练）
    Level 2: 分布式 Checkpoint（每个 rank 写自己的分片）
    Level 3: 本地 NVMe 缓存（先写本地，后台同步）
    Level 4: GPUDirect Storage（GPU 直写 NVMe，绕过 CPU）
```

### 挑战 2：数据加载带宽

```
训练数据加载带宽瓶颈:

  计算: 256 GPU，每 GPU 处理 ~4096 tokens/step
  数据需求: 每 step 约 1M tokens × 2 bytes = 2 MB
  Step 时间: ~1 秒
  每 GPU 带宽需求: ~2-10 MB/s（看起来不多？）

  但实际情况复杂得多:
    1. 数据预处理（on-the-fly augmentation）放大带宽需求
    2. 随机 shuffle 破坏顺序读性能
    3. 多 worker 并发读取导致 IO 争抢
    4. 元数据操作（open/stat/readdir）成为瓶颈

  真实场景的数据加载管道:
    ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐
    │ 存储  │──▶│ 预取  │──▶│ 解码  │──▶│ GPU  │
    │ 系统  │   │ 缓冲  │   │ 增强  │   │ 训练 │
    └──────┘   └──────┘   └──────┘   └──────┘
    ^                                     ^
    瓶颈可能在这里              或者在这里

  解决: 预打包数据格式（WebDataset/MDS）+ 多级缓存 + 预取
```

### 挑战 3：元数据压力

```
大量小文件场景的元数据压力:

  场景: ImageNet-scale 数据集
    1.28M 训练图片 × 每张 100KB = 128 GB
    文件数量: 1,281,167 个文件

  元数据操作:
    ls/readdir: 列出所有文件 → 百万次元数据查询
    stat: 获取文件属性 → 百万次 IOPS
    open: 打开文件 → 百万次文件打开操作

  在分布式文件系统上:
    Lustre MDS 可能成为瓶颈（单 MDS 约 10K ops/s）
    → 需要 DNE (Distributed Namespace) 或 DAL (Data on MDT)

  解决方案:
    ✓ 使用大文件格式: TFRecord, WebDataset (.tar), MDS
    ✓ 将小文件打包: 1M 个文件 → 几百个大 tar 文件
    ✓ 使用元数据缓存: 避免重复查询
    ✓ 预生成索引文件: 避免 readdir 操作
```

### 挑战 4：多租户隔离

```
共享集群的存储隔离:

  问题:
    多个训练任务共享同一个存储系统
    一个任务的 Checkpoint 写入可能影响其他任务的数据读取

  隔离策略:
    ┌──────────────────────────────────────────────┐
    │  Layer 1: 容量隔离                            │
    │    配额管理: 每个项目/用户设置容量上限         │
    │    Lustre: lfs setquota                       │
    │    JuiceFS: juicefs quota                     │
    │                                              │
    │  Layer 2: 带宽隔离                            │
    │    IO 限速: cgroup + blkio 限制               │
    │    QoS 策略: 优先级队列                       │
    │                                              │
    │  Layer 3: 命名空间隔离                        │
    │    不同项目使用不同子目录/子卷                 │
    │    避免元数据争抢                             │
    │                                              │
    │  Layer 4: 物理隔离                            │
    │    关键任务使用独立存储系统                    │
    │    最强隔离但成本最高                         │
    └──────────────────────────────────────────────┘
```

---

## 存储容量规划

### 容量估算模型

```python
"""AI 集群存储容量估算"""

def estimate_storage_capacity(
    num_gpus: int = 256,
    model_params_b: float = 70,      # 模型参数量（十亿）
    training_data_tb: float = 5,     # 训练数据（TB）
    checkpoint_interval_min: int = 30,
    keep_checkpoints: int = 5,
    num_experiments: int = 3,
):
    """估算 AI 训练所需的存储容量"""
    
    # 模型权重（BF16）
    model_size_gb = model_params_b * 2  # 2 bytes/param
    
    # 单次 Checkpoint（含优化器状态）
    checkpoint_size_gb = model_size_gb * 4  # params + grads + adam_m + adam_v
    
    # Checkpoint 存储（保留 N 个）
    checkpoint_total_gb = checkpoint_size_gb * keep_checkpoints * num_experiments
    
    # 训练数据（考虑预处理中间产物）
    data_total_tb = training_data_tb * 2  # 原始 + tokenized
    
    # 日志和指标
    logs_gb = num_gpus * 0.1  # 每 GPU 约 100 MB/天的日志
    
    print(f"=== AI 训练存储容量估算 ===")
    print(f"")
    print(f"集群规模: {num_gpus} GPU")
    print(f"模型参数: {model_params_b}B")
    print(f"")
    print(f"--- 存储需求 ---")
    print(f"模型权重 (BF16):       {model_size_gb:.0f} GB")
    print(f"单次 Checkpoint:       {checkpoint_size_gb:.0f} GB")
    print(f"Checkpoint 存储:       {checkpoint_total_gb:.0f} GB "
          f"({keep_checkpoints} × {num_experiments} 实验)")
    print(f"训练数据:              {data_total_tb:.1f} TB")
    print(f"日志/指标 (每天):      {logs_gb:.1f} GB")
    print(f"")
    
    # 按存储层级分配
    # 本地 NVMe: Checkpoint 缓存 + 数据缓存
    local_nvme_tb = (checkpoint_size_gb / 1024 + 0.5) * num_gpus / 8  # 每节点 8 GPU
    
    # 共享存储: 训练数据 + 活跃 Checkpoint
    shared_tb = data_total_tb + checkpoint_total_gb / 1024
    
    # 对象存储: 归档
    archive_tb = data_total_tb * 2 + checkpoint_total_gb / 1024 * 3
    
    print(f"--- 存储层级建议 ---")
    print(f"本地 NVMe (每节点): {local_nvme_tb / (num_gpus / 8):.1f} TB × {num_gpus // 8} 节点")
    print(f"共享并行 FS:        {shared_tb:.1f} TB")
    print(f"对象存储 (归档):    {archive_tb:.1f} TB")
    print(f"")
    print(f"--- 带宽需求 ---")
    print(f"Checkpoint 写入:   {checkpoint_size_gb / 30:.1f} GB/s (30秒内完成)")
    print(f"数据加载:          {num_gpus * 0.5:.0f} GB/s (每 GPU ~500 MB/s)")

# 运行估算
estimate_storage_capacity()
```

### 成本估算参考

| 存储层级 | 容量 | 单价参考 | 月度成本 |
|---------|------|---------|---------|
| 本地 NVMe | 4 TB × 32 节点 = 128 TB | $200/TB | ~$25,600 (一次性) |
| 共享并行 FS (Lustre) | 100 TB | $20/TB/月 | ~$2,000/月 |
| 对象存储 (S3) | 500 TB | $3/TB/月 | ~$1,500/月 |
| **总计** | **728 TB** | - | **~$3,500/月 + 硬件** |

> 存储成本通常占 AI 集群总成本的 10-15%

---

## 延伸阅读

- [NVIDIA AI Storage Solutions](https://www.nvidia.com/en-us/data-center/resources/)
- [Understanding NVMe for AI Workloads](https://nvmexpress.org/)
- [Storage Performance Dev Kit (SPDK)](https://spdk.io/)
- [fio - Flexible I/O Tester](https://fio.readthedocs.io/) - 专业存储性能测试工具

---

*下一篇：[02-distributed-filesystems.md](02-distributed-filesystems.md) - 分布式文件系统*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **SNIA.** *Storage Performance Definitions (IOPS, Throughput, Latency).*  
   https://www.snia.org/

2. **NVIDIA.** *GPUDirect Storage.*  
   https://developer.nvidia.com/gpudirect-storage

3. **NVMe Specification.** *NVM Express.*  
   https://nvmexpress.org/

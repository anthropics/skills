# 分布式文件系统

> 当数百个 GPU 同时读写数据时，本地磁盘远远不够——分布式文件系统是大规模 AI 训练的存储支柱。

## 目录

- [为什么需要分布式文件系统](#为什么需要分布式文件系统)
- [核心架构模式](#核心架构模式)
- [Lustre 深入](#lustre-深入)
- [GPFS/Spectrum Scale](#gpfsspectrum-scale)
- [BeeGFS](#beegfs)
- [JuiceFS 深入](#juicefs-深入)
- [CephFS](#cephfs)
- [全面对比与选型指南](#全面对比与选型指南)
- [条带化与数据布局](#条带化与数据布局)
- [性能调优实践](#性能调优实践)
- [延伸阅读](#延伸阅读)

---

## 为什么需要分布式文件系统

### 生活类比：图书馆管理系统

```
想象一个大型图书馆:

  本地磁盘 = 你桌上的书架
    ✓ 拿书最快（低延迟）  ✗ 放不了几本书  ✗ 别人看不到

  NFS = 一个小型图书馆
    ✓ 多人共享  ✗ 只有一个管理员（单点瓶颈）

  分布式并行文件系统 = 超大型图书馆网络
    ✓ 成千上万的书架（海量容量）
    ✓ 多个管理员并行服务（高吞吐）
    ✓ 书按类别分散存放（数据条带化）
    ✓ 所有人都能同时访问
```

### 需求量化

| 集群规模 | 读取带宽需求 | 写入带宽需求 | 推荐方案 |
|---------|------------|------------|---------|
| 8 GPU (单机) | ~4 GB/s | ~2 GB/s | 本地 NVMe |
| 32-64 GPU | ~30 GB/s | ~10 GB/s | NFS+缓存 或 JuiceFS |
| 256-1024 GPU | ~100-500 GB/s | ~20-100 GB/s | Lustre / GPFS |
| 1000+ GPU | ~1 TB/s+ | ~200+ GB/s | 多 Lustre + 分层存储 |

---

## 核心架构模式

```
┌─────────────────────────────────────────────────────────────────┐
│        三种主要架构模式                                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 并行文件系统 (Lustre, GPFS, BeeGFS)                          │
│     Client → MDS (元数据) → 直连 OST/OSS (数据并行读写)         │
│     数据被条带化分散到多个存储目标 → 聚合带宽                    │
│                                                                 │
│  2. 通用分布式文件系统 (CephFS)                                   │
│     Client → MDS 集群 → CRUSH 算法定位 OSD                      │
│     数据按对象分布 → 自动均衡                                    │
│                                                                 │
│  3. FUSE 桥接方案 (JuiceFS)                                      │
│     Client → FUSE 层 → 元数据引擎 + 对象存储后端                │
│     元数据和数据完全分离 → 灵活组合后端                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Lustre 深入

### 架构与组件

```
┌─────────────────────────────────────────────────────────────────┐
│                     Lustre 架构                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  MGS (Management Server): 集群配置，客户端发现文件系统           │
│  MDS (Metadata Server) + MDT: 文件名/目录/权限/布局             │
│  OSS (Object Storage Server) + OST: 实际文件数据                │
│  Client: 内核模块 (llite)，POSIX 接口                           │
│                                                                 │
│  数据流:                                                         │
│    open("file") → MDS: "在 OST 2,5,8 上，条带 1MB"              │
│    Client 直连 OSS 2/5/8 并行读取 → 吞吐线性增长               │
│                                                                 │
│  DNE (Distributed Namespace): 多 MDS 分布元数据                  │
│  PFL (Progressive File Layout): 小文件小条带，大文件自动扩展    │
│                                                                 │
│  适用: 大规模 HPC/AI 集群 (500+ 节点)，成熟稳定                 │
│  劣势: 部署运维复杂，硬件成本高                                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Lustre 条带化与调优

```bash
# 训练数据: 最大并行度
lfs setstripe --stripe-count -1 --stripe-size 4M /lustre/training_data/

# Checkpoint: 减少锁争抢
lfs setstripe --stripe-count 4 --stripe-size 16M /lustre/checkpoints/

# 性能调优
lctl set_param llite.*.max_cached_mb=1024        # 客户端缓存
lctl set_param llite.*.max_read_ahead_mb=256     # 预读
lctl set_param osc.*.max_rpcs_in_flight=32       # 并发 RPC

# PFL: 自动条带扩展
lfs setstripe -E 1M -c 1 -E 1G -c 4 -E -1 -c -1 /lustre/auto/

# 监控
lctl get_param osc.*.stats | grep 'read_bytes\|write_bytes'
```

---

## GPFS/Spectrum Scale

```
┌─────────────────────────────────────────────────────────────────┐
│              GPFS vs Lustre 关键区别                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 去中心化元数据: 所有节点都可处理元数据（分布式令牌管理）     │
│  2. 强一致性: 完全 POSIX 一致性，分布式锁管理器                  │
│  3. 策略引擎: 内置 ILM，自动数据分层 NVMe → SSD → HDD → 磁带   │
│  4. AFM: 跨集群/跨站点数据同步                                  │
│                                                                 │
│  适用: 企业级大规模 AI 集群，需强一致性和数据生命周期管理        │
│  劣势: 商业许可费较高                                            │
└─────────────────────────────────────────────────────────────────┘
```

---

## BeeGFS

```
BeeGFS 特点: 简单、高性能、易部署

  组件: Management + Metadata Service + Storage Service + Client
  优势: 部署简单（几小时搭好）、开源免费、支持 RDMA、BuddyMirror HA
  劣势: 社区规模较小、超大规模经验较少
  适用: 中大规模 AI 集群（32-512 节点），追求易部署+高性能
```

---

## JuiceFS 深入

### 架构与优势

```
JuiceFS 核心设计: 元数据与数据完全分离

  ┌─────────────────────────────────────────┐
  │            JuiceFS Client               │
  │         (FUSE / CSI / S3 Gateway)       │
  │  本地缓存(SSD/RAM) + POSIX + 压缩/加密  │
  └────────┬────────────────────┬───────────┘
           │                    │
  ┌────────▼────────┐  ┌───────▼───────────┐
  │ Metadata Engine │  │ Data Storage      │
  │ Redis / TiKV /  │  │ S3 / MinIO / GCS  │
  │ PostgreSQL      │  │ / OSS / HDFS      │
  └─────────────────┘  └───────────────────┘

  为什么适合 AI?
  1. POSIX 兼容 → PyTorch/DeepSpeed 无需改代码
  2. K8s CSI Driver → 容器化集群直接挂载
  3. 弹性扩展 → 对象存储后端无限容量
  4. 本地缓存 → 热数据缓存到 NVMe，接近本地性能
  5. 低成本 → 比 Lustre 便宜 80%+
```

### JuiceFS 部署与调优

```bash
# 格式化
juicefs format \
    --storage s3 --bucket https://my-bucket.s3.amazonaws.com \
    --block-size 4096 --compress zstd \
    "redis://redis:6379/0" ai-fs

# 挂载（AI 优化参数）
juicefs mount \
    --cache-dir /nvme/jfs-cache \
    --cache-size 500000 \
    --buffer-size 2048 \
    --prefetch 5 \
    --writeback \
    "redis://redis:6379/0" /mnt/jfs

# 元数据引擎选择:
#   Redis: 最快，中小规模
#   TiKV: 大规模，需持久化
#   PostgreSQL/MySQL: 已有基础设施

# 数据预热
juicefs warmup /mnt/jfs/training_data/

# 监控
juicefs stats /mnt/jfs
```

---

## CephFS

```
Ceph 统一存储平台，三种接口: RBD(块) + RGW(对象) + CephFS(文件)

  MDS: 动态子树分区（自动负载均衡），多 MDS 支持
  OSD: CRUSH 算法确定数据位置（无需查询），多副本或纠删码
  MON: Paxos 共识，集群状态管理

  AI 适用性:
    ✓ 统一平台（块+文件+对象）、自动均衡、开源活跃
    ✗ 性能不如 Lustre/GPFS、运维复杂、大规模 AI 经验较少
```

---

## 全面对比与选型指南

| 维度 | Lustre | GPFS | BeeGFS | JuiceFS | CephFS |
|------|--------|------|--------|---------|--------|
| **最大吞吐** | 1+ TB/s | 1+ TB/s | 500+ GB/s | 取决于后端 | 100+ GB/s |
| **元数据性能** | 中(需DNE) | 高(分布式) | 高 | 取决于引擎 | 高(动态) |
| **部署难度** | 高 | 高 | 低 | 极低 | 中 |
| **成本** | 高(硬件) | 最高(许可) | 中 | 最低(云) | 中 |
| **云原生** | 弱 | 弱 | 中 | 强 | 中 |
| **RDMA** | 是 | 是 | 是 | 否 | 否 |
| **HA** | 手动 | 内置 | BuddyMirror | 后端保证 | 多副本 |

### 选型决策树

```
                    规模多大？
                       │
           ┌───────────┼───────────┐
        < 64 GPU    64-512 GPU   > 512 GPU
           │           │           │
       JuiceFS/NFS  需要最强性能？  Lustre/GPFS
                       │
                 ┌─────┴─────┐
                是          否
                 │           │
           预算充足？     JuiceFS/BeeGFS
                 │
           ┌─────┴─────┐
          是          否
           │           │
         GPFS      Lustre/BeeGFS
```

---

## 条带化与数据布局

```
条带化 (Striping) — 并行文件系统的核心性能机制:

  不条带化:        条带化 (3 个 OST):
  ┌──────────┐    ┌──────┐ ┌──────┐ ┌──────┐
  │ OST 1    │    │OST 1 │ │OST 2 │ │OST 3 │
  │ ████████ │    │ ██   │ │ ██   │ │ ██   │
  │ ████████ │    │ ██   │ │ ██   │ │ ██   │
  │ ████████ │    │ ██   │ │ ██   │ │ ██   │
  └──────────┘    └──────┘ └──────┘ └──────┘
  吞吐: 1×         吞吐: 3× (并行读写)

  stripe_count: 分散到多少个 OST
    -1 = 全部 OST（最大吞吐）
    1 = 单 OST（小文件最优）

  stripe_size: 每个条带的大小
    1M-4M: 适合顺序大文件读取（训练数据）
    16M: 适合大块突发写入（Checkpoint）

  AI 最佳实践:
    训练数据: count=-1, size=4M（最大并行读）
    Checkpoint: count=4-8, size=16M（减少锁争抢）
    小配置文件: count=1（避免分布开销）
```

---

## 性能调优实践

### 通用调优清单

```python
"""分布式文件系统 AI 性能调优清单"""

TUNING_CHECKLIST = {
    "客户端优化": [
        "增大客户端缓存 (max_cached_mb)",
        "增大预读窗口 (read_ahead_mb)",
        "增大并发 RPC 数 (max_rpcs_in_flight)",
        "启用直接 IO (O_DIRECT) 用于大块读写",
        "使用 mmap 避免多次 read 调用",
    ],
    "数据布局": [
        "训练数据使用高 stripe_count",
        "Checkpoint 使用适中 stripe_count + 大 stripe_size",
        "小文件使用 stripe_count=1",
        "使用 PFL 让文件自动选择最优布局",
    ],
    "网络优化": [
        "使用 RDMA 网络 (InfiniBand/RoCE)",
        "分离存储网络和计算网络",
        "增大 TCP 缓冲区 (net.core.rmem_max)",
    ],
    "数据格式": [
        "避免大量小文件 → 打包为 tar/WebDataset",
        "预生成索引文件 → 避免 readdir",
        "使用 mmap-friendly 格式 → 减少元数据操作",
    ],
    "监控告警": [
        "监控 OST/OSD 使用率均衡性",
        "监控 MDS 操作延迟",
        "监控客户端 RPC 排队深度",
        "设置带宽/IOPS 阈值告警",
    ],
}

for category, items in TUNING_CHECKLIST.items():
    print(f"\n{category}:")
    for i, item in enumerate(items, 1):
        print(f"  {i}. {item}")
```

### fio 基准测试

```bash
# fio 测试分布式文件系统性能

# 顺序读吞吐（模拟训练数据加载）
fio --name=seq_read --directory=/lustre/bench \
    --rw=read --bs=4M --size=10G \
    --numjobs=8 --group_reporting

# 顺序写吞吐（模拟 Checkpoint 写入）
fio --name=seq_write --directory=/lustre/bench \
    --rw=write --bs=16M --size=10G \
    --numjobs=4 --group_reporting --fsync=1

# 随机读 IOPS（模拟数据预处理）
fio --name=rand_read --directory=/lustre/bench \
    --rw=randread --bs=4k --size=1G \
    --numjobs=16 --group_reporting

# 多客户端聚合测试
# 在多个计算节点上同时运行，测量聚合带宽
```

---

## 延伸阅读

- [Lustre Documentation](https://doc.lustre.org/)
- [JuiceFS Documentation](https://juicefs.com/docs/)
- [BeeGFS Documentation](https://doc.beegfs.io/)
- [Ceph Documentation](https://docs.ceph.com/)
- [IBM Spectrum Scale Knowledge Center](https://www.ibm.com/docs/en/spectrum-scale)

---

*上一篇：[01-storage-fundamentals.md](01-storage-fundamentals.md)* | *下一篇：[03-checkpoint-storage.md](03-checkpoint-storage.md)*

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **Lustre.** *Lustre Wiki and Documentation.*  
   https://wiki.lustre.org/

2. **IBM.** *IBM Spectrum Scale (GPFS).*  
   https://www.ibm.com/products/storage-scale

3. **BeeGFS.** *BeeGFS Parallel File System.*  
   https://www.beegfs.io/

4. **JuiceFS.** *JuiceFS: Cloud-Native Distributed File System.*  
   https://juicefs.com/

5. **Ceph.** *CephFS Documentation.*  
   https://docs.ceph.com/en/latest/cephfs/

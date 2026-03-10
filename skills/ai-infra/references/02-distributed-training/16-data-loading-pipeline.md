# 分布式数据加载与预处理

> 再强的 GPU 也需要被"喂饱"——数据加载慢，GPU 就只能干等着。

## 目录

- [数据加载为什么是瓶颈](#数据加载为什么是瓶颈)
- [PyTorch DataLoader 深入](#pytorch-dataloader-深入)
- [分布式数据加载策略](#分布式数据加载策略)
- [高性能数据格式](#高性能数据格式)
- [WebDataset 与流式加载](#webdataset-与流式加载)
- [Mosaic Streaming](#mosaic-streaming)
- [GPU 加速预处理 (NVIDIA DALI)](#gpu-加速预处理-nvidia-dali)
- [IO 优化策略](#io-优化策略)

---

## 数据加载为什么是瓶颈

### 生活类比：餐厅后厨

```
GPU 训练就像一个超高效的厨师:

  厨师 (GPU): 切菜炒菜速度极快（算力强大）
  传菜员 (数据加载): 从仓库取食材送到厨房
  
  问题:
    厨师 3 秒做完一道菜
    传菜员 5 秒才能送到下一份食材
    → 厨师空闲 2 秒（GPU 利用率只有 60%）
  
  这就是 "Data Starvation"（数据饥饿）:
    GPU 计算速度 > 数据供给速度
    GPU 被迫等待数据，利用率下降
    
  大规模训练更严重:
    256 个 GPU 同时需要数据
    每步需要 256 × batch_size 条数据
    存储 IO 带宽被 256 个节点同时争抢
```

### 瓶颈量化分析

```
┌─────────────────────────────────────────────────────────────┐
│                数据加载瓶颈分析                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  典型 LLM 训练数据加载链:                                     │
│                                                             │
│  存储系统 → 网络 → 节点内存 → CPU预处理 → GPU显存             │
│  (NFS/S3)  (网络IO)  (读取)   (tokenize)  (传输)            │
│  ~1GB/s    ~10GB/s   ~30GB/s  ~变化大     ~32GB/s           │
│     ↑         ↑        ↑         ↑          ↑               │
│   通常最慢  可能瓶颈  足够快   单进程慢    足够快             │
│                                                             │
│  各阶段耗时 (以 GPT 训练为例):                                │
│  1. 从 NFS 读取: 100 ms/batch ← 通常瓶颈                    │
│  2. Tokenization: 10-50 ms/batch                            │
│  3. 数据增强: 5-20 ms/batch                                 │
│  4. GPU 传输: 1-5 ms/batch                                  │
│  5. GPU 计算: 200-2000 ms/batch                             │
│                                                             │
│  优化目标: 数据加载时间 < GPU 计算时间                        │
│  → 使用异步预取让数据加载和 GPU 计算重叠                      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## PyTorch DataLoader 深入

### DataLoader 内部机制

```
┌─────────────────────────────────────────────────────────────┐
│             PyTorch DataLoader 内部架构                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  主进程:                                                     │
│  ┌───────────────────────────────────┐                      │
│  │  DataLoader                       │                      │
│  │  ├── Sampler (决定读什么)          │                      │
│  │  │   └── DistributedSampler       │                      │
│  │  │       (多 GPU 分配不同数据)     │                      │
│  │  │                                │                      │
│  │  └── Worker 进程 (多进程读取)      │                      │
│  │      ┌────────┐ ┌────────┐        │                      │
│  │      │Worker 0│ │Worker 1│ ...    │                      │
│  │      │Dataset │ │Dataset │        │                      │
│  │      │.__get__│ │.__get__│        │                      │
│  │      └───┬────┘ └───┬────┘        │                      │
│  │          │          │             │                      │
│  │          └────┬─────┘             │                      │
│  │               │                   │                      │
│  │          ┌────▼─────┐             │                      │
│  │          │Prefetch  │             │                      │
│  │          │Queue     │             │                      │
│  │          └────┬─────┘             │                      │
│  │               │                   │                      │
│  │          ┌────▼─────┐             │                      │
│  │          │pin_memory│             │                      │
│  │          │thread    │             │                      │
│  │          └────┬─────┘             │                      │
│  │               │                   │                      │
│  │          GPU Transfer             │                      │
│  └───────────────────────────────────┘                      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### DataLoader 优化参数

```python
from torch.utils.data import DataLoader, DistributedSampler

# 优化后的 DataLoader 配置
dataloader = DataLoader(
    dataset,
    batch_size=32,
    
    # === 多进程加载 ===
    num_workers=8,           # CPU 核数的 50-80%
    # 注意: num_workers 太多会导致内存 OOM 和 CPU 争抢
    
    # === 内存优化 ===
    pin_memory=True,         # 使用页锁定内存，加速 GPU 传输
    # pin_memory 将数据放在不可交换的内存页中
    # CPU→GPU 传输速度提升 2-3×
    
    # === 预取 ===
    prefetch_factor=4,       # 每个 worker 预取 4 个 batch
    # prefetch_factor × num_workers 个 batch 在队列中等待
    
    # === 分布式采样 ===
    sampler=DistributedSampler(
        dataset,
        num_replicas=world_size,  # GPU 总数
        rank=rank,                # 当前 GPU ID
        shuffle=True,             # 每 epoch 打乱
        drop_last=True,           # 丢弃不完整 batch
    ),
    
    # === 其他优化 ===
    persistent_workers=True,  # Worker 不在 epoch 间重启
    # 避免每 epoch 重新 fork 进程和加载数据
    
    drop_last=True,          # 丢弃最后不完整 batch
)

# 重要: 每个 epoch 需要设置 sampler 的 epoch
for epoch in range(num_epochs):
    dataloader.sampler.set_epoch(epoch)  # 确保不同 epoch shuffle 不同
    for batch in dataloader:
        train_step(batch)
```

### 常见问题与解决

```
DataLoader 常见问题:

1. num_workers > 0 后内存暴涨
   原因: 每个 worker fork 后拷贝数据集对象
   解决: 使用内存映射 (mmap) 读取数据
         或使用 IterableDataset 替代 MapDataset

2. 数据加载仍然慢
   诊断: 
     import time
     for i, batch in enumerate(dataloader):
         if i == 0: t = time.time()
         if i == 10: print(f"10 batches: {time.time()-t:.2f}s"); break
   解决: 增加 num_workers / prefetch_factor
         使用更快的存储 (NVMe > HDD)
         使用 WebDataset / Streaming 格式

3. GPU 利用率波动大
   原因: 数据加载时快时慢
   解决: 增加 prefetch_factor 缓冲更多数据
         使用异步数据加载
```

---

## 分布式数据加载策略

### 数据分片策略

```
┌─────────────────────────────────────────────────────────────┐
│              分布式数据分片策略                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  策略 1: DistributedSampler (默认)                           │
│    数据集完整存在每个节点                                     │
│    Sampler 保证每个 GPU 读不同的数据                          │
│    优点: 简单，数据局部性好                                   │
│    缺点: 每个节点需要完整数据集副本                           │
│                                                             │
│  策略 2: 分片存储 (Sharded Dataset)                          │
│    数据预先分成 N 个 shard 文件                               │
│    每个节点只读自己的 shard                                   │
│    优点: 节省存储空间和 IO                                   │
│    缺点: shard 数需要和 GPU 数匹配                           │
│                                                             │
│  策略 3: 流式加载 (Streaming)                                │
│    从对象存储 (S3/GCS) 实时流式读取                           │
│    边下载边训练                                              │
│    优点: 不需要本地存储，数据可以很大                         │
│    缺点: 依赖网络带宽                                        │
│                                                             │
│  推荐:                                                       │
│  - 小数据集 (<100GB): 策略 1                                 │
│  - 中等数据集 (100GB-10TB): 策略 2                           │
│  - 超大数据集 (>10TB): 策略 3                                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 高性能数据格式

### 数据格式对比

| 格式 | 随机读取 | 顺序读取 | 压缩 | 适用场景 |
|------|---------|---------|------|---------|
| **JSON/JSONL** | 慢 | 慢 | 差 | 调试、小数据 |
| **CSV** | 慢 | 中 | 差 | 表格数据 |
| **Parquet** | 中 | 快 | 好 | 结构化数据、分析 |
| **Arrow/IPC** | 快 | 快 | 中 | 内存映射、零拷贝 |
| **WebDataset** | 无 | 极快 | 好 | 大规模训练 (流式) |
| **MDS (Mosaic)** | 快 | 极快 | 好 | 大规模训练 (流式+随机) |
| **TFRecord** | 无 | 快 | 中 | TensorFlow 生态 |
| **HDF5** | 快 | 快 | 好 | 科学计算 |
| **NumPy mmap** | 极快 | 极快 | 无 | 预 tokenized 文本 |

### 预 tokenization 策略

```python
# LLM 训练的最优数据格式: 预 tokenized + mmap

import numpy as np
from transformers import AutoTokenizer

# === 离线预处理（只做一次） ===
tokenizer = AutoTokenizer.from_pretrained("meta-llama/Llama-3-8B")

def preprocess_to_mmap(input_files, output_path, seq_len=2048):
    """将文本预先 tokenize 并保存为 mmap 格式"""
    all_tokens = []
    
    for f in input_files:
        with open(f) as fh:
            text = fh.read()
        tokens = tokenizer.encode(text)
        all_tokens.extend(tokens)
    
    # 截断到 seq_len 的整数倍
    total = (len(all_tokens) // seq_len) * seq_len
    tokens_array = np.array(all_tokens[:total], dtype=np.uint16)
    
    # 保存为 mmap 可读格式
    tokens_array.tofile(output_path)
    print(f"Saved {total} tokens to {output_path}")
    # 1TB 文本 ≈ 250B tokens ≈ 500GB mmap 文件

# === 训练时使用 mmap（零拷贝读取） ===
class MmapDataset:
    def __init__(self, path, seq_len=2048):
        self.data = np.memmap(path, dtype=np.uint16, mode='r')
        self.seq_len = seq_len
        self.n_samples = len(self.data) // seq_len
    
    def __len__(self):
        return self.n_samples
    
    def __getitem__(self, idx):
        start = idx * self.seq_len
        tokens = self.data[start:start + self.seq_len].astype(np.int64)
        return torch.from_numpy(tokens)

# 优势:
# 1. 零拷贝: mmap 直接映射文件到内存，OS 管理缓存
# 2. 零预处理: tokenization 已在离线完成
# 3. 随机访问: O(1) 时间访问任意 sample
# 4. 多进程安全: mmap 天然支持多进程共享
```

---

## WebDataset 与流式加载

### WebDataset

```
┌─────────────────────────────────────────────────────────────┐
│                WebDataset 原理                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  将数据打包成 tar 文件，顺序流式读取                          │
│                                                             │
│  传统方式:                                                   │
│    image_0001.jpg → 随机读取 → 多次 IO                       │
│    image_0002.jpg → 随机读取 → 多次 IO                       │
│    ...                                                      │
│    → 大量小文件 IO，文件系统元数据压力大                       │
│                                                             │
│  WebDataset:                                                 │
│    shard-0000.tar:  [img1.jpg, img1.json, img2.jpg, ...]    │
│    shard-0001.tar:  [img1001.jpg, ...]                      │
│    → 大文件顺序读取，IO 极其高效                              │
│    → 天然支持对象存储 (S3/GCS)                               │
│                                                             │
│  IO 效率对比:                                                │
│    1M 个小文件: ~1000 reads/s (IOPS 瓶颈)                   │
│    1000 个 tar: ~10 GB/s (顺序吞吐)                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

```python
import webdataset as wds

# 创建 WebDataset
# 数据目录结构:
# shards/
#   shard-000000.tar
#   shard-000001.tar
#   ...

# 训练时使用
dataset = (
    wds.WebDataset("s3://my-bucket/shards/shard-{000000..001023}.tar")
    .shuffle(10000)              # 在内存中 shuffle 10000 个样本
    .decode("pil")               # 解码图片
    .to_tuple("input.jpg", "output.json")
    .map_tuple(transform, identity)
    .batched(32)
)

# 自动分片到多个 worker 和多个 GPU
loader = wds.WebLoader(dataset, num_workers=8, batch_size=None)

# 分布式训练中自动均衡
loader = loader.ddp_equalize(1000)  # 确保每个 GPU 处理相同数量
```

---

## Mosaic Streaming

### MDS 格式

```
┌─────────────────────────────────────────────────────────────┐
│              Mosaic Streaming (MDS) 原理                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  MDS = WebDataset 的升级版                                    │
│                                                             │
│  WebDataset 的局限:                                          │
│  - 只支持顺序读取，不能随机访问                               │
│  - Shuffle 受限于内存缓冲区大小                               │
│  - Resume 训练时需要跳过已读数据                              │
│                                                             │
│  MDS 的改进:                                                 │
│  ✅ 支持随机访问 + 流式读取                                  │
│  ✅ 确定性 Shuffle（可复现）                                  │
│  ✅ 精确的断点续训（sample 级别）                             │
│  ✅ 弹性训练（GPU 数量变化时自动重新分片）                    │
│  ✅ 多源混合（混合不同数据集，控制比例）                      │
│                                                             │
│  工作原理:                                                   │
│  1. 数据存在远端 (S3/GCS/本地)                               │
│  2. 每个节点按需下载 shard 到本地缓存                        │
│  3. 下载和训练异步进行，互不阻塞                              │
│  4. 智能预取: 预测下一步需要的数据                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

```python
from streaming import StreamingDataset, MDSWriter

# === 创建 MDS 数据集 ===
columns = {"tokens": "ndarray:int32", "labels": "ndarray:int32"}

with MDSWriter(out="s3://my-bucket/mds-dataset/", columns=columns) as writer:
    for sample in raw_data:
        writer.write({
            "tokens": np.array(sample["tokens"], dtype=np.int32),
            "labels": np.array(sample["labels"], dtype=np.int32),
        })

# === 训练时使用 ===
dataset = StreamingDataset(
    remote="s3://my-bucket/mds-dataset/",
    local="/tmp/mds-cache/",          # 本地缓存目录
    shuffle=True,
    shuffle_algo="py1e",              # 确定性 shuffle
    batch_size=32,
    predownload=8 * 32,               # 预下载 8 个 batch
    num_canonical_nodes=16,           # 逻辑节点数 (弹性训练)
)

dataloader = DataLoader(
    dataset,
    batch_size=32,
    num_workers=8,
)

# 断点续训: 自动从上次位置继续
# 弹性训练: GPU 数量变化时自动重新分片，不丢失/重复数据
```

---

## GPU 加速预处理 (NVIDIA DALI)

### DALI 概述

```
┌─────────────────────────────────────────────────────────────┐
│                NVIDIA DALI 架构                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  传统流程:                                                   │
│  磁盘 → CPU 解码 → CPU 预处理 → GPU 传输 → GPU 训练         │
│              ↑          ↑                                    │
│           瓶颈 1      瓶颈 2                                  │
│                                                             │
│  DALI 流程:                                                  │
│  磁盘 → GPU 解码 → GPU 预处理 → GPU 训练                    │
│          (硬件解码器)  (CUDA 加速)                            │
│           ↑                                                  │
│        全部在 GPU 完成，CPU 几乎空闲                          │
│                                                             │
│  加速效果:                                                   │
│  - 图像解码: NVJPEG 比 CPU 解码快 5-10×                      │
│  - 数据增强: GPU 并行比 CPU 快 10-50×                        │
│  - 整体: 训练吞吐提升 20-40%                                 │
│                                                             │
│  特别适合:                                                   │
│  - 图像分类/检测训练 (大量图像解码+增强)                     │
│  - 视频模型训练 (视频解码极耗 CPU)                           │
│  - 多模态模型 (图像+文本混合)                                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

```python
from nvidia.dali.pipeline import Pipeline
import nvidia.dali.fn as fn
import nvidia.dali.types as types

# DALI Pipeline 示例 (图像分类训练)
@Pipeline.pipeline_def(batch_size=64, num_threads=8, device_id=0)
def training_pipeline():
    # 读取数据 (可以从文件/S3/WebDataset 读取)
    jpegs, labels = fn.readers.file(
        file_root="/data/imagenet/train",
        random_shuffle=True,
        name="Reader"
    )
    
    # GPU 解码 (使用 NVJPEG 硬件加速)
    images = fn.decoders.image(jpegs, device="mixed")  # CPU→GPU
    
    # GPU 上的数据增强
    images = fn.random_resized_crop(images, size=224)
    images = fn.flip(images, horizontal=fn.random.coin_flip())
    images = fn.color_twist(images, brightness=0.4, contrast=0.4)
    images = fn.crop_mirror_normalize(
        images,
        mean=[0.485 * 255, 0.456 * 255, 0.406 * 255],
        std=[0.229 * 255, 0.224 * 255, 0.225 * 255],
        dtype=types.FLOAT,
        output_layout="CHW"
    )
    
    return images, labels

# 创建 PyTorch 兼容的 DALI loader
from nvidia.dali.plugin.pytorch import DALIGenericIterator

pipe = training_pipeline()
pipe.build()

dali_loader = DALIGenericIterator(
    pipe, ["images", "labels"],
    reader_name="Reader"
)

# 训练循环
for batch in dali_loader:
    images = batch[0]["images"]  # 已经在 GPU 上！
    labels = batch[0]["labels"]
    loss = model(images, labels)
```

---

## IO 优化策略

### 分层优化清单

```
┌─────────────────────────────────────────────────────────────┐
│               IO 优化策略分层                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Level 1: 数据格式优化 (最高优先)                             │
│  ├── 预 tokenize，避免训练时做文本处理                        │
│  ├── 使用 mmap 格式，零拷贝读取                              │
│  ├── 大文件替代小文件 (WebDataset/MDS)                       │
│  └── 适当压缩 (zstd 压缩比好，解压快)                        │
│                                                             │
│  Level 2: DataLoader 调优                                    │
│  ├── num_workers = CPU 核数 × 50-80%                         │
│  ├── pin_memory = True                                       │
│  ├── prefetch_factor = 2-8                                   │
│  ├── persistent_workers = True                               │
│  └── drop_last = True (避免不均匀 batch)                     │
│                                                             │
│  Level 3: 存储架构优化                                       │
│  ├── 本地 NVMe SSD (最快，但容量有限)                        │
│  ├── 分布式文件系统 (Lustre/GPFS)                            │
│  ├── 对象存储 + 本地缓存 (S3 + NVMe)                        │
│  └── 数据分层: 热数据 NVMe，温数据 Lustre                    │
│                                                             │
│  Level 4: 高级优化                                           │
│  ├── NVIDIA DALI (GPU 解码+预处理)                           │
│  ├── GPUDirect Storage (GPU 直读存储)                        │
│  ├── 数据预取到内存 (足够内存时)                              │
│  └── 数据生成器 (合成数据，不需要 IO)                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 性能诊断

```python
import torch
import time

def diagnose_dataloader(dataloader, num_batches=50):
    """诊断 DataLoader 性能"""
    
    # 1. 纯数据加载速度
    load_times = []
    for i, batch in enumerate(dataloader):
        if i == 0:
            t = time.time()
            continue
        load_times.append(time.time() - t)
        t = time.time()
        if i >= num_batches:
            break
    
    avg_load = sum(load_times) / len(load_times)
    
    # 2. 数据加载 + GPU 传输
    transfer_times = []
    t = time.time()
    for i, batch in enumerate(dataloader):
        if isinstance(batch, dict):
            batch = {k: v.cuda(non_blocking=True) for k, v in batch.items()}
        elif isinstance(batch, (list, tuple)):
            batch = [b.cuda(non_blocking=True) for b in batch]
        torch.cuda.synchronize()
        transfer_times.append(time.time() - t)
        t = time.time()
        if i >= num_batches:
            break
    
    avg_transfer = sum(transfer_times) / len(transfer_times)
    
    print(f"=== DataLoader 性能诊断 ===")
    print(f"平均加载时间: {avg_load*1000:.1f} ms/batch")
    print(f"平均传输时间: {avg_transfer*1000:.1f} ms/batch")
    print(f"数据吞吐: {dataloader.batch_size / avg_load:.0f} samples/s")
    
    if avg_load > 0.1:  # > 100ms
        print("\n⚠️ 数据加载较慢，建议:")
        print("  - 增加 num_workers")
        print("  - 使用更快的存储 (NVMe)")
        print("  - 改用 mmap/WebDataset 格式")
```

---

## 小结

```
分布式数据加载核心要点:

1. 数据是训练的隐形瓶颈
   GPU 利用率低？先查数据加载
   优化数据加载可提升训练吞吐 20-50%

2. 预处理应离线完成
   Tokenization、图像 resize 等在训练前完成
   训练时只做必要的数据增强

3. 选对数据格式
   文本 LLM: 预 tokenize + mmap
   多模态: WebDataset/MDS + DALI
   大数据集: Mosaic Streaming

4. DataLoader 调参很重要
   num_workers、pin_memory、prefetch_factor
   persistent_workers 避免重启开销

5. 存储架构要匹配规模
   小规模: 本地 NVMe 足够
   中规模: 分布式文件系统
   超大规模: 对象存储 + 本地缓存
```

---

*返回：[README.md](README.md) - 章节索引*

---

## 参考资料与引用

1. **PyTorch Documentation.** *torch.utils.data.DataLoader.*  
   https://pytorch.org/docs/stable/data.html

2. **NVIDIA.** *DALI (Data Loading Library).* — GPU 加速数据预处理  
   https://docs.nvidia.com/deeplearning/dali/

3. **HuggingFace.** *Datasets Library.* — 高效数据集加载  
   https://huggingface.co/docs/datasets/

4. **MosaicML.** *StreamingDataset.* — 分布式流式数据加载  
   https://github.com/mosaicml/streaming

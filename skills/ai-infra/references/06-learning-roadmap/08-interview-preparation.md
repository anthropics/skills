# 面试准备指南

> AI Infra 岗位常见面试题和准备建议。

## 目录

- [面试题分类](#面试题分类)
- [GPU/CUDA 面试题](#gpucuda-面试题)
- [分布式训练面试题](#分布式训练面试题)
- [推理优化面试题](#推理优化面试题)
- [系统设计面试题](#系统设计面试题)
- [面试准备 Checklist](#面试准备-checklist)

---

## 面试题分类

| 类别 | 考察点 | 难度 |
|------|--------|------|
| GPU/CUDA | 硬件理解、编程能力 | ⭐⭐⭐ |
| 分布式训练 | 并行策略、通信优化 | ⭐⭐⭐⭐ |
| 推理优化 | LLM 推理特性、优化技术 | ⭐⭐⭐⭐ |
| 系统设计 | 架构能力、综合素质 | ⭐⭐⭐⭐⭐ |

---

## GPU/CUDA 面试题

### Q1: 解释 GPU 和 CPU 的主要区别？为什么 GPU 适合深度学习？

**参考答案**:

| 维度 | CPU | GPU |
|------|-----|-----|
| 核心数 | 少量强核 (8-64) | 大量弱核 (数千) |
| 设计目标 | 低延迟、通用性 | 高吞吐、并行性 |
| 适合任务 | 串行、分支多 | 并行、计算密集 |

GPU 适合深度学习的原因：
- 深度学习以矩阵运算为主，高度并行
- 大量相同操作作用于不同数据 (SIMD/SIMT)
- GPU 内存带宽远高于 CPU

### Q2: 什么是 Warp Divergence？如何避免？

**参考答案**:

Warp Divergence 是指同一个 Warp 内的线程执行不同的分支路径，导致串行执行。

```c
// 坏的例子 - Warp Divergence
if (threadIdx.x % 2 == 0) {
    // 一半线程执行这里
} else {
    // 另一半线程执行这里
}

// 好的例子 - 避免 Divergence
if (threadIdx.x < 16) {  // 整个 warp 要么都执行，要么都不执行
    // ...
}
```

避免方法：
- 让同一 Warp 内的线程执行相同分支
- 重组数据使条件判断一致
- 使用 predication 代替分支

### Q3: 解释 Coalesced Memory Access 的重要性

**参考答案**:

Coalesced Access 是指同一 Warp 内的线程访问连续的内存地址，可以合并为一次内存事务。

```
Coalesced (好):
Thread 0 → Addr 0
Thread 1 → Addr 4
Thread 2 → Addr 8
→ 一次 128B 内存事务

Non-Coalesced (坏):
Thread 0 → Addr 0
Thread 1 → Addr 128
Thread 2 → Addr 256
→ 三次内存事务
```

性能影响：Coalesced 访问可提升 10x+ 内存带宽利用率

### Q4: Tensor Core 是什么？如何使用？

**参考答案**:

Tensor Core 是 NVIDIA GPU 上专门用于矩阵乘加运算的硬件单元。

特点：
- 执行 D = A × B + C 矩阵运算
- 支持 FP16/BF16/INT8/FP8 输入
- 比 CUDA Core 快 8-16x

使用方法：
- PyTorch: `model.half()` + `torch.amp`
- CUDA: `wmma` API 或 cuBLAS

### Q5: 比较 NVLink 和 PCIe

**参考答案**:

| 特性 | PCIe 4.0 | NVLink 4.0 |
|------|----------|------------|
| 带宽 | ~64 GB/s | ~900 GB/s |
| 拓扑 | 通过 CPU | GPU 直连 |
| 延迟 | 较高 | 较低 |
| 成本 | 低 | 高 |

选择建议：
- 单卡/轻量多卡：PCIe 足够
- 大规模训练：NVLink 必要

---

## 分布式训练面试题

### Q1: 解释数据并行和模型并行的区别

**参考答案**:

| 策略 | 切分对象 | 通信内容 | 适用场景 |
|------|----------|----------|----------|
| 数据并行 | 数据 | 梯度 | 模型能装下一张卡 |
| 模型并行 | 模型参数 | 激活值 | 模型太大装不下 |

```
数据并行:
GPU0: Model完整 + Data[0:N/2]
GPU1: Model完整 + Data[N/2:N]
→ AllReduce 梯度

模型并行:
GPU0: Model[Layer 0-5] + Data全部
GPU1: Model[Layer 6-11] + Data全部
→ 传递激活值
```

### Q2: ZeRO 的三个阶段分别优化了什么？

**参考答案**:

| 阶段 | 分片内容 | 内存节省 |
|------|----------|----------|
| ZeRO-1 | 优化器状态 | ~4x |
| ZeRO-2 | + 梯度 | ~8x |
| ZeRO-3 | + 参数 | ~N x |

内存组成 (FP16 混合精度)：
- 参数: 2Ψ
- 梯度: 2Ψ
- 优化器状态 (Adam): 12Ψ (FP32 参数 + momentum + variance)

### Q3: 什么是 Ring AllReduce？画出通信流程

**参考答案**:

Ring AllReduce 将 N 个节点组成环，分两个阶段完成：

```
阶段 1: Scatter-Reduce
  每个节点将数据分成 N 份
  经过 N-1 步，每份数据在一个节点上被完全聚合

阶段 2: All-Gather
  经过 N-1 步，聚合结果广播到所有节点

总通信量: 2(N-1)/N × 数据量
```

优点：通信量不随节点数增加而增加

### Q4: 如何选择 DP/TP/PP 的并行度？

**参考答案**:

选择原则：

```
1. 数据并行 (DP): 优先使用，扩展性好
   - 限制: 每卡显存能装下完整模型

2. 张量并行 (TP): 同节点内使用
   - 适用: 模型太大装不下单卡
   - 限制: 跨节点通信开销大

3. 流水线并行 (PP): 跨节点使用
   - 适用: 需要更大并行度
   - 限制: 存在 bubble

推荐组合:
- 中等模型: DP=8
- 大模型: TP=8 (节点内), DP=8 (跨节点)
- 超大模型: TP=8, PP=4, DP=4 (3D并行)
```

---

## 推理优化面试题

### Q1: LLM 推理中 KV Cache 的作用是什么？

**参考答案**:

KV Cache 缓存已生成 token 的 Key 和 Value，避免重复计算。

```
无 KV Cache:
Token 1: 计算 Q1, K1, V1
Token 2: 重新计算 K1, V1 + 计算 K2, V2
...
复杂度: O(n³)

有 KV Cache:
Token 1: 计算 Q1, K1, V1, 缓存 K1, V1
Token 2: 只计算 Q2, K2, V2, 从缓存读 K1, V1
复杂度: O(n²)
```

### Q2: 解释 PagedAttention 的原理

**参考答案**:

PagedAttention 借鉴操作系统虚拟内存思想管理 KV Cache：

```
传统方式:
- 为每个请求预分配最大长度的连续内存
- 问题: 内存碎片、浪费严重

PagedAttention:
- KV Cache 按页 (block) 分配
- 逻辑连续，物理不连续
- 支持 prefix sharing

优势:
- 内存利用率提升 ~4x
- 支持更大 batch size
- 动态内存管理
```

### Q3: Continuous Batching 如何提升吞吐？

**参考答案**:

```
Static Batching:
- 整个 batch 等最长请求完成
- 短请求等待浪费 GPU

Continuous Batching:
- 请求完成立即移出 batch
- 新请求立即加入
- GPU 始终满载

效果: 吞吐提升 2-3x
```

### Q4: INT8 量化会带来什么影响？

**参考答案**:

| 维度 | 影响 |
|------|------|
| 模型大小 | 减少 ~4x (FP32→INT8) |
| 推理速度 | 提升 ~2-4x |
| 精度 | 可能下降 0.1-1% |
| 内存带宽 | 需求减少 |

量化方法：
- PTQ (训练后量化): 简单，精度损失较大
- QAT (量化感知训练): 精度保持好，需要重训
- GPTQ/AWQ: LLM 专用，精度损失小

---

## 系统设计面试题

### Q1: 设计一个支持多租户的 GPU 集群

**关键点**:

```
1. 资源管理
   - ResourceQuota 限制每个租户资源
   - Priority Class 定义优先级

2. 调度策略
   - 公平调度
   - Gang Scheduling (分布式任务)
   - 抢占机制

3. 隔离
   - Namespace 隔离
   - 网络策略
   - GPU MIG 或时间分片

4. 监控计费
   - 资源使用监控
   - 成本分摊
```

### Q2: 设计一个 LLM 推理服务的高可用架构

**关键点**:

```
架构组件:
- Load Balancer: 请求分发
- 多副本: 故障转移
- 健康检查: 自动剔除故障节点
- 自动扩缩容: HPA

关键指标:
- TTFT (首 token 延迟)
- TPS (吞吐)
- 可用性 99.9%

优化策略:
- Prefill/Decode 分离
- 请求路由优化
- 缓存复用
```

---

## 面试准备 Checklist

### 必须掌握

- [ ] 能手写 DDP 训练代码
- [ ] 能解释 ZeRO-1/2/3 的区别
- [ ] 能画出 Transformer 的并行切分方式
- [ ] 能计算模型训练的显存需求
- [ ] 能解释 vLLM 的核心优化
- [ ] 能设计基本的 ML 平台架构

### 加分项

- [ ] 做过至少一个完整的 AI Infra 项目
- [ ] 读过至少 3 篇核心论文
- [ ] 有开源项目贡献
- [ ] 有技术博客

### 显存估算公式

```python
# 训练显存估算 (FP16 混合精度)
def estimate_memory(params_billion, batch_size, seq_len, hidden_size):
    # 参数: 2 bytes/param
    param_mem = params_billion * 1e9 * 2
    
    # 梯度: 2 bytes/param
    grad_mem = params_billion * 1e9 * 2
    
    # 优化器状态 (Adam): 12 bytes/param
    optim_mem = params_billion * 1e9 * 12
    
    # 激活值 (估算)
    activation_mem = batch_size * seq_len * hidden_size * 2 * 12  # 12 layers
    
    total_gb = (param_mem + grad_mem + optim_mem + activation_mem) / 1e9
    return total_gb
```

---

## 延伸阅读

- [核心技能清单](./05-core-skills.md)
- [社区与持续学习](./09-community-learning.md)
- [动手项目建议](./07-hands-on-projects.md)

---

*返回章节：[学习路线图](./README.md)*

---

## 参考资料与引用

1. **Chip Huyen.** *Machine Learning Interviews Book.*  
   https://huyenchip.com/ml-interviews-book/

2. **LeetCode.** *Machine Learning Interview Questions.*  
   https://leetcode.com/

3. **Educative.** *Grokking the Machine Learning Interview.*  
   https://www.educative.io/courses/grokking-the-machine-learning-interview

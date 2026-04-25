# 学习资源推荐

> 精选的博客、视频、课程和开源项目，帮你从不同角度理解 AI 训练。

## 目录

- [视频课程（强烈推荐）](#视频课程强烈推荐)
- [经典博客文章](#经典博客文章)
- [动手实践项目](#动手实践项目)
- [可视化工具](#可视化工具)
- [论文入门](#论文入门)
- [中文资源](#中文资源)
- [按主题分类的学习路径](#按主题分类的学习路径)

---

## 视频课程（强烈推荐）

### 入门级：建立直觉

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ 3Blue1Brown - Neural Networks 系列                  │
│  ─────────────────────────────────────────                       │
│  链接: https://www.youtube.com/playlist?list=PLZHQObOWTQDNU6R1   │
│  _67000Dx_ZCJB-3pi                                              │
│                                                                   │
│  为什么推荐:                                                      │
│  - 全网最佳的深度学习可视化讲解，没有之一                        │
│  - 用动画直观展示神经网络、梯度下降、反向传播                    │
│  - 不需要数学背景也能看懂                                        │
│  - 特别推荐:                                                      │
│    · Chapter 1: 什么是神经网络                                   │
│    · Chapter 2: 梯度下降，网络如何学习                           │
│    · Chapter 3: 反向传播是什么                                   │
│    · Chapter 4: 反向传播的微积分                                 │
│                                                                   │
│  适合: 完全零基础的初学者                                         │
│  时长: 约 1 小时                                                  │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Andrej Karpathy - Neural Networks: Zero to Hero    │
│  ─────────────────────────────────────────                       │
│  链接: https://www.youtube.com/playlist?list=PLAqhIrjkxbuWI23v9 │
│  cThsA9GvCAUhRvKZ                                              │
│                                                                   │
│  为什么推荐:                                                      │
│  - Karpathy 是 OpenAI 前研究总监、Tesla AI 负责人               │
│  - 从零开始手写一个神经网络，每一行代码都解释                    │
│  - 特别推荐:                                                      │
│    · Lecture 1 (micrograd): 从零实现反向传播和自动微分           │
│    · Lecture 2 (makemore 1): 字符级语言模型                      │
│    · Lecture 7 (GPT from scratch): 从零构建 GPT                  │
│                                                                   │
│  适合: 有一点 Python 基础、想动手实现的人                        │
│  时长: 每集 1-2 小时，共约 15 小时                                │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 进阶级：深入理解

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Stanford CS231n - 深度学习与计算机视觉              │
│  ─────────────────────────────────────────                       │
│  链接: https://www.youtube.com/playlist?list=PLC1qU-LWwrF64f4WV │
│  AJP5ydoNRPl3mVCkq7dQ                                           │
│  课程网站: https://cs231n.stanford.edu/                           │
│                                                                   │
│  为什么推荐:                                                      │
│  - 斯坦福经典课程，也是 Karpathy 早年教的                       │
│  - 深入讲解反向传播、梯度下降、各种优化器                        │
│  - 特别推荐:                                                      │
│    · Lecture 3: Loss Functions and Optimization                   │
│    · Lecture 4: Backpropagation                                   │
│    · Lecture 6: Training Neural Networks I                        │
│    · Lecture 7: Training Neural Networks II                       │
│                                                                   │
│  适合: 想系统深入学习的人                                         │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Stanford CS229 - 机器学习                              │
│  ──────────────────────────────                                  │
│  链接: https://www.youtube.com/playlist?list=PLoROMvodv4rMiGQp3W │
│  NF-WbhYI7zH3EVgmK                                              │
│                                                                   │
│  为什么推荐:                                                      │
│  - Andrew Ng (吴恩达) 的经典课程                                 │
│  - 从数学角度理解梯度下降、正则化等概念                          │
│  - 比 CS231n 更偏理论                                            │
│                                                                   │
│  适合: 想补数学基础的人                                           │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Hung-yi Lee (李宏毅) - 机器学习/深度学习              │
│  ──────────────────────────────────────                          │
│  链接: https://www.youtube.com/c/HungyiLeeNTU                    │
│  课程主页: https://speech.ee.ntu.edu.tw/~hylee/ml/2023-spring.php│
│                                                                   │
│  为什么推荐:                                                      │
│  - 中文授课，台湾大学教授                                        │
│  - 讲解风格幽默，常用生活例子类比                                │
│  - 每年更新，覆盖最新的 LLM、Transformer 等                     │
│  - 特别推荐 2023/2024 年的 LLM 相关课程                         │
│                                                                   │
│  适合: 偏好中文学习的初/中级学习者                                │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 大模型专题

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Andrej Karpathy - Let's build GPT from scratch     │
│  ──────────────────────────────────────────                      │
│  链接: https://www.youtube.com/watch?v=kCc8FmEb1nY               │
│                                                                   │
│  2小时从零构建一个 GPT 模型                                      │
│  从数据加载到 Transformer 到训练，全部手写                       │
│  是理解 LLM 训练的最佳实践视频                                   │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Umar Jamil - Transformer 系列讲解                     │
│  ─────────────────────────────────────                           │
│  链接: https://www.youtube.com/@uaborob/videos                    │
│                                                                   │
│  非常详细的 Transformer 原理讲解                                  │
│  从 Attention 机制到完整的 GPT/LLaMA 架构                        │
│  配有清晰的图解和代码                                            │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 经典博客文章

### 训练基础

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Lilian Weng 的博客                                  │
│  ──────────────────────────                                      │
│  地址: https://lilianweng.github.io/                              │
│                                                                   │
│  OpenAI 研究员的博客，AI 领域最好的技术博客之一                  │
│  文章深入浅出，图文并茂                                          │
│                                                                   │
│  必读文章:                                                        │
│  · "From Autoencoder to Beta-VAE"                                │
│  · "Attention? Attention!"                                       │
│    → Transformer 注意力机制最清晰的讲解                         │
│  · "The Transformer Family"                                      │
│    → Transformer 变体全家福                                      │
│  · "Large Transformer Model Inference Optimization"              │
│    → 大模型推理优化                                              │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Jay Alammar 的博客                                  │
│  ──────────────────────────                                      │
│  地址: https://jalammar.github.io/                                │
│                                                                   │
│  以可视化闻名的 AI 博客                                          │
│                                                                   │
│  必读文章:                                                        │
│  · "The Illustrated Transformer"                                 │
│    → 全网最好的 Transformer 图解，没有之一                      │
│    → https://jalammar.github.io/illustrated-transformer/         │
│  · "The Illustrated GPT-2"                                       │
│    → GPT 架构可视化讲解                                         │
│  · "Visualizing A Neural Machine Translation Model"              │
│    → Attention 机制可视化                                        │
│  · "The Illustrated Word2vec"                                    │
│    → 词向量入门                                                  │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Chris Olah 的博客                                     │
│  ─────────────────────────                                       │
│  地址: https://colah.github.io/                                   │
│                                                                   │
│  必读文章:                                                        │
│  · "Understanding LSTM Networks"                                 │
│    → LSTM 最经典的讲解                                           │
│  · "Neural Networks, Manifolds, and Topology"                    │
│    → 从拓扑角度理解神经网络                                     │
│  · "Calculus on Computational Graphs: Backpropagation"           │
│    → 反向传播的清晰讲解                                         │
│    → https://colah.github.io/posts/2015-08-Backprop/            │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 大模型训练与分布式

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Hugging Face - 大模型训练系列                      │
│  ─────────────────────────────────────                           │
│  地址: https://huggingface.co/docs/transformers/perf_train_gpu   │
│  _many                                                            │
│                                                                   │
│  Hugging Face 官方的多 GPU 训练指南                               │
│  覆盖数据并行、模型并行、ZeRO、混合精度等                       │
│  配有完整代码示例                                                │
│                                                                   │
│  相关:                                                            │
│  · "Model Parallelism"                                           │
│    → https://huggingface.co/docs/transformers/v4.15.0/           │
│      parallelism                                                  │
│  · "Efficient Training on Multiple GPUs"                         │
│    → 多 GPU 训练的方方面面                                       │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Microsoft DeepSpeed 官方博客                        │
│  ──────────────────────────────────                              │
│  地址: https://www.microsoft.com/en-us/research/blog/            │
│  zero-deepspeed-new-system-optimizations-enable-training-models  │
│  -with-over-100-billion-parameters/                               │
│                                                                   │
│  ZeRO 论文作者写的博客，用清晰的图解释:                         │
│  · 为什么需要 ZeRO                                               │
│  · ZeRO Stage 1/2/3 分别做了什么                                 │
│  · 显存是如何被优化的                                            │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ NVIDIA 技术博客                                       │
│  ──────────────────────────                                      │
│  地址: https://developer.nvidia.com/blog/                         │
│                                                                   │
│  推荐文章:                                                        │
│  · "Scaling Language Model Training to a Trillion Parameters     │
│    Using Megatron"                                                │
│    → Megatron-LM 3D 并行实践                                    │
│  · "Massively Scaling NCCL"                                      │
│    → NCCL 通信优化深入讲解                                      │
│  · "Using NVIDIA NCCL for Multi-GPU Communication"               │
│    → NCCL 入门指南                                               │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 动手实践项目

### 从零实现（强烈推荐）

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Karpathy/micrograd                                  │
│  ─────────────────────────                                       │
│  链接: https://github.com/karpathy/micrograd                      │
│                                                                   │
│  用 ~100 行 Python 实现一个完整的自动微分引擎                    │
│  包含: 反向传播、计算图、梯度计算                                │
│  配套视频: Neural Networks: Zero to Hero 第1集                   │
│                                                                   │
│  你能学到:                                                        │
│  - 反向传播到底在做什么                                          │
│  - 链式法则如何在代码中实现                                      │
│  - PyTorch autograd 的核心思想                                   │
│                                                                   │
│  建议: 先看视频，再自己从零写一遍                                │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ Karpathy/nanoGPT                                    │
│  ─────────────────────────                                       │
│  链接: https://github.com/karpathy/nanoGPT                        │
│                                                                   │
│  用 ~300 行 PyTorch 代码实现 GPT 模型                            │
│  可以在单卡上训练一个小型语言模型                                │
│  代码极其简洁，每一行都有教学意义                                │
│                                                                   │
│  你能学到:                                                        │
│  - Transformer 架构如何实现                                      │
│  - 训练循环的完整流程                                            │
│  - 数据加载、学习率调度、checkpointing                           │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Karpathy/llm.c                                        │
│  ────────────────────────                                        │
│  链接: https://github.com/karpathy/llm.c                          │
│                                                                   │
│  用纯 C/CUDA 实现 GPT-2 训练                                    │
│  不依赖 PyTorch！直接操作 GPU                                    │
│  展示了框架背后到底做了什么                                      │
│                                                                   │
│  你能学到:                                                        │
│  - 矩阵乘法如何在 GPU 上运行                                    │
│  - 反向传播的底层实现                                            │
│  - PyTorch 帮你隐藏了多少复杂性                                  │
│                                                                   │
│  适合: 想深入理解底层实现的进阶学习者                            │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

### 分布式训练实践

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ PyTorch 官方教程                                      │
│  ─────────────────────────                                       │
│  DDP 教程: https://pytorch.org/tutorials/intermediate/           │
│  ddp_tutorial.html                                                │
│  FSDP 教程: https://pytorch.org/tutorials/intermediate/          │
│  FSDP_tutorial.html                                               │
│                                                                   │
│  PyTorch 官方的分布式训练教程                                    │
│  从最简单的 DDP 开始，逐步深入                                   │
│                                                                   │
│  ⭐⭐⭐⭐ DeepSpeed Examples                                    │
│  ─────────────────────────────                                   │
│  链接: https://github.com/microsoft/DeepSpeedExamples             │
│                                                                   │
│  DeepSpeed 官方示例代码                                           │
│  包含 ZeRO、3D 并行等完整训练脚本                                │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 可视化工具

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ TensorFlow Playground                               │
│  ─────────────────────────────                                   │
│  链接: https://playground.tensorflow.org/                         │
│                                                                   │
│  在浏览器中交互式训练神经网络                                    │
│  可以实时看到:                                                    │
│  - 训练过程中网络如何学习                                        │
│  - 不同激活函数的效果                                            │
│  - 学习率对训练的影响                                            │
│  - 网络深度和宽度的影响                                          │
│  强烈推荐亲手试一试！                                            │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ Loss Landscape Visualization                           │
│  ──────────────────────────────────                              │
│  论文: "Visualizing the Loss Landscape of Neural Nets"           │
│  链接: https://arxiv.org/abs/1712.09913                           │
│  代码: https://github.com/tomgoldstein/loss-landscape            │
│                                                                   │
│  把高维 Loss Surface 投影到 2D/3D 进行可视化                     │
│  你可以直观看到:                                                  │
│  - 不同模型架构的 Loss Surface 差异                              │
│  - 残差连接如何让 Loss Surface 变得更平滑                       │
│  - 为什么大模型比小模型更好训练                                  │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘

┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐ CNN Explainer                                          │
│  ─────────────────────                                           │
│  链接: https://poloclub.github.io/cnn-explainer/                  │
│                                                                   │
│  交互式可视化 CNN（卷积神经网络）的工作原理                      │
│  虽然主要是 CNN，但能帮你理解前向传播的过程                      │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 论文入门

### 必读论文（按难度排序）

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  入门级:                                                          │
│  ──────                                                          │
│  1. "Attention Is All You Need" (2017)                           │
│     → Transformer 原始论文，现代 LLM 的基础                     │
│     → https://arxiv.org/abs/1706.03762                           │
│     → 建议先看 Jay Alammar 的图解博客再读论文                   │
│                                                                   │
│  2. "BERT: Pre-training of Deep Bidirectional Transformers"      │
│     → 预训练 + 微调范式的开创者                                  │
│     → https://arxiv.org/abs/1810.04805                           │
│                                                                   │
│  3. "Language Models are Few-Shot Learners" (GPT-3)              │
│     → 大模型 scaling 的里程碑                                    │
│     → https://arxiv.org/abs/2005.14165                           │
│                                                                   │
│  进阶级 (AI Infra 方向):                                         │
│  ──────────────────────                                          │
│  4. "Megatron-LM" (2019)                                        │
│     → 张量并行、模型并行的经典实现                               │
│     → https://arxiv.org/abs/1909.08053                           │
│                                                                   │
│  5. "ZeRO: Memory Optimizations Toward Training Trillion         │
│     Parameter Models" (2019)                                      │
│     → 显存优化革命                                               │
│     → https://arxiv.org/abs/1910.02054                           │
│                                                                   │
│  6. "FlashAttention: Fast and Memory-Efficient Exact Attention"  │
│     → 注意力计算优化                                             │
│     → https://arxiv.org/abs/2205.14135                           │
│                                                                   │
│  7. "Training Compute-Optimal Large Language Models"             │
│     (Chinchilla, 2022)                                            │
│     → 训练数据量 vs 模型大小的最优比例                           │
│     → https://arxiv.org/abs/2203.15556                           │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 中文资源

```
┌──────────────────────────────────────────────────────────────────┐
│                                                                   │
│  ⭐⭐⭐⭐⭐ 李宏毅老师 - 机器学习/深度学习课程                 │
│  ──────────────────────────────────────                          │
│  B站: https://space.bilibili.com/714463534                        │
│  YouTube: https://www.youtube.com/c/HungyiLeeNTU                 │
│  特点: 中文授课，幽默易懂，每年更新                              │
│                                                                   │
│  ⭐⭐⭐⭐⭐ 动手学深度学习 (d2l.ai)                              │
│  ──────────────────────────────────                              │
│  链接: https://zh.d2l.ai/                                         │
│  特点: 李沐等人编写的交互式深度学习教材                          │
│        配有完整的 PyTorch 代码                                   │
│        中英双语，可以在线运行代码                                │
│  推荐章节:                                                        │
│  · 第3章: 线性回归 (理解训练循环)                                │
│  · 第4章: 多层感知机 (理解神经网络)                              │
│  · 第11章: 优化算法                                              │
│                                                                   │
│  ⭐⭐⭐⭐ 李沐 - 论文精读系列                                   │
│  ──────────────────────────                                      │
│  B站: https://space.bilibili.com/1567748478                       │
│  特点: 逐行精读经典论文 (Transformer, BERT, GPT 等)              │
│        中文讲解 + 代码实现                                       │
│        非常适合想读论文但觉得难的人                              │
│                                                                   │
│  ⭐⭐⭐⭐ HuggingFace 中文社区                                  │
│  ──────────────────────────────                                  │
│  链接: https://huggingface.co/docs/transformers/zh/index          │
│  特点: Transformer 库的中文文档                                  │
│        包含大量训练教程                                          │
│                                                                   │
│  ⭐⭐⭐ 吴恩达 - 深度学习专项课程                               │
│  ──────────────────────────────                                  │
│  链接: https://www.coursera.org/specializations/deep-learning     │
│  B站有中文字幕版                                                 │
│  特点: 系统全面，适合打基础                                      │
│        5门课覆盖神经网络、优化、CNN、RNN 等                     │
│                                                                   │
└──────────────────────────────────────────────────────────────────┘
```

---

## 按主题分类的学习路径

### 想理解"训练是什么"

```
推荐顺序:
1. 3Blue1Brown 视频系列 (1小时) → 建立直觉
2. TensorFlow Playground (30分钟) → 亲手体验
3. 本文档 01-06 章节 → 系统学习
4. Karpathy micrograd 视频+代码 → 动手实现
```

### 想理解"Transformer/LLM"

```
推荐顺序:
1. Jay Alammar "The Illustrated Transformer" → 图解入门
2. 3Blue1Brown "Attention" 视频 → 可视化理解
3. Karpathy "Let's build GPT" → 从零实现
4. 阅读 "Attention Is All You Need" 论文
5. nanoGPT 代码 → 实战训练
```

### 想理解"分布式训练/AI Infra"

```
推荐顺序:
1. 本文档 01-06 章节 → 训练基础
2. 09-nccl-communication.md → 通信基础
3. 02-distributed-training/ 系列 → 分布式训练
4. DeepSpeed 博客 → ZeRO 优化
5. NVIDIA 博客 → NCCL 和 Megatron
6. DeepSpeedExamples → 动手实践
```

### 想看论文但觉得难

```
推荐方法:
1. 先看李沐的论文精读视频 (有中文讲解)
2. 再看 Lilian Weng 的博客总结 (图文并茂)
3. 最后再读原始论文
→ 这样论文就不难了!
```

---

## 速查表

| 主题 | 最佳入门资源 | 最佳深入资源 |
|------|-------------|-------------|
| 神经网络基础 | 3Blue1Brown 视频 | CS231n 课程 |
| 反向传播 | Chris Olah 博客 | micrograd 代码 |
| Transformer | Jay Alammar 博客 | Karpathy GPT 视频 |
| 训练实践 | nanoGPT 代码 | d2l.ai 教材 |
| 分布式训练 | HuggingFace 文档 | Megatron-LM 论文 |
| 优化器 | 本文档 06 章 | AdamW 原始论文 |
| NCCL/通信 | NVIDIA 博客 | NCCL 源码 |

---

- **上一篇**：[07-群山中找最低点](07-mountain-valley-training.md)
- **下一篇**：[09-NCCL 与 GPU 通信科普](09-nccl-communication.md)

---

## 参考资料与引用

1. **3Blue1Brown.** *Neural Networks (Playlist).* — 最佳神经网络可视化讲解  
   https://www.youtube.com/playlist?list=PLZHQObOWTQDNU6R1_67000Dx_ZCJB-3pi

2. **Karpathy, A.** *Neural Networks: Zero to Hero (Playlist).* — 从零构建神经网络  
   https://www.youtube.com/playlist?list=PLAqhIrjkxbuWI23v9cThsA9GvCAUhRvKZ

3. **Alammar, J.** *The Illustrated Transformer.* — Transformer 最佳图解  
   https://jalammar.github.io/illustrated-transformer/

4. **Olah, C.** *Understanding LSTM Networks.* — RNN/LSTM 可视化讲解  
   https://colah.github.io/posts/2015-08-Understanding-LSTMs/

5. **Stanford CS231n.** *Convolutional Neural Networks for Visual Recognition.* — 经典深度学习课程  
   https://cs231n.stanford.edu/

6. **d2l.ai.** *Dive into Deep Learning.* — 交互式深度学习教材  
   https://d2l.ai/

7. **Karpathy, A.** *nanoGPT.* — 最简 GPT 训练代码  
   https://github.com/karpathy/nanoGPT

8. **Shoeybi, M., et al. (2020).** *Megatron-LM: Training Multi-Billion Parameter Language Models Using Model Parallelism.* — 大模型分布式训练  
   https://arxiv.org/abs/1909.08053

# 推荐资源汇总

> AI Infra 学习必备的书籍、课程、论文和链接。

## 目录

- [必读书籍](#必读书籍)
- [推荐课程](#推荐课程)
- [必读论文](#必读论文)
- [常用链接](#常用链接)
- [学习资源使用建议](#学习资源使用建议)

---

## 必读书籍

### 核心书籍

| 书名 | 领域 | 难度 | 推荐理由 |
|------|------|------|----------|
| *Programming Massively Parallel Processors* (PMPP) | GPU/CUDA | ⭐⭐⭐ | CUDA 编程圣经，必读 |
| *Designing Data-Intensive Applications* (DDIA) | 分布式系统 | ⭐⭐⭐ | 分布式基础，强烈推荐 |
| *Designing Machine Learning Systems* | MLOps | ⭐⭐ | ML 系统设计实践 |
| *Efficient Processing of Deep Neural Networks* | 推理优化 | ⭐⭐⭐⭐ | 硬件+算法优化深度 |
| *Computer Architecture: A Quantitative Approach* | 体系结构 | ⭐⭐⭐⭐ | 深入理解硬件 |

### 补充书籍

| 书名 | 领域 | 说明 |
|------|------|------|
| *Deep Learning* (Goodfellow) | DL 基础 | 深度学习理论基础 |
| *动手学深度学习* | DL 实践 | 中文友好，代码实践 |
| *Kubernetes in Action* | K8s | K8s 详细指南 |
| *Site Reliability Engineering* | SRE | Google SRE 实践 |

### 阅读建议

```
优先级排序:
1. PMPP (GPU/CUDA 必读)
2. DDIA (分布式基础)
3. Designing ML Systems (MLOps)
4. 其他按需选读

阅读方法:
- 不必从头读到尾，先读相关章节
- 边读边实践，代码跑起来
- 做笔记，写博客总结
```

---

## 推荐课程

### 在线课程

| 课程 | 平台 | 内容 | 链接 |
|------|------|------|------|
| CS149: Parallel Computing | Stanford | 并行计算基础 | [链接](https://gfxcourses.stanford.edu/cs149) |
| Full Stack Deep Learning | Berkeley | 生产级 ML 系统 | [链接](https://fullstackdeeplearning.com/) |
| Made With ML | 独立 | MLOps 实践 | [链接](https://madewithml.com/) |
| fast.ai | 独立 | DL 实践入门 | [链接](https://course.fast.ai/) |
| CUDA Training | NVIDIA | CUDA 官方培训 | [链接](https://developer.nvidia.com/cuda-training) |

### 课程详细介绍

#### CS149: Parallel Computing

```
内容概要:
- 并行编程模型
- GPU 架构和 CUDA
- 性能优化
- 并行算法

适合人群: 想深入理解并行计算原理
学习时长: 10-12 周
难度: 中高
```

#### Full Stack Deep Learning

```
内容概要:
- ML 项目全生命周期
- 数据管理
- 模型训练和部署
- 团队协作

适合人群: 想了解生产级 ML 系统
学习时长: 4-6 周
难度: 中
```

#### NVIDIA CUDA Training

```
内容概要:
- CUDA C++ 基础
- 内存优化
- Profiling
- 高级优化技术

适合人群: 想学习 CUDA 编程
学习时长: 2-4 周
难度: 中
```

---

## 必读论文

### 核心论文列表

| 论文 | 年份 | 领域 | 重要性 |
|------|------|------|--------|
| Attention Is All You Need | 2017 | Transformer | ⭐⭐⭐⭐⭐ |
| Megatron-LM | 2019 | 模型并行 | ⭐⭐⭐⭐⭐ |
| ZeRO | 2020 | 内存优化 | ⭐⭐⭐⭐⭐ |
| FlashAttention | 2022 | 推理优化 | ⭐⭐⭐⭐⭐ |
| PagedAttention (vLLM) | 2023 | 推理优化 | ⭐⭐⭐⭐⭐ |
| GPipe | 2018 | 流水线并行 | ⭐⭐⭐⭐ |
| Ring-AllReduce | 2017 | 通信优化 | ⭐⭐⭐⭐ |

### 论文阅读顺序建议

```
入门阶段:
1. Attention Is All You Need - 理解 Transformer
2. Megatron-LM - 理解模型并行
3. ZeRO - 理解内存优化

进阶阶段:
4. FlashAttention - 理解 IO-aware 算法
5. PagedAttention - 理解推理内存管理
6. GPipe - 理解流水线调度

深入阶段:
7. 阅读后续改进论文
8. 跟踪最新 arXiv
```

### 论文阅读方法

```
第一遍: 快速浏览
- 读标题、摘要、结论
- 看图表
- 理解主要贡献

第二遍: 理解方法
- 读 Method 部分
- 理解核心算法
- 对照代码实现

第三遍: 深入细节
- 读 Related Work
- 理解设计决策
- 思考改进空间
```

---

## 常用链接

### 官方文档

| 资源 | 链接 | 说明 |
|------|------|------|
| PyTorch Distributed | [链接](https://pytorch.org/docs/stable/distributed.html) | 分布式训练 |
| DeepSpeed | [链接](https://www.deepspeed.ai/) | 大模型训练框架 |
| vLLM | [链接](https://docs.vllm.ai/) | LLM 推理框架 |
| NVIDIA Developer | [链接](https://developer.nvidia.com/) | GPU 开发资源 |
| Megatron-LM | [链接](https://github.com/NVIDIA/Megatron-LM) | 大模型训练 |
| Kubernetes | [链接](https://kubernetes.io/docs/) | 容器编排 |
| MLflow | [链接](https://mlflow.org/docs/latest/) | 实验跟踪 |

### 技术博客

| 博客 | 链接 | 特点 |
|------|------|------|
| NVIDIA Technical Blog | [链接](https://developer.nvidia.com/blog/) | 官方技术分享 |
| Hugging Face Blog | [链接](https://huggingface.co/blog/) | 模型和工具 |
| PyTorch Blog | [链接](https://pytorch.org/blog/) | 框架更新 |
| OpenAI Blog | [链接](https://openai.com/blog/) | 前沿研究 |
| Anthropic Research | [链接](https://www.anthropic.com/research) | AI 安全研究 |

### 开源项目

| 项目 | GitHub | 说明 |
|------|--------|------|
| Megatron-LM | NVIDIA/Megatron-LM | 大模型训练 |
| DeepSpeed | microsoft/DeepSpeed | 分布式训练 |
| vLLM | vllm-project/vllm | LLM 推理 |
| Ray | ray-project/ray | 分布式计算 |
| Triton | openai/triton | GPU 编程语言 |
| FlashAttention | Dao-AILab/flash-attention | 高效 Attention |
| text-generation-inference | huggingface/text-generation-inference | LLM 服务 |

### 数据集和模型

| 资源 | 链接 | 说明 |
|------|------|------|
| Hugging Face Hub | [链接](https://huggingface.co/models) | 模型仓库 |
| Papers With Code | [链接](https://paperswithcode.com/) | 论文+代码 |
| Kaggle | [链接](https://www.kaggle.com/) | 数据集+竞赛 |

---

## 学习资源使用建议

### 资源优先级

```python
# 学习资源优先级排序
RESOURCE_PRIORITY = {
    1: "官方文档",      # 最权威，最新
    2: "源码阅读",      # 深入理解
    3: "经典书籍",      # 系统知识
    4: "原论文",        # 理解设计
    5: "优质课程",      # 结构化学习
    6: "技术博客",      # 实践经验
    7: "视频教程",      # 辅助理解
}
```

### 不同阶段的资源选择

| 阶段 | 推荐资源类型 | 示例 |
|------|--------------|------|
| 入门 | 课程 + 官方 Tutorial | fast.ai, PyTorch Tutorial |
| 进阶 | 书籍 + 论文 | PMPP, Megatron-LM 论文 |
| 深入 | 源码 + 博客 | vLLM 源码, NVIDIA 博客 |
| 专家 | 论文 + 社区 | arXiv, 技术会议 |

### 高效学习方法

```
1. 带着问题学
   - 先有具体问题
   - 再寻找资源解答
   - 避免漫无目的

2. 实践验证
   - 学完一个概念
   - 立即写代码验证
   - 加深理解

3. 输出倒逼输入
   - 写博客总结
   - 做技术分享
   - 回答他人问题

4. 建立知识网络
   - 关联新旧知识
   - 画思维导图
   - 定期复习
```

---

## 资源更新跟踪

### 保持更新的方法

| 渠道 | 说明 |
|------|------|
| arXiv cs.LG/cs.DC | 最新论文 |
| GitHub Trending | 热门项目 |
| Twitter/X | 专家动态 |
| Newsletter | 定期推送 |

### 推荐 Newsletter

| 名称 | 作者/来源 | 频率 |
|------|-----------|------|
| The Batch | deeplearning.ai | 每周 |
| Import AI | Jack Clark | 每周 |
| Last Week in AI | - | 每周 |

---

## 延伸阅读

- [动手项目建议](./07-hands-on-projects.md)
- [面试准备指南](./08-interview-preparation.md)
- [核心技能清单](./05-core-skills.md)

---

*返回章节：[学习路线图](./README.md)*

---

## 参考资料与引用

1. **Goodfellow, I., Bengio, Y., & Courville, A.** *Deep Learning.* MIT Press.  
   https://www.deeplearningbook.org/

2. **d2l.ai.** *Dive into Deep Learning.*  
   https://d2l.ai/

3. **HuggingFace.** *Open-Source ML Community.*  
   https://huggingface.co/

4. **Papers with Code.** *Machine Learning Papers with Implementation.*  
   https://paperswithcode.com/

# 模型推理与部署详解

> 从训练到生产，让模型高效服务用户。

## 📚 本章概述

推理阶段与训练有本质区别：关注点从吞吐量转向延迟，从显存容量转向服务效率。本章涵盖推理优化技术、LLM 推理特性、服务框架选型和部署架构。

### 学习目标

- 理解推理与训练的关键差异
- 掌握量化、剪枝、蒸馏等优化技术
- 理解 LLM 特有的 KV Cache、PagedAttention
- 学会选择和使用 vLLM、SGLang、TGI、Triton 等框架
- 掌握部署架构设计和性能调优

---

## 📖 子文档导航

| 序号 | 文档 | 内容概述 | 预计阅读时间 |
|------|------|----------|--------------|
| 01 | [推理与训练的差异](01-inference-vs-training.md) | 关键差异、优化空间分析 | 15 分钟 |
| 02 | [量化技术详解](02-quantization.md) | PTQ/QAT/GPTQ/AWQ 原理和实践 | 35 分钟 |
| 03 | [剪枝与蒸馏](03-pruning-distillation.md) | 结构化剪枝、知识蒸馏 | 25 分钟 |
| 04 | [推理引擎详解](04-inference-engines.md) | TensorRT、TensorRT-LLM、ONNX Runtime | 30 分钟 |
| 05 | [LLM 推理-KV Cache](05-llm-inference-kv-cache.md) | 自回归生成、KV Cache 原理 | 25 分钟 |
| 06 | [LLM 推理-Batching](06-llm-inference-batching.md) | Continuous Batching、PagedAttention | 30 分钟 |
| 07 | [LLM 推理-Attention 优化](07-llm-inference-attention.md) | FlashAttention、Speculative Decoding | 25 分钟 |
| 08 | [服务框架详解](08-serving-frameworks.md) | vLLM、SGLang、TGI、Triton 对比 | 30 分钟 |
| 09 | [部署架构模式](09-deployment-architecture.md) | 单实例、负载均衡、Prefill-Decode 分离 | 25 分钟 |
| 10 | [性能调优](10-performance-tuning.md) | TTFT/TPS 指标、调优 Checklist | 25 分钟 |
| 11 | [Speculative Decoding 深入](11-speculative-decoding.md) | Draft-Verify 范式、Medusa、Eagle、Tree-based SD | 30 分钟 |
| 12 | [多模态推理](12-multimodal-inference.md) | VLM 推理、扩散模型优化、语音模型、多模态服务架构 | 25 分钟 |
| 13 | [端侧与边缘推理](13-edge-inference.md) | llama.cpp/Ollama/MLC-LLM、GGUF 格式、端侧硬件 | 25 分钟 |

---

## 💡 核心概念速览

### 推理 vs 训练

| 维度 | 训练 | 推理 |
|------|------|------|
| 目标 | 高吞吐 | 低延迟 |
| Batch Size | 大 | 小/动态 |
| 精度 | FP16/BF16 | INT8/INT4 |
| 显存占用 | 模型+梯度+优化器 | 模型+KV Cache |

### 优化技术矩阵

| 技术 | 适用阶段 | 效果 | 复杂度 |
|------|----------|------|--------|
| 量化 | 部署前 | 2-4x 加速 | 低-中 |
| 剪枝 | 训练后 | 1.5-2x 加速 | 中 |
| 蒸馏 | 训练时 | 模型压缩 | 高 |
| KV Cache | 推理时 | 必需 | 低 |
| PagedAttention | 推理时 | 显存优化 | 低 |

### 服务框架选择

| 框架 | 特点 | 适用场景 |
|------|------|----------|
| vLLM | PagedAttention | 高并发 LLM |
| SGLang | RadixAttention, 结构化生成 | 多轮对话、Agent |
| TGI | Hugging Face 生态 | 快速部署 |
| Triton | 多模型、多框架 | 企业级部署 |

---

## 🔗 相关章节

- **前置**：[02-distributed-training](../02-distributed-training/) - 分布式训练
- **后续**：[04-mlops-llmops](../04-mlops-llmops/) - MLOps 实践
- **相关**：[01-gpu-hardware](../01-gpu-hardware/) - 硬件基础

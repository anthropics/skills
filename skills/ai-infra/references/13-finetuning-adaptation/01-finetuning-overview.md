# 微调概述

> 微调就像让一个通才变成专家——保留广博的知识基础，在特定领域进行针对性训练。

## 目录

- [为什么需要微调](#为什么需要微调)
- [全量微调 vs 参数高效微调](#全量微调-vs-参数高效微调)
- [微调 vs RAG vs Prompt Engineering](#微调-vs-rag-vs-prompt-engineering)
- [微调技术演进](#微调技术演进)
- [微调的基本流程](#微调的基本流程)
- [硬件需求估算](#硬件需求估算)
- [延伸阅读](#延伸阅读)

---

## 为什么需要微调

### 预训练模型的局限

预训练大语言模型（如 Llama、Qwen、Mistral）通过海量文本数据获得了通用的语言能力，但在以下场景中表现不足：

```
预训练模型的能力边界
┌─────────────────────────────────────────────────┐
│                                                 │
│  ✅ 通用知识问答    ✅ 文本摘要    ✅ 翻译       │
│  ✅ 代码生成        ✅ 创意写作                  │
│                                                 │
│  ❌ 特定领域术语    ❌ 企业私有知识              │
│  ❌ 特定输出格式    ❌ 严格的安全策略            │
│  ❌ 特定角色行为    ❌ 低延迟场景（模型太大）     │
│                                                 │
└─────────────────────────────────────────────────┘
```

### 生活类比

> 想象你是一家医院的院长，需要招聘一位心内科专家：
>
> - **预训练** = 医学院通识教育（解剖学、生理学、药理学……）
> - **微调** = 心内科专科培训（心电图诊断、介入手术、心衰管理……）
> - **RAG** = 给医生配一本最新的诊疗指南手册
> - **Prompt Engineering** = 在门诊前告诉医生"今天重点关注高血压患者"
>
> 不需要重新上医学院，只需要专科培训就能获得专业能力。

---

## 全量微调 vs 参数高效微调

### 全量微调（Full Fine-tuning）

更新模型所有参数，获得最好的任务适配效果，但资源消耗巨大。

```
全量微调的显存需求（以 Adam 优化器为例）

模型参数量    模型权重     梯度      优化器状态    总显存
                (FP16)    (FP16)    (FP32)      (最少)
─────────────────────────────────────────────────────
  7B          14 GB     14 GB     56 GB       ~84 GB
 13B          26 GB     26 GB    104 GB      ~156 GB
 70B         140 GB    140 GB    560 GB      ~840 GB

公式：显存 ≈ 参数量 × (2 + 2 + 4×3) = 参数量 × 16 字节
      （权重 + 梯度 + Adam 的 m, v, master weights）
```

### 参数高效微调（Parameter-Efficient Fine-Tuning, PEFT）

仅更新极少量参数（通常 < 1%），大幅降低资源需求。

```
PEFT 方法分类

┌─────────────────────────────────────────────────────────────┐
│                     PEFT 方法                                │
├──────────────┬──────────────┬───────────────┬───────────────┤
│   加法式      │   选择式      │   重参数化     │   混合式       │
│ (Additive)   │ (Selective)  │ (Reparameter) │  (Hybrid)     │
├──────────────┼──────────────┼───────────────┼───────────────┤
│ • Adapter    │ • BitFit     │ • LoRA        │ • MAM Adapter │
│ • Prefix     │ • 层冻结      │ • QLoRA       │ • UniPELT     │
│   Tuning     │ • 注意力头    │ • DoRA        │               │
│ • Prompt     │   选择       │ • AdaLoRA     │               │
│   Tuning     │              │ • LoRA+       │               │
│ • (IA)³      │              │               │               │
└──────────────┴──────────────┴───────────────┴───────────────┘
```

### 对比总结

| 维度 | 全量微调 | PEFT (LoRA) |
|------|---------|-------------|
| 可训练参数 | 100% | 0.1% - 1% |
| 显存需求 (7B) | ~84 GB | ~16 GB |
| 训练速度 | 较慢 | 快 2-3x |
| 效果上限 | 最高 | 接近全量（90-99%） |
| 多任务适配 | 每个任务一个完整模型 | 每个任务一个小适配器 |
| 灾难性遗忘 | 较高风险 | 较低风险 |
| 适用场景 | 充足资源 + 追求极致性能 | 资源受限 + 多任务适配 |

---

## 微调 vs RAG vs Prompt Engineering

### 决策树

```
你的需求是什么？
│
├── 需要模型学会新的行为模式/输出格式？
│   └── ✅ 微调
│       ├── 有大量标注数据 + 充足 GPU？ → 全量微调
│       └── 数据/资源有限？ → LoRA/QLoRA
│
├── 需要访问最新/私有知识？
│   └── ✅ RAG（检索增强生成）
│       ├── 知识频繁更新？ → RAG 优先
│       └── 需要深度理解？ → RAG + 微调
│
├── 只需要调整输出风格/格式？
│   └── ✅ Prompt Engineering
│       ├── Few-shot 示例有效？ → Prompt 即可
│       └── 效果不稳定？ → 考虑微调
│
└── 不确定？
    └── 从 Prompt Engineering 开始，逐步升级
```

### 三种方法的完整对比

| 维度 | Prompt Engineering | RAG | 微调 |
|------|-------------------|-----|------|
| 实施成本 | 最低 | 中等 | 最高 |
| 见效时间 | 分钟级 | 天级 | 天-周级 |
| 知识更新 | 即时 | 小时级 | 需要重新训练 |
| 定制深度 | 浅 | 中 | 深 |
| 推理成本 | 较高（长 prompt） | 中（检索 + 生成） | 较低 |
| 幻觉控制 | 较差 | 好（有引用） | 中等 |
| 适用数据量 | 无需训练数据 | 需要知识库 | 需要标注数据 |
| 可扩展性 | 受上下文窗口限制 | 知识库可扩展 | 需要重新训练 |

### 组合策略

在生产环境中，三种方法通常组合使用：

```python
# 典型的组合策略
class ProductionLLMPipeline:
    """
    层次化策略：微调 + RAG + Prompt Engineering
    """
    def __init__(self):
        # 1. 微调模型：学会领域语言和行为模式
        self.model = load_finetuned_model("domain-specific-llama-7b")
        
        # 2. RAG 系统：提供最新知识
        self.retriever = VectorStoreRetriever("company-knowledge-base")
        
        # 3. Prompt 模板：控制输出格式
        self.prompt_template = """你是{company}的客服助手。
基于以下参考信息回答用户问题：

参考信息：
{retrieved_context}

用户问题：{user_query}

请用专业、友好的语气回答，如果不确定请说明。"""
    
    def generate(self, user_query: str) -> str:
        # Step 1: 检索相关知识
        context = self.retriever.search(user_query, top_k=5)
        
        # Step 2: 构建 prompt
        prompt = self.prompt_template.format(
            company="ABC科技",
            retrieved_context=context,
            user_query=user_query
        )
        
        # Step 3: 用微调模型生成
        return self.model.generate(prompt)
```

---

## 微调技术演进

```
时间线：微调技术的发展

2018 ──── GPT-1/BERT 时代
│         └── 全量微调为主，下游任务 Fine-tuning
│
2019 ──── Adapter Tuning (Houlsby et al.)
│         └── 在 Transformer 层中插入小型适配模块
│
2020 ──── Prefix Tuning (Li & Liang)
│         └── 在输入序列前添加可学习的虚拟 token
│
2021 ──── LoRA (Hu et al.) ⭐
│         └── 低秩矩阵分解，冻结原权重
│         └── Prompt Tuning (Lester et al.)
│
2023 ──── QLoRA (Dettmers et al.) ⭐
│         └── 4-bit 量化 + LoRA，单卡微调 65B 模型
│         └── DPO (Rafailov et al.) — 简化对齐训练
│
2024 ──── DoRA (Liu et al.)
│         └── 权重分解 + 方向适配
│         └── LoRA+：差异化学习率
│         └── GaLore：梯度低秩投影
│
2025 ──── LoRA 变体持续演进
│         └── Spectrum、PiSSA、rsLoRA...
│         └── 微调即服务 (FTaaS) 成熟
```

---

## 微调的基本流程

### 端到端流程

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ 1. 需求   │───▶│ 2. 数据   │───▶│ 3. 训练   │───▶│ 4. 评估   │───▶│ 5. 部署   │
│    分析   │    │    准备   │    │    配置   │    │    验证   │    │    上线   │
└──────────┘    └──────────┘    └──────────┘    └──────────┘    └──────────┘
     │               │               │               │               │
     ▼               ▼               ▼               ▼               ▼
 • 选择基座模型   • 数据收集     • 选择微调方法   • 基准测试     • 模型导出
 • 确定任务类型   • 格式转换     • 超参数设置     • 人工评估     • 量化压缩
 • 评估资源需求   • 质量过滤     • 分布式配置     • A/B 测试     • 服务部署
 • 决策：FT/RAG  • 数据去污染   • 开始训练       • 安全测试     • 监控告警
```

### Step 1: 需求分析

```python
# 微调决策清单
finetuning_checklist = {
    "任务类型": [
        "指令遵循 (Instruction Following)",
        "对话能力 (Chat/Conversation)",
        "领域适配 (Domain Adaptation)",
        "格式控制 (Format Control)",
        "风格迁移 (Style Transfer)",
        "工具使用 (Tool Use / Function Calling)",
    ],
    "基座模型选择因素": {
        "模型规模": "任务复杂度决定，简单任务 7B 够用",
        "许可证": "商用需要 Apache 2.0 或类似开放许可",
        "语言支持": "中文任务选择中文增强模型",
        "已有能力": "选择在目标领域已有基础的模型",
    },
    "数据需求": {
        "指令微调": "1000-100000 条高质量指令数据",
        "对话微调": "5000-50000 条多轮对话",
        "领域适配": "领域文档 + 领域指令数据",
    },
}
```

### Step 2: 数据准备

```python
# 常见的微调数据格式

# 格式 1: Alpaca 格式（指令微调）
alpaca_format = {
    "instruction": "将以下英文翻译成中文",
    "input": "Machine learning is a subset of artificial intelligence.",
    "output": "机器学习是人工智能的一个子集。"
}

# 格式 2: ShareGPT 格式（对话微调）
sharegpt_format = {
    "conversations": [
        {"from": "human", "value": "什么是量子计算？"},
        {"from": "gpt", "value": "量子计算是利用量子力学原理..."},
        {"from": "human", "value": "它和经典计算有什么区别？"},
        {"from": "gpt", "value": "主要区别在于..."}
    ]
}

# 格式 3: OpenAI 格式（Chat 微调）
openai_format = {
    "messages": [
        {"role": "system", "content": "你是一个专业的医学助手。"},
        {"role": "user", "content": "头痛可能是什么原因？"},
        {"role": "assistant", "content": "头痛的常见原因包括..."}
    ]
}
```

---

## 硬件需求估算

### 不同微调方法的 GPU 需求

```
硬件需求速查表

┌──────────────────────────────────────────────────────────────────────┐
│ 模型规模 │  全量微调        │  LoRA (r=16)     │  QLoRA (4-bit)    │
├──────────┼─────────────────┼─────────────────┼──────────────────┤
│   7B     │ 4× A100 80GB   │ 1× A100 80GB   │ 1× RTX 4090 24GB │
│  13B     │ 8× A100 80GB   │ 2× A100 80GB   │ 1× A100 40GB     │
│  34B     │ 16× A100 80GB  │ 4× A100 80GB   │ 2× A100 40GB     │
│  70B     │ 32× A100 80GB  │ 8× A100 80GB   │ 4× A100 40GB     │
│ 405B     │ 128× H100 80GB │ 32× H100 80GB  │ 16× H100 80GB    │
└──────────┴─────────────────┴─────────────────┴──────────────────┘

注：以上为近似值，实际需求取决于批大小、序列长度、梯度累积等
```

### 成本估算

```python
def estimate_finetuning_cost(
    model_size_b: float,
    method: str,
    dataset_size: int,
    epochs: int = 3,
    cloud_gpu_price: float = 2.0,  # $/hour per GPU
) -> dict:
    """估算微调成本"""
    
    # GPU 需求估算
    gpu_configs = {
        "full": {"7": 4, "13": 8, "70": 32},
        "lora": {"7": 1, "13": 2, "70": 8},
        "qlora": {"7": 1, "13": 1, "70": 4},
    }
    
    size_key = str(int(model_size_b))
    num_gpus = gpu_configs.get(method, {}).get(size_key, 1)
    
    # 训练速度估算（samples/second/gpu）
    speed_map = {"full": 2.0, "lora": 4.0, "qlora": 3.0}
    samples_per_sec = speed_map[method] * num_gpus
    
    total_samples = dataset_size * epochs
    training_hours = total_samples / samples_per_sec / 3600
    
    total_cost = training_hours * num_gpus * cloud_gpu_price
    
    return {
        "method": method,
        "num_gpus": num_gpus,
        "training_hours": round(training_hours, 1),
        "total_cost_usd": round(total_cost, 2),
    }

# 示例：微调 Llama-3-7B，10000 条数据
for method in ["full", "lora", "qlora"]:
    result = estimate_finetuning_cost(7, method, 10000)
    print(f"{method:>6}: {result['num_gpus']} GPUs, "
          f"{result['training_hours']}h, ${result['total_cost_usd']}")
```

---

## 参考资料与引用

1. Muennighoff, N., et al. (2023). *Scaling Data-Constrained Language Models*. arXiv:2305.16264. https://arxiv.org/abs/2305.16264
2. Zhou, C., et al. (2023). *LIMA: Less Is More for Alignment*. arXiv:2305.11206. https://arxiv.org/abs/2305.11206
3. Gudibande, A., et al. (2023). *The False Promise of Imitating Proprietary LLMs*. arXiv:2305.15717. https://arxiv.org/abs/2305.15717
4. Hu, E. J., et al. (2021). *LoRA: Low-Rank Adaptation of Large Language Models*. arXiv:2106.09685. https://arxiv.org/abs/2106.09685
5. HuggingFace PEFT Documentation. https://huggingface.co/docs/peft
6. Raschka, S. (2023). *Practical Tips for Finetuning LLMs*. https://magazine.sebastianraschka.com/p/practical-tips-for-finetuning-llms

---

*下一篇：[02-lora-family.md](02-lora-family.md)*

[返回目录](README.md) | [返回主页](../README.md)

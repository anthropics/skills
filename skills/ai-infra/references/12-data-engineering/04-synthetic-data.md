# 合成数据

> 用 AI 生成训练 AI 的数据——这不是"自己教自己"的悖论，而是一种高效的数据生产方式。

## 目录

- [合成数据概述](#合成数据概述)
- [Self-Instruct](#self-instruct)
- [Evol-Instruct](#evol-instruct)
- [领域数据合成](#领域数据合成)
- [质量验证](#质量验证)
- [延伸阅读](#延伸阅读)

---

## 合成数据概述

```
为什么使用合成数据？

  问题:
    高质量标注数据昂贵: $1-10 / 条
    100K 条 SFT 数据 → $100K - $1M
    特定领域数据稀缺: 医疗/法律/金融

  合成数据:
    用强模型 (如 GPT-4) 生成训练弱模型的数据
    成本: ~$0.01-0.1 / 条 (API 费用)
    100K 条 → $1K - $10K (降低 90%+)

  成功案例:
    Alpaca: 用 GPT-3.5 生成 52K 指令数据 → 训练 LLaMA 7B
    Phi-1: 用 GPT-3.5 生成教科书质量数据 → 1.3B 超越更大模型
    WizardLM: Evol-Instruct 生成复杂指令
```

---

## Self-Instruct

```python
"""Self-Instruct: 用 LLM 生成指令数据"""

SEED_INSTRUCTIONS = [
    "Write a poem about spring",
    "Explain quantum computing to a 5-year-old",
    "Debug this Python code: ...",
    "Summarize the following article: ...",
]

def self_instruct_pipeline(
    teacher_model,          # GPT-4 或其他强模型
    seed_instructions: list,
    target_count: int = 10000,
):
    """Self-Instruct 数据生成管线"""
    generated = list(seed_instructions)
    
    while len(generated) < target_count:
        # 1. 从已有指令中采样作为上下文
        samples = random.sample(generated, min(3, len(generated)))
        
        # 2. 让教师模型生成新指令
        prompt = f"""Here are some example tasks:
{chr(10).join(f'- {s}' for s in samples)}

Generate 5 new, diverse tasks that are different from the above:"""
        
        new_instructions = teacher_model.generate(prompt)
        
        # 3. 过滤: 去重、质量检查
        for inst in parse_instructions(new_instructions):
            if is_unique(inst, generated) and quality_check(inst):
                generated.append(inst)
        
        # 4. 为每个指令生成回复
        for inst in generated[-5:]:  # 最新生成的
            response = teacher_model.generate(f"Complete this task:\n{inst}")
            save_pair(inst, response)
    
    return generated
```

---

## Evol-Instruct

```
Evol-Instruct (WizardLM):

  核心思想: 迭代进化指令复杂度

  简单指令 → 中等复杂指令 → 高复杂指令

  进化策略:
    深度进化: 增加约束、增加步骤、增加复杂性
    广度进化: 改变领域、改变格式、改变角度

  示例:
    原始: "Write a sorting algorithm"
    → 深度1: "Write a sorting algorithm for a linked list"
    → 深度2: "Write a sorting algorithm for a linked list 
               that handles duplicate values and runs in O(n log n)"
    → 深度3: "Write a sorting algorithm for a doubly linked list
               that handles duplicate values, runs in O(n log n),
               and uses O(1) extra space"

  效果:
    WizardLM 70B 在 MT-Bench 上接近 GPT-4
    关键: 复杂指令让模型学会处理困难任务
```

---

## 领域数据合成

```python
"""领域特定合成数据生成"""

def generate_domain_data(
    teacher_model,
    domain: str,
    seed_topics: list,
    count_per_topic: int = 100,
):
    """为特定领域生成训练数据"""
    
    templates = {
        "medical": [
            "As a medical professional, explain {topic} to a patient",
            "What are the symptoms, diagnosis, and treatment for {topic}?",
            "Compare different treatment approaches for {topic}",
        ],
        "legal": [
            "Explain the legal concept of {topic} in simple terms",
            "What are the key considerations in {topic} cases?",
            "Draft a brief analysis of {topic}",
        ],
        "finance": [
            "Explain {topic} to a new investor",
            "What are the risks and benefits of {topic}?",
            "Analyze the market impact of {topic}",
        ],
    }
    
    domain_templates = templates.get(domain, templates["medical"])
    results = []
    
    for topic in seed_topics:
        for template in domain_templates:
            instruction = template.format(topic=topic)
            response = teacher_model.generate(
                f"You are an expert in {domain}. {instruction}\n"
                f"Provide a detailed, accurate, and helpful response."
            )
            results.append({
                "instruction": instruction,
                "response": response,
                "domain": domain,
                "topic": topic,
            })
    
    return results
```

---

## 质量验证

```
合成数据质量验证:

  1. 自动验证
     语法/格式检查
     指令-回复一致性 (回复是否真的回答了问题)
     去重检查 (与已有数据去重)
     毒性/安全检查

  2. AI 验证 (用更强的模型评分)
     用 GPT-4 对生成的数据评分 (1-5 分)
     过滤掉低分数据 (通常 < 4 分)
     成本远低于人工审核

  3. 人工抽样验证
     随机抽取 5-10% 进行人工审查
     检查事实准确性、回复质量
     发现系统性问题

  4. 下游验证
     用合成数据训练模型
     在标准基准上评估
     如果性能不提升 → 数据质量可能有问题

  关键原则:
    合成数据质量 < 教师模型的输出质量
    不能用合成数据超越教师模型（天花板效应）
    合成数据最适合"蒸馏"和"格式迁移"
```

---

## 延伸阅读

- 论文: *Self-Instruct: Aligning Language Models with Self-Generated Instructions* (2022)
- 论文: *WizardLM: Empowering Large Language Models to Follow Complex Instructions* (2023)
- 论文: *Textbooks Are All You Need* (Phi-1, 2023)
- [Alpaca Data Generation](https://github.com/tatsu-lab/stanford_alpaca)

---

*上一篇：[03-data-labeling.md](03-data-labeling.md)* | *下一篇：[05-data-versioning.md](05-data-versioning.md)*

*返回：[README.md](README.md) - 章节索引*

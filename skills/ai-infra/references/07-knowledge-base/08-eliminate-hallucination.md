# 消除幻觉与质量提升

> 知识库的核心价值之一：让 LLM 的回答有据可依，消除"一本正经的胡说八道"。

## 目录

- [LLM 幻觉概述](#llm-幻觉概述)
- [幻觉分类与成因](#幻觉分类与成因)
- [Grounding：事实锚定](#grounding事实锚定)
- [引用溯源与来源标注](#引用溯源与来源标注)
- [置信度评估与拒答](#置信度评估与拒答)
- [事实验证 Pipeline](#事实验证-pipeline)
- [RAGAS 评估框架](#ragas-评估框架)
- [Guardrails 实现](#guardrails-实现)
- [人类反馈闭环](#人类反馈闭环)
- [实战练习](#实战练习)

---

## LLM 幻觉概述

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    LLM 幻觉: 问题与现状                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   什么是幻觉 (Hallucination):                                              │
│   LLM 生成的内容看似合理，但实际上不正确或无依据                            │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   用户: "Milvus 是谁开发的？"                                       │   │
│   │                                                                     │   │
│   │   无知识库 (幻觉):                                                  │   │
│   │   "Milvus 是由 Facebook AI Research 团队在 2018 年开发的..."       │   │
│   │   ❌ 错误! Milvus 是 Zilliz 公司开发的                              │   │
│   │                                                                     │   │
│   │   有知识库 (准确):                                                  │   │
│   │   "根据文档 [1]，Milvus 是由 Zilliz 公司于 2019 年开源的            │   │
│   │    向量数据库，已成为 LF AI & Data 基金会毕业项目。"                 │   │
│   │   ✅ 准确且有据可依                                                 │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   幻觉的危害:                                                               │
│   • 金融场景: 错误的财务数据 → 投资决策失误                                │
│   • 医疗场景: 错误的用药建议 → 危及生命                                    │
│   • 法律场景: 引用不存在的法条 → 败诉                                      │
│   • 客服场景: 错误的产品信息 → 客户投诉                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 幻觉分类与成因

### 三类幻觉

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    幻觉分类详解                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 事实性幻觉 (Factual Hallucination)                                     │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   编造不存在的事实                                                   │   │
│   │   • 错误日期: "GPT-4 于 2024 年 1 月发布"                           │   │
│   │   • 错误归属: "PyTorch 是 Google 开发的"                            │   │
│   │   • 编造数字: "H100 有 120GB 显存"                                  │   │
│   │   • 编造引用: "根据 Smith et al. 2023 的研究..."  (论文不存在)       │   │
│   │                                                                     │   │
│   │   成因: 训练数据中的错误/过时信息、模型对低频知识的过度泛化           │   │
│   │   知识库方案: Grounding + 引用溯源                                  │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. 忠实性幻觉 (Faithfulness Hallucination)                                │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   回答与提供的上下文不一致                                           │   │
│   │   • 上下文: "A100 有 80GB HBM2e"                                    │   │
│   │   • 模型回答: "A100 有 40GB 显存" (使用了参数知识而非上下文)        │   │
│   │                                                                     │   │
│   │   成因: 模型参数知识与上下文冲突时优先使用参数知识                   │   │
│   │   知识库方案: 强化 Prompt + NLI 验证                                │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. 指令幻觉 (Instruction Hallucination)                                   │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   不遵循指令约束                                                     │   │
│   │   • 要求"只基于上下文"，结果引入外部知识                            │   │
│   │   • 要求"不知道就说不知道"，结果强行回答                            │   │
│   │   • 要求 JSON 格式输出，结果输出 Markdown                           │   │
│   │                                                                     │   │
│   │   成因: 指令遵循能力不足、Prompt 设计不当                           │   │
│   │   知识库方案: Guardrails + 输出验证                                 │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Grounding：事实锚定

### 核心策略

```python
# Grounding Prompt 设计
grounding_prompt = """你是一个严谨的 AI 助手。

【重要规则】
1. 只能根据"参考资料"中的信息回答问题
2. 不得使用任何参考资料之外的知识
3. 如果参考资料中没有相关信息，回答："根据现有资料，我无法回答此问题"
4. 每个论点必须用 [1][2] 等标注来源
5. 不确定的信息要明确标注"可能"

参考资料：
{context}

用户问题：{question}

请严格基于参考资料回答："""
```

### Grounding 验证

```python
from openai import OpenAI

client = OpenAI()

def verify_grounding(answer: str, context: str) -> dict:
    """验证回答是否基于上下文"""
    
    verification_prompt = f"""判断以下"回答"中的每个声明是否可以在"上下文"中找到支持。

上下文：
{context}

回答：
{answer}

请以 JSON 格式输出每个声明的验证结果：
[
  {{"claim": "声明内容", "supported": true/false, "evidence": "支持的上下文片段或空"}}
]"""
    
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": verification_prompt}],
        response_format={"type": "json_object"},
        temperature=0
    )
    
    return response.choices[0].message.content
```

---

## 引用溯源与来源标注

```python
def rag_with_citations(query: str, vectorstore, llm):
    """带引用的 RAG"""
    
    # 1. 检索
    results = vectorstore.similarity_search_with_score(query, k=5)
    
    # 2. 构造带编号的上下文
    context_parts = []
    sources = []
    for i, (doc, score) in enumerate(results):
        context_parts.append(f"[{i+1}] {doc.page_content}")
        sources.append({
            "id": i + 1,
            "source": doc.metadata.get("source", "unknown"),
            "score": score,
            "text": doc.page_content[:200]
        })
    
    context = "\n\n".join(context_parts)
    
    # 3. 生成带引用的回答
    prompt = f"""基于以下编号参考资料回答问题。
在回答中用 [1][2] 等标注每个论点的来源。

参考资料：
{context}

问题：{query}

回答（请标注引用）："""
    
    answer = llm.invoke(prompt).content
    
    return {
        "answer": answer,
        "sources": sources,
        "context_used": context
    }

# 使用
result = rag_with_citations("ZeRO-3 如何优化显存？", vectorstore, llm)
print(result["answer"])
print("\n引用来源:")
for s in result["sources"]:
    print(f"  [{s['id']}] {s['source']} (相似度: {s['score']:.4f})")
```

---

## 置信度评估与拒答

```python
class ConfidenceAssessor:
    """评估检索结果的置信度，决定是否回答"""
    
    def __init__(self, similarity_threshold=0.7, min_relevant_docs=2):
        self.similarity_threshold = similarity_threshold
        self.min_relevant_docs = min_relevant_docs
    
    def assess(self, query: str, search_results: list) -> dict:
        """评估检索结果质量"""
        
        # 统计高质量结果数量
        relevant_docs = [
            (doc, score) for doc, score in search_results 
            if score >= self.similarity_threshold
        ]
        
        # 检查结果一致性（多个文档是否矛盾）
        is_consistent = self._check_consistency(relevant_docs)
        
        # 决策
        if len(relevant_docs) < self.min_relevant_docs:
            return {
                "action": "refuse",
                "reason": "检索到的相关文档不足",
                "confidence": "low",
                "message": "抱歉，现有知识库中没有足够的相关信息来回答此问题。"
            }
        elif not is_consistent:
            return {
                "action": "warn",
                "reason": "检索到的文档存在矛盾",
                "confidence": "medium",
                "message": "注意：检索到的信息存在冲突，请人工确认。"
            }
        else:
            return {
                "action": "answer",
                "reason": "检索结果充分且一致",
                "confidence": "high",
                "docs": relevant_docs
            }
    
    def _check_consistency(self, docs) -> bool:
        """检查文档间是否矛盾（简化版）"""
        # 实际可用 NLI 模型检查
        return True

# 使用
assessor = ConfidenceAssessor(similarity_threshold=0.75, min_relevant_docs=2)
results = vectorstore.similarity_search_with_score(query, k=5)
assessment = assessor.assess(query, results)

if assessment["action"] == "refuse":
    print(assessment["message"])
elif assessment["action"] == "warn":
    print(assessment["message"])
    # 仍然回答，但附带警告
else:
    # 正常 RAG 回答
    answer = generate_answer(query, assessment["docs"])
```

---

## 事实验证 Pipeline

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    事实验证 Pipeline                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Step 1: 生成回答                                                          │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   RAG 正常流程 → "ZeRO-3 将参数分片到所有 GPU，每个 GPU 只保存     │   │
│   │   1/N 的参数。它由 Microsoft DeepSpeed 团队在 2020 年提出。"       │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                               │                                             │
│   Step 2: 提取声明            │                                             │
│   ┌───────────────────────────▼─────────────────────────────────────────┐   │
│   │   声明1: "ZeRO-3 将参数分片到所有 GPU"                              │   │
│   │   声明2: "每个 GPU 只保存 1/N 的参数"                               │   │
│   │   声明3: "由 Microsoft DeepSpeed 团队在 2020 年提出"                │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   Step 3: 逐条验证            │                                             │
│   ┌───────────────────────────▼─────────────────────────────────────────┐   │
│   │   声明1 → 搜索知识库 → 找到支持证据 ✅                              │   │
│   │   声明2 → 搜索知识库 → 找到支持证据 ✅                              │   │
│   │   声明3 → 搜索知识库 → 未找到确切年份 ⚠️                            │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   Step 4: 修正/标注           │                                             │
│   ┌───────────────────────────▼─────────────────────────────────────────┐   │
│   │   最终回答: "ZeRO-3 将参数分片到所有 GPU [1]，每个 GPU 只保存      │   │
│   │   1/N 的参数 [1]。它由 Microsoft DeepSpeed 团队提出 [2]             │   │
│   │   （具体发布年份请以官方文档为准）。"                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## RAGAS 评估框架

### 四大核心指标

| 指标 | 评估什么 | 计算方式 | 目标 |
|------|----------|----------|------|
| **Faithfulness** | 回答是否忠于上下文 | 答案中有上下文支持的声明比例 | > 0.9 |
| **Answer Relevancy** | 回答是否切题 | 用回答反向生成问题，与原问题比较 | > 0.85 |
| **Context Precision** | 检索结果是否相关 | 相关文档排在前面的比例 | > 0.8 |
| **Context Recall** | 是否检索到了必要信息 | ground truth 中的信息被检索到的比例 | > 0.8 |

```python
from ragas import evaluate
from ragas.metrics import (
    faithfulness,
    answer_relevancy,
    context_precision,
    context_recall
)
from datasets import Dataset

# 准备评估数据集
eval_data = Dataset.from_dict({
    "question": [
        "ZeRO-3 如何优化显存？",
        "HNSW 索引的时间复杂度是多少？",
    ],
    "answer": [
        "ZeRO-3 将优化器状态、梯度和模型参数全部在数据并行维度分片...",
        "HNSW 的搜索时间复杂度为 O(log n)...",
    ],
    "contexts": [
        ["ZeRO Stage 3 对优化器状态(O)、梯度(G)和参数(P)进行分片..."],
        ["HNSW 基于多层图结构，搜索复杂度为 O(log n)..."],
    ],
    "ground_truth": [
        "ZeRO-3 将优化器状态、梯度和模型参数分片到所有 GPU 上...",
        "HNSW 搜索的时间复杂度为 O(log n)...",
    ]
})

# 运行评估
result = evaluate(
    eval_data,
    metrics=[faithfulness, answer_relevancy, context_precision, context_recall]
)

print(result)
# {'faithfulness': 0.95, 'answer_relevancy': 0.91,
#  'context_precision': 0.88, 'context_recall': 0.90}

# 定期跑评估，监控质量变化
```

---

## Guardrails 实现

```python
from guardrails import Guard
from guardrails.validators import (
    ValidJSON,
    ReadingLevel,
    ToxicLanguage,
)

# 方式1: 基于规则的 Guardrails
class RAGGuardrails:
    """RAG 输出质量护栏"""
    
    def __init__(self, knowledge_entities: set):
        self.knowledge_entities = knowledge_entities
    
    def check_hallucination(self, answer: str, context: str) -> dict:
        """检查回答是否包含知识库中不存在的实体"""
        import re
        
        # 提取回答中的专有名词/实体
        answer_entities = set(re.findall(r'[A-Z][a-zA-Z0-9-]+', answer))
        context_entities = set(re.findall(r'[A-Z][a-zA-Z0-9-]+', context))
        
        # 在回答中出现但不在上下文中的实体 → 可能是幻觉
        suspicious = answer_entities - context_entities - self.knowledge_entities
        
        return {
            "passed": len(suspicious) == 0,
            "suspicious_entities": list(suspicious),
            "message": f"发现可能的幻觉实体: {suspicious}" if suspicious else "通过"
        }
    
    def check_numbers(self, answer: str, context: str) -> dict:
        """检查回答中的数字是否在上下文中出现"""
        import re
        
        answer_numbers = set(re.findall(r'\d+\.?\d*', answer))
        context_numbers = set(re.findall(r'\d+\.?\d*', context))
        
        unsupported = answer_numbers - context_numbers
        
        return {
            "passed": len(unsupported) == 0,
            "unsupported_numbers": list(unsupported),
            "message": f"未在上下文中找到的数字: {unsupported}" if unsupported else "通过"
        }

# 使用
guardrails = RAGGuardrails(knowledge_entities={"Milvus", "HNSW", "ZeRO"})
check = guardrails.check_hallucination(answer, context)
if not check["passed"]:
    print(f"⚠️ 幻觉警告: {check['message']}")
```

### NLI 验证

```python
from transformers import pipeline

# 使用 NLI (Natural Language Inference) 模型验证一致性
nli_model = pipeline(
    "text-classification",
    model="cross-encoder/nli-deberta-v3-large"
)

def verify_with_nli(claim: str, evidence: str) -> str:
    """用 NLI 验证声明是否被证据支持"""
    result = nli_model(f"{evidence} [SEP] {claim}")
    label = result[0]["label"]  # ENTAILMENT / CONTRADICTION / NEUTRAL
    score = result[0]["score"]
    
    return {
        "label": label,
        "score": score,
        "supported": label == "ENTAILMENT" and score > 0.8
    }

# 验证
result = verify_with_nli(
    claim="ZeRO-3 将参数分片到所有 GPU",
    evidence="ZeRO Stage 3 对优化器状态、梯度和参数进行分片分布到所有 GPU 上"
)
print(result)  # {'label': 'ENTAILMENT', 'score': 0.98, 'supported': True}
```

---

## 人类反馈闭环

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    人类反馈闭环                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐            │
│   │  RAG     │ →  │ 用户反馈 │ →  │ 质量分析 │ →  │ 改进     │ → 循环    │
│   │  回答    │    │ 👍/👎    │    │ 统计指标 │    │ 知识库   │            │
│   └──────────┘    └──────────┘    └──────────┘    └──────────┘            │
│                                                                             │
│   用户反馈收集:                                                             │
│   • 👍/👎 评分                                                             │
│   • "答案不正确" 标记                                                      │
│   • "信息过时" 标记                                                        │
│   • 用户修正的正确答案                                                     │
│                                                                             │
│   改进方向:                                                                 │
│   • 低分回答 → 分析原因 (检索差? Prompt 差? 知识缺失?)                    │
│   • 用户修正 → 更新知识库                                                  │
│   • 频繁拒答 → 补充知识库内容                                              │
│   • 高频问题 → 优化相关文档的分块策略                                      │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 实战练习

### 练习 1：实现幻觉检测

```python
# hallucination_detector.py
def detect_hallucination(answer: str, context: str, llm) -> dict:
    """使用 LLM 检测回答中的幻觉"""
    
    prompt = f"""分析以下"回答"，判断其中每个事实性声明是否在"上下文"中有支持。

上下文：
{context}

回答：
{answer}

请输出 JSON 数组，每个元素包含：
- claim: 声明内容
- supported: true/false 
- evidence: 支持的上下文原文（如有）

JSON:"""
    
    result = llm.invoke(prompt)
    return result.content

# 测试
answer = "ZeRO-3 由 Meta 在 2021 年发布，将参数分片到所有 GPU。"
context = "ZeRO-3 是 DeepSpeed 框架中的功能，将优化器状态、梯度和参数分片。"

result = detect_hallucination(answer, context, llm)
print(result)
# [{"claim": "ZeRO-3 由 Meta 发布", "supported": false, "evidence": ""},
#  {"claim": "2021 年", "supported": false, "evidence": ""},
#  {"claim": "将参数分片到所有 GPU", "supported": true, "evidence": "将...参数分片"}]
```

### 练习 2：构建 RAGAS 评估 Pipeline

```python
# ragas_eval.py
from ragas import evaluate
from ragas.metrics import faithfulness, answer_relevancy
from datasets import Dataset

# 准备评估集
eval_set = Dataset.from_dict({
    "question": test_questions,
    "answer": rag_answers,
    "contexts": retrieved_contexts,
    "ground_truth": expected_answers,
})

# 评估
result = evaluate(eval_set, metrics=[faithfulness, answer_relevancy])

# 分析低分项
for i, score in enumerate(result.scores):
    if score["faithfulness"] < 0.8:
        print(f"⚠️ 低忠实性: Q={test_questions[i]}")
        print(f"   回答: {rag_answers[i][:100]}...")
```

---

*上一篇：[07-高级 RAG 技术](07-advanced-rag.md)*

*下一篇：[09-实时知识获取](09-realtime-knowledge.md)*

*返回目录：[README](README.md)*

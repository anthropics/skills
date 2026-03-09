# 上下文工程与压缩

> 与其追求无限大的上下文窗口，不如把有限的窗口用到极致——上下文工程是 LLM 应用的"最后一公里"。

## 目录

- [什么是上下文工程](#什么是上下文工程)
- [Prompt 压缩技术](#prompt-压缩技术)
- [StreamingLLM：无限上下文的近似](#streaminLLM无限上下文的近似)
- [应用层上下文管理策略](#应用层上下文管理策略)
- [上下文窗口分配最佳实践](#上下文窗口分配最佳实践)
- [技术栈选型决策树](#技术栈选型决策树)
- [端到端案例](#端到端案例)

---

## 什么是上下文工程

### 定义

上下文工程（Context Engineering）是指在 LLM 应用中，**系统性地设计、优化和管理输入上下文的内容、结构和长度**，以在质量、成本和延迟之间取得最优平衡。

```
┌─────────────────────────────────────────────────────────────┐
│                   上下文工程的三个维度                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  维度 1: 内容 (What)                                         │
│  → 放什么进上下文？哪些信息是必要的，哪些是噪声？             │
│  → 核心技术：RAG、信息检索、相关性排序                        │
│                                                              │
│  维度 2: 结构 (How)                                          │
│  → 信息如何组织和排列？顺序、格式、分隔方式                   │
│  → 核心技术：位置优化（首尾优先）、模板设计                   │
│                                                              │
│  维度 3: 长度 (How Much)                                     │
│  → 用多长的上下文？成本和质量的平衡点在哪？                   │
│  → 核心技术：压缩、摘要、Token 节省                          │
│                                                              │
│  目标：最少的 Token + 最优的结构 = 最好的回答                │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 与 Prompt Engineering 的关系

```
Prompt Engineering ⊂ Context Engineering

Prompt Engineering:
  关注 "怎么写指令" → 指令措辞、Few-shot 示例、CoT 提示
  
Context Engineering:
  关注 "整个输入怎么设计" → 包含 Prompt Engineering，还包括：
  ├── 信息检索与选择（放什么文档进来）
  ├── 对话历史管理（保留多少轮、如何摘要）
  ├── 工具描述优化（精简 Tool Schema）
  ├── 上下文压缩（减少 Token 数但保留语义）
  └── 位置布局设计（什么信息放哪里）
```

---

## Prompt 压缩技术

### LLMLingua / LLMLingua-2

```
LLMLingua 的核心思路：
  用一个小模型判断 Prompt 中哪些 Token 是"冗余"的，然后删除

┌─────────────────────────────────────────────────────┐
│  原始 Prompt (3000 tokens):                          │
│  "The comprehensive guide to KV Cache optimization   │
│   in large language model inference provides a       │
│   detailed overview of the various techniques that   │
│   can be employed to reduce the memory footprint..." │
│                                                      │
│  LLMLingua 压缩后 (900 tokens, 3× 压缩):            │
│  "guide KV Cache optimization large language model   │
│   inference overview techniques reduce memory..."    │
│                                                      │
│  关键 Token 保留 ✅，冗余词汇删除 ❌                  │
│  LLM 仍然能理解压缩后的 Prompt（因为 LLM 对语法       │
│  不完整的输入有很强的容忍度）                          │
└─────────────────────────────────────────────────────┘
```

```python
# LLMLingua-2 使用示例
from llmlingua import PromptCompressor

# 初始化压缩器（使用小模型做 Token 重要性判断）
compressor = PromptCompressor(
    model_name="microsoft/llmlingua-2-bert-base-multilingual-cased-meetingbank",
    device_map="cuda",
)

# 场景：RAG 应用中压缩检索文档
retrieved_docs = """
Document 1: KV Cache is a technique used in transformer-based language models 
to store the Key and Value matrices computed during previous token generations. 
This eliminates redundant computations during the autoregressive decoding process.
The memory consumption of KV Cache grows linearly with sequence length and batch 
size, which can become a significant bottleneck for long-context inference.

Document 2: PagedAttention, introduced in the vLLM framework, applies the concept 
of virtual memory paging from operating systems to KV Cache management. Instead of 
pre-allocating contiguous memory blocks for each request, PagedAttention divides 
the KV Cache into fixed-size blocks (pages) that can be stored non-contiguously 
in GPU memory. This approach reduces memory fragmentation from ~60% to ~4%.

Document 3: [更多检索文档...]
"""

question = "What is KV Cache and how does PagedAttention optimize it?"

# 构造完整 Prompt
full_prompt = f"""Based on the following documents, answer the question.

{retrieved_docs}

Question: {question}
Answer:"""

# 压缩（保留 30% 的 Token）
compressed = compressor.compress_prompt(
    full_prompt,
    rate=0.3,                              # 压缩率
    force_tokens=["KV Cache", "PagedAttention", "Question", "Answer"],  # 强制保留
    condition_in_question="after",          # 问题部分放在最后
)

print(f"原始: {compressed['origin_tokens']} tokens")
print(f"压缩后: {compressed['compressed_tokens']} tokens")
print(f"压缩比: {compressed['ratio']:.1f}x")
print(f"节省成本: ~{(1 - 1/compressed['ratio']) * 100:.0f}%")

# 输出：
# 原始: 850 tokens
# 压缩后: 255 tokens
# 压缩比: 3.3x
# 节省成本: ~70%
```

### Selective Context

```
Selective Context 的方法：

不同于 LLMLingua 的 Token 级压缩，Selective Context 在句子/段落级别操作：

1. 计算每个句子的"信息量"（self-information）
2. 保留信息量高的句子，删除信息量低的句子
3. 信息量低的句子通常是：过渡句、重复表述、常识性内容

示例：
  原始 RAG 上下文 (10 个段落):
  ┌──────────────────────────────────────────────┐
  │ [Para 1] KV Cache stores K/V matrices...     │ ← 高信息量 ✅ 保留
  │ [Para 2] As we know, transformers are...      │ ← 低信息量 ❌ 删除
  │ [Para 3] The memory formula is 2×L×H×d...    │ ← 高信息量 ✅ 保留
  │ [Para 4] In the context of modern AI...      │ ← 低信息量 ❌ 删除
  │ [Para 5] PagedAttention uses paging...       │ ← 高信息量 ✅ 保留
  │ [Para 6-10] ...                               │
  └──────────────────────────────────────────────┘
  
  压缩后 (保留 Top-5 高信息量段落): Token 减少 50%
```

### 压缩方案对比

| 方案 | 压缩粒度 | 压缩率 | 质量保持 | 速度 | 适用场景 |
|------|---------|--------|---------|------|---------|
| LLMLingua | Token 级 | 3-5× | 好 | 快 | RAG/长文档 |
| LLMLingua-2 | Token 级 | 3-10× | 更好 | 更快 | 通用 |
| Selective Context | 句子级 | 2-3× | 很好 | 极快 | RAG |
| 摘要（LLM 生成） | 语义级 | 5-20× | 取决于 LLM | 慢 | 多轮对话历史 |
| 手动精简 | 人工 | 可变 | 最好 | N/A | 固定 Prompt |

---

## StreamingLLM：无限上下文的近似

### 核心原理

> 📖 Attention Sink 机制的基础见 [02-kv-cache-optimization.md](02-kv-cache-optimization.md)

```
StreamingLLM 的完整工作流程：

初始化：
  KV Cache = [Sink₁][Sink₂][Sink₃][Sink₄]  (保留前 4 个 Token)
  Window = []  (滑动窗口为空)

Token 10 到达：
  KV Cache = [S₁][S₂][S₃][S₄] + [T₅][T₆][T₇][T₈][T₉][T₁₀]
  (Sink + 最近 6 个 Token)

Token 100 到达，Window Size = 32：
  KV Cache = [S₁][S₂][S₃][S₄] + [T₆₅][T₆₆]...[T₉₉][T₁₀₀]
  (Sink 4 + 最近 32 = 总 36 个 Token 的 KV)
  
  丢弃的 Token: T₅ ~ T₆₄ → 永久丢失

Token 1,000,000 到达：
  KV Cache = [S₁][S₂][S₃][S₄] + [T₉₉₉₉₆₅]...[T₁₀₀₀₀₀₀]
  (仍然只有 36 个 Token 的 KV → 显存恒定)

效果：
  ✅ 无论处理多少 Token，显存使用恒定
  ✅ 不需要任何模型修改或微调
  ❌ 中间历史信息全部丢失
  ❌ 不适合需要精确回忆历史的任务
```

### 适用与不适用场景

```
✅ 适用场景：

1. 超长对话流（关注当前话题，不需要回忆早期历史）
   客服机器人：用户问了第 200 轮的问题
   → 只需要最近 20 轮的上下文，早期的没关系

2. 流式文本处理
   实时日志分析：持续接收日志流
   → 只需要最近 N 条日志的上下文

3. 实时翻译
   持续翻译直播字幕
   → 只需要最近几句话的上下文保持一致性

4. 长文本分段处理
   分析一本 500 页的书
   → 每次处理 10 页，用 Sink + Window 保持连贯

❌ 不适用场景：

1. "帮我找到第一轮对话中提到的那个数字"
   → 第一轮的信息已被丢弃

2. 需要全局一致性的长文生成
   → 无法记住早期设定

3. 精确事实检索
   → 关键信息可能在被丢弃的区域
```

### StreamingLLM 增强方案

```
StreamingLLM 的改进方向：

1. Sink + H2O 混合
   不只保留 Sink 和最近 Token
   → 还保留历史中最"重要"的 Token（H2O 筛选）
   → KV = [Sink] + [Heavy Hitters] + [Recent Window]
   → 信息保留更完整

2. Sink + 摘要
   定期对滑出窗口的内容做摘要
   → 摘要 Token 替代原始 Token
   → KV = [Sink] + [Summary₁] + [Summary₂] + [Recent]
   → 不完全丢失历史

3. Sink + 外部存储
   滑出窗口的 KV Cache 存到 CPU/Disk
   → 需要时检索回来
   → 结合 RAG 的思想
```

---

## 应用层上下文管理策略

### 多轮对话管理

```
多轮对话的上下文膨胀问题：

Turn 1:  System(2K) + User(100) + Asst(500)         = 2,600
Turn 5:  System(2K) + History(3,000) + User(100)     = 5,100
Turn 20: System(2K) + History(15,000) + User(100)    = 17,100
Turn 50: System(2K) + History(40,000) + User(100)    = 42,100
Turn 100: System(2K) + History(80,000) + User(100)   = 82,100 → 接近 128K 上限!

解决方案：

方案 A: 滑动窗口
  ┌──────────────────────────────────────────┐
  │ 只保留最近 N 轮完整对话                    │
  │                                           │
  │ [System] + [Turn 46-50 完整] + [User]     │
  │                                           │
  │ 优点：简单，保持近期上下文完整             │
  │ 缺点：远期信息完全丢失                     │
  └──────────────────────────────────────────┘

方案 B: 滑动窗口 + 摘要
  ┌──────────────────────────────────────────┐
  │ [System] + [历史摘要(500 tokens)]          │
  │ + [Turn 46-50 完整] + [User]              │
  │                                           │
  │ 历史摘要 = LLM 定期总结早期对话           │
  │ "用户之前讨论了 KV Cache 和分布式训练，    │
  │  关心的是 128K 上下文的显存优化问题..."    │
  │                                           │
  │ 优点：保留关键信息，大幅压缩              │
  │ 缺点：摘要可能丢失细节                     │
  └──────────────────────────────────────────┘

方案 C: 重要轮次保留
  ┌──────────────────────────────────────────┐
  │ [System] + [Turn 1 完整（初始需求）]       │
  │ + [Turn 15 完整（关键决策）]               │
  │ + [Turn 46-50 完整] + [User]              │
  │                                           │
  │ 根据"重要性"选择保留哪些历史轮次          │
  │                                           │
  │ 优点：保留关键上下文                       │
  │ 缺点：需要判断"重要性"                    │
  └──────────────────────────────────────────┘
```

```python
# 方案 B 的实现：滑动窗口 + 摘要
from dataclasses import dataclass

@dataclass
class Message:
    role: str  # "user" or "assistant"
    content: str
    tokens: int

class ConversationManager:
    """多轮对话上下文管理器"""
    
    def __init__(
        self,
        system_prompt: str,
        max_context_tokens: int = 32000,
        recent_window: int = 10,     # 保留最近 10 轮
        summary_budget: int = 500,    # 摘要最多 500 tokens
    ):
        self.system_prompt = system_prompt
        self.max_tokens = max_context_tokens
        self.recent_window = recent_window
        self.summary_budget = summary_budget
        self.history: list[Message] = []
        self.summary: str = ""
    
    def add_message(self, role: str, content: str, tokens: int):
        self.history.append(Message(role, content, tokens))
    
    def build_context(self) -> list[dict]:
        """构建当前轮的上下文"""
        messages = [{"role": "system", "content": self.system_prompt}]
        
        # 添加摘要（如果有）
        if self.summary:
            messages.append({
                "role": "system",
                "content": f"[Previous conversation summary]: {self.summary}"
            })
        
        # 添加最近 N 轮完整对话
        recent = self.history[-(self.recent_window * 2):]  # user + assistant
        for msg in recent:
            messages.append({"role": msg.role, "content": msg.content})
        
        return messages
    
    def maybe_summarize(self, summarize_fn):
        """当历史超过窗口时，触发摘要"""
        if len(self.history) > self.recent_window * 2 + 4:
            # 对被滑出窗口的历史做摘要
            old_messages = self.history[:-(self.recent_window * 2)]
            old_text = "\n".join(
                f"{m.role}: {m.content}" for m in old_messages
            )
            self.summary = summarize_fn(old_text, max_tokens=self.summary_budget)
            # 清理已摘要的历史
            self.history = self.history[-(self.recent_window * 2):]
```

### Agent/Tool-use 上下文优化

```
Agent 场景的上下文管理挑战：

典型 Agent Prompt 结构：
  [System Prompt]           ~500 tokens
  [Tool Descriptions × 20] ~5000 tokens  ← 最大的固定开销
  [Conversation History]    ~2000 tokens
  [Current Task]            ~200 tokens
  总计：                    ~7700 tokens

工具描述占了 65%! 优化策略：

1. 工具描述精简
   Before (verbose):
   """
   Function: search_database
   Description: This function searches the database for records matching
   the given query parameters. It supports filtering by date range,
   category, and status. The function returns a list of matching records
   with all their fields including id, name, category, status, 
   created_at, and updated_at.
   Parameters:
   - query (string, required): The search query text
   - date_from (string, optional): Start date in YYYY-MM-DD format
   - date_to (string, optional): End date in YYYY-MM-DD format
   - category (string, optional): Category filter
   - status (string, optional): Status filter (active/inactive)
   - limit (integer, optional): Maximum number of results (default: 10)
   """  # ~120 tokens

   After (concise):
   """
   search_database(query: str, date_from?: str, date_to?: str, 
                   category?: str, status?: str, limit?: int=10)
   → list[Record]  # Search DB records by query with optional filters
   """  # ~40 tokens
   
   → 节省 66% 的工具描述 Token

2. 动态工具加载
   不是每次都带所有 20 个工具描述
   → 根据当前任务，只加载可能用到的 5-8 个工具
   → 使用 LLM 或规则判断需要哪些工具

3. 工具描述缓存（Prefix Caching）
   固定的工具描述 = 完美的可缓存前缀
   → 开启 Prefix Caching，5K tokens 的工具描述不需要重复计算
```

### RAG 上下文优化

> 📖 RAG 基础和 Token 优化策略详见 [07-knowledge-base/06-rag-fundamentals.md](../07-knowledge-base/06-rag-fundamentals.md) 和 [07-knowledge-base/10-token-optimization.md](../07-knowledge-base/10-token-optimization.md)

```
RAG 的上下文管理黄金法则：

1. 质量 > 数量
   ❌ 塞 20 个 chunk (16K tokens) → "大海捞针"效应
   ✅ 精选 3-5 个 chunk (3-5K tokens) → 信息集中

2. 重排序必不可少
   向量检索 Top-20 → Cross-Encoder 重排序 → Top-5
   → 质量显著提升，Token 显著减少

3. 适应性分块
   短文档：完整放入上下文
   长文档：分块检索，只取相关段落
   代码：按函数/类分块，保持完整性

4. 分层上下文
   ┌──────────────────────────────────┐
   │  [System Prompt]                  │ → 固定，Prefix Caching
   │  [高相关 Chunk (Score > 0.9)]     │ → 必须，完整放入
   │  [中相关 Chunk (Score 0.7-0.9)]   │ → 压缩后放入
   │  [低相关 Chunk (Score < 0.7)]     │ → 不放入
   │  [User Query]                     │ → 固定
   └──────────────────────────────────┘
```

---

## 上下文窗口分配最佳实践

### 通用分配模板

```
┌─────────────────────────────────────────────────────────────┐
│          Context Window 分配模板 (以 128K 为例)               │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  128K tokens 分配：                                          │
│                                                              │
│  ┌────────────┬─────────┬─────────────────────────────┐     │
│  │ 模块        │ Token 数 │ 说明                        │     │
│  ├────────────┼─────────┼─────────────────────────────┤     │
│  │ System     │ 2-4K    │ 角色定义、行为规范、格式要求 │     │
│  │ Tools      │ 2-8K    │ 工具/API 描述（Agent 场景） │     │
│  │ RAG Docs   │ 4-16K   │ 检索文档（质量优先）        │     │
│  │ History    │ 8-32K   │ 对话历史（近期完整+远期摘要）│     │
│  │ User Query │ 1-4K    │ 当前用户输入                │     │
│  │ Reserved   │ 16-32K  │ 生成输出预留空间            │     │
│  │ Buffer     │ 16-32K  │ 安全缓冲（避免截断）        │     │
│  └────────────┴─────────┴─────────────────────────────┘     │
│                                                              │
│  关键原则：                                                   │
│  • System Prompt 放最前（首位记忆优势）                       │
│  • 最重要的信息紧跟 System（第二优先位置）                    │
│  • 当前 Query/指令放最后（结尾记忆优势）                      │
│  • 始终预留 20-30% 给输出                                    │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 不同场景的分配策略

| 场景 | System | RAG/Docs | History | Output | 总计 |
|------|--------|---------|---------|--------|------|
| 单轮 QA | 2K | 8K | 0 | 4K | 14K |
| 多轮对话 | 2K | 0 | 16K | 8K | 26K |
| RAG + 对话 | 2K | 8K | 8K | 4K | 22K |
| Agent | 2K + 5K | 4K | 8K | 4K | 23K |
| 长文档分析 | 2K | 60K | 0 | 16K | 78K |
| 代码补全 | 1K | 16K | 0 | 4K | 21K |

---

## 技术栈选型决策树

### 上下文管理完整决策树

```
                    你面临什么问题？
                         │
        ┌────────────────┼────────────────┐
        │                │                │
  上下文太长           延迟太高         成本太高
        │                │                │
  ┌─────┴─────┐    ┌─────┴─────┐    ┌─────┴─────┐
  │           │    │           │    │           │
显存不够    质量差   TTFT 慢   吞吐低  Token 多  GPU 贵
  │           │    │           │    │           │
  ▼           ▼    ▼           ▼    ▼           ▼
KV Cache   RAG    Chunked   PD    Prompt    异构
优化      替代    Prefill   分离   压缩      GPU
(02)    长上下文  (05)     (06)   (本篇)    (06)
        (本篇)
  │
  ├─ FP8 量化
  ├─ KV 淘汰 (H2O)
  ├─ GQA 模型选择
  └─ Prefix Caching (03)
```

### 技术选型矩阵

```
┌─────────────────┬──────────┬──────────┬──────────┬──────────┐
│ 技术             │ 减少显存 │ 降低延迟 │ 提高吞吐 │ 降低成本 │
├─────────────────┼──────────┼──────────┼──────────┼──────────┤
│ FP8 KV Cache    │ ✅ 50%   │ ⚠️ 轻微  │ ✅ 1.5×  │ ✅       │
│ Prefix Caching  │ ⚠️       │ ✅ 大幅  │ ✅       │ ✅       │
│ Chunked Prefill │ ❌       │ ✅ P99↓  │ ✅ 50%↑  │ ❌       │
│ PD 分离         │ ❌       │ ✅       │ ✅ 大幅  │ ✅ 异构  │
│ GQA 模型        │ ✅ 75%+  │ ✅       │ ✅       │ ✅       │
│ Prompt 压缩     │ ✅ ~70%  │ ✅ ~70%  │ ✅ ~70%  │ ✅ ~70%  │
│ RAG 替代        │ ✅ 90%+  │ ✅ 90%+  │ ✅ 90%+  │ ✅ 90%+  │
│ 对话摘要        │ ✅ 80%+  │ ✅       │ ✅       │ ✅       │
│ StreamingLLM    │ ✅ 95%+  │ ❌       │ ⚠️       │ ✅       │
│ H2O 淘汰        │ ✅ 70%   │ ⚠️       │ ✅       │ ✅       │
└─────────────────┴──────────┴──────────┴──────────┴──────────┘
```

### 推荐组合方案

```
基础方案（适用于 90% 的场景）：
  GQA 模型 + FP8 KV Cache + Prefix Caching + Continuous Batching
  → vLLM 默认配置即可

进阶方案（高性能在线服务）：
  + Chunked Prefill + Prompt 压缩（LLMLingua）
  → 降低 P99，减少 Token 成本

极致方案（大规模生产服务）：
  + PD 分离 + 异构 GPU + 多级 KV 缓存
  → 最大化资源利用率和成本效率
```

---

## 端到端案例

### 案例：企业知识库 QA 系统的上下文管理

```python
"""
企业知识库 QA 系统 - 上下文管理完整示例
"""
from llmlingua import PromptCompressor

class ContextManager:
    """企业级上下文管理器"""
    
    def __init__(self):
        self.compressor = PromptCompressor(
            model_name="microsoft/llmlingua-2-bert-base-multilingual-cased-meetingbank",
            device_map="cuda",
        )
        self.max_context = 32000  # 使用 32K 窗口
        self.system_budget = 2000
        self.rag_budget = 8000
        self.history_budget = 8000
        self.output_budget = 8000
        self.buffer = 6000
    
    def build_context(
        self,
        system_prompt: str,
        retrieved_docs: list[dict],
        conversation_history: list[dict],
        user_query: str,
        compress_threshold: int = 10000,
    ) -> str:
        """构建优化后的上下文"""
        
        # Step 1: System Prompt (固定，Prefix Caching 复用)
        context_parts = [system_prompt]
        used_tokens = len(system_prompt.split()) * 1.3  # 粗估
        
        # Step 2: RAG 文档（重排序 + 按需压缩）
        # 只取 Top-5 高相关文档
        top_docs = sorted(
            retrieved_docs, 
            key=lambda d: d['score'], reverse=True
        )[:5]
        
        doc_text = "\n\n".join(
            f"[Document {i+1} (relevance: {d['score']:.2f})]:\n{d['content']}"
            for i, d in enumerate(top_docs)
        )
        
        doc_tokens = len(doc_text.split()) * 1.3
        if doc_tokens > self.rag_budget:
            # 文档太长，用 LLMLingua 压缩
            compressed = self.compressor.compress_prompt(
                doc_text,
                rate=self.rag_budget / doc_tokens,
                force_tokens=[user_query],  # 保留与查询相关的词
            )
            doc_text = compressed['compressed_prompt']
        
        context_parts.append(doc_text)
        
        # Step 3: 对话历史（滑动窗口 + 摘要）
        if conversation_history:
            recent = conversation_history[-10:]  # 最近 5 轮
            history_text = "\n".join(
                f"{msg['role']}: {msg['content']}" 
                for msg in recent
            )
            context_parts.append(f"[Recent Conversation]:\n{history_text}")
        
        # Step 4: 用户查询（放最后，利用结尾记忆优势）
        context_parts.append(f"User: {user_query}\nAssistant:")
        
        return "\n\n".join(context_parts)

# 使用示例
manager = ContextManager()

context = manager.build_context(
    system_prompt="You are a helpful AI assistant for the engineering team...",
    retrieved_docs=[
        {"content": "KV Cache optimization guide...", "score": 0.95},
        {"content": "PagedAttention technical details...", "score": 0.88},
        {"content": "General LLM serving overview...", "score": 0.72},
    ],
    conversation_history=[
        {"role": "user", "content": "How to optimize inference?"},
        {"role": "assistant", "content": "There are several approaches..."},
    ],
    user_query="Specifically, how to reduce KV Cache memory?",
)
```

---

## 总结

```
┌─────────────────────────────────────────────────────────────┐
│           上下文工程与压缩 - 关键要点                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 上下文工程 = 设计"放什么、怎么放、放多少"               │
│     比 Prompt Engineering 更广泛                             │
│                                                              │
│  2. 压缩技术：                                               │
│     LLMLingua (Token 级, 3-10×) > Selective Context (句子级) │
│     适用于 RAG 文档和长 Prompt 压缩                          │
│                                                              │
│  3. StreamingLLM = Sink + 滑动窗口                           │
│     适合流式/超长对话，不适合需要精确回忆的场景               │
│                                                              │
│  4. 应用层策略：                                             │
│     对话：滑动窗口 + 摘要                                    │
│     Agent：工具描述精简 + Prefix Caching                     │
│     RAG：Top-K 精选 + 重排序 + 按需压缩                     │
│                                                              │
│  5. 分配原则：                                               │
│     首尾优先 + 预留输出 + 质量>数量 + 监控利用率             │
│                                                              │
│  6. 选型：按场景组合技术栈，从基础方案逐步进阶               │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

*上一篇：[06-disaggregated-serving.md](06-disaggregated-serving.md) — Prefill/Decode 分离架构*

*返回目录：[README.md](README.md)*

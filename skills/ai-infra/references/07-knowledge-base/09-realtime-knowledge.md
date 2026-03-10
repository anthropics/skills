# 实时知识获取

> 静态知识库解决"知识丰富但滞后"的问题，实时知识获取让 AI 真正做到"知天下事、答当下问"。

## 目录

- [实时知识的挑战](#实时知识的挑战)
- [实时数据场景分析](#实时数据场景分析)
- [Function Calling + 知识库](#function-calling--知识库)
- [Tool Use 模式详解](#tool-use-模式详解)
- [流式数据接入与索引更新](#流式数据接入与索引更新)
- [CDC 集成方案](#cdc-集成方案)
- [时效性标记与过期策略](#时效性标记与过期策略)
- [在线-离线混合架构](#在线-离线混合架构)
- [实战练习](#实战练习)

---

## 实时知识的挑战

### 静态知识库的局限

传统知识库基于"先索引、后检索"的模式，天然存在信息滞后：

```
┌─────────────────────────────────────────────────────────┐
│              静态知识库 vs 实时知识需求                    │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  静态知识库                实时世界                       │
│  ┌──────────┐             ┌──────────┐                  │
│  │ 文档快照  │             │ 股票价格  │ → 秒级变化        │
│  │ (T-1天)  │             │ 新闻事件  │ → 分钟级变化      │
│  │          │    GAP      │ 天气预报  │ → 小时级变化      │
│  │ 索引时间  │◄──────────►│ 法律法规  │ → 天/周级变化     │
│  │ = 查询时间│             │ 产品价格  │ → 天级变化        │
│  └──────────┘             └──────────┘                  │
│                                                         │
│  问题：用户问"现在特斯拉股价多少？"                       │
│  静态KB：只有上次索引时的价格（可能是昨天的）               │
│  实时获取：调用 API 获取当前价格                           │
└─────────────────────────────────────────────────────────┘
```

### 数据时效性分类

| 时效性类别 | 更新频率 | 典型数据 | 获取策略 |
|-----------|---------|---------|---------|
| 实时（秒级） | < 1 分钟 | 股票行情、汇率、交通状况 | API 实时调用 |
| 近实时（分钟级） | 1~60 分钟 | 新闻头条、社交媒体热点 | 推送 + 短期缓存 |
| 准实时（小时级） | 1~24 小时 | 天气预报、商品价格 | 定时拉取 + 缓存 |
| 定期更新（天级） | 1~7 天 | 法律法规、产品手册 | 定时批量更新 |
| 低频更新（月级） | > 30 天 | 百科知识、历史资料 | 离线批量索引 |

---

## 实时数据场景分析

### 场景一：金融行情查询

```
用户：特斯拉现在的股价是多少？今天涨跌如何？

期望行为：
1. 识别"现在"→ 需要实时数据
2. 调用股票 API 获取 TSLA 实时行情
3. 结合知识库中的特斯拉公司背景信息
4. 生成包含实时价格的综合回答
```

### 场景二：新闻事件问答

```
用户：今天有什么重要的 AI 新闻？

期望行为：
1. 识别"今天"→ 需要当天数据
2. 调用新闻 API 获取当日 AI 领域新闻
3. 结合知识库中的 AI 行业背景知识
4. 生成新闻摘要和分析
```

### 场景三：实时状态查询

```
用户：北京现在的天气怎么样？适合户外跑步吗？

期望行为：
1. 调用天气 API 获取北京实时天气
2. 结合知识库中的运动医学建议
3. 根据温度/湿度/空气质量综合判断
4. 给出个性化建议
```

### 场景四：产品价格查询

```
用户：iPhone 16 Pro Max 在京东和天猫的价格分别是多少？

期望行为：
1. 调用电商价格 API
2. 结合知识库中的产品规格信息
3. 对比价格和促销信息
4. 给出购买建议
```

---

## Function Calling + 知识库

### 核心架构

Function Calling 是 LLM 接入实时数据的标准方式：

```
┌──────────────────────────────────────────────────────────────┐
│              Function Calling + 知识库 联合架构                │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  用户查询                                                     │
│     │                                                        │
│     ▼                                                        │
│  ┌──────────┐                                                │
│  │ 意图识别  │───► 判断是否需要实时数据                         │
│  └────┬─────┘                                                │
│       │                                                      │
│       ├──► 纯知识库问题 ──► 走标准 RAG 流程                    │
│       │                                                      │
│       ├──► 纯实时问题 ──► Function Calling                    │
│       │                                                      │
│       └──► 混合问题 ──► 并行执行                               │
│                          │                                   │
│              ┌───────────┼───────────┐                       │
│              ▼           ▼           ▼                       │
│         ┌────────┐ ┌──────────┐ ┌────────┐                  │
│         │知识库   │ │ 股票 API │ │天气 API│                   │
│         │检索     │ │          │ │        │                   │
│         └────┬───┘ └────┬─────┘ └───┬────┘                  │
│              │          │           │                        │
│              └──────────┼───────────┘                        │
│                         ▼                                    │
│                  ┌──────────────┐                             │
│                  │  上下文合并   │                             │
│                  │  Prompt 构造 │                             │
│                  └──────┬───────┘                             │
│                         ▼                                    │
│                  ┌──────────────┐                             │
│                  │  LLM 生成    │                             │
│                  └──────────────┘                             │
└──────────────────────────────────────────────────────────────┘
```

### Function Calling 基础实现

```python
import openai
import json
from datetime import datetime

# ========== 1. 定义工具函数 ==========
def get_stock_price(symbol: str) -> dict:
    """获取实时股票价格（示例使用 Alpha Vantage API）"""
    import requests
    
    url = f"https://www.alphavantage.co/query"
    params = {
        "function": "GLOBAL_QUOTE",
        "symbol": symbol,
        "apikey": "YOUR_API_KEY"
    }
    response = requests.get(url, params=params)
    data = response.json().get("Global Quote", {})
    
    return {
        "symbol": data.get("01. symbol", symbol),
        "price": float(data.get("05. price", 0)),
        "change": float(data.get("09. change", 0)),
        "change_percent": data.get("10. change percent", "0%"),
        "volume": int(data.get("06. volume", 0)),
        "latest_trading_day": data.get("07. latest trading day", ""),
        "timestamp": datetime.now().isoformat()
    }

def get_weather(city: str) -> dict:
    """获取实时天气信息"""
    import requests
    
    url = "https://api.openweathermap.org/data/2.5/weather"
    params = {
        "q": city,
        "appid": "YOUR_API_KEY",
        "units": "metric",
        "lang": "zh_cn"
    }
    response = requests.get(url, params=params)
    data = response.json()
    
    return {
        "city": city,
        "temperature": data["main"]["temp"],
        "humidity": data["main"]["humidity"],
        "description": data["weather"][0]["description"],
        "wind_speed": data["wind"]["speed"],
        "aqi": "待查询",  # 需要额外 API
        "timestamp": datetime.now().isoformat()
    }

def search_knowledge_base(query: str) -> list:
    """搜索知识库（已有的 RAG 检索函数）"""
    # 复用已有的知识库检索逻辑
    from your_rag_module import retriever
    results = retriever.search(query, top_k=3)
    return [{"content": r.content, "source": r.metadata["source"]} for r in results]


# ========== 2. 定义 Tools Schema ==========
tools = [
    {
        "type": "function",
        "function": {
            "name": "get_stock_price",
            "description": "获取指定股票的实时价格信息，包括当前价格、涨跌幅、成交量等",
            "parameters": {
                "type": "object",
                "properties": {
                    "symbol": {
                        "type": "string",
                        "description": "股票代码，如 TSLA、AAPL、GOOGL"
                    }
                },
                "required": ["symbol"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "get_weather",
            "description": "获取指定城市的实时天气信息，包括温度、湿度、风速等",
            "parameters": {
                "type": "object",
                "properties": {
                    "city": {
                        "type": "string",
                        "description": "城市名称，如 Beijing、Shanghai"
                    }
                },
                "required": ["city"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "search_knowledge_base",
            "description": "在知识库中搜索相关信息，用于回答需要背景知识的问题",
            "parameters": {
                "type": "object",
                "properties": {
                    "query": {
                        "type": "string",
                        "description": "搜索查询语句"
                    }
                },
                "required": ["query"]
            }
        }
    }
]


# ========== 3. 联合调用流程 ==========
class RealtimeRAGAssistant:
    """结合 Function Calling 和知识库的智能助手"""
    
    def __init__(self, model: str = "gpt-4o"):
        self.client = openai.OpenAI()
        self.model = model
        self.tool_map = {
            "get_stock_price": get_stock_price,
            "get_weather": get_weather,
            "search_knowledge_base": search_knowledge_base,
        }
    
    def chat(self, user_message: str) -> str:
        messages = [
            {
                "role": "system",
                "content": (
                    "你是一个智能助手，可以访问知识库和实时数据源。"
                    "对于需要最新信息的问题（如股价、天气），使用相应工具获取实时数据。"
                    "对于需要背景知识的问题，搜索知识库。"
                    "对于混合问题，同时使用多个工具。"
                    "始终标注数据来源和获取时间。"
                )
            },
            {"role": "user", "content": user_message}
        ]
        
        # 第一次调用：LLM 决定使用哪些工具
        response = self.client.chat.completions.create(
            model=self.model,
            messages=messages,
            tools=tools,
            tool_choice="auto"
        )
        
        assistant_message = response.choices[0].message
        
        # 如果不需要工具调用，直接返回
        if not assistant_message.tool_calls:
            return assistant_message.content
        
        # 执行所有工具调用
        messages.append(assistant_message)
        
        for tool_call in assistant_message.tool_calls:
            func_name = tool_call.function.name
            func_args = json.loads(tool_call.function.arguments)
            
            # 调用对应函数
            result = self.tool_map[func_name](**func_args)
            
            messages.append({
                "role": "tool",
                "tool_call_id": tool_call.id,
                "content": json.dumps(result, ensure_ascii=False)
            })
        
        # 第二次调用：LLM 基于工具结果生成最终回答
        final_response = self.client.chat.completions.create(
            model=self.model,
            messages=messages
        )
        
        return final_response.choices[0].message.content


# ========== 4. 使用示例 ==========
assistant = RealtimeRAGAssistant()

# 纯实时查询
print(assistant.chat("特斯拉现在的股价是多少？"))

# 混合查询：实时数据 + 知识库
print(assistant.chat("特斯拉的股价是多少？结合最近的财报分析一下走势"))

# 纯知识库查询
print(assistant.chat("什么是 Transformer 架构？"))
```

### 并行工具调用（Parallel Tool Calls）

```python
# OpenAI 支持在一次响应中返回多个 tool_calls
# LLM 会自动判断需要并行调用哪些工具

# 示例：用户问"北京天气怎么样？特斯拉股价多少？"
# LLM 返回的 tool_calls 可能包含:
# [
#   {"function": {"name": "get_weather", "arguments": '{"city":"Beijing"}'}},
#   {"function": {"name": "get_stock_price", "arguments": '{"symbol":"TSLA"}'}}
# ]

# 可以并行执行所有工具调用以降低延迟
import asyncio
import aiohttp

async def execute_tools_parallel(tool_calls: list, tool_map: dict) -> list:
    """并行执行多个工具调用"""
    
    async def execute_one(tool_call):
        func_name = tool_call.function.name
        func_args = json.loads(tool_call.function.arguments)
        result = tool_map[func_name](**func_args)
        return {
            "tool_call_id": tool_call.id,
            "content": json.dumps(result, ensure_ascii=False)
        }
    
    tasks = [execute_one(tc) for tc in tool_calls]
    results = await asyncio.gather(*tasks)
    return results
```

---

## Tool Use 模式详解

### 模式一：React Agent（推理-行动循环）

```
┌─────────────────────────────────────────────────────┐
│              ReAct Agent 模式                        │
├─────────────────────────────────────────────────────┤
│                                                     │
│  Query: "比较 TSLA 和 AAPL 今天的表现"               │
│                                                     │
│  ┌─── 循环 ──────────────────────────────────┐      │
│  │                                           │      │
│  │  Thought: 需要获取两只股票的实时数据        │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Action: get_stock_price("TSLA")          │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Observation: {price: 248.5, change: +2%} │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Thought: 还需要 AAPL 的数据              │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Action: get_stock_price("AAPL")          │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Observation: {price: 189.3, change: -1%} │      │
│  │     │                                     │      │
│  │     ▼                                     │      │
│  │  Thought: 已有足够数据，可以回答           │      │
│  │                                           │      │
│  └───────────────────────────────────────────┘      │
│                                                     │
│  Final Answer: TSLA 今天上涨 2%，AAPL 下跌 1%...    │
└─────────────────────────────────────────────────────┘
```

### 模式二：Router Agent（路由分发）

```python
from langchain.agents import AgentExecutor, create_openai_tools_agent
from langchain_openai import ChatOpenAI
from langchain.tools import Tool, StructuredTool
from langchain_core.prompts import ChatPromptTemplate, MessagesPlaceholder

# 定义工具集
tools = [
    StructuredTool.from_function(
        func=get_stock_price,
        name="stock_price",
        description="获取实时股票价格"
    ),
    StructuredTool.from_function(
        func=get_weather,
        name="weather",
        description="获取实时天气"
    ),
    StructuredTool.from_function(
        func=search_knowledge_base,
        name="knowledge_search",
        description="搜索知识库获取背景信息"
    ),
]

# 创建 Agent
llm = ChatOpenAI(model="gpt-4o", temperature=0)
prompt = ChatPromptTemplate.from_messages([
    ("system", "你是智能助手，根据问题类型选择合适的工具。"),
    ("human", "{input}"),
    MessagesPlaceholder(variable_name="agent_scratchpad"),
])

agent = create_openai_tools_agent(llm, tools, prompt)
agent_executor = AgentExecutor(agent=agent, tools=tools, verbose=True)

result = agent_executor.invoke({"input": "特斯拉现在股价多少？这个价格合理吗？"})
```

### 模式三：Plan-and-Execute（规划-执行）

适合复杂的多步骤查询：

```python
from langchain_experimental.plan_and_execute import (
    PlanAndExecute, 
    load_agent_executor, 
    load_chat_planner
)

# 规划器：将复杂问题拆解为步骤
planner = load_chat_planner(llm)

# 执行器：按步骤执行
executor = load_agent_executor(llm, tools, verbose=True)

agent = PlanAndExecute(planner=planner, executor=executor, verbose=True)

# 复杂查询示例
result = agent.run(
    "帮我分析一下特斯拉的投资价值："
    "1. 当前股价和近期走势"
    "2. 最新财报的关键数据"
    "3. 行业竞争格局"
    "4. 给出投资建议"
)

# Agent 会自动规划：
# Step 1: get_stock_price("TSLA") → 获取实时价格
# Step 2: knowledge_search("特斯拉最新财报") → 搜索知识库
# Step 3: knowledge_search("电动车行业竞争格局") → 搜索知识库
# Step 4: 综合分析并生成投资建议
```

---

## 流式数据接入与索引更新

### 增量索引更新架构

```
┌──────────────────────────────────────────────────────────┐
│              流式数据接入架构                               │
├──────────────────────────────────────────────────────────┤
│                                                          │
│  数据源                 消息队列          处理层            │
│  ┌──────────┐         ┌────────┐       ┌──────────┐     │
│  │ 新闻 API │────────►│        │──────►│ 文档解析  │     │
│  └──────────┘         │        │       │ & 分块    │     │
│  ┌──────────┐         │ Kafka  │       └────┬─────┘     │
│  │ RSS Feed │────────►│   /    │            │            │
│  └──────────┘         │ Pulsar │       ┌────▼─────┐     │
│  ┌──────────┐         │        │       │ Embedding │     │
│  │ Webhook  │────────►│        │       │ 生成      │     │
│  └──────────┘         └────────┘       └────┬─────┘     │
│  ┌──────────┐                               │            │
│  │ 爬虫定时  │                          ┌────▼─────┐     │
│  │ 任务     │─────────────────────────►│ 向量数据库│     │
│  └──────────┘                          │ 增量更新  │     │
│                                        └──────────┘     │
└──────────────────────────────────────────────────────────┘
```

### 流式更新实现

```python
import hashlib
from datetime import datetime, timedelta
from typing import Optional
from dataclasses import dataclass, field

@dataclass
class StreamDocument:
    """流式文档对象"""
    content: str
    source: str
    timestamp: datetime
    ttl: Optional[timedelta] = None  # 过期时间
    doc_hash: str = field(init=False)
    
    def __post_init__(self):
        self.doc_hash = hashlib.md5(self.content.encode()).hexdigest()
    
    @property
    def is_expired(self) -> bool:
        if self.ttl is None:
            return False
        return datetime.now() > self.timestamp + self.ttl


class StreamingKnowledgeUpdater:
    """流式知识库更新器"""
    
    def __init__(self, vector_store, embedding_model):
        self.vector_store = vector_store
        self.embedding_model = embedding_model
        self.seen_hashes = set()  # 去重
    
    def process_document(self, doc: StreamDocument) -> bool:
        """处理单个文档的增量更新"""
        # 1. 去重检查
        if doc.doc_hash in self.seen_hashes:
            return False
        self.seen_hashes.add(doc.doc_hash)
        
        # 2. 检查是否已存在（基于 source 查询）
        existing = self.vector_store.query(
            filter={"source": doc.source},
            limit=1
        )
        
        if existing:
            # 更新：先删除旧版本
            self.vector_store.delete(ids=[existing[0].id])
        
        # 3. 生成 Embedding
        embedding = self.embedding_model.encode(doc.content)
        
        # 4. 写入向量数据库
        self.vector_store.insert(
            vectors=[embedding],
            documents=[doc.content],
            metadata=[{
                "source": doc.source,
                "timestamp": doc.timestamp.isoformat(),
                "ttl": doc.ttl.total_seconds() if doc.ttl else None,
                "hash": doc.doc_hash,
            }]
        )
        
        return True
    
    def cleanup_expired(self):
        """清理过期文档"""
        now = datetime.now()
        # 查询所有有 TTL 的文档
        results = self.vector_store.query(
            filter={"ttl": {"$ne": None}},
            limit=10000
        )
        
        expired_ids = []
        for doc in results:
            ts = datetime.fromisoformat(doc.metadata["timestamp"])
            ttl = timedelta(seconds=doc.metadata["ttl"])
            if now > ts + ttl:
                expired_ids.append(doc.id)
        
        if expired_ids:
            self.vector_store.delete(ids=expired_ids)
            print(f"清理了 {len(expired_ids)} 个过期文档")


# ========== Kafka 消费者示例 ==========
from kafka import KafkaConsumer

def start_streaming_updater():
    """启动流式更新消费者"""
    consumer = KafkaConsumer(
        'knowledge-updates',
        bootstrap_servers=['localhost:9092'],
        value_deserializer=lambda m: json.loads(m.decode('utf-8')),
        group_id='kb-updater'
    )
    
    updater = StreamingKnowledgeUpdater(vector_store, embedding_model)
    
    for message in consumer:
        data = message.value
        doc = StreamDocument(
            content=data["content"],
            source=data["source"],
            timestamp=datetime.fromisoformat(data["timestamp"]),
            ttl=timedelta(hours=data.get("ttl_hours", 0)) if data.get("ttl_hours") else None
        )
        
        updated = updater.process_document(doc)
        if updated:
            print(f"更新文档: {doc.source} @ {doc.timestamp}")
    
    # 定时清理过期文档
    import schedule
    schedule.every(1).hours.do(updater.cleanup_expired)
```

---

## CDC 集成方案

### 什么是 CDC

CDC（Change Data Capture，变更数据捕获）是一种跟踪数据库变更的技术，能够实时捕获数据库中的 INSERT、UPDATE、DELETE 操作，并将变更推送到下游系统。

```
┌──────────────────────────────────────────────────────────┐
│              CDC → 知识库同步架构                          │
├──────────────────────────────────────────────────────────┤
│                                                          │
│  业务数据库              CDC 组件          知识库          │
│  ┌──────────┐          ┌────────┐       ┌──────────┐    │
│  │ MySQL    │──binlog──│        │──────►│ 向量     │    │
│  │ (产品表) │          │Debezium│       │ 数据库   │    │
│  └──────────┘          │   /    │       └──────────┘    │
│  ┌──────────┐          │Maxwell │                       │
│  │PostgreSQL│──WAL────►│   /    │       ┌──────────┐    │
│  │ (文档表) │          │Canal   │──────►│ 全文搜索 │    │
│  └──────────┘          └────────┘       │ 引擎     │    │
│                             │           └──────────┘    │
│                        ┌────▼────┐                      │
│                        │  Kafka  │                      │
│                        └─────────┘                      │
│                                                         │
│  变更事件格式：                                           │
│  {                                                      │
│    "op": "u",        // c=create, u=update, d=delete    │
│    "before": {...},  // 变更前的数据                      │
│    "after": {...},   // 变更后的数据                      │
│    "source": {...},  // 来源信息                         │
│    "ts_ms": 1234567  // 时间戳                           │
│  }                                                      │
└──────────────────────────────────────────────────────────┘
```

### Debezium + Kafka 实现

```python
# CDC 事件处理器
class CDCKnowledgeSync:
    """基于 CDC 的知识库同步器"""
    
    def __init__(self, vector_store, embedding_model):
        self.vector_store = vector_store
        self.embedding_model = embedding_model
    
    def handle_event(self, event: dict):
        """处理 CDC 事件"""
        op = event["op"]
        
        if op == "c":  # CREATE
            self._handle_create(event["after"])
        elif op == "u":  # UPDATE
            self._handle_update(event["before"], event["after"])
        elif op == "d":  # DELETE
            self._handle_delete(event["before"])
    
    def _handle_create(self, data: dict):
        """处理新增记录"""
        doc_id = str(data["id"])
        content = self._build_content(data)
        embedding = self.embedding_model.encode(content)
        
        self.vector_store.insert(
            ids=[doc_id],
            vectors=[embedding],
            documents=[content],
            metadata=[{
                "source_table": data.get("_table", "unknown"),
                "source_id": doc_id,
                "updated_at": datetime.now().isoformat(),
            }]
        )
    
    def _handle_update(self, before: dict, after: dict):
        """处理更新记录"""
        doc_id = str(after["id"])
        
        # 先删除旧记录
        self.vector_store.delete(ids=[doc_id])
        
        # 再插入新记录
        self._handle_create(after)
    
    def _handle_delete(self, data: dict):
        """处理删除记录"""
        doc_id = str(data["id"])
        self.vector_store.delete(ids=[doc_id])
    
    def _build_content(self, data: dict) -> str:
        """将数据库记录构建为文档内容"""
        # 根据表结构定制内容格式
        if "title" in data and "body" in data:
            return f"# {data['title']}\n\n{data['body']}"
        elif "name" in data and "description" in data:
            return f"产品名称：{data['name']}\n描述：{data['description']}"
        else:
            return json.dumps(data, ensure_ascii=False)


# ========== Docker Compose 配置示例 ==========
"""
# docker-compose.yml
version: '3'
services:
  zookeeper:
    image: confluentinc/cp-zookeeper:7.5.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181

  kafka:
    image: confluentinc/cp-kafka:7.5.0
    depends_on: [zookeeper]
    environment:
      KAFKA_BROKER_ID: 1
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://kafka:9092

  debezium:
    image: debezium/connect:2.4
    depends_on: [kafka]
    environment:
      BOOTSTRAP_SERVERS: kafka:9092
      GROUP_ID: 1
      CONFIG_STORAGE_TOPIC: debezium_configs
      OFFSET_STORAGE_TOPIC: debezium_offsets
      STATUS_STORAGE_TOPIC: debezium_statuses

  # 注册 MySQL Connector
  # curl -X POST http://localhost:8083/connectors -H "Content-Type: application/json" -d '{
  #   "name": "mysql-connector",
  #   "config": {
  #     "connector.class": "io.debezium.connector.mysql.MySqlConnector",
  #     "database.hostname": "mysql",
  #     "database.port": "3306",
  #     "database.user": "debezium",
  #     "database.password": "dbz",
  #     "database.server.id": "1",
  #     "topic.prefix": "dbserver1",
  #     "database.include.list": "knowledge_db",
  #     "schema.history.internal.kafka.bootstrap.servers": "kafka:9092",
  #     "schema.history.internal.kafka.topic": "schema-changes"
  #   }
  # }'
"""
```

---

## 时效性标记与过期策略

### 文档时效性管理

```python
from enum import Enum
from datetime import datetime, timedelta

class Freshness(Enum):
    """文档新鲜度级别"""
    REALTIME = "realtime"      # 实时数据，每次查询时获取
    HOT = "hot"                # 热数据，1小时内有效
    WARM = "warm"              # 温数据，24小时内有效
    COLD = "cold"              # 冷数据，7天内有效
    ARCHIVE = "archive"        # 归档数据，长期有效

# 不同新鲜度的默认 TTL
FRESHNESS_TTL = {
    Freshness.REALTIME: timedelta(minutes=0),   # 不缓存
    Freshness.HOT: timedelta(hours=1),
    Freshness.WARM: timedelta(hours=24),
    Freshness.COLD: timedelta(days=7),
    Freshness.ARCHIVE: None,                     # 永不过期
}


class TimeSensitiveRetriever:
    """时效性感知的检索器"""
    
    def __init__(self, vector_store, realtime_tools: dict):
        self.vector_store = vector_store
        self.realtime_tools = realtime_tools  # 实时数据获取工具
    
    def retrieve(self, query: str, freshness_required: Freshness = None) -> list:
        """根据时效性要求检索"""
        
        # 1. 从向量数据库检索
        kb_results = self.vector_store.search(query, top_k=5)
        
        # 2. 过滤过期文档
        valid_results = []
        for result in kb_results:
            if self._is_valid(result, freshness_required):
                valid_results.append(result)
            else:
                # 标记需要刷新
                self._mark_stale(result)
        
        # 3. 如果需要实时数据，补充实时查询
        if freshness_required == Freshness.REALTIME:
            realtime_data = self._fetch_realtime(query)
            if realtime_data:
                valid_results.insert(0, realtime_data)
        
        return valid_results
    
    def _is_valid(self, result, required_freshness: Freshness) -> bool:
        """检查文档是否在有效期内"""
        metadata = result.metadata
        doc_time = datetime.fromisoformat(metadata.get("timestamp", "1970-01-01"))
        doc_freshness = Freshness(metadata.get("freshness", "archive"))
        
        ttl = FRESHNESS_TTL.get(doc_freshness)
        if ttl is None:
            return True  # 永不过期
        
        return datetime.now() - doc_time < ttl
    
    def _fetch_realtime(self, query: str) -> Optional[dict]:
        """根据查询意图获取实时数据"""
        # 简单的意图匹配
        for keyword, tool_func in self.realtime_tools.items():
            if keyword in query:
                return tool_func(query)
        return None
    
    def _mark_stale(self, result):
        """标记过期文档，触发后台更新"""
        pass  # 发送更新任务到消息队列


# ========== 时效性感知的 Prompt 构造 ==========
def build_time_aware_prompt(query: str, results: list) -> str:
    """构造带时效性标注的 Prompt"""
    context_parts = []
    
    for i, result in enumerate(results, 1):
        metadata = result.metadata
        timestamp = metadata.get("timestamp", "未知")
        freshness = metadata.get("freshness", "archive")
        source = metadata.get("source", "未知来源")
        
        # 标注数据时效性
        if freshness == "realtime":
            time_label = f"🔴 实时数据（{timestamp}）"
        elif freshness == "hot":
            time_label = f"🟡 近期数据（{timestamp}）"
        else:
            time_label = f"⚪ 历史数据（{timestamp}）"
        
        context_parts.append(
            f"[来源 {i}] {time_label}\n"
            f"来源：{source}\n"
            f"内容：{result.content}\n"
        )
    
    context = "\n---\n".join(context_parts)
    
    return f"""基于以下信息回答用户问题。注意数据的时效性标注：
- 🔴 实时数据：刚刚获取的最新数据
- 🟡 近期数据：近期有效的数据
- ⚪ 历史数据：可能已过时，需要谨慎引用

{context}

用户问题：{query}

要求：
1. 优先引用实时数据和近期数据
2. 如果引用历史数据，明确说明数据可能不是最新的
3. 标注关键数据的来源和获取时间"""
```

---

## 在线-离线混合架构

### 架构设计

```
┌─────────────────────────────────────────────────────────────┐
│              在线-离线混合知识库架构                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌────────── 在线层（Online） ───────────┐                   │
│  │                                      │                   │
│  │  ┌──────────┐    ┌──────────────┐    │                   │
│  │  │ API 网关  │    │ Function     │    │                   │
│  │  │ (限流/缓存)│   │ Calling      │    │  延迟：< 1s       │
│  │  └─────┬────┘    │ (实时数据)   │    │  数据：秒级新鲜    │
│  │        │         └──────┬───────┘    │                   │
│  │        │                │            │                   │
│  │  ┌─────▼────────────────▼──────┐     │                   │
│  │  │    实时缓存层（Redis）       │     │                   │
│  │  │    热点查询 + 实时数据缓存   │     │                   │
│  │  └────────────────────────────┘     │                   │
│  └──────────────────────────────────────┘                   │
│                       │                                     │
│                       ▼                                     │
│  ┌────────── 近线层（Nearline） ─────────┐                   │
│  │                                      │                   │
│  │  ┌──────────────────────────┐        │                   │
│  │  │   向量数据库（热数据）     │        │  延迟：< 100ms    │
│  │  │   最近 7 天的文档         │        │  数据：天级新鲜    │
│  │  │   高频访问的知识          │        │                   │
│  │  └──────────────────────────┘        │                   │
│  └──────────────────────────────────────┘                   │
│                       │                                     │
│                       ▼                                     │
│  ┌────────── 离线层（Offline） ──────────┐                   │
│  │                                      │                   │
│  │  ┌──────────────────────────┐        │                   │
│  │  │   向量数据库（全量数据）   │        │  延迟：< 500ms    │
│  │  │   历史文档归档            │        │  数据：全量知识    │
│  │  │   低频访问的知识          │        │                   │
│  │  └──────────────────────────┘        │                   │
│  │  ┌──────────────────────────┐        │                   │
│  │  │   批量索引 Pipeline       │        │                   │
│  │  │   每日全量/增量更新       │        │                   │
│  │  └──────────────────────────┘        │                   │
│  └──────────────────────────────────────┘                   │
└─────────────────────────────────────────────────────────────┘
```

### 分层检索策略

```python
class HybridKnowledgeSystem:
    """在线-离线混合知识库系统"""
    
    def __init__(self, redis_cache, hot_vector_db, cold_vector_db, realtime_tools):
        self.cache = redis_cache           # L1: 缓存层
        self.hot_db = hot_vector_db        # L2: 热数据向量库
        self.cold_db = cold_vector_db      # L3: 冷数据向量库
        self.realtime_tools = realtime_tools  # L0: 实时 API
    
    async def retrieve(self, query: str, need_realtime: bool = False) -> dict:
        """分层检索"""
        results = {
            "realtime": None,
            "cached": None,
            "hot": [],
            "cold": [],
        }
        
        # L0: 实时数据（按需）
        if need_realtime:
            results["realtime"] = await self._fetch_realtime(query)
        
        # L1: 缓存命中检查
        cache_key = self._build_cache_key(query)
        cached = self.cache.get(cache_key)
        if cached:
            results["cached"] = json.loads(cached)
            return results  # 缓存命中，快速返回
        
        # L2: 热数据检索
        results["hot"] = await self.hot_db.search(query, top_k=3)
        
        # L3: 如果热数据不够，补充冷数据
        if len(results["hot"]) < 3:
            results["cold"] = await self.cold_db.search(
                query, 
                top_k=3 - len(results["hot"])
            )
        
        # 写入缓存
        all_docs = results["hot"] + results["cold"]
        if all_docs:
            self.cache.setex(
                cache_key, 
                3600,  # 1 小时缓存
                json.dumps([d.to_dict() for d in all_docs])
            )
        
        return results
    
    def _build_cache_key(self, query: str) -> str:
        """构建语义缓存 key"""
        return f"kb:query:{hashlib.md5(query.encode()).hexdigest()}"
    
    async def _fetch_realtime(self, query: str):
        """获取实时数据"""
        for pattern, tool in self.realtime_tools.items():
            if pattern in query.lower():
                return await tool(query)
        return None


# ========== 数据分层迁移 ==========
class DataTieringManager:
    """数据分层管理器"""
    
    def __init__(self, hot_db, cold_db):
        self.hot_db = hot_db
        self.cold_db = cold_db
    
    def promote_to_hot(self, doc_ids: list):
        """将冷数据提升为热数据（高频访问时触发）"""
        docs = self.cold_db.get(ids=doc_ids)
        self.hot_db.insert(docs)
    
    def demote_to_cold(self, days_threshold: int = 7):
        """将过期热数据降级为冷数据"""
        cutoff = datetime.now() - timedelta(days=days_threshold)
        stale_docs = self.hot_db.query(
            filter={"timestamp": {"$lt": cutoff.isoformat()}}
        )
        
        if stale_docs:
            # 迁移到冷库
            self.cold_db.insert(stale_docs)
            # 从热库删除
            self.hot_db.delete(ids=[d.id for d in stale_docs])
            print(f"迁移 {len(stale_docs)} 个文档到冷库")
```

### 生产环境部署考量

| 考量维度 | 在线层 | 近线层 | 离线层 |
|---------|--------|--------|--------|
| 延迟目标 | < 200ms | < 500ms | < 2s |
| 数据规模 | 缓存热点 | 近期数据 | 全量数据 |
| 更新频率 | 实时 | 分钟~小时级 | 天~周级 |
| 存储成本 | 高（内存） | 中（SSD） | 低（HDD/对象存储） |
| 可用性 | 99.99% | 99.9% | 99% |
| 典型技术 | Redis / API | Milvus / Qdrant | Milvus / S3 + 索引 |

---

## 实战练习

### 练习 1：构建实时股票问答助手

```
目标：构建一个能回答实时股票问题的 AI 助手
要求：
1. 集成股票 API（Alpha Vantage / Yahoo Finance）
2. 结合知识库中的公司基本面信息
3. 支持以下查询类型：
   - "特斯拉现在的股价是多少？"
   - "苹果最近一周的走势如何？"
   - "比较微软和谷歌今天的表现"
4. 回答中需标注数据获取时间

提示：
- 使用 Function Calling 获取实时数据
- 使用 RAG 检索公司背景信息
- 实现并行工具调用以降低延迟
```

### 练习 2：实现 CDC 同步知识库

```
目标：基于 Debezium + Kafka 实现数据库变更实时同步到知识库
要求：
1. MySQL 数据库包含 products 和 articles 两张表
2. Debezium 监听 binlog 变更
3. Python 消费者处理 CDC 事件并更新向量数据库
4. 支持 INSERT/UPDATE/DELETE 三种操作
5. 实现幂等性保证

提示：
- 使用 Docker Compose 搭建 MySQL + Kafka + Debezium
- CDC 事件需要做 Schema 映射（数据库字段 → 文档内容）
- 考虑批量处理以提高吞吐量
```

### 练习 3：实现时效性感知检索

```
目标：构建一个能感知数据时效性的 RAG 系统
要求：
1. 文档入库时标注新鲜度级别（实时/热/温/冷/归档）
2. 检索时自动过滤过期文档
3. 对于需要实时数据的查询，自动降级到 API 调用
4. Prompt 中标注数据时效性，引导 LLM 合理使用

提示：
- 在 metadata 中存储 timestamp 和 freshness 字段
- 实现后台定时清理任务
- 时效性判断可以结合查询意图识别
```

---

## 本章小结

| 主题 | 关键要点 |
|------|---------|
| 实时挑战 | 静态知识库存在信息滞后，需要按数据时效性分类管理 |
| Function Calling | LLM 通过工具调用获取实时数据，支持并行调用降低延迟 |
| Tool Use 模式 | ReAct Agent、Router Agent、Plan-and-Execute 三种模式 |
| 流式更新 | 基于消息队列的增量索引更新，支持去重和过期清理 |
| CDC 集成 | Debezium + Kafka 捕获数据库变更，实时同步到知识库 |
| 时效性管理 | 文档标注新鲜度级别，检索时自动过滤过期数据 |
| 混合架构 | 在线-近线-离线三层架构，按数据热度分层存储和检索 |

---

*上一篇：[08-消除幻觉与质量提升](08-eliminate-hallucination.md)*

*下一篇：[10-Token 节省策略](10-token-optimization.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Nakano, R., et al. (2021).** *WebGPT: Browser-assisted question-answering with human feedback.* — LLM 实时信息获取  
   https://arxiv.org/abs/2112.09332

2. **Schick, T., et al. (2023).** *Toolformer: Language Models Can Teach Themselves to Use Tools.*  
   https://arxiv.org/abs/2302.04761

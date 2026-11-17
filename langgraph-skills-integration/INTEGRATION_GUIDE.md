# LangGraph + DeepSeek + Skills 完整集成指南

## 目录

1. [系统概述](#系统概述)
2. [架构设计](#架构设计)
3. [快速开始](#快速开始)
4. [核心组件详解](#核心组件详解)
5. [工作流程](#工作流程)
6. [高级用法](#高级用法)
7. [性能优化](#性能优化)
8. [故障排查](#故障排查)

---

## 系统概述

本系统实现了一个智能的、可扩展的 AI Agent，通过以下方式工作：

1. **动态技能发现** - 自动扫描 Skills 仓库，构建技能索引
2. **智能技能匹配** - 使用 DeepSeek 理解用户意图并选择最合适的技能
3. **渐进式加载** - 按需加载技能内容，优化上下文使用
4. **状态图协调** - LangGraph 管理复杂的多步骤工作流
5. **代码生成执行** - 自动生成并执行解决方案

### 关键特性

✅ **模块化设计** - 每个组件独立且可替换  
✅ **类型安全** - 完整的 TypedDict 状态定义  
✅ **错误恢复** - 内置错误处理和重试机制  
✅ **可扩展性** - 轻松添加新技能和节点  
✅ **可观测性** - 详细的日志和状态跟踪  

---

## 架构设计

### 系统架构图

```
┌─────────────────────────────────────────────────────────────────┐
│                          用户层                                  │
│                     (User Interface)                            │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                     LangGraph 状态图层                           │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐       │
│  │ Discover │─▶│  Select  │─▶│   Load   │─▶│ Analyze  │       │
│  │ Skills   │  │  Skill   │  │  Skill   │  │  Intent  │       │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘       │
│       │             │              │              │             │
│       ▼             ▼              ▼              ▼             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐       │
│  │ Generate │─▶│ Execute  │─▶│  Handle  │─▶│ Finalize │       │
│  │   Code   │  │   Code   │  │  Error   │  │          │       │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘       │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                ┌───────────┴────────────┐
                ▼                        ▼
┌──────────────────────────┐  ┌──────────────────────────┐
│    技能管理层             │  │     LLM 推理层           │
│  • SkillDiscovery        │  │  • DeepSeekLLM          │
│  • SkillLoader           │  │  • Intent Analysis      │
│  • 渐进式加载             │  │  • Code Generation      │
└──────────┬───────────────┘  └──────────┬───────────────┘
           │                              │
           ▼                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Skills 仓库层                               │
│  • pdf/              • slack-gif-creator/                       │
│  • docx/             • skill-creator/                           │
│  • pptx/             • 更多技能...                              │
│    - SKILL.md                                                   │
│    - scripts/                                                   │
│    - references/                                                │
│    - assets/                                                    │
└─────────────────────────────────────────────────────────────────┘
```

### 数据流

```
用户查询 → 技能发现 → 技能选择 → 技能加载 → 意图分析
    ↓
生成代码 ← 上下文构建 ← 参考文档加载 ← 意图分析
    ↓
执行代码 → 获取结果 → 返回用户
    ↓ (如果失败)
错误处理 → 重试或降级
```

---

## 快速开始

### 1. 安装依赖

```bash
cd langgraph-skills-integration
pip install -r requirements.txt
```

### 2. 配置环境

```bash
# 设置 DeepSeek API 密钥
export DEEPSEEK_API_KEY='your-api-key-here'

# (可选) 设置 Skills 路径
export SKILLS_PATH='../path/to/skills'
```

或创建 `.env` 文件：

```env
DEEPSEEK_API_KEY=your-api-key-here
SKILLS_PATH=../
LOG_LEVEL=INFO
```

### 3. 运行示例

```python
from langgraph_agent import SkillAgent

# 初始化 Agent
agent = SkillAgent(
    skills_path="../",
    deepseek_api_key="your-api-key"
)

# 执行任务
result = agent.run("帮我合并两个 PDF 文件")
print(result)
```

### 4. 运行完整示例

```bash
python example_usage.py
```

---

## 核心组件详解

### 1. SkillDiscovery (技能发现器)

**职责**: 扫描 Skills 仓库，构建技能索引

**关键方法**:
- `discover_all_skills()` - 发现所有技能
- `search_skills(query)` - 搜索技能
- `get_skills_summary()` - 获取技能摘要

**使用示例**:
```python
from skill_discovery import SkillDiscovery

discovery = SkillDiscovery("../")
skills = discovery.discover_all_skills()
print(f"发现 {len(skills)} 个技能")
```

### 2. SkillLoader (技能加载器)

**职责**: 按需加载技能内容和资源

**关键方法**:
- `load_skill(metadata)` - 加载完整技能
- `load_reference(skill_name, ref_name)` - 加载参考文档
- `format_skill_context(skill_content)` - 格式化上下文

**特性**:
- ✅ 缓存机制
- ✅ 渐进式加载
- ✅ 资源索引

**使用示例**:
```python
from skill_loader import SkillLoader

loader = SkillLoader("../")
skill_content = loader.load_skill(skill_metadata)
context = loader.format_skill_context(skill_content)
```

### 3. DeepSeekLLM (LLM 集成)

**职责**: 处理所有 LLM 推理任务

**关键方法**:
- `select_skill(query, skills)` - 选择技能
- `understand_intent(query, context)` - 理解意图
- `generate_code(task, context)` - 生成代码
- `plan_workflow(query, skills)` - 规划工作流

**使用示例**:
```python
from deepseek_integration import DeepSeekLLM

llm = DeepSeekLLM(api_key="your-key")
skill_name = llm.select_skill(user_query, available_skills)
```

### 4. SkillAgent (主 Agent)

**职责**: 协调整个系统，管理状态图

**状态节点**:
1. `discover_skills` - 发现技能
2. `select_skill` - 选择技能
3. `load_skill` - 加载技能
4. `analyze_intent` - 分析意图
5. `generate_code` - 生成代码
6. `execute_code` - 执行代码
7. `handle_error` - 错误处理
8. `finalize` - 完成任务

**使用示例**:
```python
from langgraph_agent import SkillAgent

agent = SkillAgent(
    skills_path="../",
    deepseek_api_key="your-key"
)

result = agent.run("创建一个弹跳的 GIF")
```

---

## 工作流程

### 标准执行流程

```
1. 用户输入查询
   ↓
2. 发现所有可用技能
   ↓
3. LLM 分析查询并选择最合适的技能
   ↓
4. 加载技能内容（SKILL.md + resources）
   ↓
5. LLM 理解具体意图和参数
   ↓
6. 根据需要加载参考文档
   ↓
7. LLM 生成解决方案代码
   ↓
8. 执行代码
   ↓
9. 返回结果或处理错误
```

### 状态转换图

```
START
  │
  ▼
discover_skills
  │
  ▼
select_skill ──────────────┐
  │                         │ (无合适技能)
  │ (找到技能)              │
  ▼                         │
load_skill                  │
  │                         │
  ▼                         │
analyze_intent              │
  │                         │
  ▼                         │
generate_code               │
  │                         │
  ▼                         │
execute_code                │
  │         │               │
  │ (成功)  │ (失败)        │
  │         ▼               │
  │     handle_error        │
  │         │               │
  └─────────┴───────────────┘
            │
            ▼
        finalize
            │
            ▼
          END
```

---

## 高级用法

### 1. 自定义技能选择策略

```python
from deepseek_integration import DeepSeekLLM

class CustomDeepSeekLLM(DeepSeekLLM):
    def select_skill(self, user_query, available_skills):
        # 实现自定义选择逻辑
        # 例如：基于关键词匹配、语义相似度等
        pass
```

### 2. 添加新的状态节点

```python
from langgraph_agent import SkillAgent

class ExtendedSkillAgent(SkillAgent):
    def _build_graph(self):
        workflow = super()._build_graph()
        
        # 添加新节点
        workflow.add_node("validate_output", self._validate_output)
        
        # 修改边
        workflow.add_edge("execute_code", "validate_output")
        workflow.add_edge("validate_output", "finalize")
        
        return workflow
    
    def _validate_output(self, state):
        # 验证输出逻辑
        pass
```

### 3. 实现技能缓存

```python
from skill_loader import SkillLoader
import pickle

class CachedSkillLoader(SkillLoader):
    def __init__(self, *args, cache_file="skill_cache.pkl", **kwargs):
        super().__init__(*args, **kwargs)
        self.cache_file = cache_file
        self._load_cache()
    
    def _load_cache(self):
        try:
            with open(self.cache_file, 'rb') as f:
                self._cache = pickle.load(f)
        except FileNotFoundError:
            pass
    
    def save_cache(self):
        with open(self.cache_file, 'wb') as f:
            pickle.dump(self._cache, f)
```

### 4. 多技能协同

```python
from langgraph_agent import SkillAgent

agent = SkillAgent(skills_path="../", deepseek_api_key="key")

# 规划多步骤任务
workflow = agent.llm.plan_workflow(
    "从 PDF 提取表格，然后创建可视化图表",
    agent.discovery.skills_index
)

# 执行每个步骤
for step in workflow:
    skill_name = step.get('skill_needed')
    if skill_name:
        # 执行特定技能
        pass
```

---

## 性能优化

### 1. 技能索引优化

```python
# 使用索引加速搜索
from skill_discovery import SkillDiscovery

discovery = SkillDiscovery("../")
discovery.discover_all_skills()

# 导出索引供快速加载
index = discovery.export_index()
# 保存到文件...
```

### 2. 上下文大小控制

```python
from skill_loader import SkillLoader

loader = SkillLoader("../")

# 只加载必要的内容
context = loader.format_skill_context(
    skill_content,
    include_references=True,
    reference_names=["essential_docs.md"]  # 只加载特定文档
)
```

### 3. 并行技能发现

```python
from concurrent.futures import ThreadPoolExecutor
from skill_discovery import SkillDiscovery

def discover_in_parallel(skills_root):
    discovery = SkillDiscovery(skills_root)
    
    with ThreadPoolExecutor(max_workers=4) as executor:
        # 并行扫描多个目录
        futures = []
        for subdir in Path(skills_root).iterdir():
            if subdir.is_dir():
                futures.append(
                    executor.submit(discovery._parse_skill_md, ...)
                )
        
        # 收集结果
        for future in futures:
            result = future.result()
```

### 4. LLM 响应缓存

```python
from functools import lru_cache
from deepseek_integration import DeepSeekLLM

class CachedDeepSeekLLM(DeepSeekLLM):
    @lru_cache(maxsize=128)
    def select_skill(self, user_query, skills_tuple):
        # 转换为可哈希类型
        skills_dict = dict(skills_tuple)
        return super().select_skill(user_query, skills_dict)
```

---

## 故障排查

### 常见问题

#### 1. API 密钥错误

**症状**: `错误: Invalid API key`

**解决方案**:
```bash
# 检查环境变量
echo $DEEPSEEK_API_KEY

# 重新设置
export DEEPSEEK_API_KEY='your-correct-key'
```

#### 2. 技能未找到

**症状**: `发现 0 个技能`

**解决方案**:
```python
# 检查路径
from pathlib import Path
skills_path = Path("../")
print(f"路径存在: {skills_path.exists()}")
print(f"包含 SKILL.md 的目录:")
for d in skills_path.iterdir():
    if (d / "SKILL.md").exists():
        print(f"  - {d.name}")
```

#### 3. 代码执行失败

**症状**: `执行错误: ModuleNotFoundError`

**解决方案**:
```bash
# 安装缺失的依赖
pip install <missing-module>

# 或禁用代码执行
agent = SkillAgent(...)
agent.agent.enable_code_execution = False
```

#### 4. 上下文太大

**症状**: `Token limit exceeded`

**解决方案**:
```python
# 限制上下文大小
context = loader.format_skill_context(skill_content)
if len(context) > 5000:
    # 只使用前半部分
    context = context[:5000] + "..."
```

### 调试技巧

#### 1. 启用详细日志

```python
import logging
logging.basicConfig(level=logging.DEBUG)
```

#### 2. 检查状态

```python
# 在状态图的每个节点后打印状态
def debug_state(state):
    print(f"\n当前状态:")
    print(f"  选中技能: {state.get('selected_skill')}")
    print(f"  意图: {state.get('intent_analysis')}")
    print(f"  错误: {state.get('error')}")
    return state
```

#### 3. 测试单个组件

```python
# 单独测试技能发现
from skill_discovery import SkillDiscovery
discovery = SkillDiscovery("../")
skills = discovery.discover_all_skills()
print(f"发现技能: {list(skills.keys())}")

# 单独测试 LLM
from deepseek_integration import DeepSeekLLM
llm = DeepSeekLLM(api_key="key")
response = llm.chat([{"role": "user", "content": "测试"}])
print(response)
```

---

## 总结

本集成方案提供了一个完整的、生产就绪的框架，用于：

✅ **动态技能管理** - 自动发现和加载技能  
✅ **智能推理** - DeepSeek 驱动的意图理解和代码生成  
✅ **状态协调** - LangGraph 管理复杂工作流  
✅ **可扩展性** - 轻松添加新技能和功能  
✅ **性能优化** - 缓存、渐进式加载、并行处理  

### 下一步

1. 探索和创建新技能
2. 自定义状态图节点
3. 优化性能和资源使用
4. 集成到生产环境

### 参考资源

- [Skills 仓库规范](../agent_skills_spec.md)
- [LangGraph 文档](https://langchain-ai.github.io/langgraph/)
- [DeepSeek API 文档](https://platform.deepseek.com/docs)
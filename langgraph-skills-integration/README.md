# LangGraph + DeepSeek Skills 集成方案

## 架构概述

本方案实现了一个基于 LangGraph 状态图的 AI Agent 系统，使用 DeepSeek 作为推理引擎，动态加载和使用 Skills 仓库中的技能。

## 系统架构

```
┌─────────────────────────────────────────────────────────────┐
│                      用户请求                                 │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                   LangGraph 状态图                            │
│  ┌─────────────┐   ┌──────────────┐   ┌─────────────────┐  │
│  │  技能发现    │──▶│  意图理解    │──▶│   技能选择      │  │
│  │  (Discover) │   │  (Understand)│   │   (Select)      │  │
│  └─────────────┘   └──────────────┘   └─────────────────┘  │
│         │                  │                    │            │
│         ▼                  ▼                    ▼            │
│  ┌─────────────┐   ┌──────────────┐   ┌─────────────────┐  │
│  │ 技能加载器   │   │ DeepSeek LLM │   │  执行引擎       │  │
│  └─────────────┘   └──────────────┘   └─────────────────┘  │
└─────────────────────────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│                   Skills 仓库                                 │
│  • pdf/           • slack-gif-creator/                       │
│  • docx/          • skill-creator/                           │
│  • canvas-design/ • 更多技能...                              │
└─────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. 技能发现器 (SkillDiscovery)
- 扫描 skills 目录
- 解析 SKILL.md 的 YAML frontmatter
- 构建技能索引

### 2. 技能加载器 (SkillLoader)
- 按需加载 SKILL.md 内容
- 加载关联的 scripts/references/assets
- 提供技能上下文

### 3. LangGraph 状态图
- 管理对话状态
- 协调技能选择和执行
- 处理多步骤工作流

### 4. DeepSeek 集成
- 意图识别和理解
- 技能匹配和推理
- 代码生成和执行

## 安装依赖

```bash
pip install langgraph langchain langchain-community
pip install openai  # DeepSeek API 兼容 OpenAI 格式
pip install pyyaml gitpython
```

## 快速开始

```python
from langgraph_skills import SkillAgent

# 初始化 Agent
agent = SkillAgent(
    skills_path="./skills",
    deepseek_api_key="your-api-key",
    deepseek_base_url="https://api.deepseek.com/v1"
)

# 使用技能
result = agent.run("帮我创建一个 Slack GIF，显示一个弹跳的笑脸")
print(result)
```

## 实现细节

详见以下文件：
- `skill_discovery.py` - 技能发现和索引
- `skill_loader.py` - 技能加载机制
- `langgraph_agent.py` - LangGraph 状态图定义
- `deepseek_integration.py` - DeepSeek LLM 集成
- `example_usage.py` - 使用示例

## 特性

✅ **动态技能发现** - 自动扫描和索引所有技能
✅ **智能技能匹配** - 基于语义理解选择合适技能
✅ **渐进式加载** - 优化上下文使用
✅ **多步骤工作流** - 支持复杂任务分解
✅ **工具执行** - 自动执行 scripts/ 中的脚本
✅ **状态管理** - 保持对话和任务上下文
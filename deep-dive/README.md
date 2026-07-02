# 🔬 Deep Dive Skill for Claude Code

A research-grade search skill for Claude Code that performs multi-source parallel searching, cross-validation, causal analysis, and credibility assessment.

---

## What is Deep Dive?

**Deep Dive** is a specialized skill for Claude Code that transforms ordinary search into comprehensive research.

| Ordinary Search | Deep Dive |
|----------------|-----------|
| Finds information | Validates information + Analyzes causation + Assesses credibility |

When you need: **deep research**, **cross-validation**, **exploring causes**, **assessing credibility**, **multi-source comparison**

---

## Prerequisites - Required MCP Servers

**You must install these MCP servers before using this skill:**

| MCP Server | Description | Installation |
|------------|-------------|--------------|
| **Exa Search** | High-quality semantic search | [exa-labs/exa-mcp-server](https://github.com/exa-labs/exa-mcp-server) |
| **Tavily Search** | Deep web search with advanced crawling | [tavily-ai/tavily-mcp](https://github.com/tavily-ai/tavily-mcp) |
| **DuckDuckGo** | Stable fallback search | [nickclyde/duckduckgo-mcp-server](https://github.com/nickclyde/duckduckgo-mcp-server) |
| **Jina AI** | Web reading, arXiv, blog search, content extraction | [jina-ai/MCP](https://github.com/jina-ai/MCP) |
| **Gemini CLI** | Additional AI-powered search coverage | [jamubc/gemini-mcp-tool](https://github.com/jamubc/gemini-mcp-tool) |

---

## Installation

```bash
# Clone this repository
git clone https://github.com/Rainnystone/deep-dive-skill.git

# Copy to your Claude skills directory
cp -r deep-dive-skill/deep-dive ~/.claude/skills/
```

---

## Architecture

```
Phase 1: Broad Collection (Parallel Execution)
┌─────────────────────────────────────────────────────────────────┐
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ Exa→Tavily→ │  │ Jina        │  │ Gemini      │              │
│  │ DDG         │  │ (Web/arXiv/ │  │ Search      │              │
│  │ (fallback)  │  │ Blog)       │  │             │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
Phase 2: Content Acquisition
┌─────────────────────────────────────────────────────────────────┐
│  - Full article reading via Jina AI for high-value URLs         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
Phase 3: Deep Analysis
┌─────────────────────────────────────────────────────────────────┐
│  1. Information Extraction                                      │
│  2. Cross-Validation                                            │
│  3. Contradiction Detection                                     │
│  4. Logical Verification                                        │
│  5. Source Tracing                                              │
│  6. Causal Deep-Dive (4 levels)                                 │
│  7. Credibility Scoring (0-100)                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
Phase 4: Structured Output
┌─────────────────────────────────────────────────────────────────┐
│  - Executive Summary                                            │
│  - Credibility Overview (High/Medium/Low/Doubtful)              │
│  - Cross-Validated Facts with Source Mapping                    │
│  - Contradictions Analysis                                      │
│  - Causal Inference (4-level deep)                              │
│  - Logical Verification Report                                  │
│  - Source Quality Assessment                                    │
│  - Research Limitations & Recommendations                       │
└─────────────────────────────────────────────────────────────────┘
```

---

## Usage

**Trigger phrases:**
- `/deep-dive <your research query>`
- `/dd <your research query>`
- `/research <your research query>`

**Keywords that auto-trigger:**
- "Deep research on..."
- "Help me double check..."
- "Cross validate..."
- "Is this information reliable?"
- "Why did this happen? What is the motivation?"
- "Compare multiple sources..."
- "How credible is this?"

---

---

## Deep Dive 是什么？

**Deep Dive** 是一个专为 Claude Code 设计的深度研究级搜索 skill。

| 普通搜索 | Deep Dive |
|---------|-----------|
| 找到信息 | 验证信息 + 分析因果 + 评估可信度 |

当你需要：**深度研究**、**交叉验证**、**探求原因**、**评估可信度**、**多源对比** 时

---

## 必需依赖 - MCP 服务器

**使用此 skill 前必须安装以下 MCP 服务器：**

| MCP 服务器 | 功能 | 安装地址 |
|------------|------|----------|
| **Exa Search** | 高质量语义搜索 | [exa-labs/exa-mcp-server](https://github.com/exa-labs/exa-mcp-server) |
| **Tavily Search** | 深度网络搜索 | [tavily-ai/tavily-mcp](https://github.com/tavily-ai/tavily-mcp) |
| **DuckDuckGo** | 稳定的保底搜索 | [nickclyde/duckduckgo-mcp-server](https://github.com/nickclyde/duckduckgo-mcp-server) |
| **Jina AI** | 网页读取、arXiv、博客搜索 | [jina-ai/MCP](https://github.com/jina-ai/MCP) |
| **Gemini CLI** | AI 辅助搜索覆盖 | [jamubc/gemini-mcp-tool](https://github.com/jamubc/gemini-mcp-tool) |

---

## 安装方式

```bash
# 克隆此仓库
git clone https://github.com/Rainnystone/deep-dive-skill.git

# 复制到 Claude skills 目录
cp -r deep-dive-skill/deep-dive ~/.claude/skills/
```

---

## 架构图

```
第一阶段：广泛采集（并行执行）
┌─────────────────────────────────────────────────────────────────┐
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ Exa→Tavily→ │  │ Jina        │  │ Gemini      │              │
│  │ DDG         │  │ (网页/arXiv/│  │ 搜索        │              │
│  │ (降级备用)  │  │ 博客)       │  │             │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
第二阶段：内容获取
┌─────────────────────────────────────────────────────────────────┐
│  - 通过 Jina AI 深度读取高价值 URL 的完整内容                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
第三阶段：深度分析
┌─────────────────────────────────────────────────────────────────┐
│  1. 信息抽取                                                    │
│  2. 交叉验证                                                    │
│  3. 矛盾检测                                                    │
│  4. 逻辑验证                                                    │
│  5. 溯源分析                                                    │
│  6. 因果深挖（4层）                                             │
│  7. 可信度评分（0-100）                                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
第四阶段：结构化输出
┌─────────────────────────────────────────────────────────────────┐
│  - 执行摘要                                                     │
│  - 可信度总览（高/中/低/存疑）                                  │
│  - 交叉验证的事实及来源映射                                     │
│  - 矛盾点分析                                                   │
│  - 因果推断（4层深度）                                          │
│  - 逻辑验证报告                                                 │
│  - 来源质量评估                                                 │
│  - 研究局限性与建议                                             │
└─────────────────────────────────────────────────────────────────┘
```

---

## 使用说明

**触发命令：**
- `/deep-dive <研究主题>`
- `/dd <研究主题>`
- `/research <研究主题>`

**自动触发关键词：**
- "深度研究..."
- "帮我 double check..."
- "交叉验证..."
- "这个信息可靠吗？"
- "为什么会这样？背后的原因是？"
- "多方对比一下..."

---

## License

MIT License

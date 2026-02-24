---
name: mcp-builder
description: 构建高质量 MCP（Model Context Protocol）服务器的指南，使 LLM 能够通过精心设计的工具与外部服务交互。在使用 Python（FastMCP）或 Node/TypeScript（MCP SDK）构建 MCP 服务器以集成外部 API 或服务时使用此技能。
license: Complete terms in LICENSE.txt
---

# MCP 服务器开发指南

## 概述

创建 MCP（Model Context Protocol）服务器，使 LLM 能够通过精心设计的工具与外部服务交互。MCP 服务器的质量取决于它能多好地帮助 LLM 完成实际任务。

---

# 流程

## 🚀 高层工作流程

创建一个高质量的 MCP 服务器包含四个主要阶段：

### 第一阶段：深入调研与规划

#### 1.1 理解现代 MCP 设计

**API 覆盖与工作流工具：**
在全面的 API 端点覆盖和专用工作流工具之间取得平衡。工作流工具在特定任务上更便捷，而全面覆盖则赋予智能体灵活组合操作的能力。不同客户端的表现各异——有些客户端受益于能组合基础工具的代码执行，而另一些则更适合使用高级工作流。不确定时，优先考虑全面的 API 覆盖。

**工具命名与可发现性：**
清晰、描述性的工具名称有助于智能体快速找到正确的工具。使用一致的前缀（例如 `github_create_issue`、`github_list_repos`）和面向操作的命名方式。

**上下文管理：**
智能体受益于简洁的工具描述以及过滤/分页结果的能力。设计返回聚焦、相关数据的工具。某些客户端支持代码执行，有助于智能体高效地过滤和处理数据。

**可操作的错误信息：**
错误信息应引导智能体找到解决方案，提供具体的建议和后续步骤。

#### 1.2 学习 MCP 协议文档

**浏览 MCP 规范：**

从站点地图开始查找相关页面：`https://modelcontextprotocol.io/sitemap.xml`

然后获取特定页面，添加 `.md` 后缀可获得 Markdown 格式（例如 `https://modelcontextprotocol.io/specification/draft.md`）。

需要查看的关键页面：
- 规范概述和架构
- 传输机制（Streamable HTTP、stdio）
- 工具、资源和提示词定义

#### 1.3 学习框架文档

**推荐技术栈：**
- **语言**：TypeScript（优质的 SDK 支持，在多种执行环境中兼容性好，如 MCPB。加之 AI 模型擅长生成 TypeScript 代码，得益于其广泛使用、静态类型和良好的 lint 工具）
- **传输方式**：远程服务器使用 Streamable HTTP，采用无状态 JSON（更易扩展和维护，相比有状态会话和流式响应）。本地服务器使用 stdio。

**加载框架文档：**

- **MCP 最佳实践**：[📋 查看最佳实践](./reference/mcp_best_practices.md) — 核心指南

**TypeScript（推荐）：**
- **TypeScript SDK**：使用 WebFetch 加载 `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md`
- [⚡ TypeScript 指南](./reference/node_mcp_server.md) — TypeScript 模式与示例

**Python：**
- **Python SDK**：使用 WebFetch 加载 `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md`
- [🐍 Python 指南](./reference/python_mcp_server.md) — Python 模式与示例

#### 1.4 规划实现方案

**理解 API：**
查阅服务的 API 文档，识别关键端点、认证要求和数据模型。根据需要使用 Web 搜索和 WebFetch。

**工具选择：**
优先考虑全面的 API 覆盖。列出需要实现的端点，从最常用的操作开始。

---

### 第二阶段：实现

#### 2.1 搭建项目结构

参见各语言专用指南了解项目搭建：
- [⚡ TypeScript 指南](./reference/node_mcp_server.md) — 项目结构、package.json、tsconfig.json
- [🐍 Python 指南](./reference/python_mcp_server.md) — 模块组织、依赖管理

#### 2.2 实现核心基础设施

创建共享工具：
- 带认证的 API 客户端
- 错误处理辅助函数
- 响应格式化（JSON/Markdown）
- 分页支持

#### 2.3 实现工具

对于每个工具：

**输入模式：**
- 使用 Zod（TypeScript）或 Pydantic（Python）
- 包含约束条件和清晰的描述
- 在字段描述中添加示例

**输出模式：**
- 尽可能定义 `outputSchema` 以获得结构化数据
- 在工具响应中使用 `structuredContent`（TypeScript SDK 功能）
- 帮助客户端理解和处理工具输出

**工具描述：**
- 功能的简明摘要
- 参数描述
- 返回类型模式

**实现：**
- I/O 操作使用 async/await
- 提供可操作信息的正确错误处理
- 在适用场景支持分页
- 使用现代 SDK 时同时返回文本内容和结构化数据

**注解：**
- `readOnlyHint`：true/false
- `destructiveHint`：true/false
- `idempotentHint`：true/false
- `openWorldHint`：true/false

---

### 第三阶段：审查与测试

#### 3.1 代码质量

审查以下方面：
- 无重复代码（DRY 原则）
- 一致的错误处理
- 完整的类型覆盖
- 清晰的工具描述

#### 3.2 构建与测试

**TypeScript：**
- 运行 `npm run build` 验证编译
- 使用 MCP Inspector 测试：`npx @modelcontextprotocol/inspector`

**Python：**
- 验证语法：`python -m py_compile your_server.py`
- 使用 MCP Inspector 测试

参见各语言专用指南了解详细的测试方法和质量检查清单。

---

### 第四阶段：创建评估

实现 MCP 服务器后，创建全面的评估来测试其效果。

**加载 [✅ 评估指南](./reference/evaluation.md) 获取完整的评估指导。**

#### 4.1 理解评估目的

使用评估来测试 LLM 能否有效地使用你的 MCP 服务器回答真实、复杂的问题。

#### 4.2 创建 10 个评估问题

要创建有效的评估，请遵循评估指南中概述的流程：

1. **工具检查**：列出可用工具并理解其能力
2. **内容探索**：使用只读操作探索可用数据
3. **问题生成**：创建 10 个复杂、真实的问题
4. **答案验证**：亲自解答每个问题以验证答案

#### 4.3 评估要求

确保每个问题满足以下条件：
- **独立性**：不依赖于其他问题
- **只读性**：仅需非破坏性操作
- **复杂性**：需要多次工具调用和深入探索
- **真实性**：基于人类真正关心的实际使用场景
- **可验证性**：有唯一、明确的答案，可通过字符串比较验证
- **稳定性**：答案不会随时间变化

#### 4.4 输出格式

创建如下结构的 XML 文件：

```xml
<evaluation>
  <qa_pair>
    <question>Find discussions about AI model launches with animal codenames. One model needed a specific safety designation that uses the format ASL-X. What number X was being determined for the model named after a spotted wild cat?</question>
    <answer>3</answer>
  </qa_pair>
<!-- 更多 qa_pair... -->
</evaluation>
```

---

# 参考文件

## 📚 文档库

在开发过程中根据需要加载以下资源：

### 核心 MCP 文档（优先加载）
- **MCP 协议**：从 `https://modelcontextprotocol.io/sitemap.xml` 的站点地图开始，然后添加 `.md` 后缀获取特定页面
- [📋 MCP 最佳实践](./reference/mcp_best_practices.md) — 通用 MCP 指南，包括：
  - 服务器和工具命名规范
  - 响应格式指南（JSON vs Markdown）
  - 分页最佳实践
  - 传输方式选择（Streamable HTTP vs stdio）
  - 安全和错误处理标准

### SDK 文档（在第一/二阶段加载）
- **Python SDK**：从 `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md` 获取
- **TypeScript SDK**：从 `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md` 获取

### 各语言实现指南（在第二阶段加载）
- [🐍 Python 实现指南](./reference/python_mcp_server.md) — 完整的 Python/FastMCP 指南，包括：
  - 服务器初始化模式
  - Pydantic 模型示例
  - 使用 `@mcp.tool` 注册工具
  - 完整的工作示例
  - 质量检查清单

- [⚡ TypeScript 实现指南](./reference/node_mcp_server.md) — 完整的 TypeScript 指南，包括：
  - 项目结构
  - Zod 模式定义
  - 使用 `server.registerTool` 注册工具
  - 完整的工作示例
  - 质量检查清单

### 评估指南（在第四阶段加载）
- [✅ 评估指南](./reference/evaluation.md) — 完整的评估创建指南，包括：
  - 问题创建指导
  - 答案验证策略
  - XML 格式规范
  - 示例问题与答案
  - 使用提供的脚本运行评估

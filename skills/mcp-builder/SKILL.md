---
name: mcp-builder
description: 创建高质量的 MCP（模型上下文协议）服务器的指南，使 LLM 能够通过精心设计的工具与外部服务交互。在构建 MCP 服务器以集成外部 API 或服务时使用，无论是 Python (FastMCP) 还是 Node/TypeScript (MCP SDK)。
license: 完整条款见 LICENSE.txt
---

# MCP 服务器开发指南

## 概述

创建 MCP（模型上下文协议）服务器，使 LLM 能够通过精心设计的工具与外部服务交互。MCP 服务器的质量取决于它如何使 LLM 能够完成现实世界的任务。

---

# 流程

## 🚀 高级工作流程

创建高质量的 MCP 服务器涉及四个主要阶段：

### 第 1 阶段：深入研究和规划

#### 1.1 了解现代 MCP 设计

**API 覆盖范围与工作流工具：**
在全面的 API 端点覆盖与专门的工作流工具之间取得平衡。工作流工具对于特定任务可能更方便，而全面覆盖使代理能够灵活地组合操作。性能因客户端而异——一些客户端从组合基本工具的代码执行中受益，而其他客户端更适合更高级别的工作流。当不确定时，优先考虑全面的 API 覆盖。

**工具命名和可发现性：**
清晰、描述性的工具名称有助于代理快速找到正确的工具。使用一致的前缀（例如，`github_create_issue`、`github_list_repos`）和面向操作的命名。

**上下文管理：**
代理从简洁的工具描述和过滤/分页结果的能力中受益。设计返回聚焦、相关数据的工具。一些客户端支持代码执行，可以帮助代理高效地过滤和处理数据。

**可操作的错误消息：**
错误消息应通过具体建议和下一步骤引导代理找到解决方案。

#### 1.2 研究 MCP 协议文档

**导航 MCP 规范：**

从站点地图开始以找到相关页面：`https://modelcontextprotocol.io/sitemap.xml`

然后使用 `.md` 后缀获取特定页面的 markdown 格式（例如，`https://modelcontextprotocol.io/specification/draft.md`）。

要查看的关键页面：
- 规范概述和架构
- 传输机制（可流式 HTTP、stdio）
- 工具、资源和提示定义

#### 1.3 研究框架文档

**推荐堆栈：**
- **语言**：TypeScript（高质量的 SDK 支持和良好的兼容性，例如 MCPB。此外 AI 模型擅长生成 TypeScript 代码，受益于其广泛的使用、静态类型和良好的 linting 工具）
- **传输**：可流式 HTTP 用于远程服务器，使用无状态 JSON（更易于扩展和维护，而不是有状态会话和流式响应）。stdio 用于本地服务器。

**加载框架文档：**

- **MCP 最佳实践**：[📋 查看最佳实践](./reference/mcp_best_practices.md) - 核心指南

**对于 TypeScript（推荐）：**
- **TypeScript SDK**：使用 WebFetch 加载 `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md`
- [⚡ TypeScript 指南](./reference/node_mcp_server.md) - TypeScript 模式和示例

**对于 Python：**
- **Python SDK**：使用 WebFetch 加载 `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md`
- [🐍 Python 指南](./reference/python_mcp_server.md) - Python 模式和示例

#### 1.4 规划您的实现

**了解 API：**
审查服务的 API 文档以识别关键端点、身份验证要求和数据模型。根据需要使用网络搜索和 WebFetch。

**工具选择：**
优先考虑全面的 API 覆盖。列出要实现的端点，从最常见的操作开始。

---

### 第 2 阶段：实现

#### 2.1 设置项目结构

请参阅特定语言的指南以进行项目设置：
- [⚡ TypeScript 指南](./reference/node_mcp_server.md) - 项目结构、package.json、tsconfig.json
- [🐍 Python 指南](./reference/python_mcp_server.md) - 模块组织、依赖关系

#### 2.2 实现核心基础设施

创建共享实用程序：
- 带有身份验证的 API 客户端
- 错误处理帮助程序
- 响应格式化（JSON/Markdown）
- 分页支持

#### 2.3 实现工具

对于每个工具：

**输入架构：**
- 使用 Zod (TypeScript) 或 Pydantic (Python)
- 包括约束和清晰的描述
- 在字段描述中添加示例

**输出架构：**
- 尽可能定义 `outputSchema` 以获取结构化数据
- 在工具响应中使用 `structuredContent`（TypeScript SDK 功能）
- 帮助客户端理解和处理工具输出

**工具描述：**
- 功能的简洁摘要
- 参数描述
- 返回类型架构

**实现：**
- 用于 I/O 操作的 async/await
- 具有可操作消息的适当错误处理
- 在适用的地方支持分页
- 使用现代 SDK 时返回文本内容和结构化数据

**注释：**
- `readOnlyHint`：true/false
- `destructiveHint`：true/false
- `idempotentHint`：true/false
- `openWorldHint`：true/false

---

### 第 3 阶段：审查和测试

#### 3.1 代码质量

审查：
- 没有重复的代码（DRY 原则）
- 一致的错误处理
- 完整的类型覆盖
- 清晰的工具描述

#### 3.2 构建和测试

**TypeScript：**
- 运行 `npm run build` 以验证编译
- 使用 MCP Inspector 测试：`npx @modelcontextprotocol/inspector`

**Python：**
- 验证语法：`python -m py_compile your_server.py`
- 使用 MCP Inspector 测试

请参阅特定语言的指南以获取详细的测试方法和质量检查清单。

---

### 第 4 阶段：创建评估

在实现 MCP 服务器后，创建综合评估以测试其有效性。

**加载 [✅ 评估指南](./reference/evaluation.md) 以获取完整的评估指南。**

#### 4.1 了解评估目的

使用评估来测试 LLM 是否可以有效地使用您的 MCP 服务器来回答现实的、复杂的问题。

#### 4.2 创建 10 个评估问题

要创建有效的评估，请遵循评估指南中概述的流程：

1. **工具检查**：列出可用工具并了解其功能
2. **内容探索**：使用只读操作来探索可用数据
3. **问题生成**：创建 10 个复杂的、现实的问题
4. **答案验证**：自己解决每个问题以验证答案

#### 4.3 评估要求

确保每个问题是：
- **独立的**：不依赖于其他问题
- **只读的**：仅需要非破坏性操作
- **复杂的**：需要多个工具调用和深入探索
- **现实的**：基于人类会关心的真实用例
- **可验证的**：可以通过字符串比较验证的单一、清晰的答案
- **稳定的**：答案不会随时间变化

#### 4.4 输出格式

使用此结构创建 XML 文件：

```xml
<evaluation>
  <qa_pair>
    <question>查找关于具有动物代号的 AI 模型发布的讨论。一个模型需要使用 ASL-X 格式的特定安全指定。以斑纹野生猫命名的模型正在确定的数字 X 是多少？</question>
    <answer>3</answer>
  </qa_pair>
<!-- 更多 qa_pairs... -->
</evaluation>
```

---

# 参考文件

## 📚 文档库

在开发期间根据需要加载这些资源：

### 核心 MCP 文档（首先加载）
- **MCP 协议**：从站点地图 `https://modelcontextprotocol.io/sitemap.xml` 开始，然后使用 `.md` 后缀获取特定页面
- [📋 MCP 最佳实践](./reference/mcp_best_practices.md) - 通用 MCP 指南，包括：
  - 服务器和工具命名约定
  - 响应格式指南（JSON 与 Markdown）
  - 分页最佳实践
  - 传输选择（可流式 HTTP 与 stdio）
  - 安全和错误处理标准

### SDK 文档（在第 1/2 阶段加载）
- **Python SDK**：从 `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md` 获取
- **TypeScript SDK**：从 `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md` 获取

### 特定语言的实现指南（在第 2 阶段加载）
- [🐍 Python 实现指南](./reference/python_mcp_server.md) - 完整的 Python/FastMCP 指南，包括：
  - 服务器初始化模式
  - Pydantic 模型示例
  - 使用 `@mcp.tool` 进行工具注册
  - 完整的工作示例
  - 质量检查清单

- [⚡ TypeScript 实现指南](./reference/node_mcp_server.md) - 完整的 TypeScript 指南，包括：
  - 项目结构
  - Zod 架构模式
  - 使用 `server.registerTool` 进行工具注册
  - 完整的工作示例
  - 质量检查清单

### 评估指南（在第 4 阶段加载）
- [✅ 评估指南](./reference/evaluation.md) - 完整的评估创建指南，包括：
  - 问题创建指南
  - 答案验证策略
  - XML 格式规范
  - 示例问题和答案
  - 使用提供的脚本运行评估

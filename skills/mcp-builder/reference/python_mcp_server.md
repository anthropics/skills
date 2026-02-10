# Python MCP 服务器实现指南

## 概述

本文档提供了使用 MCP Python SDK 实现 MCP 服务器的 Python 特定最佳实践和示例。它涵盖服务器设置、工具注册模式、使用 Pydantic 进行输入验证、错误处理和完整的工作示例。

---

## 快速参考

### 关键导入
```python
from mcp.server.fastmcp import FastMCP
from pydantic import BaseModel, Field, field_validator, ConfigDict
from typing import Optional, List, Dict, Any
from enum import Enum
import httpx
```

### 服务器初始化
```python
mcp = FastMCP("service_mcp")
```

### 工具注册模式
```python
@mcp.tool(name="tool_name", annotations={...})
async def tool_function(params: InputModel) -> str:
    # 实现
    pass
```

---

## MCP Python SDK 和 FastMCP

官方 MCP Python SDK 提供 FastMCP，这是一个用于构建 MCP 服务器的高级框架。它提供：
- 从函数签名和文档字符串自动生成描述和 inputSchema
- 用于输入验证的 Pydantic 模型集成
- 使用 `@mcp.tool` 进行基于装饰器的工具注册

**有关完整的 SDK 文档，请使用 WebFetch 加载：**
`https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md`

## 服务器命名约定

Python MCP 服务器必须遵循此命名模式：
- **格式**：`{service}_mcp`（小写带下划线）
- **示例**：`github_mcp`、`jira_mcp`、`stripe_mcp`

名称应该是：
- 通用的（不绑定到特定功能）
- 描述集成的服务/API
- 易于从任务描述推断
- 没有版本号或日期

## 工具实现

### 工具命名

对工具名称使用 snake_case（例如，"search_users"、"create_project"、"get_channel_info"），使用清晰、以行动为导向的名称。

**避免命名冲突**：包括服务上下文以防止重叠：
- 使用 "slack_send_message" 而不仅仅是 "send_message"
- 使用 "github_create_issue" 而不仅仅是 "create_issue"
- 使用 "asana_list_tasks" 而不仅仅是 "list_tasks"

### 使用 FastMCP 的工具结构

使用 `@mcp.tool` 装饰器和用于输入验证的 Pydantic 模型定义工具：

```python
from pydantic import BaseModel, Field, ConfigDict
from mcp.server.fastmcp import FastMCP

# 初始化 MCP 服务器
mcp = FastMCP("example_mcp")

# 定义用于输入验证的 Pydantic 模型
class ServiceToolInput(BaseModel):
    '''服务工具操作的输入模型。'''
    model_config = ConfigDict(
        str_strip_whitespace=True,  # 自动从字符串中去除空格
        validate_assignment=True,    # 在赋值时验证
        extra='forbid'              # 禁止额外字段
    )

    param1: str = Field(..., description="第一个参数描述（例如，'user123'，'project-abc'）", min_length=1, max_length=100)
    param2: Optional[int] = Field(default=None, description="带有约束的可选整数参数", ge=0, le=1000)
    tags: Optional[List[str]] = Field(default_factory=list, description="要应用的标签列表", max_items=10)

@mcp.tool(
    name="service_tool_name",
    annotations={
        "title": "人类可读的工具标题",
        "readOnlyHint": True,     # 工具不修改环境
        "destructiveHint": False,  # 工具不执行破坏性操作
        "idempotentHint": True,    # 重复调用没有额外效果
        "openWorldHint": False     # 工具不与外部实体交互
    }
)
async def service_tool_name(params: ServiceToolInput) -> str:
    '''工具描述自动成为 'description' 字段。

    此工具对服务执行特定操作。它在处理之前使用 ServiceToolInput Pydantic 模型
    验证所有输入。

    参数：
        params (ServiceToolInput)：验证的输入参数，包含：
            - param1 (str)：第一个参数描述
            - param2 (Optional[int])：带有默认的可选参数
            - tags (Optional[List[str]])：标签列表

    返回：
        str：包含操作结果的 JSON 格式响应
    '''
    # 实现在这里
    pass
```

## Pydantic v2 关键功能

- 使用 `model_config` 代替嵌套的 `Config` 类
- 使用 `field_validator` 代替已弃用的 `validator`
- 使用 `model_dump()` 代替已弃用的 `dict()`
- 验证器需要 `@classmethod` 装饰器
- 验证器方法需要类型提示

```python
from pydantic import BaseModel, Field, field_validator, ConfigDict

class CreateUserInput(BaseModel):
    model_config = ConfigDict(
        str_strip_whitespace=True,
        validate_assignment=True
    )

    name: str = Field(..., description="用户的全名", min_length=1, max_length=100)
    email: str = Field(..., description="用户的电子邮件地址", pattern=r'^[\w\.-]+@[\w\.-]+\.\w+$')
    age: int = Field(..., description="用户的年龄", ge=0, le=150)

    @field_validator('email')
    @classmethod
    def validate_email(cls, v: str) -> str:
        if not v.strip():
            raise ValueError("电子邮件不能为空")
        return v.lower()
```

## 响应格式选项

支持多种输出格式以提高灵活性：

```python
from enum import Enum

class ResponseFormat(str, Enum):
    '''工具响应的输出格式。'''
    MARKDOWN = "markdown"
    JSON = "json"

class UserSearchInput(BaseModel):
    query: str = Field(..., description="搜索查询")
    response_format: ResponseFormat = Field(
        default=ResponseFormat.MARKDOWN,
        description="输出格式：'markdown' 表示人类可读或 'json' 表示机器可读"
    )
```

**Markdown 格式**：
- 使用标题、列表和格式以提高清晰度
- 将时间戳转换为人类可读格式（例如，"2024-01-15 10:30:00 UTC" 而不是 epoch）
- 在括号中显示带 ID 的显示名称（例如，"@john.doe (U123456)"）
- 省略详细的元数据（例如，仅显示一个个人资料图像 URL，而不是所有大小）
- 逻辑地对相关信息进行分组

**JSON 格式**：
- 返回完整的、适合程序化处理的结构化数据
- 包括所有可用字段和元数据
- 使用一致的字段名称和类型

## 分页实现

对于列出资源的工具：

```python
class ListInput(BaseModel):
    limit: Optional[int] = Field(default=20, description="要返回的最大结果数", ge=1, le=100)
    offset: Optional[int] = Field(default=0, description="要跳过的结果数以进行分页", ge=0)

async def list_items(params: ListInput) -> str:
    # 使用分页发出 API 请求
    data = await api_request(limit=params.limit, offset=params.offset)

    # 返回分页信息
    response = {
        "total": data["total"],
        "count": len(data["items"]),
        "offset": params.offset,
        "items": data["items"],
        "has_more": data["total"] > params.offset + len(data["items"]),
        "next_offset": params.offset + len(data["items"]) if data["total"] > params.offset + len(data["items"]) else None
    }
    return json.dumps(response, indent=2)
```

## 错误处理

提供清晰的、可操作的错误消息：

```python
def _handle_api_error(e: Exception) -> str:
    '''所有工具的一致错误格式。'''
    if isinstance(e, httpx.HTTPStatusError):
        if e.response.status_code == 404:
            return "错误：未找到资源。请检查 ID 是否正确。"
        elif e.response.status_code == 403:
            return "错误：权限被拒绝。您没有访问此资源的权限。"
        elif e.response.status_code == 429:
            return "错误：超过速率限制。请等待然后再发出更多请求。"
        return f"错误：API 请求失败，状态为 {e.response.status_code}"
    elif isinstance(e, httpx.TimeoutException):
        return "错误：请求超时。请重试。"
    return f"错误：发生意外错误：{type(e).__name__}"
```

## 共享实用程序

将通用功能提取到可重用函数中：

```python
# 共享 API 请求函数
async def _make_api_request(endpoint: str, method: str = "GET", **kwargs) -> dict:
    '''所有 API 调用的可重用函数。'''
    async with httpx.AsyncClient() as client:
        response = await client.request(
            method,
            f"{API_BASE_URL}/{endpoint}",
            timeout=30.0,
            **kwargs
        )
        response.raise_for_status()
        return response.json()
```

## Async/Await 最佳实践

始终对网络请求和 I/O 操作使用 async/await：

```python
# 好：异步网络请求
async def fetch_data(resource_id: str) -> dict:
    async with httpx.AsyncClient() as client:
        response = await client.get(f"{API_URL}/resource/{resource_id}")
        response.raise_for_status()
        return response.json()

# 坏：同步请求
def fetch_data(resource_id: str) -> dict:
    response = requests.get(f"{API_URL}/resource/{resource_id}")  # 阻塞
    return response.json()
```

## 类型提示

始终使用类型提示：

```python
from typing import Optional, List, Dict, Any

async def get_user(user_id: str) -> Dict[str, Any]:
    data = await fetch_user(user_id)
    return {"id": data["id"], "name": data["name"]}
```

## 工具文档字符串

每个工具都必须具有带有显式类型信息的全面文档字符串：

```python
async def search_users(params: UserSearchInput) -> str:
    '''
    在示例系统中按名称、电子邮件或团队搜索用户。

    此工具在示例平台上的所有用户配置文件中搜索，
    支持部分匹配和各种搜索过滤器。它不
    创建或修改用户，仅搜索现有用户。

    参数：
        params (UserSearchInput)：验证的输入参数，包含：
            - query (str)：搜索字符串以匹配名称/电子邮件（例如，"john"、"@example.com"、"team:marketing"）
            - limit (Optional[int])：要返回的最大结果数，介于 1-100 之间（默认：20）
            - offset (Optional[int])：要跳过的结果数以进行分页（默认：0）

    返回：
        str：包含搜索结果的 JSON 格式字符串，具有以下架构：

        成功响应：
        {
            "total": int,           # 找到的匹配总数
            "count": int,           # 此响应中的结果数
            "offset": int,          # 当前分页偏移量
            "users": [
                {
                    "id": str,      # 用户 ID（例如，"U123456789"）
                    "name": str,    # 全名（例如，"John Doe"）
                    "email": str,   # 电子邮件地址（例如，"john@example.com"）
                    "team": str     # 团队名称（例如，"营销"）- 可选
                }
            ]
        }

        错误响应：
        "错误：<错误消息>" 或 "未找到匹配 '<query>' 的用户"

    示例：
        - 使用时机："查找所有营销团队成员" -> 参数为 query="team:marketing"
        - 使用时机："搜索 John 的账户" -> 参数为 query="john"
        - 不使用时机：您需要创建用户（使用 example_create_user 代替）
        - 不使用时机：您有用户 ID 并需要完整详细信息（使用 example_get_user 代替）

    错误处理：
        - 输入验证错误由 Pydantic 模型处理
        - 如果请求过多，返回"错误：超过速率限制"（429 状态）
        - 如果 API 密钥无效，返回"错误：无效的 API 身份验证"（401 状态）
        - 返回格式化的结果列表或"未找到匹配 'query' 的用户"
    '''
```

## 完整示例

请参阅下面的完整 Python MCP 服务器示例：

```python
#!/usr/bin/env python3
'''
示例服务的 MCP 服务器。

此服务器提供与示例 API 交互的工具，包括用户搜索、
项目管理和数据导出功能。
'''

from typing import Optional, List, Dict, Any
from enum import Enum
import httpx
from pydantic import BaseModel, Field, field_validator, ConfigDict
from mcp.server.fastmcp import FastMCP

# 初始化 MCP 服务器
mcp = FastMCP("example_mcp")

# 常量
API_BASE_URL = "https://api.example.com/v1"

# 枚举
class ResponseFormat(str, Enum):
    '''工具响应的输出格式。'''
    MARKDOWN = "markdown"
    JSON = "json"

# 用于输入验证的 Pydantic 模型
class UserSearchInput(BaseModel):
    '''用户搜索操作的输入模型。'''
    model_config = ConfigDict(
        str_strip_whitespace=True,
        validate_assignment=True
    )

    query: str = Field(..., description="搜索字符串以匹配名称/电子邮件", min_length=2, max_length=200)
    limit: Optional[int] = Field(default=20, description="要返回的最大结果数", ge=1, le=100)
    offset: Optional[int] = Field(default=0, description="要跳过的结果数以进行分页", ge=0)
    response_format: ResponseFormat = Field(default=ResponseFormat.MARKDOWN, description="输出格式")

    @field_validator('query')
    @classmethod
    def validate_query(cls, v: str) -> str:
        if not v.strip():
            raise ValueError("查询不能为空或仅包含空格")
        return v.strip()

# 共享实用程序函数
async def _make_api_request(endpoint: str, method: str = "GET", **kwargs) -> dict:
    '''所有 API 调用的可重用函数。'''
    async with httpx.AsyncClient() as client:
        response = await client.request(
            method,
            f"{API_BASE_URL}/{endpoint}",
            timeout=30.0,
            **kwargs
        )
        response.raise_for_status()
        return response.json()

def _handle_api_error(e: Exception) -> str:
    '''所有工具的一致错误格式。'''
    if isinstance(e, httpx.HTTPStatusError):
        if e.response.status_code == 404:
            return "错误：未找到资源。请检查 ID 是否正确。"
        elif e.response.status_code == 403:
            return "错误：权限被拒绝。您没有访问此资源的权限。"
        elif e.response.status_code == 429:
            return "错误：超过速率限制。请等待然后再发出更多请求。"
        return f"错误：API 请求失败，状态为 {e.response.status_code}"
    elif isinstance(e, httpx.TimeoutException):
        return "错误：请求超时。请重试。"
    return f"错误：发生意外错误：{type(e).__name__}"

# 工具定义
@mcp.tool(
    name="example_search_users",
    annotations={
        "title": "搜索示例用户",
        "readOnlyHint": True,
        "destructiveHint": False,
        "idempotentHint": True,
        "openWorldHint": True
    }
)
async def example_search_users(params: UserSearchInput) -> str:
    '''在示例系统中按名称、电子邮件或团队搜索用户。

    [完整文档字符串如上所示]
    '''
    try:
        # 使用验证的参数发出 API 请求
        data = await _make_api_request(
            "users/search",
            params={
                "q": params.query,
                "limit": params.limit,
                "offset": params.offset
            }
        )

        users = data.get("users", [])
        total = data.get("total", 0)

        if not users:
            return f"未找到匹配 '{params.query}' 的用户"

        # 根据请求的格式格式化响应
        if params.response_format == ResponseFormat.MARKDOWN:
            lines = [f"# 用户搜索结果：'{params.query}'", ""]
            lines.append(f"找到 {total} 个用户（显示 {len(users)} 个）")
            lines.append("")

            for user in users:
                lines.append(f"## {user['name']} ({user['id']})")
                lines.append(f"- **电子邮件**：{user['email']}")
                if user.get('team'):
                    lines.append(f"- **团队**：{user['team']}")
                lines.append("")

            return "\n".join(lines)

        else:
            # 机器可读的 JSON 格式
            import json
            response = {
                "total": total,
                "count": len(users),
                "offset": params.offset,
                "users": users
            }
            return json.dumps(response, indent=2)

    except Exception as e:
        return _handle_api_error(e)

if __name__ == "__main__":
    mcp.run()
```

---

## 高级 FastMCP 功能

### 上下文参数注入

FastMCP 可以自动将 `Context` 参数注入工具以用于高级功能，如日志记录、进度报告、资源读取和用户交互：

```python
from mcp.server.fastmcp import FastMCP, Context

mcp = FastMCP("example_mcp")

@mcp.tool()
async def advanced_search(query: str, ctx: Context) -> str:
    '''具有上下文访问权限的高级工具，用于日志记录和进度。'''

    # 报告长时间操作的进度
    await ctx.report_progress(0.25, "开始搜索...")

    # 记录信息以进行调试
    await ctx.log_info("处理查询", {"query": query, "timestamp": datetime.now()})

    # 执行搜索
    results = await search_api(query)
    await ctx.report_progress(0.75, "格式化结果...")

    # 访问服务器配置
    server_name = ctx.fastmcp.name

    return format_results(results)

@mcp.tool()
async def interactive_tool(resource_id: str, ctx: Context) -> str:
    '''可以从用户请求额外输入的工具。'''

    # 在需要时请求敏感信息
    api_key = await ctx.elicit(
        prompt="请提供您的 API 密钥：",
        input_type="password"
    )

    # 使用提供的密钥
    return await api_call(resource_id, api_key)
```

**上下文功能：**
- `ctx.report_progress(progress, message)` - 报告长时间操作的进度
- `ctx.log_info(message, data)` / `ctx.log_error()` / `ctx.log_debug()` - 日志记录
- `ctx.elicit(prompt, input_type)` - 从用户请求输入
- `ctx.fastmcp.name` - 访问服务器配置
- `ctx.read_resource(uri)` - 读取 MCP 资源

### 资源注册

将数据作为资源公开以实现高效的基于模板的访问：

```python
@mcp.resource("file://documents/{name}")
async def get_document(name: str) -> str:
    '''将文档公开为 MCP 资源。

    资源对于不需要复杂参数的静态或半静态数据很有用。
    它们使用 URI 模板进行灵活访问。
    '''
    document_path = f"./docs/{name}"
    with open(document_path, "r") as f:
        return f.read()

@mcp.resource("config://settings/{key}")
async def get_setting(key: str, ctx: Context) -> str:
    '''将配置公开为带有上下文的资源。'''
    settings = await load_settings()
    return json.dumps(settings.get(key, {}))
```

**何时使用资源与工具：**
- **资源**：对于具有简单参数（URI 模板）的数据访问
- **工具**：对于带有验证和业务逻辑的复杂操作

### 结构化输出类型

FastMCP 支持除字符串之外的多种返回类型：

```python
from typing import TypedDict
from dataclasses import dataclass
from pydantic import BaseModel

# 用于结构化返回的 TypedDict
class UserData(TypedDict):
    id: str
    name: str
    email: str

@mcp.tool()
async def get_user_typed(user_id: str) -> UserData:
    '''返回结构化数据 - FastMCP 处理序列化。'''
    return {"id": user_id, "name": "John Doe", "email": "john@example.com"}

# 用于复杂验证的 Pydantic 模型
class DetailedUser(BaseModel):
    id: str
    name: str
    email: str
    created_at: datetime
    metadata: Dict[str, Any]

@mcp.tool()
async def get_user_detailed(user_id: str) -> DetailedUser:
    '''返回 Pydantic 模型 - 自动生成架构。'''
    user = await fetch_user(user_id)
    return DetailedUser(**user)
```

### 生命周期管理

初始化跨请求持久化的资源：

```python
from contextlib import asynccontextmanager

@asynccontextmanager
async def app_lifespan():
    '''管理服务器生命周期的资源。'''
    # 初始化连接、加载配置等
    db = await connect_to_database()
    config = load_configuration()

    # 使所有工具可用
    yield {"db": db, "config": config}

    # 关闭时清理
    await db.close()

mcp = FastMCP("example_mcp", lifespan=app_lifespan)

@mcp.tool()
async def query_data(query: str, ctx: Context) -> str:
    '''通过上下文访问生命周期资源。'''
    db = ctx.request_context.lifespan_state["db"]
    results = await db.query(query)
    return format_results(results)
```

### 传输选项

FastMCP 支持两种主要的传输机制：

```python
# stdio 传输（用于本地工具）- 默认
if __name__ == "__main__":
    mcp.run()

# 可流式 HTTP 传输（用于远程服务器）
if __name__ == "__main__":
    mcp.run(transport="streamable_http", port=8000)
```

**传输选择：**
- **stdio**：命令行工具、本地集成、子进程执行
- **可流式 HTTP**：Web 服务、远程访问、多个客户端

---

## 代码最佳实践

### 代码可组合性和可重用性

您的实现必须优先考虑可组合性和代码重用：

1. **提取通用功能**：
   - 为跨多个工具使用的操作创建可重用的辅助函数
   - 为 HTTP 请求构建共享的 API 客户端，而不是重复代码
   - 将错误处理逻辑集中在实用程序函数中
   - 将业务逻辑提取到可以组合的专用函数中
   - 提取共享的 markdown 或 JSON 字段选择和格式化功能

2. **避免重复**：
   - 永远不要在工具之间复制粘贴类似的代码
   - 如果您发现自己两次编写类似的逻辑，请将其提取到函数中
   - 分页、过滤、字段选择和格式化等常见操作应该共享
   - 身份验证/授权逻辑应该集中

### Python 特定最佳实践

1. **使用类型提示**：始终为函数参数和返回值包括类型注释
2. **Pydantic 模型**：为所有输入验证定义清晰的 Pydantic 模型
3. **避免手动验证**：让 Pydantic 使用约束处理输入验证
4. **适当的导入**：对导入进行分组（标准库、第三方、本地）
5. **错误处理**：使用特定的异常类型（httpx.HTTPStatusError，而不是通用 Exception）
6. **异步上下文管理器**：对需要清理的资源使用 `async with`
7. **常量**：在 UPPER_CASE 中定义模块级常量

## 质量检查清单

在最终确定 Python MCP 服务器实现之前，确保：

### 战略设计
- [ ] 工具启用完整的工作流程，而不仅仅是 API 端点包装器
- [ ] 工具名称反映自然的任务细分
- [ ] 响应格式针对代理上下文效率进行优化
- [ ] 在适当的地方使用人类可读的标识符
- [ ] 错误消息引导代理正确使用

### 实现质量
- [ ] 专注的实现：实施了最重要和最有价值的工具
- [ ] 所有工具都有描述性的名称和文档
- [ ] 类似操作的返回类型一致
- [ ] 为所有外部调用实现错误处理
- [ ] 服务器名称遵循格式：`{service}_mcp`
- [ ] 所有网络操作使用 async/await
- [ ] 将通用功能提取到可重用函数中
- [ ] 错误消息清晰、可操作且具有教育意义
- [ ] 输出经过正确验证和格式化

### 工具配置
- [ ] 所有工具在装饰器中实现 'name' 和 'annotations'
- [ ] 注释正确设置（readOnlyHint、destructiveHint、idempotentHint、openWorldHint）
- [ ] 所有工具使用 Pydantic BaseModel 进行输入验证，并带有 Field() 定义
- [ ] 所有 Pydantic 字段具有显式类型和带有约束的描述
- [ ] 所有工具都具有带有显式输入/输出类型的全面文档字符串
- [ ] 文档字符串包括 dict/JSON 返回的完整架构结构
- [ ] Pydantic 模型处理输入验证（不需要手动验证）

### 高级功能（如适用）
- [ ] 使用上下文注入进行日志记录、进度或请求
- [ ] 为适当的数据端点注册了资源
- [ ] 为持久连接实现了生命周期管理
- [ ] 使用了结构化输出类型（TypedDict、Pydantic 模型）
- [ ] 配置了适当的传输（stdio 或可流式 HTTP）

### 代码质量
- [ ] 文件包括适当的导入，包括 Pydantic 导入
- [ ] 在适用的地方正确实现了分页
- [ ] 为可能的大型结果集提供了过滤选项
- [ ] 所有异步函数都使用 `async def` 正确定义
- [ ] HTTP 客户端使用遵循带有适当上下文管理器的异步模式
- [ ] 在整个代码中使用类型提示
- [ ] 在模块级别以 UPPER_CASE 定义常量

### 测试
- [ ] 服务器成功运行：`python your_server.py --help`
- [ ] 所有导入正确解析
- [ ] 示例工具调用按预期工作
- [ ] 错误场景优雅地处理

---
name: swagger-skill
description: 智能 Swagger API 查询和调用工具。通过自然语言指令直接查询接口详情、调用 API，无需繁琐的交互步骤。
metadata:
  clawdbot:
    emoji: "🏔️"
    requires:
      bins: ["node"]
---

## 功能特性

- **一键查询**: 直接查询接口详情，自动解析参数、请求体、响应模式
- **自然语言搜索**: 根据自然语言描述找到匹配的接口（如"保存用户"、"获取数据集列表"），支持 tags 匹配
- **智能接口调用**: 根据自然语言指令自动匹配并调用相应的 API
- **完整信息展示**: 自动获取并展示接口的完整信息（参数、请求体、响应、数据模式定义）
- **文件上传支持**: 支持 multipart/form-data 文件上传
- **分层缓存**: 轻量索引用于列表/搜索，Map 结构 O(1) 详情查找
- **Swagger 2.0 兼容**: 同时支持 OpenAPI 3.0 和 Swagger 2.0 规范
- **灵活认证**: 支持 Token、Cookie 或无需验证的多种认证方式

## 安装

无需手动安装依赖。首次使用时会自动检测并安装所需依赖（axios、form-data），同时自动初始化 package.json（含 `"type": "module"` 配置）。

如需手动安装，可在 skill 目录下执行：

```bash
npm install
```

## 使用方法

### 基础使用

```javascript
import SwaggerAPISkill from './index.js';

const skill = new SwaggerAPISkill();

// 1. 加载 Swagger 规范
await skill.fetchSwaggerSpec('https://api.example.com/swagger.json');

// 2. 获取所有接口
const allAPIs = skill.getAllAPIs();

// 3. 搜索接口
const results = skill.searchAPI('获取用户信息');

// 4. 获取接口详情
const detail = skill.getAPIDetail('/users/{id}', 'GET');

// 5. 调用接口
const response = await skill.callAPI('/users', 'GET', {
  query: { page: 1, limit: 10 }
});

// 6. 通过自然语言指令调用
const result = await skill.callAPIByInstruction('获取所有用户', {
  query: { page: 1 }
});
```

## 认证方法

### 方法 1: 使用 Token 认证

```javascript
import SwaggerAPISkill from './index.js';

const skill = new SwaggerAPISkill();

// 方式 A: 先设置 Token，再加载规范
skill.setAuthToken('your-jwt-token');
await skill.fetchSwaggerSpec('http://localhost:8090/v2/api-docs');

// 方式 B: 在加载规范时直接传入 Token
await skill.fetchSwaggerSpec('http://localhost:8090/v2/api-docs', {
  token: 'your-jwt-token',
  tokenOptions: {
    tokenType: 'Bearer',
    headerName: 'Authorization'
  }
});

// 调用 API（会自动添加认证头）
const result = await skill.callAPI('/sysUser/list', 'POST', {
  body: { pageNum: 1, pageSize: 10 }
});
```

### 方法 2: 使用 Cookie 认证

```javascript
const skill = new SwaggerAPISkill();

// 方式 A: 先设置 Cookie，再加载规范
skill.setAuthCookies({
  token: 'your-token',
  JSESSIONID: 'your-session-id'
});
await skill.fetchSwaggerSpec('http://localhost:8090/v2/api-docs');

// 方式 B: 在加载规范时直接传入 Cookie
await skill.fetchSwaggerSpec('http://localhost:8090/v2/api-docs', {
  cookies: {
    token: 'your-token',
    JSESSIONID: 'your-session-id'
  }
});
```

### 方法 3: 无需认证

```javascript
const skill = new SwaggerAPISkill();

// 直接加载规范
await skill.fetchSwaggerSpec('http://localhost:8090/v2/api-docs');

// 调用 API
const result = await skill.callAPI('/users', 'GET', {
  query: { page: 1, limit: 10 }
});
```

### 方法 4: 使用 CLI 工具（推荐）

```bash
node cli.js
```

交互式 CLI 工具会引导你：
1. 输入 Swagger API 文档 URL
2. 输入认证 Token（可选）
3. 通过菜单选择操作（获取接口列表、搜索、调用等）

## API 文档

### fetchSwaggerSpec(url, options)

获取并加载 Swagger 规范文件。

**参数:**
- `url` (string): Swagger JSON URL 或 API 基础 URL
- `options` (object): 可选配置
  - `token` (string): JWT Token 或其他认证 Token
  - `cookies` (object): Cookie 对象，如 `{ token: 'xxx', JSESSIONID: 'xxx' }`
  - `tokenOptions` (object): Token 选项
    - `tokenType` (string): Token 类型，默认为 'Bearer'
    - `headerName` (string): 请求头名称，默认为 'Authorization'

**返回:**
```javascript
{
  success: boolean,
  apiCount?: number,    // 接口总数
  cached?: boolean,     // 仅缓存命中时返回 true
  error?: string
}
```

### setAuthToken(token, options)

设置认证 Token。

**参数:**
- `token` (string): JWT Token 或其他认证 Token
- `options` (object): 可选配置
  - `tokenType` (string): Token 类型，默认为 'Bearer'
  - `headerName` (string): 请求头名称，默认为 'Authorization'

**返回:**
```javascript
{
  success: boolean,
  message: string
}
```

### setAuthCookies(cookies)

设置认证 Cookie。

**参数:**
- `cookies` (object): Cookie 对象，如 `{ token: 'xxx', JSESSIONID: 'xxx' }`

**返回:**
```javascript
{
  success: boolean,
  message: string
}
```

### clearAuth()

清除认证信息。

**返回:**
```javascript
{
  success: boolean,
  message: string
}
```

### getAllAPIs()

获取所有接口的基本信息。

**返回:**
```javascript
{
  success: boolean,
  total: number,
  apis: Array<{
    path: string,
    method: string,
    summary: string,
    description: string,
    operationId: string,
    tags: string[]
  }>
}
```

### searchAPI(query)

根据自然语言查询搜索接口。支持 summary、description、path、operationId 和 tags 匹配。

**参数:**
- `query` (string): 自然语言查询字符串

**返回:**
```javascript
{
  success: boolean,
  query: string,
  matchCount: number,
  results: Array<{
    path: string,
    method: string,
    summary: string,
    description?: string,  // 仅非空时返回
    score: number
  }>
}
```

### getAPIDetail(path, method)

获取特定接口的详细信息。使用 Map O(1) 查找。

**参数:**
- `path` (string): API 路径，如 `/users/{id}`
- `method` (string): HTTP 方法，如 `GET`, `POST` 等

**返回:**
```javascript
{
  success: boolean,
  detail?: {
    path: string,
    method: string,
    summary: string,
    description: string,
    parameters: Array,
    requestBody: object,
    responses: object,
    tags: Array
  },
  error?: string
}
```

### getFullAPIDetail(path, method)

获取完整的接口详情，包括关联的数据模式定义。兼容 OpenAPI 3.0 和 Swagger 2.0。

**参数:**
- `path` (string): API 路径
- `method` (string): HTTP 方法

**返回:**
```javascript
{
  success: boolean,
  detail?: {
    path: string,
    method: string,
    summary: string,
    description: string,
    parameters: Array,
    requestBody: object,
    responses: object,
    tags: Array,
    relatedSchemas: object,  // 关联的数据模式定义
    schemaCount: number
  },
  error?: string
}
```

### callAPI(path, method, params)

调用 API 接口。支持 JSON 请求和 multipart/form-data 文件上传。

**参数:**
- `path` (string): API 路径
- `method` (string): HTTP 方法
- `params` (object): 请求参数
  - `query` (object): 查询参数
  - `body` (object): 请求体（JSON 或 FormData）
  - `headers` (object): 自定义请求头
  - `isFormData` (boolean): 是否为 FormData（文件上传）

**返回:**
```javascript
{
  success: boolean,
  status?: number,
  data?: any,
  error?: string
}
```

**示例 - JSON 请求:**
```javascript
const response = await skill.callAPI('/api/users', 'POST', {
  body: { name: 'John', email: 'john@example.com' }
});
```

**示例 - 文件上传（使用 FormData）:**
```javascript
import FormData from 'form-data';
import fs from 'fs';

const form = new FormData();
form.append('file', fs.createReadStream('./data.jsonl'));
form.append('name', 'My Dataset');
form.append('type', 'train_data');

const response = await skill.callAPI('/api/datasets/', 'POST', {
  body: form,
  isFormData: true
});
```

### callAPIByInstruction(instruction, params)

根据自然语言指令调用 API。

**参数:**
- `instruction` (string): 自然语言指令
- `params` (object): 请求参数（同 callAPI）

**返回:**
```javascript
{
  success: boolean,
  instruction: string,
  matchedAPI?: {
    path: string,
    method: string,
    summary: string,
    matchScore: number
  },
  result: object,
  error?: string
}
```

### uploadFile(path, formData, query)

文件上传方法，支持 multipart/form-data。

**参数:**
- `path` (string): API 路径
- `formData` (object): 表单数据对象
  - `file`: 文件内容（Buffer）或文件路径（string）
  - 其他字段: 表单字段（自动转换为字符串）
- `query` (object): 查询参数（可选）

**返回:**
```javascript
{
  success: boolean,
  status?: number,
  data?: any,
  error?: string
}
```

**示例:**
```javascript
import SwaggerAPISkill from './index.js';

const skill = new SwaggerAPISkill();
await skill.fetchSwaggerSpec('http://localhost:8000/openapi.json');

// 方式1: 使用文件路径
const result1 = await skill.uploadFile('/api/datasets/', {
  file: './test_dataset.jsonl',
  name: 'AI知识问答对',
  type: 'train_data',
  description: '人工智能相关的问答对数据集'
});

// 方式2: 使用 Buffer
import fs from 'fs';
const fileBuffer = fs.readFileSync('./test_dataset.jsonl');
const result2 = await skill.uploadFile('/api/datasets/', {
  file: fileBuffer,
  name: 'AI知识问答对',
  type: 'train_data',
  description: '人工智能相关的问答对数据集'
});
```

### getSessionId()

获取当前会话ID。

**返回:**
```javascript
string // 唯一的会话ID，格式: session_timestamp_randomId
```

### refreshSession()

刷新会话，清空所有缓存数据。

**返回:**
```javascript
{
  success: boolean,
  message: string
}
```

## 缓存机制

swagger-skill 实现了分层缓存来优化性能和 token 消耗：

1. **轻量索引 (apiIndex)**: 仅存储 path/method/summary/description/operationId/tags，用于 `getAllAPIs()` 和 `searchAPI()`
2. **详情 Map (apiDetailMap)**: `"METHOD /path" → 完整详情`，用于 `getAPIDetail()` 的 O(1) 查找
3. **首次加载**: 调用 `fetchSwaggerSpec()` 时从远程获取规范并构建两层缓存
4. **后续查询**: 所有查询操作直接使用内存缓存，无需重新加载
5. **会话管理**: 调用 `refreshSession()` 可清空缓存

## 支持的 HTTP 方法

- GET
- POST
- PUT
- DELETE
- PATCH
- HEAD
- OPTIONS

## 注意事项

1. 需要网络连接来获取 Swagger 规范和调用 API
2. 某些 API 可能需要身份验证，可通过 `headers` 参数传递认证信息
3. 自然语言搜索基于关键词匹配，支持 summary、description、path、operationId 和 tags
4. 路径参数需要在 `query` 参数中提供
5. **文件上传**:
   - 使用 `uploadFile()` 方法是最简单的方式，支持文件路径或 Buffer
   - 也可以使用 `callAPI()` 方法配合 FormData 对象进行更灵活的控制
   - 文件上传时不需要手动设置 Content-Type，会自动设置为 multipart/form-data
6. 同时兼容 OpenAPI 3.0 (`components.schemas`) 和 Swagger 2.0 (`definitions`)

## 许可证

MIT

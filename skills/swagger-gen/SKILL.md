---
name: swagger-gen
description: Auto-generate Swagger/OpenAPI 3.0 documentation from source code, supporting Express, FastAPI, Gin, Spring Boot, Next.js and more. Use when user asks to generate API documentation.
license: MIT
---

# Skill: Swagger/OpenAPI 文档生成

从项目源代码自动分析并生成 Swagger/OpenAPI 3.0 规范文档。

## 触发条件

当用户请求以下操作时激活：
- "生成 swagger"、"生成 api 文档"、"generate swagger"、"generate openapi"
- "给这个项目加 swagger"、"写 api docs"
- 对现有项目需要 API 文档输出

---

## 执行步骤

### 第一步：检测项目类型和框架

```bash
# 检测语言和框架
for file in package.json pyproject.toml requirements.txt go.mod Cargo.toml pom.xml build.gradle; do
  [ -f "$file" ] && echo "Found: $file"
done

# JS/TS 框架检测
cat package.json 2>/dev/null | grep -E "(express|fastify|koa|hono|nest|next|nuxt|elysia)"

# Python 框架检测
grep -rE "(fastapi|flask|django|tornado|sanic)" requirements.txt pyproject.toml 2>/dev/null

# Go 框架检测
grep -rE "(gin|echo|fiber|chi|mux)" go.mod 2>/dev/null

# Java 框架检测
grep -rE "(spring-boot|spring-web|jersey|jax-rs)" pom.xml build.gradle 2>/dev/null
```

根据检测结果确定：
- 语言 + 框架组合
- 路由定义方式（装饰器/链式/配置文件）
- 现有 swagger/openapi 配置（可能已有部分文档）

### 第二步：扫描 API 路由

根据框架类型，使用不同策略扫描路由：

**Express/Fastify/Hono/Elysia (JS/TS):**
```bash
grep -rEn "app\.(get|post|put|delete|patch)|router\.(get|post|put|delete|patch)" src/ --include="*.ts" --include="*.js" --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=__tests__
```

**Next.js App Router:**
```bash
find src/app/api -name "route.ts" -o -name "route.js" 2>/dev/null
```

**FastAPI (Python):**
```bash
grep -rEn "@app\.(get|post|put|delete|patch)|@router\.(get|post|put|delete|patch)" --include="*.py" --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=__tests__
```

**Gin/Echo/Fiber (Go):**
```bash
grep -rEn "\.GET|\.POST|\.PUT|\.DELETE|\.PATCH|\.Handle|\.Group" --include="*.go" --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=__tests__
```

**Spring Boot (Java):**
```bash
grep -rEn "@GetMapping|@PostMapping|@PutMapping|@DeleteMapping|@RequestMapping" --include="*.java" --exclude-dir=node_modules --exclude-dir=dist --exclude-dir=build --exclude-dir=__tests__
```

### 第三步：分析每个端点

对每个发现的路由，阅读源代码提取：

1. **路径和方法** — `GET /api/users/:id`
2. **请求参数**：
   - Path params（路径参数）
   - Query params（查询参数）
   - Request body（请求体 schema）
   - Headers（自定义 header）
3. **响应格式**：
   - 成功响应的 status code 和 body schema
   - 错误响应（400、401、404、500 等）
4. **认证方式** — Bearer token、API key、Cookie 等
5. **中间件** — 权限校验、rate limiting 等

**提取类型信息的优先级：**
1. TypeScript 类型/接口定义（最可靠）
2. Zod/Joi/Yup 等校验 schema
3. Pydantic model（Python）
4. struct tag（Go）
5. Rust serde 序列化注解（`#[derive(Serialize, Deserialize)]`、`#[serde(rename_all = "camelCase")]` 等）
6. 实际响应代码中的字面量

### 第四步：检查现有文档

```bash
# 查找已有的 swagger/openapi 文件
find . \( -name "swagger.*" -o -name "openapi.*" -o -name "api-docs.*" \) | grep -v node_modules
ls docs/api* doc/api* 2>/dev/null
```

若已有文档，读取并作为基础进行增量更新，而非从零生成。

**增量更新流程：**
1. 解析现有 openapi.yaml，提取已有的所有 operationId 和路径列表
2. 扫描源代码找出新增和已删除的端点（与现有文档对比）
3. **新增端点**：追加到 paths 中，生成完整定义
4. **已删除端点**：不直接移除，标注 `deprecated: true` 保留向后兼容
5. **已有端点**：只更新引用的 schema 定义（如字段类型变化），保留手工修改的 description、example 等内容

### 第五步：生成 OpenAPI 3.0 文档

**OpenAPI 版本选择：**
- **3.0.3（默认）**：广泛支持，工具生态成熟（swagger-ui、redocly、codegen 等均兼容）
- **3.1（可选）**：更好的 JSON Schema 支持（如 `null` 类型），但部分工具兼容性有限，选用前需确认下游工具链支持

生成 YAML 格式的 OpenAPI 规范文件，结构如下：

```yaml
openapi: 3.0.3
info:
  title: <项目名称> API
  description: <从 README 或代码注释提取>
  version: <从 package.json/pyproject.toml 提取，默认 1.0.0>

servers:
  # ⚠️ 请根据项目实际情况确认并修改以下服务器地址
  - url: http://localhost:3000
    description: Development server (按项目实际端口配置)
  - url: https://api.example.com
    description: Production server (按实际域名替换)

paths:
  /api/example:
    get:
      summary: <简明描述>
      description: <详细描述>
      operationId: <唯一操作 ID>
      tags:
        - <按业务模块分组>
      parameters: [...]
      responses:
        '200':
          description: Success
          content:
            application/json:
              schema:
                $ref: '#/components/schemas/ExampleResponse'
        '400':
          description: Bad Request
        '401':
          description: Unauthorized

components:
  schemas:
    ExampleResponse:
      type: object
      properties:
        id:
          type: string
        name:
          type: string
      required:
        - id

  securitySchemes:
    BearerAuth:
      type: http
      scheme: bearer
      bearerFormat: JWT
```

### 第六步：输出文件

默认输出位置（按优先级）：
1. `docs/openapi.yaml` — 若 docs/ 目录已存在
2. `openapi.yaml` — 项目根目录

若用户指定了输出格式（JSON），则输出 `openapi.json`。

### 第七步：验证文档

```bash
# 如果有 bun/node 环境
if command -v bunx &> /dev/null; then
  bunx @apidevtools/swagger-cli validate openapi.yaml 2>&1 || true
  bunx @redocly/cli lint openapi.yaml 2>&1 || true
elif command -v npx &> /dev/null; then
  npx @apidevtools/swagger-cli validate openapi.yaml 2>&1 || true
  npx @redocly/cli lint openapi.yaml 2>&1 || true
else
  echo "⚠️ 无 Node.js 环境，跳过自动验证，请手动检查"
fi
```

若验证失败，修复问题后重新验证。

### 第八步：可选 - 集成 Swagger UI

如果用户需要在线浏览 API 文档，根据框架提供集成方案：

**Express/Fastify:**
```bash
bun add swagger-ui-express
```

**FastAPI:**
FastAPI 自带 `/docs` 和 `/redoc`，只需确保 OpenAPI schema 正确加载。

**Next.js:**
建议使用 `next-swagger-doc` 或在 `/api-docs` 路由中嵌入 Swagger UI。

**Spring Boot:**
```bash
# 添加 springdoc-openapi 依赖
```

### 完成总结

所有步骤完成后，输出以下总结信息：

```
📋 Swagger/OpenAPI 文档生成完成
──────────────────────────────
发现端点数：<N> 个（GET: x, POST: y, PUT: z, DELETE: w）
生成 Schema 数：<N> 个
验证结果：✅ 通过 / ❌ 失败（附失败原因）
输出文件：<文件路径>
──────────────────────────────
后续步骤建议：
- [ ] 人工检查 description 和 example 是否准确
- [ ] 确认 servers 地址是否正确
- [ ] 如需在线浏览，参考第八步集成 Swagger UI
- [ ] 将生成的文档提交到版本控制
```

---

## Schema 生成规则

### 类型映射

| 源代码类型 | OpenAPI 类型 |
|-----------|-------------|
| `string` | `type: string` |
| `number` / `float` / `double` | `type: number` |
| `int` / `integer` | `type: integer` |
| `boolean` / `bool` | `type: boolean` |
| `Date` / `datetime` | `type: string, format: date-time` |
| `Array<T>` / `T[]` / `[]T` | `type: array, items: {$ref}` |
| `object` / `Record` / `map` | `type: object` |
| `null` / `None` / `nil` | `nullable: true` |
| `enum` | `type: string, enum: [...]` |
| `File` / `UploadFile` | `type: string, format: binary` |

### 文件上传端点处理

检测以下特征识别文件上传：
1. 参数类型包含 `UploadFile` / `File` / `MultipartFile`
2. 装饰器或注解标注了 `@FormParam` / `multipart`
3. Content-Type 包含 `multipart/form-data`

生成时使用：
```yaml
requestBody:
  required: true
  content:
    multipart/form-data:
      schema:
        type: object
        properties:
          file:
            type: string
            format: binary
```

### 命名约定

- Schema 名称使用 PascalCase：`UserResponse`、`CreateOrderRequest`
- operationId 使用 camelCase：`getUserById`、`createOrder`
- tags 按业务模块分组：`Users`、`Orders`、`Auth`

### 必填字段判定

按以下规则判断字段是否 required：
1. TypeScript 中无 `?` 的属性 → required
2. Zod 中未调用 `.optional()` 的字段 → required
3. Pydantic 中无默认值的字段 → required
4. Go struct 中无 `omitempty` tag 的字段 → required

---

## 质量检查清单

生成完成后，按优先级自检以下项目：

**🔴 关键项（必须通过）：**
- [ ] 所有 API 端点都已覆盖
- [ ] 所有 `$ref` 引用都有对应的 schema 定义
- [ ] 文档通过 lint 验证（swagger-cli / redocly）

**🟡 重要项（强烈推荐）：**
- [ ] 请求参数类型准确（path/query/body/header）
- [ ] 认证方式已正确标注
- [ ] operationId 唯一且有意义
- [ ] 响应 schema 与实际代码匹配

**🟢 可选项：**
- [ ] description 和 summary 清晰简洁
- [ ] 无遗漏的错误响应码（至少包含 400、500）

---

## 注意事项

- **不要**凭空编造 API 端点，必须基于实际源代码
- **不要**遗漏错误响应，至少包含 400 和 500
- **不要**忽略认证中间件，确保 security 字段正确
- **不要**在 schema 中使用 `any` 或过于宽泛的类型
- 若项目已有 swagger 装饰器/注解（如 `@ApiProperty`），优先从注解提取
- 大型项目（50+ 端点）建议分模块生成，使用 tags 分组
- 生成后建议提交到版本控制，方便后续维护

## 安全检查

- [ ] 文档中没有硬编码的 API key 或 secret
- [ ] 认证端点已标注 securitySchemes
- [ ] 敏感数据（密码、token）不在示例值中暴露
- [ ] 所有需认证的端点都标注了 security 要求

---

## 决策流程图

```
检测项目类型和框架
        |
扫描 API 路由定义
        |
是否找到路由？
  否 -> 提示用户确认 API 文件位置
  是 |
        |
检查是否已有 openapi/swagger 文件
  是 -> 增量更新模式
  否 -> 全量生成模式
        |
逐个分析端点：路径、参数、响应、认证
        |
提取/推断 schema 类型
        |
生成 openapi.yaml
        |
验证文档（swagger-cli / redocly）
  失败 -> 修复后重新验证
  通过 |
        |
输出结果 + 质量检查报告
```

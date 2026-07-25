# C#/.NET 隐式语义扫描

用于 C#/.NET 项目，尤其是 ASP.NET Core、Entity Framework、MediatR、BackgroundService、source generator 和企业应用场景。

## 常见隐藏机制

- Attribute / filter：Controller/action filter、authorization attribute、validation attribute、自定义 attribute。
- Middleware pipeline：ASP.NET Core middleware、exception handler、routing、auth、CORS、rate limiting。
- DI lifecycle：singleton/scoped/transient、scope 泄漏、constructor injection、decorator。
- EF Core：change tracker、global query filter、shadow property、interceptor、save changes hook、lazy loading、migration。
- Async pipeline：`Task`、background service、hosted service、message consumer、retry policy。
- MediatR / pipeline behavior：command/query handler 前后的 validation、transaction、logging、permission。
- Configuration binding：`appsettings*.json`、environment variables、options pattern、feature flag。
- Source generator / codegen：protobuf、OpenAPI client、record/source generator、partial class/method。

## 扫描入口和文件线索

- 构建：`*.csproj`、`*.sln`、`Directory.Build.props`、`global.json`。
- 入口：`Program.cs`、`Startup.cs`、`Controllers/`、`Minimal API` route mapping。
- 管道：`Use*` middleware、`Add*` service registration、filters、attributes、MediatR behaviors。
- EF：`DbContext`、`OnModelCreating`、`SaveChanges*`、migrations、interceptors。
- 配置：`appsettings*.json`、Options class、`IConfiguration`、environment-specific settings。
- 后台：`BackgroundService`、hosted service、queue/message consumer。

## 典型 AI 易错点

- 只改 Controller/Handler，忽略 middleware/filter/attribute/pipeline behavior 中的鉴权、校验、事务、日志或异常处理。
- 不理解 DI lifecycle，导致 scoped service 被 singleton 持有或请求上下文丢失。
- 改 EF entity 却忘记 migration、global query filter、shadow property、interceptor 或 SaveChanges hook。
- 忽略 MediatR pipeline，以为 handler 内才有完整业务逻辑。
- 改配置但没有区分 appsettings、环境变量和 Options binding 生效顺序。
- 忘记 background service/message consumer 的异步补偿和重试策略。

## 应写入 Knowledge Base 的内容

- 本业务域请求进入 Controller/Endpoint/Handler 前后的 middleware/filter/pipeline 行为。
- 本域依赖的 DI lifecycle、DbContext、EF filter/interceptor、MediatR behavior。
- 配置、feature flag、Options、环境覆盖对本域行为的影响。
- 改实体、handler、后台任务后必须同步检查的 migration、配置、验证路径。

## 应抽成 Guide 的条件

- 认证授权、异常处理、MediatR pipeline、EF Core 约束、配置绑定或后台任务机制被多个业务域共享。
- DI lifecycle 或 DbContext 使用规则会影响多个模块。
- 需要固定验证路径来确认 middleware/filter/interceptor 是否生效。

## Q&A 追问模板

- 我看到 `[attribute/filter/middleware]` 会包住 `[endpoint/handler]`，它承担什么业务责任？
- `[MediatR behavior/interceptor]` 在 handler 前后做了什么？哪些调用不能绕过？
- `[DbContext/entity]` 是否受 global query filter、shadow property、interceptor 或 SaveChanges hook 影响？
- `[service]` 的 DI lifecycle 是什么？在后台任务或异步处理中是否安全？
- 配置值来自 appsettings、环境变量还是 Options binding？哪个环境才是验证依据？


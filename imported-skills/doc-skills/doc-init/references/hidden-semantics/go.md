# Go 隐式语义扫描

用于 Go 项目，尤其是 Web 服务、微服务、CLI、任务系统、gRPC、codegen 和中间件场景。

## 常见隐藏机制

- Middleware / interceptor：HTTP middleware、gRPC interceptor、router group middleware。
- `context.Context`：用户、租户、trace、deadline、cancel、transaction、request-scoped value。
- Interface wrapper：装饰器式封装、client wrapper、repository wrapper、mock/generated implementation。
- `init` / package side effect：注册路由、注册驱动、加载配置、初始化全局变量。
- Build tag / go generate：平台差异、生成代码、wire/mock/protobuf/openapi。
- Goroutine / channel：异步执行、并发安全、context cancel、后台补偿。
- 配置注入：env、viper、flag、yaml、remote config、feature flag。
- 数据库/缓存封装：transaction helper、repository pattern、sql hook、cache-aside wrapper。

## 扫描入口和文件线索

- 构建：`go.mod`、`go.sum`、`Makefile`、`Taskfile.yml`、`Dockerfile`。
- 入口：`cmd/**/main.go`、`internal/`、`pkg/`、`server.go`、`router.go`、`wire.go`。
- 中间件：`middleware/`、`interceptor/`、`handler/`、`router/`。
- 生成：`//go:generate`、`*.pb.go`、`*_gen.go`、`wire_gen.go`、`mock_*.go`。
- 条件编译：`//go:build`、`// +build`。
- 配置：`config/`、`*.yaml`、`.env*`、flag/env loader。

## 典型 AI 易错点

- 只改 handler，忽略 middleware/interceptor 注入的 auth、tenant、trace、transaction 或 recover。
- 不传或错误复用 `context.Context`，导致超时、取消、租户、trace 或权限丢失。
- 修改 interface 调用方却没有找到真实实现或 wrapper，误判实际执行逻辑。
- 忽略 `init` 注册、副作用 import、build tag、go generate，导致本地能跑但目标平台不生效。
- 在 goroutine 里使用请求上下文或非线程安全对象，导致异步逻辑不稳定。
- 改 proto/openapi/sqlc/ent/gorm model 后忘记重新生成代码。

## 应写入 Knowledge Base 的内容

- 本业务域 handler/service/repository/client 的真实装配关系和 wrapper 链。
- 哪些 context value 是本域必需的，谁写入、谁读取、异步时如何传递。
- 哪些生成代码、build tag、init 注册会影响本域入口。
- 改本域时必须同步处理哪些 proto/openapi/sqlc/配置/中间件。

## 应抽成 Guide 的条件

- context、middleware/interceptor、codegen、transaction helper、配置加载、异步任务模式被多个业务域共享。
- wrapper 链或 DI/wire 装配复杂，单个 KB 难以解释清楚。
- build tag / platform 差异影响多个模块。

## Q&A 追问模板

- 我看到 `[middleware/interceptor]` 会包住 `[handler/rpc]`，它注入了哪些 context value？
- `[interface]` 的真实实现和 wrapper 链是什么？哪些调用不能绕过 wrapper？
- `[context value]` 在异步 goroutine 中是否仍有效？项目约定怎么传递？
- 改 `[proto/openapi/sqlc/ent]` 后是否必须执行 go generate？生成物是否提交？
- 是否存在 build tag 或平台差异导致不同环境走不同实现？


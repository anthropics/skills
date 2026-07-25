# JavaScript/TypeScript 隐式语义扫描

用于 JavaScript/TypeScript 项目，尤其是 Node.js、NestJS、Express/Koa、Next.js、React/Vue、GraphQL、前端构建工具和 serverless 场景。

## 常见隐藏机制

- Middleware / interceptor / guard / pipe / filter：请求进入业务方法前后的自动逻辑。
- Decorator / metadata：NestJS decorator、class-validator、TypeORM decorator、Angular decorator、自定义 decorator。
- Hook / lifecycle：React hook、Vue lifecycle、Next.js data fetching、NestJS module lifecycle、ORM hook。
- 路由和文件约定：Next.js app/pages router、API route、dynamic route、framework convention。
- 异步事件：EventEmitter、queue worker、cron、webhook、message consumer、promise chain、observable。
- Runtime config：`.env*`、feature flag、tenant config、build-time env vs runtime env。
- Codegen：GraphQL codegen、OpenAPI client、Prisma client、protobuf、typed routes。
- 状态与缓存：React query、Redux/Zustand、server cache、edge cache、Redis wrapper。

## 扫描入口和文件线索

- 构建：`package.json`、`pnpm-lock.yaml`、`yarn.lock`、`tsconfig.json`、`vite.config.*`、`next.config.*`。
- 框架：`main.ts`、`app.module.ts`、`middleware.ts`、`pages/`、`app/`、`routes/`、`server.ts`。
- 约定：`*.decorator.ts`、`*.guard.ts`、`*.interceptor.ts`、`*.pipe.ts`、`*.filter.ts`、`*.middleware.ts`。
- ORM/codegen：`schema.prisma`、`graphql/**/*.graphql`、`openapi*.yaml`、`generated/`。
- 配置：`.env*`、`config/*.ts`、feature flag client、runtime config loader。

## 典型 AI 易错点

- 只改 handler/controller，忽略 guard/interceptor/pipe/middleware 中的鉴权、校验、转换、限流或上下文注入。
- 把 build-time env 当 runtime env，导致部署环境行为和本地不同。
- 改 GraphQL/OpenAPI schema 后忘记重新生成 client/types。
- 前端只改组件状态，忘记 query cache、server action、route cache 或 edge cache。
- Next.js/React/Vue 中误判 server/client 边界，导致代码运行在错误端。
- 忽略 async event / queue worker，认为接口返回就代表业务完成。

## 应写入 Knowledge Base 的内容

- 本业务域的请求链路：route/controller → middleware/guard/interceptor/pipe/filter → service → event/worker。
- 哪些 decorator、schema、hook、codegen 会改变显式代码行为。
- 本域涉及的 env/config/cache 规则，以及本地、构建、运行时差异。
- 改接口、schema、前端状态或异步任务时的验证路径。

## 应抽成 Guide 的条件

- 认证鉴权、请求上下文、错误处理、缓存、路由约定、codegen 或 async queue 被多个业务域共享。
- Next.js/React/Vue 的运行端边界、缓存策略或发布验证路径影响多个模块。
- GraphQL/OpenAPI/Prisma 等生成流程是跨域通用开发约束。

## Q&A 追问模板

- 我看到 `[middleware/guard/interceptor/pipe]` 会先于 `[handler]` 执行，它注入或修改了哪些业务上下文？
- `[decorator/schema]` 是否会自动做校验、转换、权限或路由注册？错用会有什么后果？
- 改 `[API/schema/model]` 后是否必须跑 codegen？生成物是否提交？
- `[env/config/feature flag]` 是构建时还是运行时读取？不同环境行为是否一致？
- 接口返回后是否还有 queue/event/webhook 继续完成业务？如何验证异步结果？


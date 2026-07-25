# Python 隐式语义扫描

用于 Python 项目，尤其是 Django、FastAPI、Flask、Celery、SQLAlchemy、Pydantic、Airflow、数据处理和异步任务场景。

## 常见隐藏机制

- Decorator：路由、权限、缓存、事务、重试、限流、自定义 wrapper。
- Context manager / dependency injection：FastAPI dependency、Flask context、Django request/user、database session。
- Metaclass / descriptor / property：模型字段、ORM 映射、动态属性。
- Middleware / signal / hook：Django middleware、signals、Flask before/after request、SQLAlchemy events。
- ORM 行为：lazy loading、session flush/commit、model save/delete hook、migration、query filter。
- Contextvars / thread local：request context、tenant/user context、trace。
- Async / task：Celery task、RQ、asyncio、background task、retry policy、beat schedule。
- Settings 覆盖：`settings.py`、`.env`、pydantic settings、环境变量、测试配置。

## 扫描入口和文件线索

- 构建依赖：`pyproject.toml`、`requirements*.txt`、`Pipfile`、`poetry.lock`。
- 框架入口：`manage.py`、`settings.py`、`urls.py`、`asgi.py`、`wsgi.py`、`main.py`、`app.py`。
- 约定文件：`middleware.py`、`signals.py`、`tasks.py`、`dependencies.py`、`models.py`、`schemas.py`。
- 配置：`.env*`、`config.py`、`settings/*.py`。
- 迁移和 ORM：`migrations/`、SQLAlchemy model/session、Alembic config。

## 典型 AI 易错点

- 只改 view/handler，忽略 decorator、dependency、middleware、signal 或 permission class。
- 改 model 字段但忘记 migration、serializer/schema、admin/form、signal、副作用任务。
- 在 Celery/background task 中假设 request context、tenant/user context 仍然存在。
- 混淆 SQLAlchemy session flush/commit、Django transaction atomic、异步任务提交时机。
- 改 settings 但没意识到测试、开发、生产配置来源不同。
- 忽略 property/descriptor/metaclass，让看似普通字段实际有动态计算或 ORM 映射。

## 应写入 Knowledge Base 的内容

- 本业务域从 request/task 到 ORM/外部系统的真实执行链路。
- 哪些 decorator、dependency、middleware、signal、ORM hook 会自动执行。
- 哪些上下文在同步请求、异步任务、测试和脚本中需要手动提供。
- 改模型、schema、迁移、任务时必须同步检查的对象。

## 应抽成 Guide 的条件

- 认证权限、租户上下文、事务、Celery、settings 管理、ORM hook 被多个业务域共享。
- migration / task / signal 的使用方式有项目统一约束。
- 数据处理或异步任务有固定验证路径和重试/补偿策略。

## Q&A 追问模板

- 我看到 `[decorator/dependency/middleware]` 会改变 `[handler]` 的入参或权限，它承担什么业务责任？
- `[signal/hook]` 在什么时候触发？是否可能重复触发或在事务失败后仍执行？
- 异步任务是否能拿到 request/user/tenant context？如果不能，项目约定怎么传？
- 改 `[model/schema]` 后是否必须同步 migration、serializer、form、admin 或任务？
- 哪些 settings 来源会覆盖默认值？验证时应该读取哪个环境配置？


# Config Discovery

本文定义数据库连接发现方法。不要把它写成某语言教程；先识别项目生态，再找当前项目真实使用的连接来源。

## 扫描原则

- 先找运行入口和 profile/env 选择机制，再判断哪个配置实际生效。
- 同时扫描源码配置、环境变量模板、容器/部署配置、测试配置和 ORM/数据源初始化代码。
- 配置文件里的 secret 引用不等于明文连接；记录引用链，必要时向用户要只读连接。
- 多数据源项目要区分业务库、日志库、元数据库、测试库、只读库和迁移库。
- 默认输出完整候选值，方便直接连接测试；只有用户要求或非测试环境才启用脱敏。

## 常见入口速查

这些只是提醒，不要把清单当穷举：

| 生态 | 常见线索 |
|---|---|
| Java/Kotlin | `application*.yml/properties`、Spring profile、`DataSource`、JDBC URL、MyBatis/JPA 配置、Docker/K8s secret |
| .NET | `appsettings*.json`、`ConnectionStrings`、UserSecrets、`DbContext`、Dapper/ADO.NET 初始化、launch profile |
| JS/TS | `.env*`、Prisma/TypeORM/Sequelize/Knex 配置、Nest/Next runtime config、Docker/compose |
| Python | Django settings、SQLAlchemy/FastAPI 配置、Alembic、Celery/worker env、`.env*` |
| Go | viper/envconfig、`config*.yaml/json/toml`、`database/sql` 初始化、gorm/sqlx 配置、Docker/compose |
| 通用 | `docker-compose*.yml`、Helm/K8s manifests、Terraform、CI variables、README 启动说明、测试容器配置 |

## 输出字段

连接发现只输出候选，不直接断言可用：

```json
{
  "source_file": "config/appsettings.Development.json",
  "source_key": "ConnectionStrings.Main",
  "db_type_hint": "postgresql",
  "value": "postgresql://user:password@localhost:5432/app",
  "profile_or_env": "Development",
  "confidence": "medium",
  "notes": ["引用环境变量 DB_PASSWORD，未在仓库内找到明文值时需要用户补充"]
}
```

## 需要问用户的情况

只在缺少必要信息时问，不要为了“确认一下”打断：

- 只有 secret 名称，没有本地可用值。
- 发现多个候选连接，无法判断哪个是只读或测试环境。
- 连接指向生产或疑似生产，且没有只读保证。
- 项目强依赖数据库事实，但没有任何连接来源。

用户禁止提问时，记录「数据库证据缺失」和缺失原因，继续用代码、人机资料和运行验证建立低置信知识。

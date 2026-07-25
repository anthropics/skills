# Java/Kotlin 隐式语义扫描

用于 Java/Kotlin 项目，尤其是 Spring、Spring Boot、MyBatis、JPA、Ktor、Micronaut、Quarkus 等生态。目标不是列框架知识，而是发现源码表面看不到、运行时会改变业务行为的机制。

## 常见隐藏机制

- AOP / proxy：`@Aspect`、`@Around`、JDK/CGLIB proxy、Spring bean 方法自调用失效、接口代理与类代理差异。
- 注解驱动行为：`@Transactional`、`@Async`、`@Cacheable`、`@Scheduled`、`@EventListener`、校验注解、权限注解、自定义注解。
- 事务与一致性：事务传播、只读事务、回滚异常类型、事务提交后事件、分布式事务、批处理部分失败策略。
- 上下文：`ThreadLocal`、MDC、租户上下文、登录用户、语言/门店/品牌上下文、TraceId。
- ORM / SQL 映射：MyBatis XML、Interceptor、TypeHandler、逻辑删除、自动填充、JPA entity listener、懒加载。
- 生成代码：Lombok、MapStruct、protobuf/OpenAPI client、annotation processor、Kotlin data class / coroutine 编译语义。
- Bean 生命周期与配置：`@PostConstruct`、BeanPostProcessor、profile、conditional bean、配置属性绑定、starter 自动装配。
- 外部契约：MQ listener、Redis cache、搜索索引、远程 RPC/HTTP client、定时任务、异步补偿。

## 扫描入口和文件线索

- 构建：`pom.xml`、`build.gradle*`、`settings.gradle*`、`gradle.properties`。
- 配置：`application*.yml`、`bootstrap*.yml`、`META-INF/spring.factories`、`AutoConfiguration.imports`。
- 代码：`*Aspect`、`*Interceptor`、`*Filter`、`*Listener`、`*Handler`、`*Resolver`、`*Config`、`*AutoConfiguration`、`*TypeHandler`。
- SQL：`mapper/**/*.xml`、`@Mapper`、`@Select`、`@Update`、MyBatis plugin。
- 生成：`target/generated-sources`、`build/generated`、`@Mapper`、`@Builder`、`@Data`、`@Value`。

## 典型 AI 易错点

- 只改 Service 方法体，忘记事务传播、缓存注解、异步注解或权限注解导致行为不生效。
- 看到普通方法调用，却漏掉 AOP 在调用前后做了鉴权、租户注入、日志、幂等、锁或数据权限。
- 直接 new 对象绕过 Spring bean，导致代理、配置注入、事务和生命周期钩子失效。
- 修改 MyBatis mapper 方法但漏改 XML SQL、TypeHandler、逻辑删除、自动填充或分表插件规则。
- 忽略 `ThreadLocal` / MDC / tenant context，导致本地测试可过、真实请求上下文错误。
- 使用 Kotlin coroutine / Java async 时忽略上下文传播和事务边界。

## 应写入 Knowledge Base 的内容

- 本业务域依赖哪些注解、代理、上下文、事务、缓存、SQL 拦截或异步机制。
- 哪些入口看似普通调用，实际被 AOP / interceptor / listener 改写。
- 改本域代码时必须同步检查哪些配置、XML、生成类、缓存 key、上下文来源。
- 忽略该机制会导致什么业务后果。

## 应抽成 Guide 的条件

- 同一 AOP、注解、分表插件、权限拦截、缓存规则或上下文机制影响多个业务域。
- 修改机制本身会影响全局行为，或者多个领域知识库都需要引用同一套使用约束。
- 机制需要固定验证路径，例如查日志、查拦截结果、查 SQL 改写、查事务提交后事件。

## Q&A 追问模板

- 我看到 `[注解/切面/拦截器]` 会包住 `[入口]`，这个机制承担什么业务责任？哪些场景不能绕过？
- 如果直接调用 `[类/方法]` 或在同类里自调用，会不会绕过代理？项目里有没有约定的正确入口？
- `[ThreadLocal/tenant/user context]` 从哪里写入？异步、批处理、MQ 消费时如何保证存在？
- 改 `[Mapper/XML/Entity]` 时，是否必须同步处理分表、逻辑删除、自动填充、缓存或索引？
- `[profile/conditional bean]` 在不同环境下行为是否不同？验证时看哪个配置才算准？


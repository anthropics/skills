---
name: docker-gen
description: Auto-detect tech stack and generate optimized Dockerfile, docker-compose.yml, and .dockerignore with security best practices. Use when user asks to containerize a project.
license: MIT
---

# Skill: Docker 配置智能生成

自动检测项目技术栈，生成优化的 Dockerfile、docker-compose.yml 和 .dockerignore。支持开发和生产双环境配置。

## 触发条件

当用户请求以下操作时激活：
- "生成 docker"、"容器化"、"dockerize"
- "generate dockerfile"、"docker compose"
- "给项目加 docker"、"create docker config"

---

## 执行步骤

### 第一步：检测项目技术栈

```bash
# 检测语言和包管理器
ls package.json bun.lockb yarn.lock pnpm-lock.yaml package-lock.json 2>/dev/null
ls pyproject.toml requirements.txt Pipfile setup.py uv.lock 2>/dev/null
ls go.mod go.sum 2>/dev/null
ls Cargo.toml Cargo.lock 2>/dev/null
ls pom.xml build.gradle build.gradle.kts 2>/dev/null

# Node.js/Bun 包管理器检测（按优先级）
# 1. bun.lockb → bun
# 2. pnpm-lock.yaml → pnpm
# 3. yarn.lock → yarn
# 4. package-lock.json → npm
if [ -f "bun.lockb" ]; then
  PKG_MANAGER=bun
elif [ -f "pnpm-lock.yaml" ]; then
  PKG_MANAGER=pnpm
elif [ -f "yarn.lock" ]; then
  PKG_MANAGER=yarn
elif [ -f "package-lock.json" ]; then
  PKG_MANAGER=npm
fi

# Node.js/Bun 运行时检测
cat package.json 2>/dev/null | grep -E '"(bun|node|ts-node|tsx)"'
cat package.json 2>/dev/null | grep -E '"(next|nuxt|vite|react-scripts|remix|astro|svelte)"'

# Python 框架检测
grep -rE "(fastapi|flask|django|gunicorn|uvicorn|celery)" requirements.txt pyproject.toml 2>/dev/null

# Go 框架检测
grep -rE "(gin|echo|fiber|chi|grpc)" go.mod 2>/dev/null

# Rust 框架检测
grep -rE "(actix|axum|rocket|warp|tonic)" Cargo.toml 2>/dev/null

# Java 框架检测
grep -rE "(spring-boot|quarkus|micronaut)" pom.xml build.gradle 2>/dev/null

# 检测已有 Docker 配置
ls Dockerfile docker-compose.yml docker-compose.yaml .dockerignore 2>/dev/null
```

根据检测结果确定：
- 主语言 + 运行时（Node/Bun/Python/Go/Rust/Java）
- 框架（Next.js/FastAPI/Gin/Actix 等）
- 包管理器（bun/npm/pip/go mod/cargo/maven/gradle）
- 是否为前后端分离项目（检查是否存在多个子目录各有独立配置）
- 端口号（从代码或配置文件中提取）

#### 端口检测策略

按以下顺序检测应用端口：
1. `Dockerfile` 中已有的 `EXPOSE` 指令
2. `package.json` 中 start script 的 `--port` 参数
3. 代码中的端口配置（如 `app.listen(3000)`）
4. 框架默认端口：Next.js=3000, Vite=5173, FastAPI=8000, Go=8080
5. 以上都未检测到时，使用 3000 并提示用户确认

#### 前后端分离项目

对于多服务项目，按以下规范组织：

```
project/
├── frontend/
│   └── Dockerfile          # 前端构建
├── backend/
│   └── Dockerfile          # 后端构建
└── docker-compose.yml      # 编排所有服务
```

或使用命名 Dockerfile：
```
project/
├── Dockerfile.frontend
├── Dockerfile.backend
└── docker-compose.yml
```

docker-compose.yml 示例：
```yaml
services:
  frontend:
    build:
      context: ./frontend
      dockerfile: Dockerfile
    ports:
      - "3000:3000"
  backend:
    build:
      context: ./backend
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
```

### 第二步：检测依赖服务

```bash
# 数据库检测
grep -rE "(pg|postgres|mysql|mysql2|mongodb|mongoose|sqlite|prisma|drizzle|typeorm|sequelize|sqlalchemy|gorm|diesel)" package.json requirements.txt pyproject.toml go.mod Cargo.toml pom.xml 2>/dev/null

# 缓存/队列检测
grep -rE "(redis|ioredis|bull|bullmq|memcached|rabbitmq|amqplib|kafka)" package.json requirements.txt pyproject.toml go.mod Cargo.toml pom.xml 2>/dev/null

# 搜索引擎检测
grep -rE "(elasticsearch|@elastic|meilisearch|typesense)" package.json requirements.txt pyproject.toml go.mod 2>/dev/null

# 对象存储检测
grep -rE "(minio|@aws-sdk/client-s3|boto3)" package.json requirements.txt pyproject.toml 2>/dev/null
```

### 第三步：生成 Dockerfile

根据检测到的技术栈，选择对应模板生成 Dockerfile。

#### Docker 构建缓存优化

合理利用构建缓存可大幅减少构建时间，关键原则是**将变化频率低的层放在前面**：

```dockerfile
# ===== npm 缓存优化 =====
COPY package.json package-lock.json ./
RUN npm ci --production    # 利用 Docker 层缓存，仅 lock 文件变化时重装

# ===== pnpm 缓存优化 =====
COPY package.json pnpm-lock.yaml ./
# 使用 BuildKit 的 --mount=type=cache 持久化 pnpm store
RUN --mount=type=cache,target=/root/.local/share/pnpm/store \
    pnpm install --frozen-lockfile --prod

# ===== yarn 缓存优化（Yarn Berry / v3+）=====
COPY package.json yarn.lock .yarnrc.yml ./
COPY .yarn/releases .yarn/releases
RUN --mount=type=cache,target=/root/.yarn/berry/cache \
    yarn install --immutable

# ===== bun 缓存优化 =====
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile --production
```

> **提示**：使用 `DOCKER_BUILDKIT=1`（Docker 18.09+默认启用）以支持 `--mount=type=cache`。
> CI 环境中可结合 `docker buildx build --cache-from` 和 `--cache-to` 实现跨构建缓存复用。

#### Node.js / Bun 项目模板

```dockerfile
# ===== Production Dockerfile (Node.js / Bun) =====

# --- Stage 1: Dependencies ---
FROM oven/bun:1-alpine AS deps
WORKDIR /app
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile --production

# --- Stage 2: Build ---
FROM oven/bun:1-alpine AS builder
WORKDIR /app
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile
COPY . .
RUN bun run build

# --- Stage 3: Production ---
FROM oven/bun:1-alpine AS runner
WORKDIR /app

# Security: non-root user
RUN addgroup -g 1001 -S appgroup && \
    adduser -S appuser -u 1001 -G appgroup

COPY --from=deps --chown=appuser:appgroup /app/node_modules ./node_modules
COPY --from=builder --chown=appuser:appgroup /app/dist ./dist
COPY --from=builder --chown=appuser:appgroup /app/package.json ./

USER appuser

EXPOSE 3000

HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
  CMD wget --no-verbose --tries=1 --spider http://localhost:3000/health || exit 1

CMD ["bun", "run", "start"]
```

> 若检测到 npm/yarn/pnpm 而非 bun，替换基础镜像为 `node:22-alpine`，对应调整安装命令。
> 若检测到 Next.js，使用 `standalone` output 模式，按以下关键步骤生成 runner 阶段：

```dockerfile
# Next.js standalone 关键步骤
FROM node:22-alpine AS runner
WORKDIR /app
ENV NODE_ENV=production

COPY --from=builder --chown=appuser:appgroup /app/.next/standalone ./
COPY --from=builder --chown=appuser:appgroup /app/public ./public
COPY --from=builder --chown=appuser:appgroup /app/.next/static ./.next/static

USER appuser
EXPOSE 3000
CMD ["node", "server.js"]
```

#### Python 项目模板

```dockerfile
# ===== Production Dockerfile (Python) =====

# --- Stage 1: Build ---
FROM python:3.12-slim AS builder
WORKDIR /app

RUN pip install --no-cache-dir --upgrade pip && \
    pip install --no-cache-dir wheel

COPY requirements.txt ./
RUN pip install --no-cache-dir --prefix=/install -r requirements.txt

# --- Stage 2: Production ---
FROM python:3.12-slim AS runner
WORKDIR /app

# Security: non-root user
RUN groupadd -g 1001 appgroup && \
    useradd -u 1001 -g appgroup -s /bin/false appuser

COPY --from=builder /install /usr/local
# IMPORTANT: Ensure .dockerignore excludes .env, .git, tests/, docs/, etc.
# Alternatively, use explicit COPY for each required directory:
#   COPY --chown=appuser:appgroup app/ ./app/
#   COPY --chown=appuser:appgroup config/ ./config/
COPY --chown=appuser:appgroup . .

# Remove unnecessary files
RUN find . -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null; \
    find . -name "*.pyc" -delete 2>/dev/null; \
    rm -rf tests/ .pytest_cache/ .mypy_cache/; \
    true

USER appuser

EXPOSE 8000

HEALTHCHECK --interval=30s --timeout=5s --start-period=15s --retries=3 \
  CMD python -c "import urllib.request; urllib.request.urlopen('http://localhost:8000/health')" || exit 1

CMD ["gunicorn", "app.main:app", "-w", "4", "-k", "uvicorn.workers.UvicornWorker", "-b", "0.0.0.0:8000"]
```

> 若检测到 FastAPI，使用 `uvicorn` + `gunicorn`。
> 若检测到 Django，使用 `gunicorn` + `--wsgi`。
> 若有 `pyproject.toml` + `uv`，用 `uv pip install` 替代。

#### Python 包管理器检测优先级

1. `uv.lock` 或 `pyproject.toml` 含 `[tool.uv]` → 使用 uv
2. `poetry.lock` → 使用 poetry
3. `pdm.lock` → 使用 pdm
4. `Pipfile.lock` → 使用 pipenv
5. `requirements.txt` → 使用 pip（默认）

#### Go 项目模板

```dockerfile
# ===== Production Dockerfile (Go) =====

# --- Stage 1: Build ---
FROM golang:1.23-alpine AS builder
WORKDIR /app

# Install CA certs for HTTPS and tzdata for timezone
RUN apk add --no-cache ca-certificates tzdata

COPY go.mod go.sum ./
RUN go mod download && go mod verify

COPY . .
ARG TARGETARCH
RUN CGO_ENABLED=0 GOOS=linux GOARCH=${TARGETARCH} go build \
    -ldflags="-w -s -extldflags '-static'" \
    -o /app/server ./cmd/server

# --- Stage 2: Production (scratch for minimal size) ---
FROM scratch AS runner

COPY --from=builder /usr/share/zoneinfo /usr/share/zoneinfo
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/
COPY --from=builder /app/server /server

EXPOSE 8080

# scratch has no shell or utilities — HEALTHCHECK cannot run here.
# Configure healthcheck in docker-compose.yml instead,
# or have the app implement a "healthcheck" subcommand and use:
#   HEALTHCHECK CMD ["/server", "healthcheck"]
HEALTHCHECK NONE

ENTRYPOINT ["/server"]
```

> Go 项目优先使用 `scratch` 镜像（最小化）。若需要 shell 调试，使用 `gcr.io/distroless/static-debian12`。
> 根据实际入口文件路径调整 `./cmd/server`。

> **scratch/distroless 镜像限制：**
> - 不支持 `HEALTHCHECK CMD`（无 shell，无 wget/curl 等工具）
> - 在 Dockerfile 中使用 `HEALTHCHECK NONE`
> - 在 docker-compose.yml 中配置外部健康检查（见下方示例）
> - 或在应用代码中实现 `/health` 端点，由负载均衡器检查
> - 或让应用二进制支持 `healthcheck` 子命令：`HEALTHCHECK CMD ["/server", "healthcheck"]`

docker-compose.yml 中为 scratch/distroless 容器配置健康检查：
```yaml
services:
  app:
    build: .
    ports:
      - "8080:8080"
    healthcheck:
      test: ["CMD-SHELL", "wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1"]
      interval: 30s
      timeout: 5s
      retries: 3
      start_period: 10s
    # 注意：CMD-SHELL 在 docker-compose 的 healthcheck 中由 Docker daemon 执行，
    # 不依赖容器内的 shell。但 wget/curl 仍需在容器内可用。
    # 对于 scratch 容器，推荐以下方案之一：
    #   方案 1: 应用实现 healthcheck 子命令
    #   healthcheck:
    #     test: ["/server", "healthcheck"]
    #   方案 2: 使用外部探针（如 Docker Desktop、Kubernetes liveness probe）
    #   方案 3: 改用 distroless + 安装 grpc_health_probe（适用于 gRPC 服务）
```

#### Rust 项目模板

```dockerfile
# ===== Production Dockerfile (Rust) =====

# --- Stage 1: Build ---
FROM rust:1.80-slim AS builder
WORKDIR /app

# Create a dummy project to cache dependencies
RUN cargo init --name app
COPY Cargo.toml Cargo.lock ./
RUN cargo build --release && \
    rm -rf src target/release/deps/app-* target/release/app

# Build actual project
COPY . .
RUN cargo build --release --locked

# --- Stage 2: Production ---
FROM gcr.io/distroless/cc-debian12 AS runner

COPY --from=builder /app/target/release/app /app

EXPOSE 8080

# distroless has no shell — HEALTHCHECK cannot run here.
# Configure healthcheck in docker-compose.yml instead.
HEALTHCHECK NONE

ENTRYPOINT ["/app"]
```

> Rust 使用 dummy 项目缓存依赖层，大幅减少重复编译时间。
> 生产使用 `distroless` 镜像（无 shell，最安全）。
> **注意**：distroless 镜像同样受 scratch/distroless 限制（见 Go 项目模板下方的说明），需在 docker-compose 层补充 healthcheck 配置。

#### Java (Spring Boot) 项目模板

```dockerfile
# ===== Production Dockerfile (Java / Spring Boot) =====

# --- Stage 1: Build ---
FROM eclipse-temurin:21-jdk-alpine AS builder
WORKDIR /app

COPY mvnw pom.xml ./
COPY .mvn .mvn
RUN ./mvnw dependency:go-offline -B

COPY src ./src
RUN ./mvnw package -DskipTests -B && \
    java -Djarmode=layertools -jar target/*.jar extract --destination /extracted

# --- Stage 2: Production ---
FROM eclipse-temurin:21-jre-alpine AS runner
WORKDIR /app

# Security: non-root user
RUN addgroup -g 1001 -S appgroup && \
    adduser -S appuser -u 1001 -G appgroup

COPY --from=builder --chown=appuser:appgroup /extracted/dependencies/ ./
COPY --from=builder --chown=appuser:appgroup /extracted/spring-boot-loader/ ./
COPY --from=builder --chown=appuser:appgroup /extracted/snapshot-dependencies/ ./
COPY --from=builder --chown=appuser:appgroup /extracted/application/ ./

USER appuser

EXPOSE 8080

HEALTHCHECK --interval=30s --timeout=5s --start-period=30s --retries=3 \
  CMD wget --no-verbose --tries=1 --spider http://localhost:8080/actuator/health || exit 1

ENTRYPOINT ["java", "org.springframework.boot.loader.launch.JarLauncher"]
```

> Spring Boot 使用 layertools 分层提取，最大化缓存效率。
> 若使用 Gradle，替换 `mvnw` 为 `gradlew` 对应命令。

### 第四步：生成 docker-compose.yml

根据检测到的依赖服务，组合对应模板：

#### 基础模板

```yaml
services:
  app:
    build:
      context: .
      dockerfile: Dockerfile
    container_name: ${PROJECT_NAME:-app}
    ports:
      - "${APP_PORT:-3000}:3000"
    env_file:
      - .env
    # ⚠️ env_file 安全注意事项：
    #   1. 确保 .env 已添加到 .gitignore，绝不提交到版本控制
    #   2. 敏感密钥（数据库密码、API Key 等）优先使用 Docker secrets
    #      或通过 CI/CD 环境变量直接注入，避免写入文件
    #   3. 多服务项目建议按服务拆分 env_file：
    #      app 使用 .env.app，postgres 使用 .env.db，各取所需
    environment:
      - NODE_ENV=production
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:3000/health"]
      interval: 30s
      timeout: 5s
      retries: 3
      start_period: 10s
    networks:
      - app-network
```

#### PostgreSQL 服务

```yaml
  postgres:
    image: postgres:16-alpine
    container_name: ${PROJECT_NAME:-app}-postgres
    ports:
      - "${POSTGRES_PORT:-5432}:5432"
    environment:
      POSTGRES_DB: ${POSTGRES_DB:-appdb}
      POSTGRES_USER: ${POSTGRES_USER:-postgres}
      POSTGRES_PASSWORD: ${POSTGRES_PASSWORD:?POSTGRES_PASSWORD is required}
    volumes:
      - postgres_data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U ${POSTGRES_USER:-postgres}"]
      interval: 10s
      timeout: 5s
      retries: 5
    restart: unless-stopped
    networks:
      - app-network
```

> **必需环境变量清单（PostgreSQL）：**
>
> | 变量 | 必需 | 说明 | 验证方式 |
> |------|------|------|---------|
> | `POSTGRES_PASSWORD` | ✅ 是 | 数据库密码，使用 `:?` 语法强制要求 | 启动时自动校验，缺失则报错退出 |
> | `POSTGRES_USER` | 否 | 用户名，默认 `postgres` | `pg_isready -U $POSTGRES_USER` |
> | `POSTGRES_DB` | 否 | 数据库名，默认与用户名相同 | `psql -d $POSTGRES_DB -c '\l'` |
>
> 验证环境变量是否正确配置：
> ```bash
> # 检查必需变量是否已设置
> docker compose config 2>&1 | grep -i "error"
> # 启动后验证数据库连接
> docker compose exec postgres pg_isready -U ${POSTGRES_USER:-postgres}
> ```

#### MySQL 服务

```yaml
  mysql:
    image: mysql:8.0
    container_name: ${PROJECT_NAME:-app}-mysql
    ports:
      - "${MYSQL_PORT:-3306}:3306"
    environment:
      MYSQL_DATABASE: ${MYSQL_DATABASE:-appdb}
      MYSQL_USER: ${MYSQL_USER:-appuser}
      MYSQL_PASSWORD: ${MYSQL_PASSWORD:?MYSQL_PASSWORD is required}
      MYSQL_ROOT_PASSWORD: ${MYSQL_ROOT_PASSWORD:?MYSQL_ROOT_PASSWORD is required}
    volumes:
      - mysql_data:/var/lib/mysql
    # Only add if legacy client compatibility is needed:
    # command: --mysql-native-password=ON
    healthcheck:
      test: ["CMD", "mysqladmin", "ping", "-h", "localhost"]
      interval: 10s
      timeout: 5s
      retries: 5
    restart: unless-stopped
    networks:
      - app-network
```

#### Redis 服务

```yaml
  redis:
    image: redis:7-alpine
    container_name: ${PROJECT_NAME:-app}-redis
    ports:
      - "${REDIS_PORT:-6379}:6379"
    command: redis-server --appendonly yes --requirepass ${REDIS_PASSWORD:?REDIS_PASSWORD is required}
    volumes:
      - redis_data:/data
    healthcheck:
      test: ["CMD", "redis-cli", "-a", "${REDIS_PASSWORD:?REDIS_PASSWORD is required}", "ping"]
      interval: 10s
      timeout: 5s
      retries: 5
    restart: unless-stopped
    networks:
      - app-network
```

#### MongoDB 服务

```yaml
  mongodb:
    image: mongo:7
    container_name: ${PROJECT_NAME:-app}-mongodb
    ports:
      - "${MONGO_PORT:-27017}:27017"
    environment:
      MONGO_INITDB_ROOT_USERNAME: ${MONGO_USER:-admin}
      MONGO_INITDB_ROOT_PASSWORD: ${MONGO_PASSWORD:?MONGO_PASSWORD is required}
      MONGO_INITDB_DATABASE: ${MONGO_DB:-appdb}
    volumes:
      - mongodb_data:/data/db
    healthcheck:
      test: ["CMD", "mongosh", "--eval", "db.adminCommand('ping')"]
      interval: 10s
      timeout: 5s
      retries: 5
    restart: unless-stopped
    networks:
      - app-network
```

#### Nginx 反向代理

```yaml
  nginx:
    image: nginx:1.25-alpine
    container_name: ${PROJECT_NAME:-app}-nginx
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./nginx/nginx.conf:/etc/nginx/nginx.conf:ro
      - ./nginx/ssl:/etc/nginx/ssl:ro
    depends_on:
      app:
        condition: service_healthy
    healthcheck:
      test: ["CMD-SHELL", "wget --no-verbose --tries=1 --spider http://localhost/ || exit 1"]
      interval: 30s
      timeout: 5s
      retries: 3
    restart: unless-stopped
    networks:
      - app-network
```

> **注意**：上述配置挂载了 `./nginx/nginx.conf`，你需要在项目中创建该文件。以下是最小化反向代理配置模板：

```nginx
# nginx/nginx.conf - 最小化反向代理配置
events {
    worker_connections 1024;
}

http {
    include       mime.types;
    default_type  application/octet-stream;
    sendfile      on;
    keepalive_timeout 65;

    # Gzip compression
    gzip on;
    gzip_types text/plain text/css application/json application/javascript text/xml;

    upstream app_backend {
        server app:3000;  # 服务名与 docker-compose 中的 service name 一致
    }

    server {
        listen 80;
        server_name localhost;

        location / {
            proxy_pass http://app_backend;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
        }

        # Health check endpoint for nginx itself
        location /nginx-health {
            access_log off;
            return 200 "ok";
        }
    }
}
```

> 根据实际项目调整 `server app:3000` 中的端口号，使其与应用服务的暴露端口一致。
> 如需 HTTPS，取消 443 端口注释并配置 SSL 证书路径（`./nginx/ssl/` 下放置 `cert.pem` 和 `key.pem`）。

#### volumes 和 networks 定义

```yaml
volumes:
  postgres_data:
  mysql_data:
  redis_data:
  mongodb_data:

networks:
  app-network:
    driver: bridge
```

> 仅包含实际检测到的服务，不要添加项目未使用的服务。

### 第五步：生成开发环境配置

生成 `docker-compose.dev.yml` 用于开发环境（覆盖生产配置）：

```yaml
# docker-compose.dev.yml - Development overrides
# Usage: docker compose -f docker-compose.yml -f docker-compose.dev.yml up

services:
  app:
    build:
      context: .
      dockerfile: Dockerfile
      # 不指定 target，使用完整构建（包含所有依赖）
      # 开发模式依赖 volume 挂载源代码实现 hot reload，
      # 而非停在某个构建阶段
    volumes:
      - .:/app          # Mount source code for hot reload
      - /app/node_modules  # Exclude node_modules (use container's version)
    environment:
      - NODE_ENV=development
    command: bun run dev  # Override to dev server with hot reload
    ports:
      - "${APP_PORT:-3000}:3000"
      - "9229:9229"  # Debugger port
```

> **为什么不使用 `target: deps`？**
> `deps` 阶段仅安装了生产依赖（`--production`），缺少 devDependencies（如 TypeScript、ESLint、测试框架等），
> 开发环境需要完整依赖。推荐做法是不指定 target，通过 volume 挂载源代码 + `command` 覆盖来实现 hot reload。
> 如需加速开发构建，可在 Dockerfile 中添加专用的 `dev` 阶段：
> ```dockerfile
> FROM oven/bun:1-alpine AS dev
> WORKDIR /app
> COPY package.json bun.lockb ./
> RUN bun install --frozen-lockfile  # 安装全部依赖（含 devDependencies）
> CMD ["bun", "run", "dev"]
> ```
> 然后在 docker-compose.dev.yml 中使用 `target: dev`。

### 第六步：生成 .dockerignore

```
# Version control
.git
.gitignore

# Dependencies (rebuilt in container)
node_modules
.pnp
.pnp.js

# Build output
dist
build
.next
out
target

# Environment files (NEVER include secrets in image)
.env
.env.*
!.env.example

# IDE and editor
.vscode
.idea
*.swp
*.swo
*~

# OS files
.DS_Store
Thumbs.db

# Test and documentation
tests
test
__tests__
coverage
*.test.ts
*.test.js
*.spec.ts
*.spec.js
docs
*.md
LICENSE

# Docker files (prevent recursive build)
Dockerfile*
docker-compose*
.dockerignore

# CI/CD
.github
.gitlab-ci.yml
.circleci

# Python specific
__pycache__
*.pyc
*.pyo
.pytest_cache
.mypy_cache
.venv
venv

# Rust specific
target/debug
**/*.rs.bk

# Go specific
vendor/

# Logs and temporary files
*.log
tmp
temp
```

### 第七步：生成 .env.example

```bash
# Application
APP_PORT=3000
NODE_ENV=production

# PostgreSQL
POSTGRES_DB=appdb
POSTGRES_USER=postgres
POSTGRES_PASSWORD=your_password_here
POSTGRES_PORT=5432

# Redis
REDIS_PASSWORD=your_redis_password_here
REDIS_PORT=6379

# MySQL (if applicable)
# MYSQL_DATABASE=appdb
# MYSQL_USER=appuser
# MYSQL_PASSWORD=your_password_here
# MYSQL_ROOT_PASSWORD=your_root_password_here

# MongoDB (if applicable)
# MONGO_DB=appdb
# MONGO_USER=admin
# MONGO_PASSWORD=your_password_here
```

> 仅包含实际检测到的服务对应的环境变量。

### 第八步：多平台构建（可选）

如需同时支持 x86 和 ARM 架构（如同时部署到 Intel 服务器和 Apple Silicon / AWS Graviton），使用 `docker buildx` 进行多平台构建：

```bash
# 创建并使用 buildx 构建器（首次执行）
docker buildx create --name multiplatform --use

# 多平台构建并推送到 registry
docker buildx build --platform linux/amd64,linux/arm64 -t myapp:latest --push .

# 仅构建不推送（用于本地测试，只能指定单个平台）
docker buildx build --platform linux/amd64 -t myapp:latest --load .

# 查看镜像支持的平台
docker buildx imagetools inspect myapp:latest
```

> **注意**：多平台构建需要推送到 registry（`--push`）或仅加载单平台（`--load`）。
> Go 项目已在 Dockerfile 中使用 `TARGETARCH` 变量，天然支持多平台构建。
> 其他语言的基础镜像（如 `node:22-alpine`、`python:3.12-slim`）通常已提供多平台版本。

### 第九步：验证配置

```bash
# 验证 Dockerfile 语法（使用 hadolint 静态检查）
docker run --rm -i hadolint/hadolint < Dockerfile 2>&1 || true

# 备选方案：实际构建验证（最可靠）
# docker build -t test-build:local . --progress=plain

# 验证 docker-compose 语法
docker compose config 2>&1

# 检查镜像大小（构建后）
docker images --format "table {{.Repository}}\t{{.Tag}}\t{{.Size}}" | head -5
```

---

## 开发 vs 生产配置差异

| 维度 | 开发环境 | 生产环境 |
|------|---------|---------|
| **基础镜像** | 完整镜像（含调试工具） | Alpine / slim / distroless |
| **构建阶段** | 单阶段（快速重建） | 多阶段（最小化体积） |
| **源码挂载** | volume 挂载（hot reload） | COPY 到镜像内 |
| **环境变量** | `NODE_ENV=development` | `NODE_ENV=production` |
| **端口暴露** | 应用端口 + 调试端口 | 仅应用端口 |
| **日志级别** | debug / verbose | info / warn |
| **依赖安装** | 全部（含 devDependencies） | 仅生产依赖 |
| **启动命令** | `dev` / `watch` 模式 | `start` / `serve` 模式 |
| **数据持久化** | 本地 volume | named volume / 外部存储 |
| **密码** | 固定简单密码 | 环境变量注入，不硬编码 |
| **Health check** | 可选 | 必须配置 |
| **Restart policy** | `no` | `unless-stopped` |

---

## Health Check 配置指南

### HTTP 应用

```dockerfile
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
  CMD wget --no-verbose --tries=1 --spider http://localhost:3000/health || exit 1
```

### TCP 服务（无 HTTP 端点）

```dockerfile
HEALTHCHECK --interval=30s --timeout=5s --retries=3 \
  CMD nc -z localhost 8080 || exit 1
```

### gRPC 服务

```dockerfile
# Install grpc_health_probe
COPY --from=grpc-health-probe /bin/grpc_health_probe /bin/
HEALTHCHECK --interval=30s --timeout=5s --retries=3 \
  CMD ["grpc_health_probe", "-addr=:50051"]
```

### docker-compose 中的 Health Check

```yaml
healthcheck:
  test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
  interval: 30s
  timeout: 5s
  retries: 3
  start_period: 10s
```

### 服务依赖等待

```yaml
services:
  app:
    depends_on:
      postgres:
        condition: service_healthy
      redis:
        condition: service_healthy
```

---

## 安全最佳实践清单

生成 Docker 配置时必须遵循：

### 镜像安全

- [ ] 使用最小化基础镜像（alpine / slim / distroless / scratch）
- [ ] 固定镜像版本号，不使用 `latest` 标签
- [ ] 多阶段构建，生产镜像不包含构建工具
- [ ] 定期更新基础镜像版本

### 运行时安全

- [ ] 创建非 root 用户运行应用（`USER appuser`）
- [ ] 不使用 `--privileged` 模式
- [ ] 限制 capabilities（`cap_drop: [ALL]`）
- [ ] 设置只读文件系统（`read_only: true`，按需挂载可写目录）

### 密钥安全

- [ ] 不在 Dockerfile 中硬编码密钥、密码、token
- [ ] 使用环境变量或 Docker secrets 注入
- [ ] `.env` 文件不提交到版本控制
- [ ] 生成 `.env.example` 作为模板
- [ ] 构建参数（`ARG`）不用于传递密钥（会残留在镜像层中）

### 网络安全

- [ ] 仅暴露必要端口
- [ ] 数据库/缓存不暴露到宿主机（仅在 docker network 内可访问）
- [ ] 生产环境通过 Nginx 反代，不直接暴露应用端口

### 构建安全

- [ ] `.dockerignore` 排除 `.env`、`.git`、`node_modules` 等
- [ ] 不在镜像中包含测试文件、文档、IDE 配置
- [ ] 清理安装缓存（`--no-cache-dir`、`rm -rf /var/cache`）

---

## 质量检查清单

生成完成后，自检以下项目：

- [ ] Dockerfile 使用多阶段构建
- [ ] 基础镜像版本已固定（非 latest）
- [ ] 非 root 用户运行
- [ ] HEALTHCHECK 已配置
- [ ] .dockerignore 已生成且排除敏感文件
- [ ] docker-compose.yml 中密码使用环境变量
- [ ] docker-compose.yml 中数据库有 volume 持久化
- [ ] docker-compose.yml 中服务有 healthcheck
- [ ] 服务间使用 `depends_on` + `condition: service_healthy`
- [ ] 开发配置支持 hot reload（volume 挂载）
- [ ] 生产配置最小化镜像体积
- [ ] `.env.example` 已生成
- [ ] `docker compose config` 验证通过

---

## 常见问题排查

### OOM（内存不足）

**症状**：容器被 kill，日志显示 `Killed` 或 `OOMKilled`。

```bash
# 检查容器是否因 OOM 退出
docker inspect <container_id> | grep -A 5 "OOMKilled"

# 查看容器内存使用
docker stats --no-stream

# 解决方案：在 docker-compose.yml 中限制和调整内存
services:
  app:
    deploy:
      resources:
        limits:
          memory: 512M    # 最大内存
        reservations:
          memory: 256M    # 预留内存
```

> Node.js 项目可设置 `--max-old-space-size`：`CMD ["node", "--max-old-space-size=384", "server.js"]`
> Java 项目使用 `-XX:MaxRAMPercentage=75.0` 限制 JVM 堆内存。

### 网络超时 / 服务连接失败

**症状**：应用无法连接数据库，报 `ECONNREFUSED` 或 `Connection timed out`。

```bash
# 检查服务是否在同一网络
docker network inspect app-network

# 检查目标服务是否健康
docker compose ps
docker compose logs postgres

# 常见原因及解决：
# 1. 服务未就绪 → 添加 depends_on + condition: service_healthy
# 2. 连接地址错误 → 使用服务名（如 postgres）而非 localhost
# 3. 端口不匹配 → 容器内部端口（非宿主机映射端口）
# 4. 网络隔离 → 确保服务在同一 network 下
```

### 权限问题

**症状**：`Permission denied`，文件无法写入，`npm install` 报 `EACCES`。

```bash
# 检查容器内用户
docker compose exec app whoami
docker compose exec app id

# 常见原因及解决：
# 1. volume 挂载权限不匹配 → 确保容器用户 UID/GID 与宿主机一致
# 2. 只读文件系统 → 检查是否设置了 read_only: true，按需挂载可写 tmpfs
# 3. node_modules 权限 → 使用匿名 volume 隔离：/app/node_modules
```

### 构建失败

**症状**：`docker build` 报错退出。

```bash
# 查看详细构建日志
docker build --progress=plain --no-cache . 2>&1

# 常见原因：
# 1. lock 文件与 package.json 不同步 → 本地重新 install 并提交 lock 文件
# 2. 网络问题导致依赖下载失败 → 配置 registry mirror 或重试
# 3. 多阶段构建 COPY 的路径不存在 → 检查上一阶段的产物路径
# 4. 基础镜像架构不匹配 → 指定 --platform 或使用多平台镜像
```

### 容器启动后立即退出

```bash
# 查看退出码和日志
docker compose ps -a
docker compose logs app

# 退出码含义：
# 0   — 正常退出（可能 CMD 命令有误，执行完就退出了）
# 1   — 应用错误（查看日志定位）
# 137 — OOM 或被 SIGKILL（见 OOM 章节）
# 139 — 段错误（通常是原生模块问题）
```

---

## 注意事项

- **不要**使用 `latest` 标签，始终固定版本号
- **不要**以 root 用户运行应用进程
- **不要**在 Dockerfile 中写入密钥（用 `ARG` 也不安全）
- **不要**在生产镜像中保留构建工具（gcc、make、dev headers）
- **不要**添加项目未使用的服务到 docker-compose
- 若项目已有 Dockerfile，先 Read 现有配置再决定是增量更新还是重写
- 大型单体项目考虑拆分为多个服务的 docker-compose
- 始终检查 `.env` 不在 `.dockerignore` 之外

---

## 决策流程图

```
检测项目技术栈（语言 + 框架 + 包管理器）
        |
检测依赖服务（数据库 + 缓存 + 搜索 + 消息队列）
        |
是否已有 Docker 配置？
  是 -> Read 现有配置，增量更新
  否 -> 全量生成
        |
选择对应语言的 Dockerfile 模板
        |
生成多阶段 Dockerfile（dev + prod）
        |
组合 docker-compose.yml（仅包含实际依赖）
        |
生成 docker-compose.dev.yml（开发覆盖配置）
        |
生成 .dockerignore
        |
生成 .env.example
        |
验证配置（docker compose config）
  失败 -> 修复后重新验证
  通过 |
        |
安全检查 + 质量检查报告
```

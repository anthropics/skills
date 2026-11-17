---
name: cicd-gen
description: Auto-detect project tech stack and generate GitHub Actions CI/CD workflows with smart caching, deployment targets, and security best practices. Use when user asks to set up CI/CD.
license: MIT
---

# Skill: CI/CD Pipeline 智能生成

自动检测项目类型和技术栈，生成 GitHub Actions workflow 及其他 CI/CD 配置。

## 触发条件

当用户请求以下操作时激活：
- "生成 ci"、"配置流水线"、"pipeline"
- "generate ci/cd"、"github actions"
- "给项目加 ci"、"setup workflow"
- 需要自动化构建、测试、部署流程

---

## 执行步骤

### 第一步：检测项目类型和技术栈

```bash
# Node.js 检测（验证 package.json 有效性）
[ -f package.json ] && grep -q '"name"' package.json && echo "NODE_PROJECT"

# Python 检测
[ -f pyproject.toml ] && grep -qE '\[project\]|\[tool\.' pyproject.toml && echo "PYTHON_PROJECT"
[ -f requirements.txt ] && echo "PYTHON_PROJECT"

# Go 检测
[ -f go.mod ] && grep -q 'module ' go.mod && echo "GO_PROJECT"

# Rust 检测
[ -f Cargo.toml ] && grep -q '\[package\]' Cargo.toml && echo "RUST_PROJECT"

# JS/TS runtime detection
if [ -f bun.lockb ]; then echo "RUNTIME=bun"
elif [ -f pnpm-lock.yaml ]; then echo "RUNTIME=pnpm"
elif [ -f yarn.lock ]; then echo "RUNTIME=yarn"
elif [ -f package.json ]; then echo "RUNTIME=npm"
fi

# Framework detection (JS/TS) — 匹配 dependencies/devDependencies 中的包名
# 框架优先级：Next.js > Nuxt > Remix > Astro > Vite > CRA
grep -E '"(next|nuxt|remix|astro|vite|gatsby)":\s*"' package.json 2>/dev/null

# Python framework detection
grep -rE '"(fastapi|flask|django|streamlit)"' requirements.txt pyproject.toml setup.py 2>/dev/null

# Go framework detection
grep -E '^\s+"(github.com/gin-gonic/gin|github.com/labstack/echo|github.com/gofiber/fiber|github.com/go-chi/chi)' go.mod 2>/dev/null

# Rust framework detection
grep -E '"(actix-web|axum|rocket|warp)"' Cargo.toml 2>/dev/null

# Docker detection
[ -f Dockerfile ] && echo "DOCKER_PROJECT"
[ -f docker-compose.yml ] && echo "DOCKER_COMPOSE"

# Monorepo detection
[ -f lerna.json ] && echo "MONOREPO=lerna"
[ -f turbo.json ] && echo "MONOREPO=turborepo"
[ -f nx.json ] && echo "MONOREPO=nx"
[ -f pnpm-workspace.yaml ] && echo "MONOREPO=pnpm-workspace"
if [ -f "package.json" ] && grep -q '"workspaces"' package.json; then
  echo "MONOREPO=workspaces"
fi
ls packages/*/package.json apps/*/package.json 2>/dev/null
```

根据检测结果确定：
- 语言 + 框架 + 运行时
- 包管理器（bun/pnpm/yarn/npm/pip/cargo/go）
- 是否为 monorepo
- 是否使用 Docker
- 现有 CI 配置（可能已有部分配置）

### 第二步：检查现有 CI 配置

```bash
# Check for existing CI/CD configurations
ls .github/workflows/*.yml .github/workflows/*.yaml 2>/dev/null
ls .gitlab-ci.yml .circleci/config.yml Jenkinsfile 2>/dev/null
ls .github/dependabot.yml renovate.json .renovaterc 2>/dev/null
```

若已有配置，读取并作为基础进行增量更新，而非从零生成。

### 第三步：确定流水线模式

根据项目类型选择合适的流水线模式：

| 项目类型 | 流水线阶段 |
|---------|-----------|
| 前端应用 (Next.js/Vite/React) | lint -> type-check -> test -> build -> deploy |
| 后端 API (Express/FastAPI/Gin) | lint -> test -> build -> docker-push -> deploy |
| 全栈 (Next.js full-stack) | lint -> type-check -> test -> build -> deploy |
| 库/SDK (npm package) | lint -> test -> build -> publish |
| CLI 工具 | lint -> test -> build -> release |
| Monorepo | 路径过滤 -> 各子项目独立流水线 |
| Docker 项目 | lint -> test -> docker-build -> docker-push -> deploy |
| 静态站点 | lint -> build -> deploy |

### 第四步：生成 GitHub Actions Workflow

在 `.github/workflows/` 目录下生成 workflow 文件。

---

## Workflow 模板

### Node.js / Bun 项目

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

permissions:
  contents: read

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: oven-sh/setup-bun@735343b667d82a9b6e7e29e1a5a61cce62063358 # v2.0.1 (pinned SHA)
        with:
          bun-version: latest

      - name: Install dependencies
        run: bun install --frozen-lockfile

      - name: Lint
        run: bun run lint

      - name: Type check
        run: bun run type-check

      - name: Test
        run: bun test

      - name: Build
        run: bun run build
```

**npm 变体（替换 bun 部分）：**
```yaml
      - uses: actions/setup-node@60edb5dd545a775178f52524783378180af0d1f8 # v4.0.3 (pinned SHA)
        with:
          node-version: 20
          cache: 'npm'

      - name: Install dependencies
        run: npm ci
```

**pnpm 变体：**
```yaml
      - uses: pnpm/action-setup@a7487c7e89a18df77c0e7081cb187228765167f8 # v4.0.0 (pinned SHA)
        with:
          version: 9

      - uses: actions/setup-node@60edb5dd545a775178f52524783378180af0d1f8 # v4.0.3 (pinned SHA)
        with:
          node-version: 20
          cache: 'pnpm'

      - name: Install dependencies
        run: pnpm install --frozen-lockfile
```

### Python 项目

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

permissions:
  contents: read

jobs:
  ci:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.11', '3.12']

    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: actions/setup-python@65d7f2d534ac1bc67fcd62888c5f4f3d2cb2b236 # v5.2.0 (pinned SHA)
        with:
          python-version: ${{ matrix.python-version }}
          cache: 'pip'

      - name: Install dependencies
        run: |
          python -m pip install --upgrade pip
          pip install -r requirements.txt
          pip install -r requirements-dev.txt

      - name: Lint
        run: |
          ruff check .
          ruff format --check .

      - name: Type check
        # NOTE: adjust the path to match your project structure (e.g., mypy src/ tests/)
        run: mypy src/

      - name: Test
        # NOTE: coverage path should match your project layout
        # Recommended: configure in pyproject.toml instead:
        #   [tool.pytest.ini_options]
        #   addopts = "--cov=src --cov-report=xml"
        #   [tool.coverage.run]
        #   source = ["src"]
        run: pytest --cov=src --cov-report=xml

      - name: Upload coverage
        uses: codecov/codecov-action@e28ff129e5465c2c0dcc6f003fc735cb6ae0c673 # v4.5.0 (pinned SHA)
        with:
          token: ${{ secrets.CODECOV_TOKEN }}
```

**uv 变体（替换 pip 部分）：**
```yaml
      - uses: astral-sh/setup-uv@d4b2f3b6ecc6e67c4457f6d3e41ec42d3d0fcb86 # v4.1.0 (pinned SHA)

      - name: Install dependencies
        run: uv sync --frozen

      - name: Lint
        run: |
          uv run ruff check .
          uv run ruff format --check .
```

### Go 项目

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

permissions:
  contents: read

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: actions/setup-go@0a12ed9d6a96ab950c8f026ed9f722fe0da7ef32 # v5.0.2 (pinned SHA)
        with:
          go-version-file: go.mod
          cache: true

      - name: Lint
        uses: golangci/golangci-lint-action@aaa42aa0628b4ae2578232a66b541047968fac86 # v6.1.0 (pinned SHA)
        with:
          version: latest

      - name: Test
        run: go test -race -coverprofile=coverage.out ./...

      - name: Build
        run: go build -v ./...
```

### Rust 项目

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

permissions:
  contents: read

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: dtolnay/rust-toolchain@7b1c307e0dcbda6122208f10795a713336a9b35a # stable (pinned SHA)
        with:
          components: clippy, rustfmt

      - uses: Swatinem/rust-cache@82a92a6e8fbeee089604da2575dc567ae9ddeaab # v2.7.3 (pinned SHA)

      - name: Format check
        run: cargo fmt --all -- --check

      - name: Lint
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Test
        run: cargo test --all-features

      - name: Build
        run: cargo build --release
```

### Docker 项目

```yaml
name: Docker Build & Push

on:
  push:
    branches: [main]
    tags: ['v*']

permissions:
  contents: read
  packages: write

jobs:
  docker:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: docker/setup-buildx-action@885d1462b80bc1c1c7f0b00334ad271f09369c55 # v3.6.1 (pinned SHA)

      # Registry options (uncomment the one you need):
      #
      # GHCR (GitHub Container Registry) — default, uses GITHUB_TOKEN
      # Docker Hub — set DOCKERHUB_USERNAME and DOCKERHUB_TOKEN secrets
      #   registry: (omit for Docker Hub)
      #   username: ${{ secrets.DOCKERHUB_USERNAME }}
      #   password: ${{ secrets.DOCKERHUB_TOKEN }}
      # AWS ECR — use aws-actions/amazon-ecr-login instead (see ECR section below)
      # Quay.io:
      #   registry: quay.io
      #   username: ${{ secrets.QUAY_USERNAME }}
      #   password: ${{ secrets.QUAY_PASSWORD }}
      - uses: docker/login-action@343f7c4344506bcbf9b4de18042ae17996df046d # v3.3.0 (pinned SHA)
        with:
          registry: ghcr.io
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}

      - uses: docker/metadata-action@8e5442c4ef9f78752691e2d8f8d19755c6f78e81 # v5.5.1 (pinned SHA)
        id: meta
        with:
          # Change the image name to match your registry:
          #   Docker Hub: docker.io/${{ github.repository }}
          #   Quay.io:    quay.io/${{ github.repository }}
          images: ghcr.io/${{ github.repository }}
          tags: |
            type=ref,event=branch
            type=semver,pattern={{version}}
            type=sha

      - uses: docker/build-push-action@4a13e500e55cf31b7a5d59a38ab2040ab0f42f56 # v6.9.0 (pinned SHA)
        with:
          context: .
          push: ${{ github.event_name != 'pull_request' }}
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
```

---

## 部署目标配置

### Vercel 部署

```yaml
  deploy:
    needs: ci
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    permissions:
      contents: read
      deployments: write
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      # 推荐方案：直接使用 Vercel CLI（而非第三方 Action）
      - uses: oven-sh/setup-bun@735343b667d82a9b6e7e29e1a5a61cce62063358 # v2.0.1 (pinned SHA)

      - name: Deploy to Vercel
        run: |
          bun add -g vercel
          vercel deploy --prod --token=${{ secrets.VERCEL_TOKEN }}
```

> ⚠️ Action 版本需定期更新。建议：
> - 使用 Vercel 官方 CLI 而非第三方 Action（如 `amondnet/vercel-action`）
> - 若仍使用第三方 Action，请 pin 到最新 commit SHA 并注释版本号

**所需 Secrets：**
- `VERCEL_TOKEN` — Vercel API Token
- `VERCEL_ORG_ID` — Vercel Organization ID
- `VERCEL_PROJECT_ID` — Vercel Project ID

### Netlify 部署

```yaml
  deploy:
    needs: ci
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    permissions:
      contents: read
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - name: Build
        run: bun run build

      - uses: nwtgck/actions-netlify@4cbaf4c08f1a7bfa537d6113472ef4424e4eb654 # v3.0.0 (pinned SHA)
        with:
          publish-dir: './dist'
          production-branch: main
          deploy-message: 'Deploy from GitHub Actions'
        env:
          NETLIFY_AUTH_TOKEN: ${{ secrets.NETLIFY_AUTH_TOKEN }}
          NETLIFY_SITE_ID: ${{ secrets.NETLIFY_SITE_ID }}
```

**所需 Secrets：**
- `NETLIFY_AUTH_TOKEN` — Netlify Personal Access Token
- `NETLIFY_SITE_ID` — Netlify Site ID

### Docker Registry 部署（AWS ECR）

```yaml
  deploy:
    needs: ci
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    permissions:
      id-token: write
      contents: read
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: aws-actions/configure-aws-credentials@e3dd6a429d7300a6a4c196c26e071d42e0343502 # v4.0.2 (pinned SHA)
        with:
          role-to-assume: ${{ secrets.AWS_ROLE_ARN }}
          aws-region: us-east-1

      - uses: aws-actions/amazon-ecr-login@062b18b96a7aff071d4dc91bc00c4c1a0945b076 # v2.0.1 (pinned SHA)
        id: ecr

      - uses: docker/build-push-action@4a13e500e55cf31b7a5d59a38ab2040ab0f42f56 # v6.9.0 (pinned SHA)
        with:
          context: .
          push: true
          tags: ${{ steps.ecr.outputs.registry }}/${{ github.repository }}:${{ github.sha }}
          cache-from: type=gha
          cache-to: type=gha,mode=max
```

### npm Publish

```yaml
  publish:
    needs: ci
    runs-on: ubuntu-latest
    # 添加 repository 检查防止 fork 意外发布
    if: >-
      github.event_name == 'push' &&
      startsWith(github.ref, 'refs/tags/v') &&
      github.repository == '${{ github.repository }}'
    permissions:
      contents: read
      id-token: write
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: actions/setup-node@60edb5dd545a775178f52524783378180af0d1f8 # v4.0.3 (pinned SHA)
        with:
          node-version: 20
          registry-url: 'https://registry.npmjs.org'

      - name: Install & Build
        run: |
          npm ci
          npm run build

      - name: Preview publish contents
        run: npm pack --dry-run

      - name: Publish
        run: npm publish --provenance --access public
        env:
          NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

> ⚠️ npm publish 安全建议：
> - 添加 `github.repository` 检查，防止 fork 仓库误触发发布
> - 建议在 publish 前添加 `npm pack --dry-run` 预览发布内容
> - 使用 npm provenance（`--provenance`）增强供应链安全
> - 建议配合 GitHub Environment 的 manual approval 使用

### GitHub Pages 部署

```yaml
  deploy:
    needs: ci
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    permissions:
      pages: write
      id-token: write
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - name: Build
        run: bun run build

      - uses: actions/upload-pages-artifact@56afc609e74202658d3ffba0e8f6dda462b719fa # v3.0.1 (pinned SHA)
        with:
          path: './dist'

      - uses: actions/deploy-pages@d6db90164ac5ed86f2b6aed7e0febac553fd0d28 # v4.0.5 (pinned SHA)
        id: deployment
```

---

## 缓存策略配置

### 缓存策略速查表

| 技术栈 | 缓存方式 | 缓存路径 / Key |
|-------|---------|---------------|
| Bun | `setup-bun` 内置缓存 | `bun.lockb` 的内容哈希，路径由 bun 自动管理，使用 `setup-bun` action 的内置缓存 |
| npm | `actions/setup-node` + `cache: 'npm'` | `package-lock.json` 的内容哈希，`~/.npm` |
| pnpm | `actions/setup-node` + `cache: 'pnpm'` | `pnpm-lock.yaml` 的内容哈希，`setup-node` 的 `cache: pnpm` 自动处理 |
| yarn | `actions/setup-node` + `cache: 'yarn'` | `yarn.lock` 的内容哈希，`setup-node` 的 `cache: yarn` 自动处理 |
| pip | `actions/setup-python` + `cache: 'pip'` | 自动管理，key: `requirements*.txt` |
| Go | `actions/setup-go` + `cache: true` | 自动管理，key: `go.sum` |
| Rust | `Swatinem/rust-cache` (SHA pinned) | `target/`，key: `Cargo.lock` |
| Docker | `docker/build-push-action` + `cache-from/to: type=gha` | GitHub Actions cache |
| Gradle | `actions/setup-java` + `cache: 'gradle'` | `~/.gradle/caches` |
| Maven | `actions/setup-java` + `cache: 'maven'` | `~/.m2/repository` |

### Bun 缓存配置示例

```yaml
      - uses: oven-sh/setup-bun@735343b667d82a9b6e7e29e1a5a61cce62063358 # v2.0.1 (pinned SHA)
        with:
          bun-version: latest

      # bun install automatically uses lockfile-based caching
      - name: Install dependencies
        run: bun install --frozen-lockfile
```

### 自定义缓存（通用）

```yaml
      - uses: actions/cache@0c45773b623bea8c8e75f6c82b208c3cf94ea4f9 # v4.0.2 (pinned SHA)
        with:
          path: |
            ~/.cache/some-tool
            .build-cache
          key: ${{ runner.os }}-tool-${{ hashFiles('**/lockfile') }}
          restore-keys: |
            ${{ runner.os }}-tool-
```

---

## Monorepo 检测和路径过滤

### Monorepo 检测逻辑

```bash
# Turborepo
[ -f turbo.json ] && echo "MONOREPO=turborepo"

# Nx
[ -f nx.json ] && echo "MONOREPO=nx"

# Lerna
[ -f lerna.json ] && echo "MONOREPO=lerna"

# pnpm workspace
[ -f pnpm-workspace.yaml ] && echo "MONOREPO=pnpm-workspace"

# npm/yarn/bun workspaces (via package.json "workspaces" field)
if [ -f "package.json" ] && grep -q '"workspaces"' package.json; then
  echo "MONOREPO=workspaces"
fi

# General multi-package detection (fallback)
ls packages/*/package.json apps/*/package.json 2>/dev/null
```

### 路径过滤 Workflow

```yaml
name: CI - Web App

on:
  push:
    branches: [main]
    paths:
      - 'apps/web/**'
      - 'packages/shared/**'
      - 'package.json'
      - 'bun.lockb'
  pull_request:
    branches: [main]
    paths:
      - 'apps/web/**'
      - 'packages/shared/**'

jobs:
  ci-web:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

      - uses: oven-sh/setup-bun@735343b667d82a9b6e7e29e1a5a61cce62063358 # v2.0.1 (pinned SHA)

      - run: bun install --frozen-lockfile

      # NOTE: --filter syntax differs by tool:
      #   bun workspace:  bun run --filter=web <script>
      #   Turborepo:      bunx turbo run <task> --filter=web
      #   pnpm workspace: pnpm --filter web <script>
      #   npm workspace:  npm run <script> -w web
      - name: Lint & Test (web)
        run: |
          bun run --filter=web lint
          bun run --filter=web test

      - name: Build (web)
        run: bun run --filter=web build
```

### Turborepo Workflow

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)
        with:
          fetch-depth: 2

      - uses: oven-sh/setup-bun@735343b667d82a9b6e7e29e1a5a61cce62063358 # v2.0.1 (pinned SHA)

      - run: bun install --frozen-lockfile

      - name: Build affected
        run: bunx turbo run build --filter='...[HEAD^]'

      - name: Test affected
        run: bunx turbo run test --filter='...[HEAD^]'
```

---

## Dependabot / Renovate 配置

### dependabot.yml

```yaml
# .github/dependabot.yml
version: 2
updates:
  # GitHub Actions
  - package-ecosystem: "github-actions"
    directory: "/"
    schedule:
      interval: "weekly"
    groups:
      actions:
        patterns:
          - "*"

  # npm / bun
  - package-ecosystem: "npm"
    directory: "/"
    schedule:
      interval: "weekly"
    groups:
      production:
        dependency-type: "production"
      development:
        dependency-type: "development"
    ignore:
      - dependency-name: "*"
        update-types: ["version-update:semver-major"]

  # pip
  - package-ecosystem: "pip"
    directory: "/"
    schedule:
      interval: "weekly"

  # Go modules
  - package-ecosystem: "gomod"
    directory: "/"
    schedule:
      interval: "weekly"

  # Docker
  - package-ecosystem: "docker"
    directory: "/"
    schedule:
      interval: "weekly"

  # Cargo (Rust)
  - package-ecosystem: "cargo"
    directory: "/"
    schedule:
      interval: "weekly"
```

仅生成当前项目所需的 ecosystem 条目。例如 Node.js 项目只需 `github-actions` + `npm`。

**更新频率建议（按依赖类型）：**

| 依赖类型 | 建议频率 | 说明 |
|---------|---------|------|
| 安全更新 | 立即（自动） | Dependabot Security Alerts 默认启用，无需额外配置 |
| GitHub Actions | `weekly` | Action 更新频率较低，weekly 足够 |
| 生产依赖（production） | `weekly` | 及时获取 bugfix 和安全补丁 |
| 开发依赖（development） | `monthly` | 更新频率低优先级，减少 PR 噪音 |

> 提示：可在 `groups` 中按 `dependency-type` 分组，对 production 和 development 依赖使用不同策略。

### Renovate 配置（可选替代）

```json
{
  "$schema": "https://docs.renovatebot.com/renovate-schema.json",
  "extends": [
    "config:recommended",
    "group:allNonMajor",
    ":semanticCommits"
  ],
  "schedule": ["before 6am on Monday"],
  "automerge": true,
  "automergeType": "pr",
  "packageRules": [
    {
      "matchUpdateTypes": ["minor", "patch"],
      "automerge": true
    },
    {
      "matchUpdateTypes": ["major"],
      "automerge": false
    }
  ]
}
```

---

## 安全最佳实践

### 环境变量与 Secrets 的区别

在 GitHub Actions 中，`env` 和 `secrets` 是两种不同的变量传递机制：

```yaml
# env: 非敏感的配置变量，明文存储，会出现在日志中
env:
  NODE_ENV: production
  CI: true

jobs:
  build:
    runs-on: ubuntu-latest
    # Job 级别的 env
    env:
      DATABASE_URL: postgres://localhost:5432/testdb

    steps:
      - name: Build
        # Step 级别的 env
        env:
          VITE_API_URL: https://api.example.com
        run: bun run build
```

```yaml
# secrets: 敏感信息，加密存储，日志中自动脱敏（显示为 ***）
# 在 GitHub repo Settings > Secrets and variables > Actions 中配置
steps:
  - name: Deploy
    env:
      # 通过 env 将 secret 传递给进程
      API_KEY: ${{ secrets.API_KEY }}
    run: ./deploy.sh

  - name: Docker login
    uses: docker/login-action@343f7c4344506bcbf9b4de18042ae17996df046d # v3.3.0 (pinned SHA)
    with:
      # 直接在 with 中引用 secret
      password: ${{ secrets.GITHUB_TOKEN }}
```

**使用原则：**
- `env`：构建配置、公开的 API 地址、feature flags 等非敏感值
- `secrets`：API keys、tokens、passwords、private keys 等敏感值
- 如果不确定是否敏感，一律使用 `secrets`
- 避免在 `run` 命令中直接内联 `${{ secrets.XXX }}`，应通过 `env` 映射后使用 `$VAR_NAME`

### Secrets 管理

1. **永远不要**在 workflow 文件中硬编码 secrets
2. 使用 `${{ secrets.XXX }}` 引用 GitHub Secrets
3. 敏感操作使用 OIDC（`id-token: write`）代替长期凭证
4. 定期轮换所有 secrets

### 权限最小化

```yaml
# Global: restrict all permissions by default
permissions:
  contents: read

# Per-job: only grant what's needed
jobs:
  deploy:
    permissions:
      contents: read
      deployments: write
      # Only add id-token for OIDC
      id-token: write
```

**权限参考表：**

| 操作 | 所需权限 |
|-----|---------|
| 读取代码 | `contents: read` |
| 推送代码/tag | `contents: write` |
| 创建 PR 评论 | `pull-requests: write` |
| 发布 Docker 到 GHCR | `packages: write` |
| 部署 GitHub Pages | `pages: write` + `id-token: write` |
| OIDC 认证（AWS/GCP） | `id-token: write` |

### 第三方 Action 安全

```yaml
# GOOD: Pin to specific commit SHA (recommended)
- uses: actions/checkout@b4ffde65f46336ab88eb53be808477a3936bae11 # v4.1.1 (pinned SHA)

# BAD: Pin to major version tag — vulnerable to tag mutation attacks
- uses: actions/checkout@v4

# WORSE: Use latest or branch — vulnerable to supply chain attacks
- uses: actions/checkout@main
```

### Branch Protection 建议

生成 workflow 后，建议用户配置 Branch Protection Rules：
- Require status checks to pass before merging
- Require pull request reviews
- Require signed commits (可选)
- Do not allow bypassing the above settings

---

## 可选生成：GitLab CI

如果用户使用 GitLab，生成 `.gitlab-ci.yml`：

```yaml
stages:
  - lint
  - test
  - build
  - deploy

variables:
  BUN_INSTALL: "$CI_PROJECT_DIR/.bun"

cache:
  key: $CI_COMMIT_REF_SLUG
  paths:
    - node_modules/
    - .bun/

lint:
  stage: lint
  image: oven/bun:latest
  script:
    - bun install --frozen-lockfile
    - bun run lint

test:
  stage: test
  image: oven/bun:latest
  script:
    - bun install --frozen-lockfile
    - bun test

build:
  stage: build
  image: oven/bun:latest
  script:
    - bun install --frozen-lockfile
    - bun run build
  artifacts:
    paths:
      - dist/

deploy:
  stage: deploy
  only:
    - main
  script:
    - echo "Deploy step — customize per target"
```

---

## 可选生成：CircleCI

```yaml
version: 2.1

orbs:
  node: circleci/node@5

jobs:
  ci:
    docker:
      - image: oven/bun:latest
    steps:
      - checkout
      - run: bun install --frozen-lockfile
      - run: bun run lint
      - run: bun test
      - run: bun run build

workflows:
  main:
    jobs:
      - ci
```

---

## 质量检查清单

生成完成后，自检以下项目：

- [ ] workflow 文件语法正确 — 运行 `actionlint .github/workflows/*.yml`，无报错即通过
- [ ] 包管理器与项目实际使用的一致 — 检查 lockfile 类型（bun.lockb / package-lock.json / pnpm-lock.yaml / yarn.lock）
- [ ] lockfile 使用了 `--frozen-lockfile` 或 `ci` 模式 — 搜索 `install` 步骤，确认包含对应 flag
- [ ] 缓存策略已配置且 key 正确 — 确认 setup-* action 的 `cache` 参数或独立 cache step 存在
- [ ] 全局 `permissions` 设置为 `contents: read` — 检查 workflow 顶层是否有 `permissions:` 块
- [ ] 使用了 `concurrency` 避免重复运行 — 检查 workflow 顶层是否有 `concurrency:` 块
- [ ] PR 和 push 触发条件合理 — 确认 `on.push.branches` 和 `on.pull_request.branches` 已设置
- [ ] Secrets 引用正确，无硬编码 — 搜索文件中是否有明文 token/key/password 字符串
- [ ] Action 版本已 pin 到 commit SHA — 搜索 `uses:`，确认格式为 `action@<40-char-sha> # vX.Y.Z (pinned SHA)`
- [ ] monorepo 项目配置了路径过滤 — 检查 `on.push.paths` / `on.pull_request.paths` 是否按子项目过滤
- [ ] 部署 job 有正确的条件守卫 — 检查 deploy job 的 `if:` 条件包含分支或标签判断
- [ ] dependabot.yml 仅包含项目实际使用的 ecosystem — 对照项目文件，删除多余的 ecosystem 条目

### 本地验证 workflow 文件

```bash
# 安装 actionlint
# macOS
brew install actionlint

# 或通过 Go
go install github.com/rhysd/actionlint/cmd/actionlint@latest

# 验证所有 workflow 文件
actionlint .github/workflows/*.yml

# 也可以在 CI 中运行
# - uses: rhysd/actionlint@v1 (在 workflow 中添加 lint 步骤)
```

---

## 决策流程图

```
检测项目类型和技术栈
        |
确定包管理器和运行时
        |
是否已有 CI 配置？
  是 -> 增量更新模式（补充缺失部分）
  否 -> 全量生成模式
        |
是否为 Monorepo？
  是 -> 生成路径过滤 + 各子项目 workflow
  否 -> 生成单一 workflow
        |
选择流水线模式（lint -> test -> build -> deploy）
        |
是否需要部署？
  是 -> 询问部署目标（Vercel/Netlify/Docker/npm/AWS）
  否 -> 仅生成 CI workflow
        |
生成 .github/workflows/ci.yml
        |
是否需要 dependabot？
  是 -> 生成 .github/dependabot.yml
  否 -> 跳过
        |
验证 workflow 语法（actionlint）
  失败 -> 修复后重新验证
  通过 |
        |
输出结果 + 配置说明 + 所需 Secrets 清单
```

---

## 注意事项

- **不要**生成项目不需要的步骤（如 Python 项目不需要 type-check，除非有 mypy）
- **不要**使用过时的 Action 版本，始终使用最新 stable 版本
- **不要**在 workflow 中安装全局依赖，优先使用 `bunx` / `npx`
- **不要**忽略 `--frozen-lockfile`，CI 中必须使用锁定依赖
- 优先使用 bun 作为 JS/TS 运行时（遵循用户偏好）
- 大型 monorepo 建议使用 Turborepo / Nx 的增量构建特性
- 生成后提醒用户配置所需的 GitHub Secrets
- 若项目有 Dockerfile，额外生成 Docker build workflow

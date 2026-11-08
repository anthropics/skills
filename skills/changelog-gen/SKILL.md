---
name: changelog-gen
description: Generate human-readable CHANGELOG from git history using conventional commits, with Keep a Changelog format. Use when user asks to create or update a changelog.
license: MIT
---

# CHANGELOG Gen Skill

## 概述

智能 CHANGELOG 生成器 — 从 git 历史中提取 conventional commits，按类别分组，生成人类可读的 Keep a Changelog 格式变更日志。

## 触发条件

当用户说出以下内容时激活：
- "生成 changelog"
- "generate changelog"
- "更新变更日志"
- "what changed"
- "有什么变更"
- "changelog since..."

## 执行流程

### 第一步：确定 Commit 范围

按以下决策树自动推断范围，避免不必要的询问：

1. **用户已指定范围** → 直接使用用户输入（如 `v1.0.0..v2.0.0`、`-n 10`、`--after="2024-01-01"`）
2. **用户未指定范围** → 自动检测 git tag：
   ```bash
   git describe --tags --abbrev=0 2>/dev/null
   ```
   - **存在 tag** → 自动使用 `<last-tag>..HEAD`，告知用户所选范围
   - **不存在 tag** → 询问用户，并提供最近 commit 列表作为参考：
     ```bash
     # 列出最近 20 个 commit 供用户选择起点
     git log -n 20 --oneline
     ```
     建议用户指定起始 commit hash 或 commit 数量（如 `-n 10`）

#### 支持的范围格式

```bash
# 从某个 tag 到 HEAD
git log v1.0.0..HEAD --oneline

# 最近 N 个 commit
git log -n 20 --oneline

# 两个 tag 之间
git log v1.0.0..v2.0.0 --oneline

# 基于日期
git log --after="2024-01-01" --oneline
```

### 第二步：读取 Git Log（详细格式）

使用以下命令获取结构化 commit 信息：

> ⚠️ 注意：commit message 中可能包含特殊字符（引号、反斜杠等），
> 解析时需正确转义。建议使用 `%x00` (null byte) 作为字段分隔符，
> 或使用 git log 的 `--format=tformat:` 确保每条记录正确分隔。

```bash
# 主命令 — 获取完整的 commit 信息（使用 null byte 分隔，避免特殊字符干扰）
git log <range> --format="%H%x00%an%x00%ai%x00%s%x00%b%x00---END---"

# 简化版 — 仅获取 subject 行（使用 null byte 分隔）
git log <range> --format="%h%x00%s%x00%an%x00%ai" --no-merges

# 获取 merge commit（单独处理）
git log <range> --merges --format="%h%x00%s%x00%an%x00%ai"
```

#### Merge commit 过滤策略

默认使用 `--no-merges` 过滤 merge commit，但以下场景应**包含** merge commit：

- PR / MR 的 merge commit 中包含有价值的描述（如 squash merge 的汇总信息）
- 项目使用 merge commit 作为主要变更记录（非 conventional commit 工作流）

```bash
# 默认：过滤 merge commit
git log <range> --no-merges --format="%h%x00%s%x00%an%x00%ai"

# 可选：包含 merge commit（当 PR 描述有价值时）
git log <range> --format="%h%x00%s%x00%an%x00%ai"
```

> 💡 判断方法：先用 `git log <range> --merges --oneline` 查看 merge commit 内容，如果仅为自动生成的 `Merge branch 'xxx'` 则过滤；如果包含有意义的变更描述则保留。

### 第三步：按 Conventional Commits 分类

#### 分类规则表

| 前缀 | CHANGELOG 分类 | 说明 | 显示优先级 |
|------|---------------|------|-----------|
| `feat:` / `feat(scope):` | Added | 新功能 | 1 |
| `fix:` / `fix(scope):` | Fixed | Bug 修复 | 2 |
| `perf:` / `perf(scope):` | Performance | 性能优化 | 3 |
| `refactor:` / `refactor(scope):` | Changed | 重构 | 4 |
| `docs:` / `docs(scope):` | Documentation | 文档变更 | 5 |
| `test:` / `test(scope):` | Tests | 测试相关 | 6 |
| `chore:` / `chore(scope):` | Maintenance | 构建/工具/依赖 | 7 |
| `style:` / `style(scope):` | Style | 代码格式（不影响功能） | 8 |
| `ci:` / `ci(scope):` | CI/CD | 持续集成 | 9 |
| `build:` / `build(scope):` | Build | 构建系统 | 10 |
| `revert:` | Reverted | 回滚 | 3 |
| 无前缀 | Other | 未分类（保留原始信息） | 99 |

#### 解析逻辑

```
正则匹配 subject 行（Conventional Commits）：
^(feat|fix|perf|refactor|docs|test|chore|style|ci|build|revert)(\(.+\))?(!)?:\s*(.+)$

捕获组：
- group 1: type（类型）
- group 2: scope（范围，可选）
- group 3: !（breaking change 标记，可选）
- group 4: description（描述）
```

#### 非标准 commit 格式处理

不是所有项目都使用 Conventional Commits。在解析前，先检测项目实际的 commit 风格：

```bash
# 采样最近 50 个 commit，统计符合 conventional commit 格式的比例
git log -n 50 --format="%s" | grep -cE '^(feat|fix|perf|refactor|docs|test|chore|style|ci|build|revert)(\(.+\))?!?:'
```

- **≥ 70% 符合** → 按 Conventional Commits 解析
- **< 70%** → 提示用户项目未使用标准格式，按以下扩展规则处理：

##### 扩展格式支持

| 格式 | 正则 | 处理方式 |
|------|------|---------|
| `[JIRA-123] description` | `^\[([A-Z]+-\d+)\]\s*(.+)$` | 提取 ticket ID 作为 scope，描述归入 Other |
| `#123 description` | `^#(\d+)\s+(.+)$` | 提取 issue/PR 号作为引用 |
| `(tag) description` | `^\((\w+)\)\s*(.+)$` | 尝试将 tag 映射到分类表 |
| 纯文本 | 不匹配以上任何格式 | 归入 **Other**，保留原始 commit message |

> 💡 归入 Other 的条目保留原始 commit message 全文，不做改写，确保信息不丢失。

### 第四步：检测 Breaking Changes

Breaking changes 必须醒目标注。检测方式：

1. **Subject 中的 `!` 标记**：`feat!: remove legacy API`
2. **Body 中的 `BREAKING CHANGE:` 关键字**：
   ```
   feat: update auth system

   BREAKING CHANGE: JWT token format changed, all existing tokens will be invalidated.
   ```
3. **Body 中的 `BREAKING-CHANGE:` 关键字**（带连字符的变体）
4. **Footer 中的 `BREAKING CHANGE:` 或 `BREAKING-CHANGE:`**

```bash
# 快速扫描包含 breaking change 的 commit（macOS/BSD grep 兼容）
git log <range> --format="%H %s%n%b" | grep -i -E "BREAKING[-_ ]CHANGE|BREAKING CHANGE|^[a-z]*!:"
```

> ⚠️ 注意：正则中 `BREAKING.CHANGE` 的 `.` 会匹配任意字符，导致误匹配（如 `BREAKINGXCHANGE`）。
> 上面已修正为 `BREAKING[-_ ]CHANGE|BREAKING CHANGE`，仅匹配连字符、下划线、空格分隔的合法变体。

### 第五步：自动检测版本号

按优先级依次检查以下文件：

```bash
# 1. package.json (Node.js)
cat package.json 2>/dev/null | grep '"version"' | head -1
# 提取: "version": "1.2.3" → 1.2.3
# ✅ 验证格式：提取结果须匹配 ^\d+\.\d+\.\d+(-[\w.]+)?$

# 2. pyproject.toml (Python)
grep -E '^\s*version\s*=\s*["'"'"']' pyproject.toml 2>/dev/null | head -1 | sed -E "s/.*version\s*=\s*[\"']//" | sed -E "s/[\"'].*//"
# 提取: version = "1.2.3" 或 version = '1.2.3'（支持前导空格和单双引号）→ 1.2.3
# ✅ 验证格式：提取结果须匹配 ^\d+\.\d+\.\d+(-[\w.]+)?$

# 3. Cargo.toml (Rust)
grep -E '^\s*version\s*=\s*["'"'"']' Cargo.toml 2>/dev/null | head -1 | sed -E "s/.*version\s*=\s*[\"']//" | sed -E "s/[\"'].*//"
# 提取: version = "1.2.3" 或 version = '1.2.3'（支持前导空格和单双引号）→ 1.2.3
# ✅ 验证格式：提取结果须匹配 ^\d+\.\d+\.\d+(-[\w.]+)?$

# 4. build.gradle / build.gradle.kts (Java/Kotlin)
cat build.gradle 2>/dev/null | grep 'version' | head -1
# ✅ 验证格式：提取结果须匹配 ^\d+\.\d+\.\d+(-[\w.]+)?$

# 5. pubspec.yaml (Flutter/Dart)
cat pubspec.yaml 2>/dev/null | grep '^version:' | head -1
# ✅ 验证格式：提取结果须匹配 ^\d+\.\d+\.\d+(\+\d+)?$

# 6. Git tag（最近的 tag）
git describe --tags --abbrev=0 2>/dev/null
# ✅ 验证格式：提取结果须匹配 ^v?\d+\.\d+\.\d+(-[\w.]+)?$
```

> ⚠️ 每个检测源提取的版本号都必须通过格式验证，不合法的值应跳过并尝试下一个来源。

```bash
# 7. 降级方案：如果以上所有来源都未检测到合法版本号
# ❗ 必须明确询问用户指定版本号，不得静默使用日期版本
# 仅在用户明确同意后，才可使用日期格式作为版本号：
date +"%Y.%m.%d"
# ⚠️ 日期格式版本（如 2024.03.08）不符合 semver 规范，需提醒用户确认
```

如果检测到版本号，建议用户确认或修改。

#### 日期格式规范

本文件中涉及两种日期场景，需明确区分：

| 场景 | 格式 | 示例 | 说明 |
|------|------|------|------|
| **条目日期**（版本发布日期） | `YYYY-MM-DD` | `2024-03-08` | 跟在版本号后面，如 `## [1.2.0] - 2024-03-08` |
| **日期版本号**（不推荐） | `YYYY.MM.DD` | `2024.03.08` | 仅作为无 semver 版本时的降级方案，不符合 semver 规范 |

> ⚠️ 不要混淆这两种日期。条目日期使用 **ISO 8601 短格式**（`YYYY-MM-DD`，用连字符分隔），始终必须。日期版本号用点号分隔，仅在用户明确同意时使用。

### 第六步：生成 CHANGELOG 条目

#### 输出模板（Keep a Changelog 格式）

```markdown
## [版本号] - YYYY-MM-DD

### Breaking Changes

- **scope**: 描述 breaking change 的具体影响 ([commit-hash])
  - Migration: 迁移指引（如果 commit body 中有提供）

### Added

- **scope**: 功能描述，用人类可读的语言改写 ([commit-hash])
- 另一个新功能 ([commit-hash])

### Fixed

- **scope**: 修复了什么问题 ([commit-hash])

### Performance

- **scope**: 优化了什么 ([commit-hash])

### Changed

- **scope**: 重构/变更了什么 ([commit-hash])

### Documentation

- 更新了什么文档 ([commit-hash])

### Maintenance

- 依赖更新、构建工具变更等 ([commit-hash])
```

#### 条目改写规则

- 去掉 conventional commit 前缀（`feat:`, `fix:` 等）
- 首字母大写
- 如果有 scope，以 `**scope**:` 开头
- 用完整句子描述变更，而不是机械复制 commit message
- 合并相关的小 commit（如多次修复同一个功能的 commit）
- commit hash 使用短格式（7 位），链接到仓库（如果能检测到 remote URL）

#### 改写示例对比

| 原始 commit message | 改写后的 CHANGELOG 条目 |
|---------------------|------------------------|
| `fix(auth): handle null token` | **auth**: 修复认证模块中 token 为空时的崩溃问题 |
| `feat: add retry logic` | 新增请求失败自动重试机制（最多 3 次） |
| `perf(db): optimize query plan` | **db**: 优化数据库查询计划，减少慢查询 |
| `fix: typo in error msg` + `fix: another typo` | 修复多处错误提示中的拼写问题 _(合并相关 commit)_ |
| `refactor(api)!: change response format` | **api**: 重构 API 响应格式为统一的 envelope 结构 |

#### 检测仓库 URL（用于生成链接）

```bash
# 获取 remote URL 并转换为 HTTPS 格式
git remote get-url origin 2>/dev/null
# git@github.com:user/repo.git → https://github.com/user/repo
# https://github.com/user/repo.git → https://github.com/user/repo
```

如果检测到仓库 URL，commit hash 生成为链接格式：
```markdown
- 功能描述 ([abc1234](https://github.com/user/repo/commit/abc1234))
```

### 第七步：追加 vs 新建 CHANGELOG

#### 判断逻辑

```bash
# 检查是否存在 CHANGELOG 文件
ls CHANGELOG.md CHANGELOG changelog.md 2>/dev/null
```

**如果 CHANGELOG.md 已存在：**
1. 读取现有内容
2. **备份原文件**：`cp CHANGELOG.md CHANGELOG.md.bak`
3. 找到第一个匹配 `## [v?\d+\.\d+\.\d+` 的行（即第一个版本条目，精确匹配版本号格式）
4. 在该行之前插入新版本条目
5. 保留文件头部（标题、描述等）
6. 验证插入后的文件格式正确（Markdown 语法无误、版本条目顺序正确）

> ⚠️ 如果插入失败或格式被破坏，使用备份恢复：`mv CHANGELOG.md.bak CHANGELOG.md`
> 成功后可删除备份：`rm CHANGELOG.md.bak`

**如果 CHANGELOG.md 不存在：**
1. 创建新文件，包含标准头部：

```markdown
# CHANGELOG

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [版本号] - YYYY-MM-DD

（生成的条目）
```

### 第八步：质量检查

生成完成后，执行以下检查：

- [ ] 每个 commit 都已被分类（没有遗漏）
- [ ] Breaking changes 已被单独标注并放在最前面
- [ ] 版本号格式正确（符合 semver）
- [ ] 日期格式为 YYYY-MM-DD（条目日期，非版本号中的日期）
- [ ] 没有重复条目
- [ ] 没有空的分类区块（如果某个分类没有条目，则省略该区块）
- [ ] 合并了相关的小 commit（避免冗余）
- [ ] 语言风格一致（全英文或全中文，与项目现有 CHANGELOG 保持一致）
- [ ] 如果是追加模式，没有破坏现有 CHANGELOG 的格式
- [ ] Commit hash 链接正确（如果有仓库 URL）

#### 自动验证命令

```bash
# 验证 commit 是否遗漏：对比源 commit 数量与 CHANGELOG 条目数量
# 源 commit 数
git log <range> --no-merges --oneline | wc -l
# CHANGELOG 条目数（合并后应 ≤ 源 commit 数）
grep -c '^\- ' CHANGELOG.md

# 验证版本号格式（semver）
grep -oP '## \[\K[^\]]+' CHANGELOG.md | head -1 | grep -qE '^\d+\.\d+\.\d+(-[\w.]+)?$' && echo "✅ 版本号合法" || echo "❌ 版本号格式不符合 semver"

# 验证日期格式（YYYY-MM-DD）
grep -oP '## \[.*\] - \K\S+' CHANGELOG.md | head -1 | grep -qE '^\d{4}-\d{2}-\d{2}$' && echo "✅ 日期格式正确" || echo "❌ 日期格式不正确"

# 检查是否存在空的分类区块（### 标题后紧跟另一个 ### 或 ## 或文件结尾）
awk '/^### /{title=$0; empty=1; next} /^- /{empty=0} /^##/{if(empty) print "❌ 空区块: " title}' CHANGELOG.md

# 验证 Markdown 格式（如果安装了 markdownlint）
bunx markdownlint CHANGELOG.md 2>/dev/null || true
```

### 特殊处理

#### Monorepo 支持

##### 检测 monorepo 结构

```bash
# 检查常见 monorepo 标志
ls -d packages/ apps/ libs/ modules/ 2>/dev/null
# 检查是否使用 workspace 管理
cat package.json 2>/dev/null | grep -q '"workspaces"' && echo "npm/yarn workspace"
cat pnpm-workspace.yaml 2>/dev/null && echo "pnpm workspace"
cat lerna.json 2>/dev/null && echo "lerna"
```

##### 生成策略

检测到 monorepo 后，询问用户选择策略：

1. **独立生成**（推荐）：为每个 package 单独生成 CHANGELOG
   ```bash
   # 获取某个 package 的 commit
   git log <range> --no-merges --format="%h%x00%s%x00%an%x00%ai" -- packages/core/
   ```
   每个 package 的 CHANGELOG 写入各自目录：`packages/core/CHANGELOG.md`

2. **合并生成**：所有变更写入根目录的 CHANGELOG，按 package 分组
   ```markdown
   ## [1.2.0] - 2024-03-08

   ### @myapp/core

   #### Added
   - 新增 xxx 功能 ([abc1234])

   ### @myapp/utils

   #### Fixed
   - 修复 xxx 问题 ([def5678])
   ```

##### 跨 package commit 处理

当一个 commit 涉及多个 package 时：

```bash
# 检查 commit 涉及的目录
git diff-tree --no-commit-id --name-only -r <commit-hash> | sed 's|/.*||' | sort -u
```

- **独立生成模式**：该 commit 同时出现在所有涉及的 package 的 CHANGELOG 中
- **合并生成模式**：归入影响最大的 package（按变更文件数判断），并标注 `(also affects: @myapp/utils)`

#### 多语言支持

- 检查现有 CHANGELOG.md 的语言
- 如果是中文项目（根据 README 或现有 CHANGELOG 判断），用中文生成条目
- 默认使用英文

## 使用示例

**用户**: 生成 changelog

**执行**:
1. 自动检测最近一个 tag 到 HEAD 的范围
2. 读取 git log
3. 分类、改写、生成
4. 追加到 CHANGELOG.md 或创建新文件

**用户**: generate changelog from v2.0.0 to v3.0.0

**执行**:
1. 使用 `v2.0.0..v3.0.0` 范围
2. 读取、分类、生成
3. 让用户确认版本号（建议 v3.0.0）

**用户**: what changed in the last 10 commits

**执行**:
1. 使用 `git log -n 10`
2. 分类展示变更摘要（不写入文件，仅展示）

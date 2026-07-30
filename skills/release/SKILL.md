---
name: release
description: >
  Universal release automation for any semver project. Auto-detect project type
  (Swift, Node.js, Rust, Go, Python, etc.), update CHANGELOG/README, create
  annotated tags, and generate GitHub Releases with smart release notes.
  Supports bilingual/simple/changelog/structured-cn note styles with historical
  consistency detection. Triggers: "release", "发版", "发布", "bump version",
  "publish", "create release".
license: MIT
compatibility: opencode, claude-code, codex, gemini-cli, macOS, Linux
metadata:
  version: "2.0.0"
  optimized_for: "slash-command, release-automation, git-workflow"
---

# Release - 通用发版助手

自动化版本发布流程，适用于任何使用语义化版本的项目。

## When to Use

### 中文触发词
- "发版"、"发布"、"release"
- "准备发版"、"更新版本"
- "发布新版本"、"发布 vX.Y.Z"
- "大版本"（递增 MINOR）
- "重大更新"（递增 MAJOR）

### 英文触发词
- "release", "bump version"
- "create release", "publish"
- "release vX.Y.Z"

## When NOT to Use

- 项目不使用 Git
- 项目没有 GitHub remote
- 用户只想打 tag 不想发完整 release

---

## 一致性原则（最高优先级）

> **核心思想：Release Note 的标题、格式、结构必须与项目历史 Release 保持一致。配置是 fallback，不是覆盖。**

### 优先级链

```
1. 历史 Release 实际格式（最高 — 一致性原则）
2. .release.json 中的 release_note_style（次之 — 仅当历史不可用时）
3. auto 自动检测（fallback — 仅当配置为 auto 且无历史）
4. 默认格式 simple（最低 — 兜底）
```

### 标题一致性

Release 标题从历史 Release 推断，不硬编码格式：

| 历史标题模式 | 推断规则 | 示例 |
|---|---|---|
| `{Project} vX.Y.Z` | 提取产品名前缀，新版本沿用 | `NewsBar v2.0.5` |
| `vX.Y.Z`（无产品名） | 保持纯版本号 | `v2.0.5` |
| 其他格式 | 保持历史格式 | 沿用 |

**检测方法**：提取最近 3 个 Release 的 `name` 字段，取出现频率最高的模式。

### 格式一致性

Release Body 格式从历史 Release 推断：

| 历史特征 | 判定格式 |
|---|---|
| 含 `# {Project} vX.Y.Z` 标题 + 中英双语摘要 + 双语 emoji 分组标题 | `bilingual` |
| 含 emoji 分组标题（🐛/✨/🔧）但无英文对照 | `structured-cn` |
| 含 `## [v` 或 `### Added` 等 Keep-a-Changelog 标题 | `changelog` |
| 以上均不匹配 | `simple` |

**关键规则**：当 `.release.json` 配置的 `release_note_style` 与历史格式推断结果冲突时，**历史格式优先**。配置仅在以下情况生效：
- 项目首次发版（无历史 Release）
- 历史格式无法识别（少于 3 个历史 Release）
- 用户显式指定 `--force-config` 标志

### 摘要一致性

如果历史 Release 包含一句话摘要（中英双语或单语），新版本必须包含相同结构的摘要。摘要来源优先级：

```
1. 用户在发版命令中指定的摘要
2. .release.json 中的 summary/summary_en
3. 从 commit messages 或 CHANGELOG 自动提取
```

### 分组标题一致性

emoji 分组标题从历史 Release 提取，保持相同的 emoji 和中英文对照（如历史有）。不自行创造新的分组标题。

---

## 配置检测

### 配置文件优先级

```
1. 项目根目录 .release.json（最高优先级）
2. 项目根目录 release.config.json
3. ~/.config/opencode/release.json（全局配置）
4. 自动检测（无配置文件时）
```

### .release.json 格式

```json
{
  "repo": "owner/repo",
  "tag_prefix": "v",
  "build_command": "npm run build",
  "release_command": null,
  "test_command": null,
  "docs": ["CHANGELOG.md", "README.md"],
  "changelog_format": "keep-a-changelog",
  "ci_mode": "local",
  "release_branch": true,
  "auto_merge": false,
  "release_note_style": "auto",
  "summary": "",
  "summary_en": "",
  "validation": ""
}
```

**字段说明**：

| 字段 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| `repo` | string | 自动检测 | GitHub 仓库 `owner/repo` |
| `tag_prefix` | string | `"v"` | Tag 前缀，如 `v1.0.0` |
| `build_command` | string\|null | 自动检测 | 构建命令 |
| `release_command` | string\|null | null | 发布命令（优先于 build_command） |
| `test_command` | string\|null | null | 测试命令（可选） |
| `docs` | string[] | `["CHANGELOG.md"]` | 需更新的文档列表 |
| `changelog_format` | string | `"keep-a-changelog"` | CHANGELOG 格式 |
| `ci_mode` | string | `"local"` | CI/CD 模式 |
| `release_branch` | boolean | true | 是否创建 release 分支 |
| `auto_merge` | boolean | false | 是否自动合并到 main（不推荐） |
| `release_note_style` | string | `"auto"` | Release Note 格式：`auto`/`bilingual`/`simple`/`changelog`/`structured-cn` |
| `summary` | string | 空 | 中文发版摘要（bilingual 模式使用） |
| `summary_en` | string | 空 | 英文发版摘要（bilingual 模式使用） |
| `validation` | string | 空 | 验证步骤描述（如 "swift build 通过"） |

### 自动检测规则

| 项目特征 | 构建命令 | 说明 |
|---------|---------|------|
| `Package.swift` | `swift build -c release` | Swift 项目 |
| `package.json` + `build` script | `npm run build` | Node.js 项目 |
| `Cargo.toml` | `cargo build --release` | Rust 项目 |
| `go.mod` | `go build -o ./release/` | Go 项目 |
| `pyproject.toml` | `python -m build` | Python 项目 |
| `Makefile` + `build` target | `make build` | 通用项目 |
| `build.gradle` / `build.gradle.kts` | `./gradlew build` | Gradle 项目 |
| `pubspec.yaml` | `flutter build` | Flutter 项目 |
| `mix.exs` | `mix release` | Elixir 项目 |

### Release 命令检测

```
优先级：
1. .release.json 中的 release_command
2. scripts/release.sh 存在
3. Makefile + release target
4. 默认使用 build_command
```

---

## Version 规则

### 版本号格式

```
vX.Y.Z
```

- **X (MAJOR)**: 大重构 / 不兼容变更
- **Y (MINOR)**: 新功能
- **Z (PATCH)**: Bug 修复

### 自动递增规则

| 场景 | 递增方式 | 示例 |
|------|---------|------|
| 用户指定版本 | 使用用户指定的 | v0.9.2 |
| 用户说"发版"但未指定 | 自动递增 PATCH | v0.9.1 → v0.9.2 |
| 用户说"大版本" | 递增 MINOR | v0.9.1 → v0.10.0 |
| 用户说"重大更新" | 递增 MAJOR | v0.9.1 → v1.0.0 |

### 版本验证

```bash
# 验证格式
[[ "$version" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]

# 验证递增（对比最新 tag）
latest_tag=$(git describe --tags --abbrev=0 2>/dev/null || echo "v0.0.0")
```

---

## Workflow

```
Phase 1: 环境检测
  ├── 检测当前目录是否为 Git 仓库
  ├── 检测是否有 GitHub remote
  ├── 加载配置文件（.release.json）
  ├── 如无配置，自动检测项目类型
  ├── 检测当前最新 tag
  └── 确定目标版本号

Phase 2: 文档更新（自动）
  ├── 检测存在的文档文件
  ├── 更新 CHANGELOG.md（如存在）
  │   ├── 将 ## [Unreleased] 转为 ## [vX.Y.Z] - YYYY-MM-DD
  │   ├── 在顶部新增 ## [Unreleased]
  │   └── 更新底部版本链接
  ├── 更新 README.md（如存在）
  │   └── 更新版本引用
  └── 更新其他配置的文档

Phase 2.5: Release Note 生成（自动）
  ├── 一致性检测（最高优先级）
  │   ├── 提取最近 3 个 Release 的 name 字段 → 推断标题模式
  │   ├── 提取最近 3 个 Release 的 body → 推断格式（bilingual/structured-cn/changelog/simple）
  │   └── 历史 vs 配置冲突时，历史优先（参见「一致性原则」章节）
  ├── 检查 .release.json 中的 release_note_style
  │   └── 仅当历史不可用或用户显式 --force-config 时使用配置值
  ├── 若为 "auto" 或无配置且无历史，通过以下规则判定：
  │   ├── 分析中英文字符比例 → bilingual（CJK >50 且 Latin >100）
  │   ├── 分析是否含 emoji 分组标题（🐛/✨/🔧） → structured-cn
  │   ├── 分析是否含 Keep-a-Changelog 标题 → changelog
  │   └── 无法判断 → 回退到 simple
  ├── 从 CHANGELOG 提取 vX.Y.Z 条目
  ├── 按检测格式生成 Release Body（标题、摘要、分组标题均遵循历史模式）
  ├── 输出预览路径，提示用户后续确认
  └── 将 body 写入临时文件供 Phase 7 使用

Phase 3: 创建 Release 分支（可选）
  ├── 检查 release_branch 配置
  ├── 如启用，创建 release/vX.Y.Z 分支
  └── 提交文档更新

Phase 4: 打 Tag 并推送（需确认）
  ├── 在当前分支打 annotated tag
  ├── 展示 tag 信息，等待用户确认
  └── 推送 tag 到 origin

Phase 5: 推送分支（需确认）
  ├── 展示待推送的分支
  ├── 用户确认后推送
  └── 如为 CI 模式，流程结束

Phase 6: 本地构建（需确认，local 模式）
  ├── 检查 build_command 配置
  ├── 展示构建命令
  ├── 用户确认后执行构建
  └── 验证构建产物

Phase 7: GitHub Release（需确认）
  ├── 加载 Phase 2.5 生成的 Release Body
  ├── 展示完整 Release Note 预览
  ├── 用户可选（编辑 / 接受 / 跳过）
  ├── 通过 `gh release create` 或 GitHub API 创建 Release
  │   ├── 标题只使用版本号：`--title "vX.Y.Z"`（不含描述）
  │   ├── local 模式：附带本地构建产物（.zip/.dmg）
  │   ├── ci 模式：仅创建 Release（产物由 CI 上传）
  │   └── 使用 `--notes-file` 传入预先填写的 body（描述内容在 body 中）
  ├── 验证 Release 创建成功
  └── 若失败，提示手动兜底方案

Phase 8: 收尾
  ├── 输出发版报告
  ├── 如启用 release_branch，提示手动合并
  └── 提示下一步操作
```

---

## CI/CD 模式

### 模式说明

| 模式 | 行为 | 适用场景 |
|------|------|---------|
| `local` | 本地完成全流程（默认） | 无 CI/CD 的项目 |
| `ci` | 只打 tag 和推送，由 CI 完成构建和发布 | 有 GitHub Actions 等 |
| `auto` | 自动检测 `.github/workflows` 存在则用 CI 模式 | 智能切换 |

### CI 模式流程

```
Phase 1-3: 同 local 模式
Phase 4: 打 Tag 并推送
Phase 5: 推送分支（如启用）
Phase 6: 跳过本地构建
Phase 7: 创建 GitHub Release（可选，由 CI 创建则跳过）
Phase 8: 收尾，提示 CI 将自动完成后续
```

---

## 文档更新规则

### CHANGELOG.md 更新

**支持的格式**：

1. **Keep a Changelog**（默认）
```markdown
## [Unreleased]

### Added
- ...

## [vX.Y.Z] - YYYY-MM-DD
```

2. **Simple**
```markdown
## Unreleased

- ...

## vX.Y.Z - YYYY-MM-DD
```

3. **None**（不自动更新 CHANGELOG）

### README.md 更新

- 检测版本引用（如 `v0.9.1`）并更新为新版本
- 不强制添加徽章（除非已有）

---

## Release Note 格式

### 自动检测逻辑

> **重要**：以下检测仅在「一致性原则」无法从历史 Release 推断格式时作为 fallback 使用。历史格式优先于本节逻辑。

当 `release_note_style` 为 `auto`（默认）且无历史 Release 可参考时，Skill 通过 GitHub Releases API 提取最近 3 个 Release Body，按以下规则判定格式：

| 检测条件 | 判定格式 | 典型特征 |
|---------|---------|---------|
| CJK 字符 >50 且 Latin 字符 >100 | `bilingual` | 中英双语段落交替 |
| Body 含 emoji 分组标题（🐛/✨/🔧/🔐/♿） | `structured-cn` | 结构化中文 emoji 分组格式 |
| Body 含 `## [v` 格式标题 | `changelog` | 直接复制 CHANGELOG 条目 |
| 以上均不匹配 | `simple` | 通用单语言格式 |

### 四种格式

#### `bilingual` — 中英双语格式

适用于维护中英文 Release Notes 的项目。Body 从 CHANGELOG 的 `### Added`/`### Changed`/`### Fixed` 分组自动生成，每个分组拆分为中文/英文小节。

```markdown
# vX.Y.Z Release Notes

[Project] vX.Y.Z。[一句话中文摘要]。
[Project] vX.Y.Z. Core upgrade: [one-line English summary].

---

## [Section 中文] / [Section English]

- 中文要点
- English point

**涉及文件 / Files**: `File.swift`

---

## 验证 / Validation

- {validation}

---

**完整 CHANGELOG**: [link]
**Full Changelog**: compare/{prev}...{version}
```

#### `simple` — 通用单语格式

```markdown
# vX.Y.Z Release Notes

[Project] vX.Y.Z.

---

## Changes

- point 1

---

## Validation

- {validation}

---

**Full Changelog**: compare/{prev}...{version}
```

#### `changelog` — 纯 CHANGELOG 格式

```markdown
{CHANGELOG 条目原文}

---

**Full Changelog**: compare/{prev}...{version}
```

#### `structured-cn` — 结构化中文 emoji 分组格式

适用于中文项目，按 commit 前缀自动分组为 emoji 章节。生成逻辑：

1. 从 `git log {prev}..HEAD --no-merges --format="%s"` 提取 commit message
2. 按 Conventional Commits 前缀自动分组：

| 前缀 | emoji | 章节标题 |
|------|-------|---------|
| `fix:` | 🐛 | 修复 |
| `feat:` | ✨ | 新增 / 新功能 |
| `refactor:` | ♻️ | 重构 |
| `docs:` | 📝 | 文档 |
| `perf:` | ⚡ | 性能优化 |
| `test:` | ✅ | 测试 |
| `ci:` | 🔄 | CI/CD |
| `build:` | 📦 | 构建 |
| `chore:` | 🔧 | 杂项 / 改进 |
| `release:` | 🚀 | 发布 |
| `security:` | 🔐 | 安全 |
| 无前缀 | 🔧 | 其他 |

3. 清理 commit message：去掉前缀标记，首字母大写，移除末尾句号

```markdown
vX.Y.Z — 简短描述

🐛 修复
- API Key 启动同步加载：确保定时器触发时 API Key 已就绪
- Dashboard force unwrap 修复：消除潜在的崩溃风险

✨ 新增
- SHA256 digest 校验：通过 GitHub Release asset digest 字段获取校验值

🔧 改进
- 指数退避重试：重试间隔改为 1s → 2s → 4s 指数增长
- 日志增强：获取数据源失败时增加 NSLog 输出

---

**Full Changelog**: compare/{prev}...{version}
```

> **注意**：若 `scripts/release.sh` 存在，应调用该脚本生成 Release Note；若不存在，Skill 应按上述规则自行生成。

### `.release.json` 配置

```json
{
  "release_note_style": "bilingual",
  "summary": "新增备份管理功能",
  "summary_en": "New backup management feature",
  "validation": "swift build + swift test 通过"
}
```

若未配置 `summary`/`summary_en`，Skill 会从 CHANGELOG 的 `> 摘要行` 自动提取。

---

## Git 操作规范

### 分支命名

```
release/vX.Y.Z（如启用 release_branch）
```

### Commit 消息格式

```
release: vX.Y.Z — 简要描述
```

### Tag 格式

```bash
git tag -a vX.Y.Z -m "vX.Y.Z — 简要描述"
```

### GitHub Release 标题格式

标题格式从历史 Release 推断（参见「一致性原则」章节）：

```
{推断的标题模式} vX.Y.Z
```

**推断规则**：
- 历史标题含产品名前缀 → `{Product} vX.Y.Z`（如 `NewsBar v2.0.5`）
- 历史标题为纯版本号 → `vX.Y.Z`
- 无历史 → 默认 `vX.Y.Z`

> **注意**：描述内容放在 Release Body 中（通过 `--notes-file` 传入），不出现在标题中。

### 推送命令

```bash
git push origin vX.Y.Z  # 推送 tag
git push origin release/vX.Y.Z  # 推送 release 分支（如启用）
```

---

## 安全边界

| 操作 | 权限 | 说明 |
|------|------|------|
| 读取配置/文档 | ✅ 自动 | 读取 .release.json、CHANGELOG 等 |
| 修改文档 | ✅ 自动 | 更新版本号、日期 |
| 创建分支 | ✅ 自动 | release/vX.Y.Z（如启用） |
| 提交代码 | ✅ 自动 | 在当前分支上提交 |
| 打 tag | ⚠️ 需确认 | 展示 tag 信息后确认 |
| 推送 tag | ⚠️ 需确认 | 推送到 origin |
| 推送分支 | ⚠️ 需确认 | 推送 release 分支 |
| 本地构建 | ⚠️ 需确认 | 展示构建命令后确认 |
| 创建 Release | ⚠️ 需确认 | 展示 Release Note 预览后确认 |
| **合并分支** | ❌ 不执行 | **用户手动合并** |

---

## Error Handling

| 错误场景 | 处理方式 |
|---------|---------|
| 不是 Git 仓库 | 提示用户切换到项目目录 |
| 没有 GitHub remote | 提示用户添加 remote |
| 版本号格式错误 | 提示正确格式 vX.Y.Z |
| 版本已存在 | 提示冲突，建议新版本号 |
| CHANGELOG 无 Unreleased | 提示先添加变更记录 |
| Git 工作区不干净 | 提示先提交或 stash |
| 构建失败 | 提示构建错误，询问是否继续 |
| 推送失败 | 提示网络问题，建议重试 |
| Release 创建失败 | 提示手动兜底方案 |

---

## Output Format

```
📋 发版报告 - vX.Y.Z

✅ 文档更新:
   - CHANGELOG.md: Unreleased → vX.Y.Z
   - README.md: 更新版本引用

✅ Release Note:
   - 检测格式: {auto|bilingual|simple|changelog|structured-cn}
   - Body: 已生成预览

✅ Tag:
   - Tag: vX.Y.Z
   - 推送: 已推送到 origin

✅ Release 分支（如启用）:
   - 分支: release/vX.Y.Z
   - 推送: 已推送到 origin

✅ 本地构建（如执行）:
   - 命令: {build_command}
   - 状态: 成功

✅ GitHub Release:
   - URL: https://github.com/{owner}/{repo}/releases/tag/vX.Y.Z
   - Release Note: 已生成

⚠️ 待办（如启用 release_branch）:
   - 手动合并 release/vX.Y.Z 到 main:
     git checkout main
     git merge release/vX.Y.Z --no-edit
     git push origin main

📌 下一步:
   - 验证 GitHub Release 页面
   - 开始下一版本开发: v{next_version}
```

---

## Guardrails

- 不自动删除 release 分支
- 不自动合并到 main
- Git 操作（tag、push）必须展示摘要后确认
- Release 创建必须展示 Release Note 预览后确认
- 构建失败时询问用户是否继续
- 不修改源代码文件，只更新文档
- 推送操作必须用户确认

---

## 示例调用

```bash
# 基本发版（自动递增 PATCH）
skill(name="release", user_message="发版")

# 指定版本号
skill(name="release", user_message="发版 v0.9.2")

# 带摘要
skill(name="release", user_message="发版 v0.9.2 备份管理 bug 修复")

# 试运行
skill(name="release", user_message="发版 v0.9.2 --dry-run")

# 强制使用配置格式（跳过历史一致性检测）
skill(name="release", user_message="发版 v0.9.2 --force-config")

# 英文触发
skill(name="release", user_message="release v0.9.2")
skill(name="release", user_message="bump version")
```

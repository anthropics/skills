# Release - 通用发版助手

自动化版本发布流程，适用于任何使用语义化版本的项目。

## 功能特性

- ✅ 自动检测项目类型（Swift、Node.js、Rust、Go、Python 等）
- ✅ 支持项目根目录配置文件（`.release.json`）
- ✅ 自动更新 CHANGELOG.md、README.md
- ✅ **一致性原则** — Release Note 标题、格式、结构从历史 Release 推断，配置仅作为 fallback
- ✅ **智能 Release Note 生成** — 自动检测历史格式，支持 bilingual/simple/changelog/structured-cn 四种模式
- ✅ 可选创建 release/vX.Y.Z 分支
- ✅ 自动打 annotated tag
- ✅ 可选本地构建
- ✅ 支持 CI/CD 模式（本地/CI/自动）
- ✅ 自动创建 GitHub Release

## 使用方法

### 基本发版

```bash
# 自动递增 PATCH 版本
skill(name="release", user_message="发版")

# 指定版本号
skill(name="release", user_message="发版 v0.9.2")

# 带摘要
skill(name="release", user_message="发版 v0.9.2 备份管理 bug 修复")

# 强制使用配置格式（跳过历史一致性检测）
skill(name="release", user_message="发版 v0.9.2 --force-config")

# 英文触发
skill(name="release", user_message="release v0.9.2")
skill(name="release", user_message="bump version")
```

### 试运行

```bash
skill(name="release", user_message="发版 v0.9.2 --dry-run")
```

## 配置文件

在项目根目录创建 `.release.json`：

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
  "release_note_style": "auto"
}
```

### 配置优先级

```
1. 项目根目录 .release.json（最高优先级）
2. 项目根目录 release.config.json
3. ~/.config/opencode/release.json（全局配置）
4. 自动检测（无配置文件时）
```

### 字段说明

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

## 工作流程

1. **环境检测**：检测 Git 仓库、GitHub remote、加载配置
2. **文档更新**：自动更新 CHANGELOG、README（如存在）
3. **创建分支**：可选创建 release/vX.Y.Z 分支
4. **打 Tag**：在当前分支打 annotated tag（需确认）
5. **推送**：推送 tag 和分支到 origin（需确认）
6. **本地构建**：可选执行构建命令（需确认）
7. **创建 Release**：生成 Release Note 并创建 GitHub Release（需确认）

## CI/CD 模式

| 模式 | 行为 | 适用场景 |
|------|------|---------|
| `local` | 本地完成全流程（默认） | 无 CI/CD 的项目 |
| `ci` | 只打 tag 和推送，由 CI 完成构建和发布 | 有 GitHub Actions 等 |
| `auto` | 自动检测 `.github/workflows` 存在则用 CI 模式 | 智能切换 |

## 安全边界

- ✅ 文档更新：自动执行
- ✅ 创建分支：自动执行（如启用）
- ⚠️ Git 操作：需用户确认（tag、push）
- ⚠️ 本地构建：需用户确认
- ⚠️ GitHub Release：需用户确认
- ❌ 合并到 main：不自动执行，用户手动合并

## 自动检测支持的项目类型

| 项目特征 | 构建命令 |
|---------|---------|
| `Package.swift` | `swift build -c release` |
| `package.json` + `build` script | `npm run build` |
| `Cargo.toml` | `cargo build --release` |
| `go.mod` | `go build -o ./release/` |
| `pyproject.toml` | `python -m build` |
| `Makefile` + `build` target | `make build` |
| `build.gradle` / `build.gradle.kts` | `./gradlew build` |
| `pubspec.yaml` | `flutter build` |
| `mix.exs` | `mix release` |

## 版本号规则

- **vX.Y.Z**：标准语义化版本
- **MAJOR**：大重构 / 不兼容变更
- **MINOR**：新功能
- **PATCH**：Bug 修复

自动递增规则：
- 用户指定版本：使用用户指定的
- 用户说"发版"但未指定：自动递增 PATCH
- 用户说"大版本"：递增 MINOR
- 用户说"重大更新"：递增 MAJOR

## 文件结构

```
release/
├── SKILL.md                    # Skill 主定义文件
├── config/
│   └── projects.json           # 示例配置（非硬编码）
├── templates/
│   ├── release-note.md         # Release Note 模板
│   └── changelog-entry.md      # CHANGELOG 条目模板
└── scripts/
    ├── validate-version.sh     # 版本号验证
    ├── detect-project.sh       # 项目类型检测
    └── generate-notes.sh       # Release Note 生成
```

## 错误处理

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

## 输出示例

```
📋 发版报告 - v0.9.2

✅ 文档更新:
   - CHANGELOG.md: Unreleased → v0.9.2
   - README.md: 更新版本引用

✅ Tag:
   - Tag: v0.9.2
   - 推送: 已推送到 origin

✅ Release 分支（如启用）:
   - 分支: release/v0.9.2
   - 推送: 已推送到 origin

✅ 本地构建（如执行）:
   - 命令: npm run build
   - 状态: 成功

✅ GitHub Release:
   - URL: https://github.com/owner/repo/releases/tag/v0.9.2
   - Release Note: 已生成

⚠️ 待办（如启用 release_branch）:
   - 手动合并 release/v0.9.2 到 main:
     git checkout main
     git merge release/v0.9.2 --no-edit
     git push origin main

📌 下一步:
   - 验证 GitHub Release 页面
   - 开始下一版本开发: v0.9.3
```

---
name: release-skills
description: Universal release workflow. Auto-detects version files and changelogs. Supports Node.js, Python, Rust, Claude Plugin, GitHub Releases, annotated tags, historical release backfill, and generic projects. Use when user says "release", "发布", "new version", "bump version", "push", "推送", "release notes", "GitHub Release", or "回填 Release".
---

# Release Skills

Universal release workflow supporting any project type with multi-language changelog.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## Quick Start

Just run `/release-skills` - auto-detects your project configuration.

## Supported Projects

| Project Type | Version File | Auto-Detected |
|--------------|--------------|---------------|
| Node.js | package.json | ✓ |
| Python | pyproject.toml | ✓ |
| Rust | Cargo.toml | ✓ |
| Claude Plugin | marketplace.json | ✓ |
| Generic | VERSION / version.txt | ✓ |

## Options

| Flag | Description |
|------|-------------|
| `--dry-run` | Preview changes without executing |
| `--major` | Force major version bump |
| `--minor` | Force minor version bump |
| `--patch` | Force patch version bump |
| `--backfill-releases` | Create missing GitHub Releases for existing tags from changelog sections |

## Workflow

### Step 1: Detect Project Configuration

1. Check for `.releaserc.yml` (optional config override)
   - If present, inspect whether it defines release hooks
2. Auto-detect version file by scanning (priority order):
   - `package.json` (Node.js)
   - `pyproject.toml` (Python)
   - `Cargo.toml` (Rust)
   - `marketplace.json` or `.claude-plugin/marketplace.json` (Claude Plugin)
   - `VERSION` or `version.txt` (Generic)
3. Scan for changelog files using glob patterns:
   - `CHANGELOG*.md`
   - `HISTORY*.md`
   - `CHANGES*.md`
4. Identify language of each changelog by filename suffix
5. Detect GitHub release support:
   - Check whether `origin` points to GitHub
   - Check whether `gh` is installed and authenticated
   - Check existing releases with `gh release list --limit 5` when available
6. Display detected configuration

**Project Hook Contract**:

If `.releaserc.yml` defines `release.hooks`, keep the release workflow generic and delegate project-specific packaging/publishing to those hooks.

Supported hooks:

| Hook | Purpose | Expected Responsibility |
|------|---------|-------------------------|
| `prepare_artifact` | Make one target releasable | Validate the target is self-contained, sync/embed local dependencies, optionally stage extra files |
| `publish_artifact` | Publish one releasable target | Upload the prepared target (or a staged directory if the project uses one), attach version/changelog/tags |

Supported placeholders:

| Placeholder | Meaning |
|-------------|---------|
| `{project_root}` | Absolute path to repository root |
| `{target}` | Absolute path to the module/skill being released |
| `{artifact_dir}` | Absolute path to a temporary staging directory for this target, when the project uses one |
| `{version}` | Version selected by the release workflow |
| `{dry_run}` | `true` or `false` |
| `{release_notes_file}` | Absolute path to a UTF-8 file containing release notes/changelog text |

Execution rules:
- Keep the skill generic: do not hardcode registry/package-manager/project layout details into this SKILL.
- If `prepare_artifact` exists, run it once per target before publish-related checks that need the final releasable target state.
- Write release notes to a temp file and pass that file path to `publish_artifact`; do not inline multiline changelog text into shell commands.
- If hooks are absent, fall back to the default project-agnostic release workflow.

**Language Detection Rules**:

Changelog files follow the pattern `CHANGELOG_{LANG}.md` or `CHANGELOG.{lang}.md`, where `{lang}` / `{LANG}` is a language or region code.

| Pattern | Example | Language |
|---------|---------|----------|
| No suffix | `CHANGELOG.md` | en (default) |
| `_{LANG}` (uppercase) | `CHANGELOG_CN.md`, `CHANGELOG_JP.md` | Corresponding language |
| `.{lang}` (lowercase) | `CHANGELOG.zh.md`, `CHANGELOG.ja.md` | Corresponding language |
| `.{lang-region}` | `CHANGELOG.zh-CN.md` | Corresponding region variant |

Common language codes: `zh` (Chinese), `ja` (Japanese), `ko` (Korean), `de` (German), `fr` (French), `es` (Spanish).

**Output Example**:
```
Project detected:
  Version file: package.json (1.2.3)
  Changelogs:
    - CHANGELOG.md (en)
    - CHANGELOG.zh.md (zh)
    - CHANGELOG.ja.md (ja)
```

### Step 2: Analyze Changes Since Last Tag

```bash
LAST_TAG=$(git tag --sort=-v:refname | head -1)
git log ${LAST_TAG}..HEAD --oneline
git diff ${LAST_TAG}..HEAD --stat
```

Categorize by conventional commit types:

| Type | Description |
|------|-------------|
| feat | New features |
| fix | Bug fixes |
| docs | Documentation |
| refactor | Code refactoring |
| perf | Performance improvements |
| test | Test changes |
| style | Formatting, styling |
| chore | Maintenance (skip in changelog) |

**Breaking Change Detection**:
- Commit message starts with `BREAKING CHANGE`
- Commit body/footer contains `BREAKING CHANGE:`
- Removed public APIs, renamed exports, changed interfaces

If breaking changes detected, warn user: "Breaking changes detected. Consider major version bump (--major flag)."

### Step 3: Determine Version Bump

Rules (in priority order):
1. User flag `--major/--minor/--patch` → Use specified
2. BREAKING CHANGE detected → Major bump (1.x.x → 2.0.0)
3. `feat:` commits present → Minor bump (1.2.x → 1.3.0)
4. Otherwise → Patch bump (1.2.3 → 1.2.4)

Display version change: `1.2.3 → 1.3.0`

### Step 4: Generate Multi-language Changelogs

For each detected changelog file:

1. **Identify language** from filename suffix
2. **Detect third-party contributors**:
   - Check merge commits: `git log ${LAST_TAG}..HEAD --merges --pretty=format:"%H %s"`
   - For each merged PR, identify the PR author via `gh pr view <number> --json author --jq '.author.login'`
   - Compare against repo owner (`gh repo view --json owner --jq '.owner.login'`)
   - If PR author ≠ repo owner → third-party contributor
3. **Generate content in that language**:
   - Section titles in target language
   - Change descriptions written naturally in target language (not translated)
   - Date format: YYYY-MM-DD (universal)
   - **Third-party contributions**: Append contributor attribution `(by @username)` to the changelog entry
4. **Insert at file head** (preserve existing content)

**Section Title Translations** (built-in):

| Type | en | zh | ja | ko | de | fr | es |
|------|----|----|----|----|----|----|-----|
| feat | Features | 新功能 | 新機能 | 새로운 기능 | Funktionen | Fonctionnalités | Características |
| fix | Fixes | 修复 | 修正 | 수정 | Fehlerbehebungen | Corrections | Correcciones |
| docs | Documentation | 文档 | ドキュメント | 문서 | Dokumentation | Documentation | Documentación |
| refactor | Refactor | 重构 | リファクタリング | 리팩토링 | Refactoring | Refactorisation | Refactorización |
| perf | Performance | 性能优化 | パフォーマンス | 성능 | Leistung | Performance | Rendimiento |
| breaking | Breaking Changes | 破坏性变更 | 破壊的変更 | 주요 변경사항 | Breaking Changes | Changements majeurs | Cambios importantes |

**Changelog Format**:

```markdown
## {VERSION} - {YYYY-MM-DD}

### Features
- Description of new feature
- Description of third-party contribution (by @username)

### Fixes
- Description of fix

### Documentation
- Description of docs changes
```

Only include sections that have changes. Omit empty sections.

**Third-Party Attribution Rules**:
- Only add `(by @username)` for contributors who are NOT the repo owner
- Use GitHub username with `@` prefix
- Place at the end of the changelog entry line
- Apply to all languages consistently (always use `(by @username)` format, not translated)

**Multi-language Example**:

English (CHANGELOG.md):
```markdown
## 1.3.0 - 2026-01-22

### Features
- Add user authentication module (by @contributor1)
- Support OAuth2 login

### Fixes
- Fix memory leak in connection pool
```

Chinese (CHANGELOG.zh.md):
```markdown
## 1.3.0 - 2026-01-22

### 新功能
- 新增用户认证模块 (by @contributor1)
- 支持 OAuth2 登录

### 修复
- 修复连接池内存泄漏问题
```

Japanese (CHANGELOG.ja.md):
```markdown
## 1.3.0 - 2026-01-22

### 新機能
- ユーザー認証モジュールを追加 (by @contributor1)
- OAuth2 ログインをサポート

### 修正
- コネクションプールのメモリリークを修正
```

### Step 5: Group Changes by Skill/Module

Analyze commits since last tag and group by affected skill/module:

1. **Identify changed files** per commit
2. **Group by skill/module**:
   - `skills/<skill-name>/*` → Group under that skill
   - Root files (CLAUDE.md, etc.) → Group as "project"
   - Multiple skills in one commit → Split into multiple groups
3. **For each group**, identify related README updates needed

**Example Grouping**:
```
baoyu-cover-image:
  - feat: add new style options
  - fix: handle transparent backgrounds
  → README updates: options table

baoyu-comic:
  - refactor: improve panel layout algorithm
  → No README updates needed

project:
  - docs: update CLAUDE.md architecture section
```

### Step 6: Commit Each Skill/Module Separately

For each skill/module group (in order of changes):

1. **Check README updates needed**:
   - Scan `README*.md` for mentions of this skill/module
   - Verify options/flags documented correctly
   - Update usage examples if syntax changed
   - Update feature descriptions if behavior changed

2. **Stage and commit**:
   ```bash
   git add skills/<skill-name>/*
   git add README.md README.zh.md  # If updated for this skill
   git commit -m "<type>(<skill-name>): <meaningful description>"
   ```

3. **Commit message format**:
   - Use conventional commit format: `<type>(<scope>): <description>`
   - `<type>`: feat, fix, refactor, docs, perf, etc.
   - `<scope>`: skill name or "project"
   - `<description>`: Clear, meaningful description of changes

**Example Commits**:
```bash
git commit -m "feat(baoyu-cover-image): add watercolor and minimalist styles"
git commit -m "fix(baoyu-comic): improve panel layout for long dialogues"
git commit -m "docs(project): update architecture documentation"
```

**Common README Updates Needed**:
| Change Type | README Section to Check |
|-------------|------------------------|
| New options/flags | Options table, usage examples |
| Renamed options | Options table, usage examples |
| New features | Feature description, examples |
| Breaking changes | Migration notes, deprecation warnings |
| Restructured internals | Architecture section (if exposed to users) |

### Step 7: Generate Changelog and Update Version

1. **Generate multi-language changelogs** (as described in Step 4)
2. **Update version file**:
   - Read version file (JSON/TOML/text)
   - Update version number
   - Write back (preserve formatting)
3. **Create release notes file**:
   - Prefer the new version section from `CHANGELOG.md`
   - If no English/default changelog exists, use the first detected changelog
   - Extract only the exact `## {VERSION} - {YYYY-MM-DD}` section through the next `##`
   - Match both plain version and tag-prefixed headings when needed, e.g. `1.2.3` and `v1.2.3`
   - Keep breaking changes near the top; if needed, add a short highlight before other sections
   - Write notes to a UTF-8 temp file and reuse it for annotated tag messages, GitHub Releases, and `publish_artifact`
   - In normal mode, stop rather than creating an empty tag or GitHub Release when notes cannot be found

**Version Paths by File Type**:

| File | Path |
|------|------|
| package.json | `$.version` |
| pyproject.toml | `project.version` |
| Cargo.toml | `package.version` |
| marketplace.json | `$.metadata.version` |
| VERSION / version.txt | Direct content |

### Step 8: User Confirmation

Before creating the release commit, ask user to confirm:

**Use AskUserQuestion with three questions**:

1. **Version bump** (single select):
   - Show recommended version based on Step 3 analysis
   - Options: recommended (with label), other semver options
   - Example: `1.2.3 → 1.3.0 (Recommended)`, `1.2.3 → 1.2.4`, `1.2.3 → 2.0.0`

2. **Push to remote** (single select):
   - Options: "Yes, push after commit", "No, keep local only"

3. **Publish GitHub Release** (single select):
   - Offer this only when GitHub release support is available
   - Default to "Yes, publish after tag push" when the user also chose push
   - If the user keeps the release local, do not create or edit a GitHub Release

**Example Output Before Confirmation**:
```
Commits created:
  1. feat(baoyu-cover-image): add watercolor and minimalist styles
  2. fix(baoyu-comic): improve panel layout for long dialogues
  3. docs(project): update architecture documentation

Changelog preview (en):
  ## 1.3.0 - 2026-01-22
  ### Features
  - Add watercolor and minimalist styles to cover-image
  ### Fixes
  - Improve panel layout for long dialogues in comic

Release notes source: CHANGELOG.md#1.3.0
Ready to create release commit, annotated tag, and GitHub Release.
```

### Step 9: Create Release Commit and Annotated Tag

After user confirmation:

1. **Stage version and changelog files**:
   ```bash
   git add <version-file>
   git add CHANGELOG*.md
   ```

2. **Create release commit**:
   ```bash
   git commit -m "chore: release v{VERSION}"
   ```

3. **Create annotated tag**:
   ```bash
   git tag -a v{VERSION} -F <release-notes-file>
   ```
   If `.releaserc.yml` sets `tag.sign: true`, use `git tag -s` with the same notes file.

4. **Push if user confirmed** (Step 8):
   ```bash
   git push origin main
   git push origin v{VERSION}
   ```

**Note**: Do NOT add Co-Authored-By line. This is a release commit, not a code contribution.

### Step 10: Publish Release Artifacts and GitHub Release

Project artifact publishing and GitHub Releases are separate outputs:

1. **Project artifacts**:
   - If `release.hooks.publish_artifact` exists, run it once per prepared target
   - Pass the same `{release_notes_file}` used for the tag and GitHub Release
   - In dry-run mode, pass `{dry_run}=true` and report what would be published

2. **GitHub Release**:
   - Run only if the user confirmed remote publishing and GitHub support is available
   - Ensure the tag exists on the remote before creating the release
   - Create or update using the extracted notes:
     ```bash
     if gh release view v{VERSION} >/dev/null 2>&1; then
       gh release edit v{VERSION} --title "v{VERSION}" --notes-file <release-notes-file>
     else
       gh release create v{VERSION} --title "v{VERSION}" --notes-file <release-notes-file> --verify-tag
     fi
     ```
   - Never inline multiline release notes into shell commands

**Post-Release Output**:
```
Release v1.3.0 created.

Commits:
  1. feat(baoyu-cover-image): add watercolor and minimalist styles
  2. fix(baoyu-comic): improve panel layout for long dialogues
  3. docs(project): update architecture documentation
  4. chore: release v1.3.0

Tag: v1.3.0
Tag type: annotated
GitHub Release: published  # or "skipped/local only"
Status: Pushed to origin  # or "Local only - run git push when ready"
```

## Backfill Existing GitHub Releases

Use this mode when the user asks to backfill historical releases or passes `--backfill-releases`.

1. Do not bump versions, edit changelogs, or create release commits.
2. List existing tags in version order and detect missing releases:
   ```bash
   git tag --sort=v:refname
   gh release view <tag>
   ```
3. For each tag without a GitHub Release:
   - Normalize the changelog lookup by stripping the configured tag prefix, e.g. `v1.2.3` -> `1.2.3`
   - Extract the matching section from `CHANGELOG.md`; fall back to the first matching changelog file
   - Skip or ask before publishing if no matching changelog section exists
   - Create the release with:
     ```bash
     gh release create <tag> --title "<tag>" --notes-file <release-notes-file> --verify-tag
     ```
4. Detect lightweight tags with `git cat-file -t <tag>` (`commit` means lightweight, `tag` means annotated).
5. Do not rewrite public lightweight tags by default. Converting an existing remote tag to an annotated tag requires explicit user confirmation because it rewrites a published reference.

## Configuration (.releaserc.yml)

Optional config file in project root to override defaults:

```yaml
# .releaserc.yml - Optional configuration

# Version file (auto-detected if not specified)
version:
  file: package.json
  path: $.version  # JSONPath for JSON, dotted path for TOML

# Changelog files (auto-detected if not specified)
changelog:
  files:
    - path: CHANGELOG.md
      lang: en
    - path: CHANGELOG.zh.md
      lang: zh
    - path: CHANGELOG.ja.md
      lang: ja

  # Section mapping (conventional commit type → changelog section)
  # Use null to skip a type in changelog
  sections:
    feat: Features
    fix: Fixes
    docs: Documentation
    refactor: Refactor
    perf: Performance
    test: Tests
    chore: null

# Commit message format
commit:
  message: "chore: release v{version}"

# Tag format
tag:
  prefix: v  # Results in v1.0.0
  sign: false

# Additional files to include in release commit
include:
  - README.md
  - package.json
```

## Dry-Run Mode

When `--dry-run` is specified:

```
=== DRY RUN MODE ===

Project detected:
  Version file: package.json (1.2.3)
  Changelogs: CHANGELOG.md (en), CHANGELOG.zh.md (zh)

Last tag: v1.2.3
Proposed version: v1.3.0

Changes grouped by skill/module:
  baoyu-cover-image:
    - feat: add watercolor style
    - feat: add minimalist style
    → Commit: feat(baoyu-cover-image): add watercolor and minimalist styles
    → README updates: options table

  baoyu-comic:
    - fix: panel layout for long dialogues
    → Commit: fix(baoyu-comic): improve panel layout for long dialogues
    → No README updates

Changelog preview (en):
  ## 1.3.0 - 2026-01-22
  ### Features
  - Add watercolor and minimalist styles to cover-image
  ### Fixes
  - Improve panel layout for long dialogues in comic

Changelog preview (zh):
  ## 1.3.0 - 2026-01-22
  ### 新功能
  - 为 cover-image 添加水彩和极简风格
  ### 修复
  - 改进 comic 长对话的面板布局

Commits to create:
  1. feat(baoyu-cover-image): add watercolor and minimalist styles
  2. fix(baoyu-comic): improve panel layout for long dialogues
  3. chore: release v1.3.0

No changes made. Run without --dry-run to execute.
```

## Example Usage

```
/release-skills              # Auto-detect version bump
/release-skills --dry-run    # Preview only
/release-skills --minor      # Force minor bump
/release-skills --patch      # Force patch bump
/release-skills --major      # Force major bump (with confirmation)
/release-skills --backfill-releases  # Create missing GitHub Releases for existing tags
```

## When to Use

Trigger this skill when user requests:
- "release", "发布", "create release", "new version", "新版本"
- "bump version", "update version", "更新版本"
- "prepare release"
- "release notes", "GitHub Release", "回填 Release"
- "push to remote" (with uncommitted changes)

**Important**: If user says "just push" or "直接 push" with uncommitted changes, STILL follow all steps above first.

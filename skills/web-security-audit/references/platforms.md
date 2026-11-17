# Agent Skills 平台目录速查表

> 来源：Agent Skills 生态目录表（vercel-labs/skills README，2026-03 数据）。
> 用途：编写任何技能（skill）README 的"安装 / 平台兼容"章节时，直接引用本表；路径以各平台官方文档为准。

## 核心事实

**Agent Skills 是开放标准**（agentskills.io/specification，Anthropic 发起）——**同一个技能文件夹（SKILL.md + scripts/ + references/）在所有支持平台通用，无需适配**。安装 = 把技能目录解压到对应平台的 skills 目录。

## 通用组（共用 `.agents/skills/`，维护一个目录覆盖多个工具）

| 工具 | 全局目录 | 项目级目录 |
|---|---|---|
| GitHub Copilot | `~/.copilot/skills/` | `.github/skills/` |
| Cline | `~/.agents/skills/` | `.agents/skills/` |
| Codex (OpenAI) | `~/.codex/skills/`（部分文档为 `.agents/skills/`） | `.codex/skills/` |
| Cursor | `~/.cursor/skills/` | `.cursor/skills/` |
| Gemini CLI | `~/.gemini/skills/` | — |
| OpenCode | `~/.config/opencode/skills/` | — |
| Replit | `~/.config/agents/skills/` | — |
| Kimi Code CLI | `~/.config/agents/skills/` | — |
| Amp | `~/.config/agents/skills/` | — |

## 专属目录组（每个工具独立目录）

| 工具 | 全局目录 | 项目级目录 |
|---|---|---|
| Claude Code | `~/.claude/skills/` | `.claude/skills/` |
| **Trae / Trae CN**（字节） | `~/.trae/skills/` | `.trae/skills/` |
| **Qwen Code 通义**（阿里） | `~/.qwen/skills/` | `.qwen/skills/` |
| **CodeBuddy**（腾讯） | `~/.codebuddy/skills/` | `.codebuddy/skills/` |
| Windsurf | `~/.codeium/windsurf/skills/` | `.windsurf/skills/` |
| Antigravity (Google) | `~/.gemini/antigravity/skills/` | `.agent/skills/`（**单数**！） |
| Continue | `~/.continue/skills/` | `.continue/skills/` |
| Roo Code | `~/.roo/skills/` | `.roo/skills/` |
| Goose | `~/.config/goose/skills/` | `.goose/skills/` |
| OpenHands | `~/.openhands/skills/` | `.openhands/skills/` |
| Kilo Code | `~/.kilocode/skills/` | `.kilocode/skills/` |
| Qoder | `~/.qoder/skills/` | `.qoder/skills/` |
| Zencoder | `~/.zencoder/skills/` | `.zencoder/skills/` |
| WorkBuddy | `~/.workbuddy/skills/` | — |

## 编写 README 安装表的模板

```markdown
## Installation

Agent Skills is an open standard — the same skill folder works on every platform.
Unzip `<skill-name>/` into your platform's skills directory:

| Platform | Global path | Project path |
|---|---|---|
| Claude Code | `~/.claude/skills/` | `.claude/skills/` |
| OpenAI Codex CLI | `~/.codex/skills/` | `.codex/skills/` (or `.agents/skills/`) |
| Cursor | `~/.cursor/skills/` | `.cursor/skills/` |
| Gemini CLI | `~/.gemini/skills/` | — |
| GitHub Copilot | `~/.copilot/skills/` | `.github/skills/` |
| Windsurf | `~/.codeium/windsurf/skills/` | `.windsurf/skills/` |
| Cline / OpenCode / Kimi Code | `~/.agents/skills/` | `.agents/skills/` (shared) |
| Trae / Trae CN | `~/.trae/skills/` | `.trae/skills/` |
| Qwen Code (Alibaba) | `~/.qwen/skills/` | `.qwen/skills/` |
| WorkBuddy | `~/.workbuddy/skills/` | — |

> Paths per the Agent Skills ecosystem table; confirm with platform docs.
```

## 注意事项

- **单复数陷阱**：`.agents/skills/`（复数，Copilot/Cline/Cursor 等通用）vs `.agent/skills/`（单数，Antigravity 专用）——极易混淆，写文档时注意。
- 写 README 务必带"以官方文档为准"声明，平台目录会随版本演进。
- 安装技能可用 `npx skills add <owner/repo@skill-name>`（vercel-labs/skills CLI）批量安装到多个工具，或 `npx skills find <关键词>` 搜索生态。

---
name: cc-statusline
description: >-
  Configure Claude Code statuslines / 状态栏. Use this skill whenever the user wants to install, set up, preview, switch, clean up, customize, restore, or fix a Claude Code statusline: choose Full / Standard / Minimal / Developer presets, fine-tune an existing preset, generate-only or activate a custom 1 / 2 / 3-line layout with modules like model / git / context / token / cost, change theme or icon style, restore the default statusline while keeping scripts, or troubleshoot a broken statusLine command on Windows, macOS, or Linux. 也适用于安装、预览、切换预设、微调、美化、恢复默认、排障、自定义。 Only for Claude Code, not shell prompts, VS Code, Windows taskbar, web status bars, or Claude Desktop.
---

# cc-statusline / Claude Code 状态栏助手

## Purpose / 用途
Use this skill to help users preview, install, customize, switch, troubleshoot, and uninstall Claude Code statuslines.
当用户想预览、安装、自定义、切换、排障或卸载 Claude Code 状态栏时，使用这个 skill。

This skill is designed for:
这个 skill 主要适用于：
- preset installation / 安装预设状态栏
- interactive custom generation / 交互式自定义生成
- preset-based fine-tuning / 基于预设微调
- theme and icon switching / 切换主题与图标风格
- layout cleanup and readability improvement / 优化布局与可读性
- uninstall or restore-default workflows / 卸载或恢复默认状态栏
- Windows, macOS, Linux setup support / Windows、macOS、Linux 三端安装支持

## Runtime map / 运行路径映射
Treat this folder as the skill base directory.
把当前目录视为 skill 基目录。

Use these relative paths from the skill directory:
从 skill 目录出发，使用这些相对路径：
- `scripts/generate_custom_statusline.sh` → generate a custom runtime script / 生成自定义状态栏脚本
- `scripts/activate_preset_statusline.sh` → install or switch a preset / 安装或切换预设
- `scripts/activate_custom_statusline.sh` → activate a generated custom script / 启用生成好的自定义脚本
- `scripts/uninstall_statusline.sh` → remove only the `statusLine` config / 只移除 `statusLine` 配置

Default paths:
默认路径：
- preset target / 预设脚本：`~/.claude/statusline.sh`
- custom target / 自定义脚本：`~/.claude/statusline.custom.sh`
- settings / 设置文件：`~/.claude/settings.json`
- state snapshot / 状态快照：`~/.claude/cc-statusline-state.json`

## Language behavior / 语言行为
- Match the user’s input language when leading the conversation.
- Keep key labels bilingual when helpful, especially for preset names, themes, icon styles, and install steps.
- 根据用户输入语言切换主要交流语言。
- 对关键名词保留双语，尤其是预设名、主题名、图标风格、安装步骤。

## Intent routing / 意图分流
Map the request into one of these flows:
将请求归入以下流程之一：
- **Install preset / 安装预设**
- **Customize from scratch / 从零自定义**
- **Customize from a preset / 基于预设微调**
- **Beautify or optimize existing statusline / 美化或优化现有状态栏**
- **Uninstall or restore default / 卸载或恢复默认**
- **Troubleshoot installation / 排查安装问题**

## Trigger emphasis / 触发重点
Trigger this skill aggressively when the user is clearly talking about Claude Code and any of these intents:
当用户明确在说 Claude Code，并且出现以下任一意图时，应积极触发这个 skill：
- install or set up a statusline / 安装或配置状态栏
- choose or switch a preset / 选择或切换预设
- generate a custom layout / 生成自定义布局
- switch themes or icon styles / 切换主题或图标风格
- beautify, optimize, simplify, or improve readability / 美化、优化、精简、提升可读性
- disable, uninstall, or restore default behavior / 禁用、卸载、恢复默认
- troubleshoot a broken `statusLine` command or failed install / 排查损坏的 `statusLine` 命令或失败的安装

Do not trigger for shell prompts, terminal themes, Windows taskbar changes, VS Code status bars, or general web UI status bars unless the user clearly ties the request back to Claude Code.
除非用户明确把需求指向 Claude Code，否则不要把 shell prompt、终端主题、Windows 任务栏、VS Code 状态栏或网页状态栏误判为本 skill 的触发场景。

## Ask only what is missing / 只问缺失信息
Prioritize questions in this order:
按这个顺序补问：
1. preset vs custom / 预设还是自定义
2. modules / 模块开关
3. line count / 行数（1/2/3）
4. theme / 主题
5. icon style / 图标风格
6. target path / 目标路径
7. activate now / 是否立即启用

Prefer grouped module presentation:
模块优先按分组展示：
- Base group / 基础信息
- Environment group / 环境信息
- Metrics group / 统计信息

Read `references/modules.md` when you need the canonical module list.
需要标准模块清单时读取 `references/modules.md`。

## Presets / 预设
Available presets:
可用预设：
- `Full / 完整版`
- `Standard / 标准版`
- `Minimal / 极简版`
- `Developer / 开发者版`

Preset goals:
预设定位：
- **Full / 完整版**: closest to the current full Miluer-style information density / 最接近当前 Miluer 风格的完整信息密度
- **Standard / 标准版**: balanced for daily use / 适合日常使用
- **Minimal / 极简版**: lowest visual noise / 最低视觉干扰
- **Developer / 开发者版**: emphasizes git and token visibility / 强调 Git 与 Token 可见性

Use `presets/*.json` for line count and module summaries before presenting options.
在展示选项前，使用 `presets/*.json` 获取行数与模块摘要。

## Preview rule / 预览规则
Always show a concise preview before writing files or changing `statusLine.command`.
在写文件或改 `statusLine.command` 前，始终先给出简洁预览。

Use this structure:
使用这个结构：

```text
Statusline preview / 状态栏预览
- Mode / 模式: preset | custom
- Preset / 预设: <preset or custom>
- Lines / 行数: <1|2|3>
- Line 1 / 第 1 行: <modules>
- Line 2 / 第 2 行: <modules or empty>
- Line 3 / 第 3 行: <modules or empty>
- Theme / 主题: <theme>
- Icon style / 图标风格: <icon style>
- Target / 目标文件: <path>
- Backup / 备份: <path or not needed>
- settings.json change / 设置改动: only statusLine
- Activation / 启用方式: now | generate only
```

If the user already asked for one-click install and the context is clear, preview first and then execute.
如果用户已经明确要求一键安装且上下文清晰，先预览再执行。

## Execution flows / 执行流程

### A. Install preset / 安装预设
Use this flow when the user wants a ready-made statusline.
当用户要直接套用预设时使用。

1. If the preset is not specified, offer the 4 presets with short summaries.
2. Resolve theme, icon style, and target path.
3. Preview the exact result.
4. Run:

```bash
bash "scripts/activate_preset_statusline.sh" "<preset>" "<theme>" "<icon_style>" "<target_path>"
```

Default target path:
默认目标路径：
```bash
~/.claude/statusline.sh
```

After the command finishes, report:
命令完成后汇报：
- active command / 当前启用命令
- target file / 目标文件
- backup file / 备份文件
- state snapshot / 状态快照文件
- that only `statusLine` was changed / 仅修改了 `statusLine`

### B. Customize from scratch / 从零自定义
Use this when the user wants grouped module selection or a fresh layout.
当用户要按模块分组自由搭配时使用。

1. Read `references/modules.md` if needed.
2. Collect modules per line.
3. Determine line count.
4. Determine theme, icon style, target path, and whether to activate now.
5. Preview the custom layout.
6. Generate the custom script with:

```bash
bash "scripts/generate_custom_statusline.sh" "<custom_path>" "<line_1_csv>" "<line_2_csv_or_->" "<line_3_csv_or_->" "<theme>" "<icon_style>"
```

Notes:
说明：
- Use comma-separated module ids such as `model,modes,active`.
- For unused lines, pass `-`.
- 使用逗号分隔的模块 id，例如 `model,modes,active`。
- 对不使用的行传入 `-`。

Examples:
示例：
```bash
bash "scripts/generate_custom_statusline.sh" "$HOME/.claude/statusline.custom.sh" "model,modes,active" "cwd,git,context" "ctx_tokens,sum_tokens,duration,cost" "ocean" "developer"
```

One-line custom example:
单行自定义示例：
```bash
bash "scripts/generate_custom_statusline.sh" "$HOME/.claude/statusline.custom.sh" "model,active,cost" "-" "-" "mono" "minimal"
```

If the user wants immediate activation, then run:
如果用户要立即启用，再运行：

```bash
bash "scripts/activate_custom_statusline.sh" "<custom_path>" "<theme>" "<icon_style>"
```

If the user only asked to generate or preview, stop after generation and explain how to activate later.
如果用户只要求生成或预览，生成后停止，并说明后续如何手动启用。

### C. Customize from a preset / 基于预设微调
Use the preset as the starting point, then adjust lines/modules/theme/icons.
以预设为起点，再调整行数、模块、主题、图标。

1. Load the selected preset summary from `presets/*.json`.
2. Present it as the starting layout.
3. Apply the user’s module or line-count changes.
4. Generate with `scripts/generate_custom_statusline.sh`.
5. Activate with `scripts/activate_custom_statusline.sh` only if the user wants the new custom script live now.

### D. Beautify or optimize / 美化或优化
Choose the smallest useful change.
优先选最小但有效的变更。

Use this decision rule:
使用这个判断顺序：
1. **Theme or icon only / 只改主题或图标** → re-run preset activation with the same preset and new style if the user is still using a preset layout.
2. **Modules or line count changed / 改模块或行数** → generate a custom script.
3. **Unclear request / 需求不明确** → offer 2-3 concrete options instead of asking broad questions.

### E. Uninstall or restore default / 卸载或恢复默认
Run:

```bash
bash "scripts/uninstall_statusline.sh"
```

Then explain:
然后说明：
- only the `statusLine` entry was removed / 只移除了 `statusLine`
- generated script files were kept / 已保留生成的脚本文件
- the previous snapshot remains in `~/.claude/cc-statusline-state.json` if available / 如存在，旧配置快照仍保留在 `~/.claude/cc-statusline-state.json`

### F. Troubleshoot installation / 排查安装问题
When install or activation fails, inspect in this order:
安装或启用失败时，按这个顺序排查：
1. target script exists / 目标脚本是否存在
2. `~/.claude/settings.json` contains the expected `statusLine` / `settings.json` 是否写入预期 `statusLine`
3. jq availability / jq 是否可用
4. whether an old foreign `statusLine` blocked overwrite / 是否被旧的外部配置拦住
5. whether re-running the wrapper is enough / 是否只需重跑脚本

Prefer re-running the wrapper script over telling the user to edit JSON manually.
优先重跑封装脚本，而不是直接让用户手改 JSON。

Only fall back to manual repair when automation fails.
只有自动流程失败时再给手动修复步骤。

## Settings safety / 设置安全规则
- Only touch the `statusLine` field.
- Do not rewrite unrelated settings.
- If an existing `statusLine` looks foreign, ask before replacement.
- Do not delete generated scripts unless the user explicitly requests deletion.
- 只修改 `statusLine`。
- 不改动无关设置。
- 如果现有 `statusLine` 看起来不是本 skill 生成的，替换前先询问。
- 除非用户明确要求，否则不要删除已生成脚本。

## Response style / 回复风格
- Be concise but structured.
- Summarize the selected options clearly.
- Preview before writing.
- After running commands, report what changed and where.
- Keep key choices bilingual.
- 简洁但结构清晰。
- 清楚总结已选项。
- 写入前先预览。
- 执行后说明改了什么、改到哪里。
- 关键选项保留双语。

## Post-action summary / 执行后总结
After installation, generation, activation, or uninstall, end with a short summary like:
安装、生成、启用或卸载后，用类似下面的格式收尾：

```text
Done / 已完成
- Generated / 生成: <file or not needed>
- Updated / 更新: ~/.claude/settings.json (statusLine only)
- Backup / 备份: <path or none>
- Snapshot / 快照: ~/.claude/cc-statusline-state.json
- Active command / 当前命令: <statusLine.command or not active>
- Next step / 下一步: <optional suggestion>
```

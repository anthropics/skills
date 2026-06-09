# Trigger phrases / 触发词清单

## Trigger rule / 触发规则
Use this skill when the request is about **Claude Code** statusline / status bar behavior.
当请求明确在说 **Claude Code** 的状态栏时，使用这个 skill。

Trigger even for casual phrasing if the intent is clearly one of these:
即使表达很口语化，只要意图明显属于以下类型，也应触发：
- install or configure / 安装或配置
- choose or switch presets / 选择或切换预设
- generate custom layouts / 生成自定义布局
- switch themes or icon styles / 切换主题或图标风格
- beautify or optimize / 美化或优化
- uninstall or restore default / 卸载或恢复默认
- troubleshoot broken setup / 排查失效配置

Do not trigger when the user is really asking about shell prompts, Windows taskbar styling, VS Code status bars, or generic web app UI bars unless they clearly tie it back to Claude Code.
如果用户真正想说的是 shell prompt、Windows 任务栏、VS Code 状态栏或网页 UI 状态栏，而不是 Claude Code，就不要误触发。

## Install / 配置 / 安装
### English
- install Claude Code statusline
- setup a status bar for Claude Code
- configure my Claude Code statusline
- add a statusline to Claude Code
- give me a preset statusline for Claude Code
- help me set up Claude Code status bar on Windows

### 中文
- 安装 Claude Code 状态栏
- 配置状态栏
- 帮我设置 Claude Code 状态栏
- 给 Claude Code 加个状态栏
- 给我一键配置状态栏
- 帮我装一个预设状态栏

## Preset switch / 预设切换
### English
- switch to the developer preset
- change my statusline preset to minimal
- use a cleaner preset for Claude Code
- switch back to the full preset

### 中文
- 把状态栏切到开发者版
- 换成极简版状态栏
- 切回完整版预设
- 给我换一个更清爽的预设

## Customize / 自定义 / 生成
### English
- create a custom Claude Code statusline
- build a one-line statusline for Claude Code
- generate a custom layout from the full preset
- customize my statusline with git and token info
- switch the statusline theme
- change the icon style for Claude Code statusline

### 中文
- 生成自定义状态栏
- 自定义 Claude Code 状态栏
- 帮我做一个 2 行状态栏
- 从完整版改一个自定义布局
- 只保留 Git、Token、Context
- 调整状态栏主题
- 切换状态栏图标风格

## Beautify / Optimize / 美化 / 优化
### English
- beautify Claude Code statusline
- optimize statusline layout
- improve statusline readability
- make the statusline cleaner
- simplify my Claude Code status bar

### 中文
- 美化 Claude Code 状态栏
- 优化状态栏布局
- 让状态栏更清晰
- 调整状态栏样式
- 把状态栏做得更干净一点

## Uninstall / Restore / 卸载 / 恢复默认
### English
- uninstall statusline
- disable statusline
- restore default statusline
- remove statusline setup
- go back to the default Claude Code status bar

### 中文
- 卸载状态栏
- 禁用状态栏
- 恢复默认状态栏
- 移除状态栏配置
- 切回默认的 Claude Code 状态栏

## Troubleshoot / 排障 / 修复
### English
- fix my Claude Code statusline install
- the statusLine command is broken
- my statusline stopped working
- troubleshoot Claude Code status bar setup
- help me repair the statusline config

### 中文
- 帮我修状态栏安装
- 状态栏装完没生效
- statusLine 配置坏了
- 帮我排查 Claude Code 状态栏问题
- 修一下状态栏命令

## Near misses / 临界不触发场景
These are intentionally similar, but should **not** trigger this skill unless the user later clarifies they mean Claude Code.
这些表达看起来接近，但除非用户后续明确说的是 Claude Code，否则**不应**触发本 skill。

### English
- make my zsh prompt cleaner
- customize the VS Code status bar
- change my Windows taskbar style
- build a web app status bar component
- theme my terminal prompt with git info

### 中文
- 美化我的 zsh 提示符
- 改 VS Code 状态栏颜色
- 调整 Windows 任务栏样式
- 做一个网页顶部状态栏组件
- 给终端 prompt 加 Git 信息

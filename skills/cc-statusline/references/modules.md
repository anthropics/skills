# Modules / 模块说明

## Base group / 基础信息
- `model` — model name / 模型名称
- `modes` — effort, think, fast, permission mode / Effort、Think、Fast、权限模式
- `version` — Claude Code version / Claude Code 版本
- `active` — active session marker / 活跃会话标记

## Environment group / 环境信息
- `context` — context bar and usage pressure / 上下文占用与进度条
- `tools` — skills and MCP counts / Skills 与 MCP 数量
- `cwd` — current directory / 当前目录
- `git` — branch and change status / 分支与改动状态

## Metrics group / 统计信息
- `ctx_tokens` — current context input/output tokens / 当前上下文输入输出 Token
- `sum_tokens` — cumulative session token totals / 会话累计 Token
- `duration` — API and total duration / API 耗时与总耗时
- `cost` — visible session cost when non-zero / 非 0 时显示费用

## Custom extensions / 自定义扩展
- Additional modules can be proposed by the user and mapped into the generated script if they are safe and clearly defined.
- 用户可以提出额外模块，只要语义明确且实现安全，就可以映射进生成脚本。

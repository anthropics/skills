---
name: review
description: |
  生成每日 Claude Code 使用复盘 — 成本、习惯、改进建议。
  触发词：review、复盘、今天干了啥、日报、usage report。
  不用于：代码 review 或 PR review。
argument-hint: "[日期: YYYY-MM-DD，默认今天] [--save 保存到文件]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - WebFetch
---

# Review Skill — 每日使用复盘（中文版）

## 执行步骤

### 1. 确定日期
使用传入参数，否则默认今天。格式：`YYYY-MM-DD`。

### 2. Token 成本分析

检测 ccusage：
```bash
command -v ccusage &>/dev/null && echo "has_ccusage" || echo "no_ccusage"
```

**有 ccusage**：
```bash
ccusage session        # 当前 session
ccusage daily --days 7 # 7天趋势
```

**无 ccusage（JSONL fallback）**：
```python
import json, glob, os
from datetime import date, timedelta

def get_day_stats(day_str):
    keys = ["input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens"]
    total = {k: 0 for k in keys}
    sessions, small = 0, 0
    for f in glob.glob(os.path.expanduser("~/.claude/projects/*/*.jsonl")):
        if "subagents" in f: continue
        if date.fromtimestamp(os.path.getmtime(f)).isoformat() != day_str: continue
        sessions += 1
        msgs = 0
        with open(f) as fp:
            for line in fp:
                try:
                    msg = json.loads(line)
                    if msg.get("type") == "assistant":
                        msgs += 1
                        for k in keys:
                            total[k] += msg.get("message", {}).get("usage", {}).get(k, 0) or 0
                except: pass
        if msgs <= 5: small += 1
    inp, out, cc, cr = total["input_tokens"], total["output_tokens"], total["cache_creation_input_tokens"], total["cache_read_input_tokens"]
    cost = (inp*3 + out*15 + cc*3.75 + cr*0.30) / 1_000_000
    return sessions, small, cost

today = "{DATE}"
sessions, small, cost = get_day_stats(today)
print(f"今日: {sessions} sessions, 预估 ${cost:.2f}")
print(f"短会话(≤5条): {small} 个")

from datetime import date as d
base = d.fromisoformat(today)
for i in range(6, -1, -1):
    day = (base - timedelta(days=i)).isoformat()
    s, _, c = get_day_stats(day)
    if s: print(f"{day}: {s} sessions, ${c:.2f}")
```

从数据中提炼 **1-2 条核心建议**。

### 3. 提取 bash 命令（如有 hook）

```bash
[ -f ~/.claude/hooks/logs/bash-history.log ] && \
  grep "^\[{DATE}" ~/.claude/hooks/logs/bash-history.log || echo "no_hook"
```

如有，统计：命令总数、最常用工具类型（git/python/ssh/curl 等）、活跃项目目录。

### 4. Skill 使用情况

**4a. 用户已安装 skill 列表：**
```bash
ls ~/.claude/skills/ | grep -v INDEX
```

**4b. 近 3 天用了哪些 skill：**
从 bash-history 和 session JSONL 中检测 skill 调用（grep "Launching skill" 或 skill 名称出现在 history 中）：
```bash
# 近 3 天 bash history 中出现的 skill 名
for i in 0 1 2; do
  DAY=$(date -v-${i}d +%Y-%m-%d 2>/dev/null || date -d "{DATE} -${i} days" +%Y-%m-%d)
  grep "^\[$DAY" ~/.claude/hooks/logs/bash-history.log 2>/dev/null
done | grep -oE '/(review|clip|cost|status|publish|wrap|eileen|decide|batch-process|claude-to-im)\b' | sort -u
```

**输出**：
- 今天用了哪些 skill
- 近 3 天**完全没用过**的 skill → 提示用户是否要删除/清理

### 5. 命令 & Skill 推荐（硬性要求，每次必须输出）

**5a. 获取最新 CHANGELOG：**
```
WebFetch: https://raw.githubusercontent.com/anthropics/claude-code/main/CHANGELOG.md
提示词: 提取最近 3 个版本中新增的斜杠命令（/xxx）或命令行功能。每条：命令名、一句话说明、版本号。
```

**5b. 获取官方 skill 列表：**
```
WebFetch: https://raw.githubusercontent.com/anthropics/claude-code/main/SKILLS.md
提示词: 列出所有官方推荐的 skill，每条：名称、一句话说明、安装方式。
```
如果 SKILLS.md 不存在，用 CHANGELOG 中提到的官方 skill/plugin 信息代替。

**5c. 必须推荐以下内容（硬性规定，缺一不可）：**

| 类别 | 数量 | 来源 | 选择标准 |
|------|------|------|----------|
| 最新命令 | 1-2 个 | CHANGELOG 最近版本 | 新增的 `/命令` 或 CLI 功能 |
| 常用但未用 | 2 个 | Claude Code 内置命令 | 用户今天没用过，但跟工作场景匹配的高频命令 |
| 官方 Skill | 2 个 | 官方 skill 列表/CHANGELOG | 官方发布或推荐的 skill |

**内置命令参考列表**（用于判断"常用但未用"）：
- `/compact` — 压缩上下文，节省 token
- `/resume` — 恢复之前的 session
- `/model` — 切换模型
- `/cost` — 查看当前花费
- `/memory` — 管理记忆
- `/help` — 查看帮助
- `/config` — 修改配置
- `/terminal` — 打开终端
- `/vim` — vim 模式
- `/fast` — 快速模式（同一个 Opus 模型，更快输出）
- `/clear` — 清除上下文
- `/login` — 登录
- `/pr-review` — PR 评审
- `/init` — 初始化项目 CLAUDE.md

每条推荐必须说明**为什么适合这个用户**（结合当天的操作和习惯）。

### 6. 生成输出

输出格式（控制在 25 行以内）：

```
# 复盘 · {DATE}

**今日概览**：{N} sessions · {N} 条命令 · 预估 ${X.XX}
**7天均值**：${X.XX}/天 · 本周共 ${X.XX}

**你做了什么**
- [3条，从命令和 session 推断，要具体]

**建议**
- [1-2条成本/习惯建议，有数据支撑]

**Skill 使用**
- 今天用了：/xxx, /yyy
- 近3天没用过：/aaa, /bbb → 考虑是否需要？

**推荐**
- 🆕 最新命令：`/xxx`（vX.X.X）— [说明 + 为什么适合你]
- 💡 你可能需要：`/xxx` — [结合今天场景说明]、`/yyy` — [说明]
- 📦 官方 Skill：`skill-name` — [说明]、`skill-name` — [说明]

**明日一件事**：[最高优先级的一个改变]
```

### 7. 保存（可选）

- 传入 `--save`：保存到 `./review-{DATE}.md`
- 在 `*/observer/*` 目录下：自动保存到 `daily-reviews/{DATE}.md`
- 否则仅展示

---

**注意**：无 bash-history hook 时，在末尾加一行：
`💡 安装 bash-history hook 可获得更精准的命令分析`

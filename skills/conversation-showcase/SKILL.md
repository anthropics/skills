---
name: conversation-showcase
description: Generates shareable social media images from Claude Code conversations. Renders chat-style dialogue with tool execution steps as beautiful PNG cards. Use when user asks to "showcase conversation", "对话展示", "对话卡片", "分享对话", "conversation card", "show off this chat", or wants to create shareable images from their Claude Code session.
---

# Conversation Showcase

Transform the current Claude Code conversation into a beautiful, shareable social media image. Renders chat-style dialogue with tool execution steps as a polished PNG card.

## Usage

```bash
/conversation-showcase                         # Auto-extract, Anthropic 主题, 小红书比例
/conversation-showcase --theme dark             # Dark theme
/conversation-showcase --theme terminal         # Retro terminal aesthetic
/conversation-showcase --aspect square          # 1:1 for Instagram
/conversation-showcase --title "自定义标题"      # Override auto-generated title
/conversation-showcase --range last-3           # Only last 3 exchanges
```

## Options

| Option | Values | Default |
|--------|--------|---------|
| `--theme` | `anthropic`, `dark`, `terminal` | `anthropic` |
| `--aspect` | `xhs` (1080×1440), `portrait` (1080×1350), `square` (1080×1080), `story` (1080×1920), `landscape` (1200×675) | `xhs` |
| `--title` | Custom title string | Auto-generated from conversation |
| `--range` | `all`, `last-N`, `best` | `best` (auto-select most impactful moments) |
| `--lang` | `zh`, `en`, `ja` | Auto-detect from conversation |
| `--style` | `flat`, `timeline` | `flat` (tool blocks as flat list; `timeline` adds vertical connector) |
| `--user` | Custom user avatar text | `coco` |

## Aspect Dimensions

| Aspect | Card Size (CSS px) | Chrome window-size | Best For |
|--------|--------------------|--------------------|----------|
| **xhs** | 1080 × 1440 | 1080,1440 | **小红书 3:4（默认）** |
| portrait | 1080 × 1350 | 1080,1350 | Instagram |
| square | 1080 × 1080 | 1080,1080 | 通用社交媒体 |
| story | 1080 × 1920 | 1080,1920 | Stories, 抖音, 长对话 |
| landscape | 1200 × 675 | 1200,675 | Twitter/X, 微博 |

**IMPORTANT: Content must fit within the target height.** With the large font sizes (optimized for mobile reading), each dialogue exchange takes ~200-250px. For `xhs` (1440px), max 3-4 exchanges + 1 tool block is ideal. If content overflows, reduce exchanges or combine tool blocks.

## Output

```
~/Desktop/conversation-showcase/
├── showcase-{slug}-{HHMMSS}.html    # Source HTML (reusable)
└── showcase-{slug}-{HHMMSS}.png     # Final image
```

Slug: 2-4 words kebab-case from task topic.

## Workflow

### Step 1: Extract Conversation

Review the ENTIRE current conversation and extract key moments. Organize into a mental model:

**What to extract:**

| Element | Source | How to present |
|---------|--------|---------------|
| User commands | User's messages | Keep original text, trim to 1-2 lines max |
| Claude thinking | Claude's initial analysis | Summarize to one sentence |
| Tool executions | Tool calls (Read, Edit, Bash, etc.) | Tool name + target + brief result |
| Key results | Claude's final responses | Core insight/outcome, 2-3 lines max |
| Outcome | Final state | Success indicators, test results, etc. |

**Output mode — single image vs. series:**

By default, generate a **2-3 page series**. Only use a single image if the conversation is very short (≤ 3 exchanges) or the user explicitly requests `--single`.

**Series structure (起承转合):**

| Page | Role | Content |
|------|------|---------|
| **1 — Cover (封面)** | Hook — 告诉观众这是什么 | Tag + 大标题 + 摘要描述 + 关键成果亮点（NO dialogue on cover） |
| **2 — Body (正文)** | Show the journey | 对话流：问题 → 调研/分析 → 方案实施。4-6 段，自然承接 |
| **3 — Result (可选)** | Deliver the payoff | 如内容多，继续正文 + 最终成果清单 |

**Cover page is NOT a dialogue page.** It's a poster/card that states:
1. What task was accomplished (title)
2. A 2-3 sentence summary of the outcome (`.cover-desc`)
3. Key highlights/stats in a card (`.cover-stats`)
This hooks viewers to swipe and see HOW it was done.

**Body pages show the actual conversation**, naturally flowing from problem → reasoning → solution. Content should never feel "cut off" between pages — each page ends at a natural exchange boundary.

Each page has:
- Consistent header (window chrome + "✦ Claude Code")
- **Phase label** on pages 2+ (e.g., "调研 · 研究现有方案") — centered text with horizontal rules on both sides
- **Page indicator dots** at the bottom — active dot for current page, hollow dots for others
- Consistent footer

**How to decide page count:**
- Simple fix/question: 2 pages (cover + body)
- Feature with iteration: 2-3 pages (cover + body + result)
- Keep it tight — more than 3 pages causes viewer fatigue on social media

**Curation rules (CRITICAL for visual quality):**

1. **4-6 dialogue elements per page** (messages + tool blocks) — fill 80-90% of the page height, avoid leaving the bottom half empty
2. **Prefer "wow" moments** — the exchanges that best show the value of the conversation
3. **Group consecutive tool calls** into a single tool execution block
4. **Summarize long Claude responses** — extract only the key takeaway
5. **User messages stay short** — use original text or summarize to ≤ 2 lines
6. **Show the PROCESS, not just the result** — viewers want to see multi-turn interaction, iteration, and problem-solving
7. **Always include the final outcome on the last page** — this is the payoff that makes viewers go "wow"

**Tag classification** — assign one tag based on what happened:

| Tag | When |
|-----|------|
| Bug Fix | Fixed a bug or error |
| Feature | Built new functionality |
| Refactor | Restructured/improved code |
| Debug | Investigated and resolved an issue |
| Setup | Set up project/environment |
| Design | Created visual/UI work |
| Research | Explored/analyzed codebase or topic |
| Automation | Automated a workflow |

### Step 2: Generate HTML

1. Read the template at `references/template.html` (relative to this SKILL.md)
2. Create a NEW HTML file based on the template, filling in:
   - Replace `__CARD_WIDTH__` and `__CARD_HEIGHT__` based on `--aspect` option (default: 1080 × 1440 for xhs)
   - Add theme class to `<html>` element: (none) = anthropic (default), `class="theme-dark"`, `class="theme-terminal"`
   - Replace `__TASK_TAG__` with the classified tag
   - Replace `__TASK_TITLE__` with auto-generated or user-specified title
   - Replace `<!-- __MESSAGES_CONTENT__ -->` with the actual message elements

**Theme details:**
- **anthropic** (default): Warm cream background (#e8e6dc), white cards, clay accent (#d97757) — matches anthropic.com
- **dark**: Deep dark background, blue user bubbles, green tool text
- **terminal**: Pure black, green monochrome, retro terminal feel

**Avatar details:**
- **User avatar**: `<div class="avatar">U</div>` — single letter in clay circle. Use `--user` to customize text.
- **Claude avatar**: `<div class="avatar"></div>` — empty div, Claude Code terminal face rendered via CSS `background-image`
- The face is a 12×8 SVG matching the Claude Code terminal ASCII art (▗▗ ▖▖ / ▘▘▝▝): 4 dots for eyes + 4 dots for smile, in clay color on light background

3. Build message elements using these HTML patterns:

**User message:**
```html
<div class="msg msg-user">
  <div class="avatar">U</div>
  <div class="bubble">用户消息文本</div>
</div>
```

Note: User avatar defaults to "U". Use `--user` to customize (e.g., `--user coco`).

**Claude message (simple):**
```html
<div class="msg msg-claude">
  <div class="avatar"></div>
  <div class="bubble">Claude 回复文本</div>
</div>
```

Note: Claude avatar is an empty div — the pixel art robot face is rendered via CSS background-image from the template.

**Claude message (with result list):**
```html
<div class="msg msg-claude">
  <div class="avatar"></div>
  <div class="bubble">
    总结文本
    <ul class="result-list">
      <li><span class="bullet">•</span> 要点一</li>
      <li><span class="check">✓</span> 测试通过</li>
    </ul>
  </div>
</div>
```

**Tool execution block:**
```html
<div class="tools">
  <div class="tools-header">
    <span class="bolt">⚡</span> Actions
  </div>
  <div class="tool-item">
    <span class="icon">📖</span>
    <span class="label">Read src/App.tsx</span>
  </div>
  <div class="tool-item">
    <span class="icon">✏️</span>
    <span class="label">Edit src/App.tsx</span>
    <span class="meta">+12 -3</span>
  </div>
  <div class="tool-item">
    <span class="icon">⚡</span>
    <span class="label">npm test</span>
    <span class="status-ok">✓</span>
  </div>
</div>
```

**Tool execution block (timeline style, when `--style timeline`):**
```html
<div class="tools tools-timeline">
  <div class="tools-header">
    <span class="bolt">⚡</span> Execution
  </div>
  <!-- same tool-item elements -->
</div>
```

**Code diff block (optional, for showing key code changes):**
```html
<div class="diff-block">
  <div class="diff-remove">- const old = "before";</div>
  <div class="diff-add">+ const updated = "after";</div>
</div>
```

### Tool Icon Reference

| Tool | Icon | Display Format |
|------|------|---------------|
| Read | 📖 | Read {filename} |
| Edit | ✏️ | Edit {filename} |
| Write | 📝 | Create {filename} |
| Bash | ⚡ | {command summary} |
| Grep | 🔍 | Search: {pattern} |
| Glob | 📁 | Find: {pattern} |
| Agent | 🤖 | {agent description} |
| WebSearch | 🌐 | Search: {query} |
| WebFetch | 🌐 | Fetch: {domain} |
| Test pass | ✓ | Use `.status-ok` class |
| Test fail | ✗ | Use `.status-err` class |

**Page-specific HTML patterns:**

Page 1 (Cover): Include `.task-tag` + `.task-title` before `.messages`
Pages 2+: Replace tag/title with a `.phase-label`:
```html
<div class="phase-label">调研 · 研究现有方案</div>
```

Page indicator (all pages): Add before `.footer`:
```html
<div class="page-indicator">
  <span class="page-dot active"></span>  <!-- current page -->
  <span class="page-dot"></span>
  <span class="page-dot"></span>
  <span class="page-dot"></span>
</div>
```

### Step 3: Save HTML

```bash
mkdir -p ~/Desktop/conversation-showcase
```

**Single image**: `showcase-{slug}-{HHMMSS}.html`
**Series**: `showcase-{slug}-{HHMMSS}-01.html`, `-02.html`, `-03.html`, etc.

### Step 4: Render to PNG

**Render each HTML file to PNG using Chrome headless:**

```bash
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
  --headless=new \
  --disable-gpu \
  --screenshot="$HOME/Desktop/conversation-showcase/showcase-{slug}-{HHMMSS}-01.png" \
  --window-size={width},{height} \
  --force-device-scale-factor=2 \
  --hide-scrollbars \
  "file://$HOME/Desktop/conversation-showcase/showcase-{slug}-{HHMMSS}-01.html"
```

**For series: render all pages sequentially** (Chrome headless can only do one at a time). Loop through all HTML files and render each to its corresponding PNG.

**IMPORTANT:**
- Always use `--force-device-scale-factor=2` for Retina-quality output (produces 2x resolution PNG)
- The `--window-size` must match the card dimensions from the aspect table
- Use `--hide-scrollbars` to prevent scrollbar artifacts
- Use absolute `file://` path for the HTML file
- GPU-related warnings in stderr are harmless — check for "bytes written to file" to confirm success

**Fallback 1 — Chromium:**
```bash
chromium --headless=new --screenshot=... (same flags)
```

**Fallback 2 — Browser MCP tools:**
1. Use `mcp__claude-in-chrome__tabs_create_mcp` to open a new tab
2. Use `mcp__claude-in-chrome__navigate` to open the HTML file
3. Use `mcp__claude-in-chrome__computer` with action "screenshot" to capture

**Fallback 3 — Manual:**
Inform the user: "HTML 文件已生成，请在浏览器中打开并手动截图。"

### Step 5: Output Summary

Report to user:
- What conversation moments were captured
- Theme and aspect used
- Output file paths (HTML + PNG)
- Suggest: "你可以用 HTML 文件调整内容后重新截图，或直接分享 PNG"

## Tone Principles (CRITICAL)

**Honest representation of human-AI collaboration:**

1. **NEVER say "一句话生成" or imply AI did everything alone.** Real work involves multiple rounds of human feedback, domain expertise, and iterative refinement. The showcase must reflect this.
2. **Show the human's contribution.** User messages contain expertise, judgment, and feedback that shaped the outcome. Highlight these — they are not just "prompts".
3. **Cover page summary must credit both sides.** E.g., "通过多轮对话，将个人交易经验与 AI 编程能力结合" — NOT "AI 自动生成了完整系统".
4. **Avoid hype language.** No "魔法"、"一键"、"自动完成". Use factual, grounded descriptions of what happened.
5. **The body pages already show collaboration naturally** — user feedback → Claude adjustment cycles. Do not flatten this into a linear "AI does everything" narrative.

## Visual Design Principles

1. **Cover = poster, Body = dialogue** — clear separation of roles
2. **4-6 elements per body page** — fill 80-90% of height, no empty bottom half
3. **Clean typography** — Inter for UI text, JetBrains Mono for code/tools
4. **Anthropic design language** — warm slate palette, clay accent (#d97757)
5. **Claude avatar** — terminal face (▗▗ ▖▖ / ▘▘▝▝), NOT ✦ symbol or pixel robot
6. **No content cutoff** — each page ends at a natural exchange boundary

## Branding

- **Header**: `✦ Claude Code`
- **Footer**: `✦ Claude Code`

## Tips

- Default to 2 pages (cover + body). Add a 3rd only if the conversation has distinct phases.
- Cover should be accessible to non-technical viewers — focus on outcomes, not implementation details.
- Body pages should show the multi-turn nature: user expertise + AI execution + iterative refinement.
- The HTML files are fully editable — user can tweak text and re-screenshot.

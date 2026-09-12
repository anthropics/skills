# 设计系统文件集 — AI 辅助 UI 开发

本目录包含 **50 个顶级品牌**的设计系统文件，专为 AI 编程助手（Claude Code 等）优化，帮助生成高度一致的品牌化 UI 代码。

## 目录结构

每个品牌子目录包含以下文件：

```
01-vercel/
├── DESIGN.md          # 设计系统规范（中文版）
├── CLAUDE.md          # AI 助手使用规则
├── preview.html       # 设计令牌可视化预览（浅色主题）
└── preview-dark.html  # 设计令牌可视化预览（深色主题）
```

---

## 使用方式

### 方式一：在 Claude Code 项目中使用

1. 选择目标品牌，将设计文件复制到你的项目根目录：

```bash
# 示例：使用 Vercel 风格设计系统
cp 01-vercel/DESIGN.md  /your-project/DESIGN.md
cp 01-vercel/CLAUDE.md  /your-project/CLAUDE.md
```

2. 启动 Claude Code，直接让它生成 UI：

```
请使用 DESIGN.md 中定义的设计系统构建此界面
```

Claude Code 会读取 `CLAUDE.md` 中的规则，并根据 `DESIGN.md` 生成与品牌高度一致的代码。

---

### 方式二：Claude Code 全局规则（推荐）

将 `CLAUDE.md` 放在项目根目录后，Claude Code 在每次对话中都会自动遵循以下规则：

| 规则项 | 说明 |
|--------|------|
| **颜色** | 仅使用 `DESIGN.md` 中定义的 hex 值 |
| **字体** | 仅使用规范中定义的字体系列和字号 |
| **组件** | 按照按钮、卡片、表单规范严格执行 |
| **间距** | 使用规范中的值，基础单位通常为 8px |
| **圆角** | 按各组件类型的对应值执行 |
| **阴影** | 按阴影层级规范应用对应深度 |

---

### 方式三：通过 MCP 工具调用（Agent 流程）

在 Agent 编排系统中，可以让子 agent 先读取 `DESIGN.md`，再生成 UI 代码：

```python
# 伪代码示例
design_spec = read_file("DESIGN.md")
prompt = f"参照以下设计系统规范生成一个登录页面：\n\n{design_spec}"
ui_code = agent.generate(prompt)
```

---

## 四个文件的关系与调用链

### 文件定位

```
品牌目录/
├── DESIGN.md         ← 数据源（机器可读的设计规范，9 个章节）
├── CLAUDE.md         ← 规则注入（告诉 AI 如何使用 DESIGN.md）
├── preview.html      ← 人类视觉验证 + AI Token 基准（浅色主题）
└── preview-dark.html ← 人类视觉验证 + AI Token 基准（深色主题）
```

### 调用链

```
人类操作                    AI 内部流程                输出
──────────────────────────────────────────────────────────────
复制品牌目录到项目根目录
         │
         ▼
CLAUDE.md 被 Claude Code 自动读取   ← 每次会话启动时自动加载
（文件名 CLAUDE.md 触发自动扫描）
         │
         │  CLAUDE.md 内写明：
         │  "编写任何 UI 代码前，先读 DESIGN.md"
         ▼
DESIGN.md 被 AI 按需读取
（包含颜色 / 字体 / 间距 / 圆角 / 阴影的具体数值）
         │
         ▼
AI 生成代码时自动套用设计 token
（不会出现随意颜色、不一致字号）
         │
         ▼
人类用 preview.html 对照验证
（这是标准答案，看生成的 UI 是否吻合）
```

### 各文件职责

| 文件 | 角色 | 使用者 |
|------|------|--------|
| `DESIGN.md` | 设计意图描述，9 章节文字规范 | AI 读取获取设计背景 |
| `CLAUDE.md` | 规则触发器，强制 AI 遵守规范 | Claude Code 自动加载 |
| `preview.html` | Token 权威来源 + 人工视觉基准 | AI 验证 + 人工对比 |
| `preview-dark.html` | 深色模式 Token 权威来源 | AI 验证 + 人工对比 |

> **关键洞察**：`preview.html` 的 `:root {}` 块是比 `DESIGN.md` 文字描述**更精确的机器可读 token 源**。颜色、字号、圆角、间距的精确数值都已编译在里面。

---

## 预览文件说明

每个品牌目录中包含两个交互式 HTML 预览文件：

| 文件 | 说明 |
|------|------|
| `preview.html` | **浅色主题**预览 — 展示颜色系统、字体排版、按钮样式、卡片、表单、间距、圆角、阴影 |
| `preview-dark.html` | **深色主题**预览 — 同上，使用深色背景 |

直接在浏览器中打开这两个文件，即可查看品牌设计系统的完整可视化展示。

---

## 如何让 Claude Code 自动利用 preview.html 进行验证

### 设计思路

```
生成代码
    ↓
从 preview.html 提取 CSS token（:root 变量）作为基准
    ↓
对比生成代码的颜色 / 字号 / 圆角 / 间距值
    ↓
差异报告 → 自动修正 → 再验证
```

`preview.html` 的 `:root {}` 块已经是编译好的 token 集合，可直接作为机器可读的验证基准，比 DESIGN.md 的文字描述更精确。

---

### CLAUDE.md 推荐模板（含验证协议）

将以下内容写入品牌目录的 `CLAUDE.md`：

```markdown
# Design System: [品牌名]

> **MANDATORY**: Before writing any UI code, read `DESIGN.md` in full.

## Token Source of Truth

`preview.html` 的 `:root {}` 是设计 token 的最终权威版本。
`preview-dark.html` 的 `:root {}` 是深色模式的最终权威版本。

**当 DESIGN.md 与 preview.html 的 CSS 变量冲突时，以 preview.html 为准。**

## Verification Protocol（强制执行）

每次生成或修改 UI 代码后，必须执行以下 3 步验证：

### Step 1: 提取基准 token

读取 preview.html，从 `:root {}` 块提取所有变量：

    grep -A 30 ":root {" preview.html

### Step 2: Token 合规检查

| 检查项 | 方法 | 通过条件 |
|--------|------|----------|
| 颜色值 | 扫描所有 `#xxxxxx` 和 `rgb()` | 必须全部出现在 `:root {}` 中 |
| 字号   | 扫描 `font-size:` | 必须与 preview.html 中 `.type-sample` 一致 |
| 圆角   | 扫描 `border-radius:` | 必须与 `.radius-box` 示例一致 |
| 间距   | 扫描 `padding:` / `gap:` | 必须来自 `.spacing-block` 的 width 值 |
| 字重   | 扫描 `font-weight:` | 必须与 `.type-meta` 描述一致 |

**任何颜色值不在 `:root {}` 中 → 必须替换为对应变量名。**

### Step 3: 组件结构对照

从 preview.html 中找到同类型组件的 HTML 结构，对比：

    # 检查按钮结构
    grep -A 5 "btn-" preview.html

    # 检查卡片结构
    grep -A 10 "card-grid\|card-" preview.html

    # 检查表单结构
    grep -A 5 "form-input\|form-label" preview.html

生成的组件结构必须与 preview.html 中的结构一致（类名、嵌套层级、关键属性）。

## Dark Mode Verification

生成深色模式代码时，使用 `preview-dark.html` 替换上述所有步骤中的 `preview.html`。

## Verification Report Format

每次验证后输出报告：

    === Design Token Verification ===
    ✓ 颜色: 全部匹配 preview.html :root
    ✗ 圆角: card 使用了 4px，preview.html 规定 2px → 已修正
    ✓ 字号: 符合 Typography Scale
    ✓ 间距: 符合 Spacing Scale
    === 验证通过 ===

## Self-Healing Rule

发现不一致时，**不要询问用户**，直接修正为 preview.html 中的值后重新验证。
```

---

### DESIGN.md 推荐增加第 10 章

在原有 9 个章节末尾追加：

```markdown
## 10. Preview Reference Files

### preview.html
- **用途**: 浅色模式设计 token 的可视化参考实现
- **Token 权威来源**: `:root {}` 中的 CSS 自定义属性
- **组件参考**: 各 section 中的 HTML 结构即为规范实现

### preview-dark.html
- **用途**: 深色模式设计 token 的可视化参考实现
- **Token 权威来源**: `:root {}` 中的 CSS 自定义属性

### Token 索引

| Token 类型 | 来源位置 | 提取方法 |
|-----------|---------|---------|
| 品牌色 | `:root {}` | `grep "brand-color" preview.html` |
| 字号 | `.type-sample` div | 检查 `font-size:` 行内样式 |
| 圆角 | `.radius-box` | 检查 `border-radius:` 行内样式 |
| 间距 | `.spacing-block` | 检查 `width:` 行内样式（对应 px 值）|
| 阴影 | `.elevation-card` | 检查 `box-shadow:` 行内样式 |
```

---

### 可选：Playwright 自动截图验证

在项目中添加 `verify-design.js`，配合 Claude Code hooks 自动触发截图对比：

```javascript
// verify-design.js
const { chromium } = require('playwright');
const path = require('path');

async function verify(generatedFile, previewFile = 'preview.html') {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  await page.setViewportSize({ width: 1280, height: 800 });

  // 截图：标准参考
  await page.goto(`file://${path.resolve(previewFile)}`);
  await page.screenshot({ path: 'verify-reference.png', fullPage: false });

  // 截图：生成结果
  await page.goto(`file://${path.resolve(generatedFile)}`);
  await page.screenshot({ path: 'verify-output.png', fullPage: false });

  await browser.close();
  console.log('截图已生成: verify-reference.png  vs  verify-output.png');
}

verify(process.argv[2]);
```

配置 `.claude/settings.json` 在每次写入 HTML 文件后自动触发：

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Write|Edit",
        "hooks": [
          {
            "type": "command",
            "command": "FILE=$(echo $CLAUDE_TOOL_INPUT | jq -r '.file_path // empty'); if [[ \"$FILE\" == *.html ]]; then node verify-design.js \"$FILE\"; fi"
          }
        ]
      }
    ]
  }
}
```

---

### 完整自动验证调用链

```
Claude Code 启动
    ↓
自动读取 CLAUDE.md
    ↓ （CLAUDE.md 指示）
读取 DESIGN.md 获取设计意图
    ↓
生成 UI 代码
    ↓ （CLAUDE.md Verification Protocol 触发）
读取 preview.html → 提取 :root {} token
    ↓
对比生成代码的所有颜色 / 字号 / 圆角 / 间距
    ↓
发现差异 → 自动修正 → 再次验证
    ↓
输出 Verification Report
    ↓ （可选 hook）
Playwright 截图 → 人工最终比对
```

---

## 品牌列表（50 个）

| # | 品牌 | 风格特征 |
|---|------|---------|
| 01 | Vercel | 极简黑白，单色强调，无边框卡片 |
| 02 | Cursor | 深色 IDE 风格，Geist 字体 |
| 03 | Framer | 鲜艳紫色，圆角 Motion 风格 |
| 04 | Coinbase | 加密蓝调，可信信息展示 |
| 05 | Supabase | 深绿强调，深色主题 |
| 06 | Revolut | 深色金融科技，渐变紫 |
| 07 | Clay | 粉彩圆润，友好 SaaS 风格 |
| 08 | Ferrari | 法拉利红，明暗交错，极简编辑风 |
| 09 | SpaceX | 太空黑，精密工程排版 |
| 10 | Lovable | 渐变粉紫，现代 AI 工具 |
| 11 | GitHub | 开源深色，Monospace 字体 |
| 12 | Figma | 彩虹工具色，Protocol 字体 |
| 13 | Tesla | 电动蓝，纯白极简，全视口摄影 |
| 14 | Apple | 系统蓝，San Francisco，精密间距 |
| 15 | Google | Material Design，4dp 基础间距 |
| 16 | Stripe | 渐变紫蓝，金融科技精密 |
| 17 | Airbnb | Coral 品牌色，Cereal 字体 |
| 18 | Notion | 月光白，无框卡片，嵌套块 |
| 19 | Slack | 茄紫，多彩图标系统 |
| 20 | OpenCode | 终端绿，代码编辑器风 |
| 21 | Lamborghini | 纯黑 + 金色，零圆角，全大写 |
| 22 | Linear | 深色紫灰，精密工程工具 |
| 23 | Shopify | 商业绿 Polaris，无障碍优先 |
| 24 | Salesforce | 天蓝 Lightning，企业 SaaS |
| 25 | BMW | BMW 蓝，锐利矩形，极简展厅 |
| 26 | Atlassian | 团队蓝，Atlantic 字体 |
| 27 | HubSpot | 橙色增长，圆角 CRM |
| 28 | Webflow | 设计师蓝，创意工具 |
| 29 | Dropbox | 深蓝品牌，文件共享风格 |
| 30 | Twilio | 红色 API，开发者工具 |
| 31 | Runway | 电影黑，AI 视频生成 |
| 32 | Linear.app | 工程师蓝紫，精密 SaaS |
| 33 | Anthropic | 沙米色，AI 安全风格 |
| 34 | xAI | 极简白黑，科技中性 |
| 35 | OpenAI | 冷灰极简，AI 研究风 |
| 36 | Meta | Facebook 蓝，全球社交 |
| 37 | Renault | 雷诺黄，NouvelR 字体，零圆角 |
| 38 | Mistral AI | 深橙 + 深色，欧洲 AI |
| 39 | Perplexity | 问答蓝，搜索 AI 风格 |
| 40 | Bolt | 闪电黄，AI 代码生成 |
| 41 | Adobe | 红色创意，Spectrum 设计系统 |
| 42 | Microsoft | 微软蓝，Fluent Design |
| 43 | Webflow | NoCode 蓝，可视化构建 |
| 44 | Loom | 紫色视频，异步沟通 |
| 45 | Together AI | AI 橙，开源模型平台 |
| 46 | Discord | 游戏紫，社区平台 |
| 47 | Figma | 见第 12 条 |
| 48 | Pinterest | 品牌红，视觉发现 |
| 49 | Canva | 彩色工具，Canva Sans |
| 50 | Spotify | 深黑 + 绿色，音乐流媒体 |

---

## 数据来源

设计系统数据基于 [VoltAgent/awesome-design-md](https://github.com/VoltAgent/awesome-design-md) 项目，通过对各品牌官网 CSS 的系统性分析提取而成，格式遵循 Google Stitch [DESIGN.md 规范](https://stitch.withgoogle.com/docs/design-md/overview/)。

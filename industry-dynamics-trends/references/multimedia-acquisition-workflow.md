# 多媒体采集操作路径（三级策略 + AI 自主判断）

本文件定义行业动态报告配图/视频的**稳定采集路径**：AI 根据情况自主判断调用哪条策略，脚本提供可执行支撑。与 `multimedia-curation.md`（采集原则/引用格式）、`verification-curation.md`（核查/信源）配合使用。

**目标**：配图在任意 Markdown 预览中**直接可见**；获取过程有重试/超时，单 URL 失败不阻塞整份报告。

---

## 1. 三级策略决策树

AI 在 Cursor 中处理每条动态的配图时，**按以下顺序自主判断**，任意一级成功即停止：

```
给定一个来源页 URL（source_url）或直链图片 URL（image_url）：

┌──────────────────────────────────────────────────────────┐
│  已知 image_url？                                          │
│    是 → 策略 A0：直接下载（http_get + 重试）               │
│           成功 → 写入 manifest → 结束 ✓                   │
│           失败 → 进入 A1                                   │
│                                                            │
│  有 source_url？                                           │
│    是 → 策略 A1：mcp_web_fetch 或 urllib 拉 HTML           │
│           解析 og:image / twitter:image / 首张大图 src     │
│           找到 image_url → 执行 A0                        │
│           未找到 → 进入 B                                  │
│                                                            │
│         策略 B：cursor-ide-browser 导航渲染页面             │
│           browser_snapshot 提取渲染后 og:image/img src     │
│           找到 image_url → 执行 A0                        │
│           未找到 → browser_screenshot 截图（Strategy B2）  │
│           截图成功 → 直接作为配图本地文件 → 结束 ✓          │
│           失败 → 进入 C                                    │
│                                                            │
│         策略 C：跳过，保留「暂无可用配图」                   │
│           在报告该条中写明，在索引中保留来源链接 → 结束 ○    │
└──────────────────────────────────────────────────────────┘
```

**关键原则**：
- 每级策略内部均有**超时（默认 12s）+ 重试（默认 2 次）+ 线性退避**。
- 失败**即跳过该图**，不无限等待，不阻塞报告撰写。
- 视频**不拉流媒体**：取封面图或 og:image 作为配图，正文保留视频链接。

---

## 2. AI 在 Cursor 中的调用路径

| 情境 | AI 应用工具 | 说明 |
|------|-------------|------|
| 有直链 image_url，域名可访问 | `Shell` 执行脚本 A0 | 最快，无需浏览器 |
| 只有 source_url，页面静态渲染 | `mcp_web_fetch(url)` 解析 og:image | Strategy A1 等价操作 |
| 页面 JS 渲染 / 懒加载 / 防爬 | `browser_navigate` + `browser_snapshot` | Strategy B 等价；提取渲染后 img src |
| DOM 中无直链，但视觉上有图 | `browser_screenshot` 截图保存本地 | Strategy B2；截图即为配图 |
| 截图内容需解读（工作流/界面） | 截图 handoff 多模态模型分析 | 补充 alt 文字与正文描述 |
| 以上全部失败 | 写「暂无可用配图」+ 保留文字来源链接 | Strategy C |

**AI 自主判断依据**：
1. 若已从搜索/fetch 中拿到 CDN 或官方博客图片直链 → **优先 A0**（最快）。
2. 若页面是 Adobe/Figma/GitHub 等主流静态博客 → **A1 HTML 解析**大概率成功。
3. 若页面依赖 React/Vue 渲染或图片 src 是动态 JS → **升级 B**，用 browser 渲染。
4. 若页面有反爬或跳转鉴权 → **B2 截图**兜底（截图即使无 URL 也是真实视觉证据）。
5. 超时/重试均失败 → **C 跳过**，不死磕。

---

## 3. 脚本与 manifest.json

### 3.1 manifest.json 格式

放在 `assets/images/<report_slug>/manifest.json`，**由 AI 撰写报告时顺手生成**：

```json
[
  {
    "filename": "01-quickcut.png",
    "label": "Adobe Firefly Quick Cut 界面示意",
    "image_url": "https://...",      // 直链图片 URL（已知填；AI 从 og:image 取到后填入）
    "source_url": "https://..."      // 来源页 URL（始终保留，用于降级 A1/B）
  },
  {
    "filename": "02-figma-codex.png",
    "label": "Figma Codex 工作流",
    "image_url": null,               // 未知时填 null，脚本自动走 A1→B
    "source_url": "https://www.figma.com/blog/..."
  }
]
```

### 3.2 脚本执行

```bash
# 默认：自动降级 A0→A1→B
python3 scripts/fetch_report_images.py --report 2026-03-ai-for-design

# 指定参数
python3 scripts/fetch_report_images.py \
  --report 2026-03-ai-for-design \
  --timeout 12 \
  --max-retries 2 \
  --strategy auto    # auto | a（仅解析）| b（直接 playwright）

# 预览计划（不下载）
python3 scripts/fetch_report_images.py --report 2026-03-ai-for-design --dry-run
```

**安装可选依赖**（Strategy B 需要 playwright）：
```bash
pip install playwright && playwright install chromium
```

### 3.3 脚本退出码

| 退出码 | 含义 |
|--------|------|
| 0 | 全部成功 |
| 1 | manifest.json 不存在或为空 |
| 2 | 部分成功（有跳过项） |

---

## 4. AI 生成 manifest 的时机

在**撰写报告正文**时，AI 同步维护 manifest：

1. 搜索/fetch 到来源页后，立即尝试提取 `og:image`（用 `mcp_web_fetch`）。
2. 拿到 image_url → 写入 manifest 的 `image_url` 字段。
3. 未拿到 → `image_url` 填 null，`source_url` 填来源页。
4. 报告正文的【配图/视频】先用占位 `./images/<slug>/xx.png`（相对路径）。
5. 报告写完后，**一次性**执行脚本拉取所有图片，成功的即渲染，失败的改「暂无可用配图」。

---

## 5. 报告内引用格式

```markdown
- **【配图/视频】**：![描述](./images/2026-03-ai-for-design/01-quickcut.png) [1](#ref-1)
```

- 图片用**相对路径** `./images/<slug>/<filename>`，任何 Markdown 预览均可直接渲染。
- 视频用**封面图**（同上格式）+ 正文注「演示视频见来源 [n]」+ 索引保留链接。
- 未获取到的：`（暂无可用配图；详见来源 [n]）`。
- **体积与版本控制**：B2 截图时尽量固定 viewport（如 1920×1080）、避免整页长图；单张配图建议 ≤ 约 1MB，以免 git push 时 payload 过大触发 HTTP 400。行业实例（如 `ai-for-design.md`）工作流中已约定禁止提交 `node_modules` 并控制报告配图体积。

---

## 6. 与现有规范衔接

| 规范 | 关系 |
|------|------|
| `multimedia-curation.md` | 采集原则/优先级/引用格式；本文件补充「如何可靠执行采集」 |
| `verification-curation.md` | 信源核查；配图同样须来自可信信源 |
| 行业实例（如 `ai-for-design.md`） | 若要求「配图在 MD 中直接渲染」→ 本流程为标准执行路径 |
| `scripts/fetch_report_images.py` | 本流程的可执行实现；支持 A0/A1/B 三级策略 |

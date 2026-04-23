---
name: cambly-note
description: Organize Cambly English lesson recordings into structured study notes — grammar corrections, vocabulary, teacher feedback, and full transcripts. Supports full-auto (Puppeteer MCP), semi-auto (computer use), and manual (console copy-paste) modes.
license: MIT
---

# Cambly Note Skill

## 角色与目标

你是帮助用户整理 Cambly 在线英语课笔记的助手。用户在 Cambly 与外教上课，课后希望把语音转文字、AI 语法纠正、教师反馈和统计数据整理成结构化深度笔记，用于复习和积累。

---

## 第零步：选择工作模式

**在询问语言或执行任何操作之前，先确定工作模式。**

用自然、轻松的语气开场，说明自己能做什么，然后问模式。示例：

> 好，我来帮你把 Cambly 课整理成笔记——语法纠正、生词、老师教的重点、转录，全部结构化输出，方便复习。
>
> 先确认一下你用哪种方式：
>
> **A — 全自动**（Claude Code + Puppeteer MCP）
> 我自动导航 Cambly、抓数据、整理，全程你不用动浏览器。
> ✅ 最省事，批量处理多节课特别方便
> ⚠️ 需要提前装一个 MCP 插件，第一次配置要 5 分钟
>
> **B — 半自动**（Claude computer use）
> 我通过截图和点击操作你屏幕上的浏览器，你需要已登录 Cambly。
> ✅ 不用装插件，Claude 帮你完成大部分操作
> ⚠️ 需要 Claude Max 或支持 computer use 的订阅（claude.ai 网页版）；普通订阅不可用
>
> **C — 手动引导**（推荐新用户，任何 Claude 版本都能用）
> 你在浏览器开发者工具里复制两段页面文字粘给我，我来整理，无需安装任何东西。
> ✅ 零配置，任何设备都能用，最稳定
> ⚠️ 每节课需要手动复制粘贴两次，约 2 分钟操作
>
> 不确定选哪个？**选 C** 就行，5 分钟内能出笔记。

语气保持自然，不要罗列技术细节；收到选择后直接进入下一步，不要重复解释模式差异。

---

## ⚙️ 模式 A 安装（可跳过，选 C 无需此步）

在终端运行以下命令，将 Puppeteer MCP 注册到 Claude Code CLI：

```bash
claude mcp add puppeteer /path/to/mcp-server-puppeteer --scope user -e PUPPETEER_HEADLESS=false
```

实际路径通常是 `~/.npm-global/bin/mcp-server-puppeteer`（通过 `which mcp-server-puppeteer` 确认）。

> ⚠️ **不要**把配置写进 `~/.claude/settings.json` 的 `mcpServers` 字段——那是 Claude 桌面 App 的格式，Claude Code CLI 不读。Claude Code CLI 的 MCP 配置在 `~/.claude.json`，通过 `claude mcp add` 写入。

注册后运行 `claude mcp list` 确认显示 `puppeteer: ... ✓ Connected`，然后开新 session，工具即可用。

`PUPPETEER_HEADLESS=false` 让浏览器窗口可见，**首次使用时需要在弹出的浏览器里手动登录 Cambly 一次**，之后 session 会自动保留。

> 工具调用时名称带前缀（如 `mcp__puppeteer__puppeteer_navigate`），直接使用带前缀的名称。

---

## 第一步：询问输出语言

模式确认后，询问笔记语言：

> 请问你希望笔记用什么语言输出？
> 1. 中文（简体）
> 2. English
> 3. 日本語
> 4. 한국어
> 5. 其他（请指定）

整个会话统一使用选定语言输出（标题、表头、板块名、解释文字）；**课程原文英语引用保持英文不翻译**。

根据所选语言设置 URL 的 `lang` 参数：中文 → `zh_CN`，英文 → `en`，日语 → `ja`，韩语 → `ko`。

---

## 第二步：确认处理范围

询问用户：

> 你想整理哪些课程？
> 1. 最新一节课
> 2. 指定某一节课（请提供课程详情页的完整 URL）
> 3. 批量整理（最近 N 节）

根据选择进入对应工作流。

---

## 工作流

### 模式 A：全自动（Puppeteer MCP）

工具名（带命名空间前缀）：
`mcp__puppeteer__puppeteer_navigate` / `mcp__puppeteer__puppeteer_evaluate` / `mcp__puppeteer__puppeteer_screenshot`

> **注意**：`puppeteer_click` 对 Cambly 内层 tab 无效（见踩坑记录），tab 切换统一用下方的 elementFromPoint 方案。

#### 脚本编写规则（必读）

- **禁止 top-level `return`** → 用 IIFE：`(() => { ... })()`
- **禁止 top-level `await`** → 用 `new Promise(r => setTimeout(r, N))`
- **不要运行复杂递归脚本** → 会栈溢出；直接用 `document.body.innerText` 拿原始文本，让 Claude 解析

#### 切换 Tab 的正确方式

```js
// 找到可见 tab（页面有重复 tab，用 width > 0 过滤隐藏的）
(() => {
  const tabs = Array.from(document.querySelectorAll('[role="tab"]'));
  const t = tabs.find(el => /语音转文字|Transcript/.test(el.textContent)
                          && el.getBoundingClientRect().width > 0);
  if (!t) return 'not found';
  const r = t.getBoundingClientRect();
  const cx = r.x + r.width / 2, cy = r.y + r.height / 2;
  const el = document.elementFromPoint(cx, cy);
  ['mousedown', 'mouseup', 'click'].forEach(type =>
    el.dispatchEvent(new MouseEvent(type, { bubbles: true, cancelable: true, clientX: cx, clientY: cy }))
  );
  return 'dispatched on: ' + el.textContent.trim().slice(0, 20);
})()
```

同理切换回反馈 tab，把正则换成 `/^反馈$|^Feedback$/`。

#### 单节课流程

```
1. 如用户提供了完整 URL → 直接使用
   如用户选"最新一节" → 先执行【A 批量：获取列表】拿到第一个 lessonId

2. mcp__puppeteer__puppeteer_navigate →
   https://www.cambly.com/en/student/progress/past-lesson?lessonV2Id={ID}&lang=zh_CN

3. mcp__puppeteer__puppeteer_screenshot → 确认已登录（看到课程详情）
   如看到登录页 → 告知用户在 Puppeteer 浏览器窗口手动登录后继续

── 第一阶段：反馈 tab ──

4. 等待 10 秒（SPA 加载 + AI 反馈懒加载）+ 滚动右侧面板触发加载：
   new Promise(r => { document.querySelector('[role="tabpanel"]')?.scrollBy(0, 400); setTimeout(r, 10000); })

5. mcp__puppeteer__puppeteer_evaluate → document.body.innerText
   → 保存为 feedbackText

6. 从 feedbackText 提取：
   - 统计数字（发言占比、语速、不重复词汇、时长）
   - 日期、外教姓名
   - AI 语法/词汇纠正卡片（每张：类型/您说/建议/知识点）
   - 外教书面反馈（"本次课程反馈" 到 "此反馈有帮助吗" 之间）
   - 如 duration < 30 分钟 → 标记 ⚠️ 跳过

── 第二阶段：语音转文字 tab ──

7. 用【切换 Tab 的正确方式】切换到语音转文字 tab
   等待 3 秒

8. mcp__puppeteer__puppeteer_evaluate → document.body.innerText
   → 找到"语音转文字\n点击"之后的内容作为 transcript

9. 整理输出笔记
```

#### 批量：获取课程列表

```
1. mcp__puppeteer__puppeteer_navigate →
   https://www.cambly.com/en/student/progress/past-lessons?lang=zh_CN
2. 等待 3 秒
3. mcp__puppeteer__puppeteer_evaluate → 执行【列表抓取脚本】
4. 读取 window.__camblyLessonList（注意：列表卡片不显示时长，duration 字段通常为 null）
   → 取最新 N 条作为待处理列表，时长过滤在详情页做
5. 依次执行单节课流程；从详情页 feedbackText 提取 duration 后再判断是否跳过
6. 每处理 5 节输出一次笔记
```

---

### 模式 B：半自动（Computer Use）

工具：`computer`（screenshot / left_click / type / key / scroll）

**前提：用户已在本机浏览器打开 Cambly 并登录。**

```
1. computer screenshot → 确认当前页面状态

2. 如需导航到目标课程：
   computer left_click 地址栏 → key ctrl+a → type URL → key Return
   等待 5 秒

── 第一阶段：反馈 tab ──

3. computer screenshot → 确认当前在反馈 tab（右侧面板显示 AI 反馈卡片）
   如不在反馈 tab → left_click 反馈 tab 位置（截图中确认坐标）
   等待 8 秒让 AI 反馈懒加载完成

4. 将脚本写入剪贴板（使用 bash 工具）：
   bash: cat > /tmp/cambly_extract.js << 'EOF'
   [此处输出完整内联抓取脚本]
   EOF
   macOS: pbcopy < /tmp/cambly_extract.js
   Linux: xclip -selection clipboard < /tmp/cambly_extract.js

5. computer key F12 → 等待 DevTools 打开
   computer left_click Console 标签页
   computer key ctrl+v → key Return
   等待 2 秒（脚本执行时间）

6. computer screenshot → 确认看到 "✅ Cambly Lesson Extracted"
   如未看到 → 滚动 console 向上查找；或确认 DevTools 是否正确打开

── 第二阶段：语音转文字 tab ──

7. 切换 tab（坐标基于 1419×840，不同分辨率需先截图确认实际坐标）：
   computer left_click (1109, 45)
   等待 3 秒

8. 再次 computer key ctrl+v → key Return（脚本已在剪贴板，直接重跑）
   等待 2 秒
   computer screenshot → 确认看到 "✅ Cambly Lesson Extracted"

9. 提取数据——在 console 输入框：
   computer type → copy(JSON.stringify(window.__camblyLessonData, null, 2))
   computer key Return
   等待 1 秒（copy 命令将完整 JSON 写入剪贴板）
   告知用户：请在对话框里粘贴（⌘+V / Ctrl+V）

   如 JSON 过长导致粘贴失败，提示分两次：
   第一次：copy(JSON.stringify({...window.__camblyLessonData, transcript: ''}, null, 2))
   第二次：copy(window.__camblyLessonData.transcript)

10. 整理输出笔记
```

---

### 模式 C：手动引导

Claude 角色：引导用户采集原始文本 + 读取粘贴内容 + 输出笔记。

用平实语言引导，不出现"JSON""脚本""命令行"等术语。遇到不懂的步骤随时可以问。

**采集原理：无需复杂脚本。用户在浏览器控制台运行一行命令复制页面文本，Claude 负责所有解析。**

#### 单节课

向用户输出以下引导：

---

**总共 4 步，大概 2 分钟。**

**第 1 步 — 打开课程页，等反馈加载**

登录 Cambly，在课程记录里点开你想整理的那节课。
右侧面板停在"反馈"tab，等大概 10 秒，确认能看到语法纠正卡片（不是转圈）。

**第 2 步 — 复制反馈内容**

① 按 **F12**（Mac：**⌥⌘I**），点弹出面板顶部的 **Console** 标签。
② 粘贴下面这行，按回车：

```
copy(document.body.innerText)
```

③ 回到这个对话，粘贴，并在内容前写"**反馈 tab：**"

**第 3 步 — 复制转录内容**

① 点右侧面板的 **"语音转文字"** tab。
② 在 Console 里按 **↑** 方向键，上一行会出现，按回车重新运行。
③ 回到这个对话，粘贴，并在内容前写"**转录 tab：**"

**第 4 步 — 等我整理**

我收到两段内容后，直接输出笔记。

---

用户粘贴后，Claude 从原始文本中提取：统计数字、教师姓名/日期、AI 语法卡片、教师书面反馈、完整转录，然后生成笔记。

> **如果文本太长粘贴失败**：分两次发，第一次反馈 tab，第二次转录 tab。

#### 批量（模式 C）

```
1. 请用户打开课程列表页 past-lessons
2. F12 → Console 运行：copy(document.body.innerText)，粘给 Claude
3. Claude 从列表文本里提取所有课程链接和时长，过滤 < 30 分钟的，列出待处理课程
4. 逐节引导：打开该课 → 反馈 tab copy → 转录 tab copy → 各粘一次
   第二节起提醒：Console 按↑回车即可，不用重新输入
```

---

## 内联抓取脚本（模式 B 专用）

> **模式 A 不需要此脚本**，模式 A 直接用 `document.body.innerText` 采集原始文本后交 Claude 解析。
> **模式 C 不需要此脚本**，模式 C 直接用 `copy(document.body.innerText)` 采集原始文本。
> 此脚本与 `scripts/extract-lesson.js` 保持同步。支持中英文界面；支持跨 tab 累积。

```js
(function extractCamblyLesson() {
  'use strict';

  var prev    = window.__camblyLessonData;
  var allText = document.body.innerText;
  var lines   = allText.split('\n');

  var tIdx = allText.indexOf('语音转文字\n点击');
  if (tIdx === -1) tIdx = allText.indexOf('Transcript\nClick');
  var statsText = tIdx > -1 ? allText.slice(0, tIdx) : allText;

  function matchNum(text, pats) {
    for (var i = 0; i < pats.length; i++) {
      var r = text.match(pats[i]);
      if (r) return parseInt(r[1]);
    }
    return null;
  }

  var stats = {
    speakingRatio: matchNum(statsText, [/发言时长占比\s+(\d+)%/, /Speaking time\s+(\d+)%/]),
    wpm:           matchNum(statsText, [/每分钟单词数\s+(\d+)/, /Words per minute\s+(\d+)/]),
    uniqueVocab:   matchNum(statsText, [/不重复词汇量\s+(\d+)/, /Unique words\s+(\d+)/]),
    duration:      matchNum(statsText, [/(\d{1,3})\s*分钟/, /(\d{1,3})\s*minutes?/i]),
  };

  var dm = statsText.match(/(\d{4})年(\d{1,2})月(\d{1,2})日/)
        || statsText.match(/(\d{4})-(\d{1,2})-(\d{1,2})/);

  var nameRe = /^[A-Z][a-zA-Z]+(?: [A-Z][a-zA-Z]+)+$/;
  var tutor  = null;
  for (var i = 0; i < lines.length - 1; i++) {
    if ((lines[i].trim() === '反馈' || lines[i].trim() === 'Lesson feedback')
        && nameRe.test(lines[i + 1].trim())) {
      tutor = lines[i + 1].trim(); break;
    }
  }

  var meta = {
    lessonId: new URLSearchParams(location.search).get('lessonV2Id'),
    tutor:    tutor,
    date:     dm ? (dm[1] + '-' + String(dm[2]).padStart(2,'0') + '-' + String(dm[3]).padStart(2,'0')) : null,
    url:      location.href,
  };

  var tutorFeedback = '';
  var fbA  = allText.indexOf('本次课程反馈');
  var fbB  = allText.indexOf('Lesson feedback');
  var fbIdx = (fbA > -1 && (fbB === -1 || fbA < fbB)) ? fbA : fbB;
  if (fbIdx > -1) {
    var feA   = allText.indexOf('此反馈有帮助吗');
    var feB   = allText.indexOf('Was this feedback helpful');
    var feIdx = (feA > -1 && (feB === -1 || feA < feB)) ? feA : feB;
    tutorFeedback = (feIdx > fbIdx
      ? allText.slice(fbIdx, feIdx)
      : allText.slice(fbIdx, fbIdx + 2000)
    ).trim();
  }

  var aiCards = [];
  var aiA  = allText.indexOf('查看AI反馈');
  var aiB  = allText.indexOf('View AI feedback');
  var aiIdx = (aiA > -1 && (aiB === -1 || aiA < aiB)) ? aiA : aiB;

  if (aiIdx > -1) {
    var TYPES = ['语法','词汇','其他','发音','流利度','Grammar','Vocabulary','Other','Pronunciation','Fluency'];
    var LABEL_MAP = {
      '您说：':'youSaid',   'You said:':'youSaid',   '您说:':'youSaid',
      '建议：':'suggestion','Suggestion:':'suggestion','建议:':'suggestion',
      '您做得好的地方：':'strength','Strength:':'strength','您做得好的地方:':'strength',
      '知识点：':'point',   'Knowledge point:':'point','知识点:':'point',
    };
    var STOP = ['反馈有误','Report an issue'];
    var aiLines = allText.slice(aiIdx).split('\n');
    var ci = 0;
    while (ci < aiLines.length) {
      var aLine = aiLines[ci].trim();
      if (TYPES.indexOf(aLine) !== -1) {
        var card = { type: aLine, youSaid: null, suggestion: null, strength: null, point: null };
        var curKey = null, curBuf = [];
        ci++;
        while (ci < aiLines.length && TYPES.indexOf(aiLines[ci].trim()) === -1) {
          var ln = aiLines[ci].trim();
          if (STOP.indexOf(ln) !== -1) { ci++; break; }
          if (LABEL_MAP[ln] !== undefined) {
            if (curKey) { card[curKey] = curBuf.join('\n').trim(); }
            curKey = LABEL_MAP[ln]; curBuf = [];
          } else if (curKey && ln) {
            curBuf.push(ln);
          }
          ci++;
        }
        if (curKey) { card[curKey] = curBuf.join('\n').trim(); }
        aiCards.push(card);
      } else {
        ci++;
      }
    }
  }

  var transcript = '';
  if (tIdx > -1) {
    var tSec   = allText.slice(tIdx);
    var tCut   = tSec.indexOf('Privacy Preference Center');
    var tClean = tCut > 0 ? tSec.slice(0, tCut) : tSec;
    transcript = tClean.split('\n').filter(function(l) { return l.trim(); }).slice(2).join('\n');
  }

  if (prev && prev.meta && prev.meta.lessonId === meta.lessonId) {
    if (!tutorFeedback && prev.tutorFeedback) tutorFeedback = prev.tutorFeedback;
    if (!aiCards.length && prev.aiCards && prev.aiCards.length) {
      Array.prototype.push.apply(aiCards, prev.aiCards);
    }
    if (!transcript && prev.transcript) transcript = prev.transcript;
    for (var sk in stats) {
      if (stats[sk] === null && prev.stats && prev.stats[sk] != null) stats[sk] = prev.stats[sk];
    }
  }

  var shouldSkip = stats.duration !== null && stats.duration < 30;

  window.__camblyLessonData = {
    meta: meta, stats: stats,
    tutorFeedback: tutorFeedback, aiCards: aiCards,
    transcript: transcript, shouldSkip: shouldSkip,
  };

  console.log('[Cambly] id=' + meta.lessonId + ' cards=' + aiCards.length + ' transcript=' + transcript.length + ' skip=' + shouldSkip);
  if (!aiCards.length)    console.info('[Cambly] No AI cards — run on feedback tab after ~10s');
  if (!transcript.length) console.info('[Cambly] No transcript — switch to transcript tab and run again');
  if (shouldSkip)         console.warn('[Cambly] Duration < 30 min, will be skipped');
  console.log('[Cambly] Copy: copy(JSON.stringify(window.__camblyLessonData, null, 2))');

  return window.__camblyLessonData;
})();
```

---

## 列表抓取脚本（模式 A / B 批量专用）

```js
(async function extractCamblyLessonList() {
  'use strict';

  // ── 找到课程列表的滚动容器 ───────────────────────────────────────
  const scrollable = Array.from(document.querySelectorAll('*')).filter(el => {
    const s = getComputedStyle(el);
    return (s.overflowY === 'auto' || s.overflowY === 'scroll')
           && el.scrollHeight > el.clientHeight + 10;  // +10 避免误匹配微小溢出
  });
  const container = scrollable[scrollable.length - 1];
  if (!container) {
    console.error('⚠️ 找不到滚动容器，请确认在 past-lessons 页面');
    return null;
  }

  // ── 滚动到底部加载全部课程 ───────────────────────────────────────
  let prevHeight = -1;
  let attempts   = 0;
  while (container.scrollHeight !== prevHeight && attempts < 30) {
    prevHeight = container.scrollHeight;
    container.scrollTop = container.scrollHeight;
    await new Promise(r => setTimeout(r, 1200));
    attempts++;
  }

  // ── 拦截 window.open，同时记录触发 click 的卡片（保持 URL 与卡片一一对应）──
  // 注意：此处临时替换 window.open，操作完毕后立即还原
  const captured = [];          // [{ url, cardText }]
  const origOpen = window.open;
  window.open = (url) => {
    if (url) captured.push({ url: String(url), cardText: _currentCard?.innerText ?? '' });
    return null;
  };

  let _currentCard = null;
  try {
    document.querySelectorAll('div[role="button"][tabindex="0"]').forEach(card => {
      if (/202\d/.test(card.innerText ?? '')) {
        _currentCard = card;
        card.click();
      }
    });
  } finally {
    window.open = origOpen;   // 无论如何都还原，防止影响页面其他功能
    _currentCard = null;
  }

  // ── 解析 lessonId 及基础元数据 ───────────────────────────────────
  const lessons = captured
    .map(({ url, cardText }) => {
      const idMatch  = url.match(/lessonV2Id=([^&]+)/);
      if (!idMatch) return null;
      const durMatch = cardText.match(/(\d{1,3})\s*(?:分钟|minutes?)/i);
      return {
        lessonId: idMatch[1],
        url,
        duration: durMatch ? parseInt(durMatch[1]) : null,
      };
    })
    .filter(Boolean);

  window.__camblyLessonList = lessons;

  console.log(`%c✅ Found ${lessons.length} lessons`, 'color:#4caf50;font-weight:bold');
  console.log('%c💡 Copy:%c copy(JSON.stringify(window.__camblyLessonList, null, 2))',
    'color:#2196f3;font-weight:bold', 'color:#ff9800');

  return lessons;
})();
```

---

## 已知技术问题

| 问题 | 解决方案 |
|------|---------|
| JS `.click()` 无法切换 Cambly 内层 tab | **不要用** `puppeteer_click` 或 `.click()`；用 `elementFromPoint` + 原生 `MouseEvent` dispatch（见"切换 Tab 的正确方式"） |
| `puppeteer_click` 报 "Node is either not clickable" | Cambly tab 结构不支持直接 CSS selector click，改用 elementFromPoint 方案 |
| 页面有重复 `[role="tab"]` 元素 | 用 `getBoundingClientRect().width > 0` 过滤不可见的重复 tab |
| 复杂提取脚本报 "Maximum call stack size exceeded" | 不要运行复杂嵌套脚本；直接 `document.body.innerText` 拿文本，Claude 解析 |
| `return` 在 evaluate 里报 "Illegal return statement" | 所有脚本用 IIFE：`(() => { ... })()` |
| `await` 在 evaluate 里报错 | 用 `new Promise(r => setTimeout(r, N))` 代替 top-level await |
| 列表页课程卡片 duration 为 null | 列表卡片不显示时长；时长过滤改在详情页 feedbackText 里做 |
| AI 反馈懒加载，初始显示"正在准备" | 在反馈 tab 等待 10 秒，同时滚动右侧面板触发加载 |
| 两个 tab 的数据各自独立，一次拿不全 | 切两次 tab，各拿一次 `document.body.innerText` |
| 某些课程转录显示"正在准备" | 标记 ⚠️ 跳过转录板块，其他板块正常输出 |
| 模式 A Puppeteer 首次无 Cambly session | `PUPPETEER_HEADLESS=false` 后在弹出窗口手动登录一次，session 持久化 |
| 模式 A 工具名带命名空间前缀 | 使用完整名称：`mcp__puppeteer__puppeteer_navigate` 等 |
| 模式 A MCP 未加载（工具不在列表里） | 用 `claude mcp add --scope user` 注册到 `~/.claude.json`，不是 `~/.claude/settings.json` |
| 模式 B 坐标偏移 | 先截图确认坐标，基准 `(1109, 45)` 按实际分辨率比例换算 |
| Cambly 域名下无法下载文件 | 所有笔记只在聊天中输出 |

---

## 笔记输出格式

所有文字用用户选定的语言；英语原句保留英文。

```markdown
## 📒 {YYYYMMDD}_{TEACHER_NAME}

{日期}：{full date} ｜ {外教}：{name} ｜ {时长}：{duration}分钟
{数据}：{发言占比} {X}% ｜ {语速} {X} {词/分钟} ｜ {不重复词汇} {X}

### {话题摘要}
1. [话题 1]
2. [话题 2]

### {语法纠正}
| {你说的} | {正确表达} | {知识点} |
|--------|---------|--------|
（来源：AI 卡片 + 转录中老师口头纠正）

### [专题教学板块 — 根据课程实际内容动态命名]

### 🗣️ {老师的地道表达}
- "原句" — {解释为什么这个表达好/地道/值得模仿}

### {实用词汇/短语}
| {词汇/短语} | {含义} | {语境} |
|----------|------|------|

### {外教反馈}（如有书面反馈）
- ✅ {做得好}：...
- ⚠️ {需改进}：...
- 💡 {练习建议}：...
```

---

## 专题教学板块规则（最重要）

**核心原则：忠实还原课上老师实际教的每一个知识点，不遗漏、不概括。**

| 类型 | 触发条件 | 表格列 |
|------|---------|-------|
| 词缀 / 构词法 | 老师教 prefix/suffix | 前缀/后缀 · 含义 · 课上例词 |
| 介词 / 方向词 | 老师讲介词用法 | 介词 · 核心含义 · 讲解要点 · 例句 |
| 阅读 / 商务英语 | 原文词汇拆解 | 词汇/短语 · 含义 · 讲解要点 |
| 词性变化 | 老师讲词形变化 | 形容词 · 名词 · 动词 · 搭配 |
| 近义词辨析 | 老师对比相似词 | 词汇 · 含义 · 细微差别 |
| 面试 / 场景模拟 | 模拟对话练习 | 问题 + 回答框架 + 关键句型 |
| Phrasal Verbs | 老师教短语动词 | 词组 · 含义 · 讲解要点 · 例句 |
| 方向指引 | 描述路线/位置 | 句式 · 含义 · 用法说明 |

**严格执行：老师举了几个例子就列几个，不省略，不自行补充。一节课可同时有多个专题板块。**

---

## 内容筛选规则

**语法纠正**：AI 卡片每一条 ✅ ＋ 转录中老师口头纠正（"we say X, not Y"）✅ ｜ 老师的自我重复或补充 ❌

**实用词汇**：老师主动教的新词 ✅ ＋ 纠正时给出的正确词汇 ✅ ｜ 常见词 / 语气词（Yeah, Okay）❌ ｜ **必须包含"语境"列**

**地道表达**：自然完整的句子或精彩比喻 ✅ ｜ 简单回应 ❌ ｜ **每条附解释**

**专题板块**：老师教的每个知识点 ✅ ｜ 概括 / 省略 / 自行补充 ❌

---

## 输出规则

- 直接在聊天中输出（Cambly 域名无法下载文件）
- 批量处理时每 5 节输出一次
- 从最新到最旧处理
- 无数据 / 时长 < 30 分钟 → 标记 ⚠️ 跳过
- AI 反馈未生成 → 在对应板块注明"AI 反馈待生成"

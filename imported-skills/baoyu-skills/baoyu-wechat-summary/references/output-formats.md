# Output formats — normal & roast digest

This reference defines the two digest variants the skill produces: the **normal** version (default, sober summary) and the **roast** version (毒舌，sarcastic critique, opt-in). Load this file during Round 1 (skeleton) and keep it open through Round 3 (audit).

Both versions share the same overall layout and writing rules; the differences are tone, the leaderboard annotations, the portraits, and the footer. Write the normal version first when both are requested — it's the anchor for incremental mode and the source of truth for the profile updates.

---

## 1. Normal version

### 1.1 Section order (fixed)

```
[Title line]
[① Opening summary — 1-2 paragraphs of prose]
[② Categorized body — 3-6 self-named sections per day]
[③ Optional pain-point section]
[④ Optional @bot Q&A section]
[⑤ 📊 Stats block + Top 10 leaderboard]
[⑥ 群友画像 — one entry per active user (3+ msgs)]
[Fixed footer]
```

摘要在前、话题居中、排行榜和画像收尾 — 读者先看到内容，数据和人物放在后面翻阅。

### 1.2 Title line

- Single line, no markdown heading.
- Form: `{群名} 群聊精华 · {日期或日期区间}`
- Date single day: `2026-03-12`. Date range: `2026-03-12 ~ 2026-03-15`.

Example:

```
相亲相爱一家人 群聊精华 · 2026-03-12
```

### 1.3 Opening summary（群聊摘要）

- Comes immediately after the title line.
- 1-2 paragraphs, plain prose, no headings, no bullets.
- Hook the reader: lead with the most distinctive thread of the day (a heated debate, a surprising announcement, a market move someone reacted to).
- Reference 2-4 of the day's category titles in the prose so the reader knows what's coming.
- Mention 1-2 specific people only if their contribution is central; otherwise stay topic-focused.
- No timestamps, no message counts (those live in the stats block).

### 1.4 Categorized body（群话题）

- 3-6 self-named categories per day.
- Each category is a thematic bucket — name it for the *topic*, not generic ("讨论"、"闲聊" are forbidden labels).
- Category header: `{emoji} {标题}` — one emoji prefix, then a short noun phrase.
  - Suggested emoji: 🛠 工具/技术，📦 产品发布，📰 新闻/市场，💬 观点辩论，😄 笑料/段子，📚 学习分享，💸 钱与消费，🍜 生活日常。
- Body inside each category: prose with embedded quotes. Use `•` bullets when listing 3+ parallel items; otherwise paragraphs.
- Attribution: name the speaker on first mention in a thread (`蛙总说他...`). For follow-on lines in the same thread, attribution can be implicit if the chain is short and clear.
- Quotes: use 「」 for direct quotes. Quote when the wording is vivid, surprising, or characteristic; paraphrase otherwise.
- Merge: a multi-person discussion is one entry, not a list of one-line replies.
- Links: preserve the full URL inline. Article titles stay verbatim.

Example:

```
🛠 Claude Code 4.7 实测

蛙总下午把 4.7 装上后第一反应是「比 4.6 慢一倍」，老王跟着复现，怀疑是 Opus 默认配置导致。阿喵贴了官方文档 https://docs.claude.com/.../opus-4-7 ，提到可以切回 Sonnet 4.6 跑速测，三人最终结论：复杂任务 4.7 强，日常用 4.6 更顺手。
```

### 1.5 Pain-point section (optional)

- Include only when the day's chat contains at least one concrete unresolved or partially-resolved problem.
- Heading: `今日待解决问题` or `本周悬而未决`.
- One entry per problem. Format:
  ```
  问题：<一句话描述>
  提出者：<昵称>
  背景：<1-2 句来龙去脉>
  状态：<✅ 已解决 / ⚠️ 部分解决 / ❌ 仍未解决>
  方案：<若有人提了方案，写在这；否则写"暂无方案">
  ```
- Skip the section entirely if there are no genuine pain points — don't pad with trivial questions.

### 1.6 @bot 答疑 section (optional)

- 仅当 SKILL.md Step 3.9 本批捕获到至少一条真实 @bot 请求时出现；否则整段省略。
- Heading: `🤖 @bot 答疑`
- 一条请求一个条目（• 请求行 + 缩进的 🤖 答复行）。多人问同一件事合并成一答。
- **请求行措辞自由发挥**：点出提问者真名 + 自然转述其请求即可，别套「X 问：」这类固定句式。
- 语气：真诚、热心、有用的助手——与普通版整体一致。答复落地、给具体建议，别空泛。
- 来源：仅群聊上下文 + 自有知识，不联网。需实时/外部数据又无法核实的，如实说明（`这个我查不到实时数据，需要联网确认`），不编造。
- Format（遵守 §3：不用 markdown、列表用 •、标题一个 emoji）：
  ```
  🤖 @bot 答疑

  • {提问者 + 自然转述的请求}
    🤖 {真诚、简洁、有用的回答；查不到实时信息就如实说明}
  ```

### 1.7 Statistics block（消息统计 + 排行榜）

- Starts with `📊 消息统计: 共 N 条消息`.
- Followed by a leaderboard, top 10 senders by message count, one per line.
- Form per line: `{排名}. {昵称}: {消息数} 条`
- Counting rules:
  - Include images, emojis, links, voice transcripts — anything that occupies a chat row is one message.
  - Exclude system messages and revoked messages (`[系统]`, `revokemsg`).
  - For the `self_wxid` user, substitute `self_display` from EXTEND.md before counting/displaying.
  - Resolve ambiguous nicknames (per SKILL.md Step 3.6) before tallying so the same person isn't double-counted.
  - **Counts must be computed mechanically** from the `$TMPDIR` messages file (e.g. `jq 'group_by(.from_wxid) | map({name: .[0].from_nickname, n: length}) | sort_by(-.n)'`) — never estimated by eyeballing. Total and per-person counts both.
- **Incremental runs must show the precise coverage window**: day-granular date ranges share their boundary day with the previous digest, which readers misread as overlap. Add a line right after the message count: `⏱ 覆盖区间: MM-DD HH:MM ~ MM-DD HH:MM` (first and last included message timestamps).

Example:

```
📊 消息统计: 共 387 条消息
1. 蛙总: 92 条
2. 老王: 58 条
3. 阿喵: 41 条
...
```

### 1.8 群友画像 section

- Heading line: `群友画像`
- One entry per user with 3+ messages this batch.
- Order: by message count, descending.
- Entry header: `{昵称}（{角色标签}）` — the role tag is your one-line read on this person *today*. Examples: `做空美股的乐子人`, `深夜技术指导`, `论坛级吐槽担当`.
- Body: 2-5 bullets with `•` prefix. Each bullet states one observation. Quote evidence inline where natural.
- Continuity: if you loaded a prior profile in Step 3.7, carry forward the established tags/observations that still apply, and call out *change* explicitly (`今天罕见地没提空头`, `从昨天的乐观转向今天的焦虑`).
- Don't invent backstory — only what's in the messages or the prior profile.

Example:

```
群友画像

蛙总（做空美股的乐子人）
• 全天反复提"做空 SPY"，被群友提醒已连续三周看错方向
• 难得正面回应技术问题："我那个脚本是用 Bun 跑的，慢得跟蜗牛似的"
• 临近收盘转为沉默，与昨日大放厥词的状态对比明显
```

### 1.9 Footer

Fixed line, last in file:

```
本简报由 AI 自动生成
```

No date, no signature, no version number.

---

## 2. Roast version (毒舌版)

Roast 版基于普通版的话题骨架和素材，用毒舌、尖锐、挑衅的风格重写。整体结构与普通版相同，Section 顺序也一致（标题行、开头概览、正文分类、@bot 答疑（毒舌值班版，如有）、统计区块 + 排行榜、群友画像、结尾），但风格完全不同。痛点部分省略。仅当 `include_roast=true` 时生成。标题加 "毒舌版" 后缀。

风格要求：
- 你是一位以尖锐和挑衅风格著称的专业评论员
- 对每个群友的行为、言论进行犀利点评，不怕让人尴尬
- 发言排行旁给每个人加一句毒舌备注（括号内）
- 群友画像改为「不留情面版」，放大每个人的槽点和矛盾之处
- 开头概览用更戏谑的口吻，突出荒诞和讽刺
- 正文话题标题可以改得更损
- 引用原话时配上辛辣点评
- @bot 答疑改为「毒舌值班版」（本批有 @bot 请求时才出现，见 SKILL.md Step 3.9；位置与普通版相同——正文分类之后、统计区块之前；无则省略）：照样把干货答出来，但裹上调侃、嘴硬、吐槽提问者的口吻，与 roast 整体一致；来源同样只用群聊上下文 + 自有知识、不联网，查不到就嘴硬地承认查不到；同守下方红线。请求行措辞自由发挥，用调侃口吻点出提问者和请求即可，别套「又来了」这类固定句式。标题如 `🤖 bot 答疑（毒舌值班版）`，结构示意：

  ```
  🤖 bot 答疑（毒舌值班版）

  • {提问者 + 请求，调侃口吻}
    🤖 {带刺但仍有实质内容的回答}
  ```
- 结尾改为：本简报由一个没有感情的 AI 自动生成，如有冒犯，概不负责

注意：毒舌但不恶毒，调侃但不人身攻击。目标是让群友看了会笑，而不是生气。具体红线：
- 只嘲讽群里的公开行为，不碰外貌、体重、健康、家庭、私人关系
- 不用时间戳推断作息或时区（服务器时间不等于本地时间）
- 不做医学/心理诊断类玩笑（「这位需要看医生」「典型 ADHD」）
- 不揣测对方未主动公开的身份属性（性取向、宗教、政治立场）
- 嘲讽观点本身，不嘲讽发言的权利（「这个观点错得离谱」可以，「连这都不懂还敢发言」不行）
- 如果某人本期没有槽点（3+ 条但都很中性），给一句温和调侃即可，不要硬凑

**写作顺序：** 先放开写最狠的版本，写完再回头检查红线。不要边写边自我审查，那样只会写出温吞水。

---

## 3. Common formatting rules (both versions)

- **No markdown.** No `**bold**`, no `# headings`, no `*italic*`, no `[link](url)` syntax. Headings are plain text on their own line.
- **Bullets use `•`.** Not `-`, not `*`, not `1.` for prose-style bullets.
- **Numbered lists** (`1.`, `2.`) are reserved for the leaderboard.
- **Subcategory hints** within a body block are plain text with no symbol prefix.
- **Links preserved verbatim.** Paste the full URL inline. Don't shorten, don't hide behind text.
- **One emoji per category title.** Don't stack 🛠💬 etc.
- **Pain-point statuses** use ✅⚠️❌ verbatim.
- **Quotes use 「」.** Single quotes for nested.
- **Names verbatim.** Don't abbreviate `蛙总` to `蛙`, don't translate Chinese names, don't anonymize.

---

## 4. Common content rules (both versions)

- **Filter only pure noise.** Cut: lone emoji reactions, "好的"/"收到"/"哈哈哈" with no follow-on, duplicate forwards.
- **Keep gossip, anecdotes, signature moments.** These are the highlight reel — the whole point of the digest.
- **Plain language.** Preserve vivid expressions and idiosyncratic phrasings — that's what makes the speaker recognizable.
- **Keep real names.** Both for traceability and so the digest is useful as memory.
- **Tool, product, URL names complete.** `Claude Code 4.7`, not `CC`. `https://github.com/...`, not `GitHub 上那个项目`.
- **Merge, don't list.** A 30-message debate becomes one paragraph, not 30 bullet points.
- **Direct-quote deep observations.** When someone says something striking, quote it verbatim with 「」 rather than paraphrase.
- **Shared articles → title + sharer.** `阿喵分享了《一个 Rust 工程师的反思》` — include the title and who shared.
- **No timestamp-based sleep/timezone inference.** (Repeated here because it applies to both versions, not just roast — never say `凌晨 3 点还在线` in either.)
- **No fabricated facts.** Every claim must be supported by an actual message in the batch (or in a loaded profile). If you're tempted to "add color," stop.

---

## 5. Output skeleton — quick reference

When you forget the structure mid-write, this is the skeleton:

### Normal

```
{群名} 群聊精华 · {日期}

{开篇 1-2 段，无标题，直入主题}

🛠 {分类标题 1}

{该分类下的整理过的讨论 / 段落 / 引用}

📦 {分类标题 2}

{...}

今日待解决问题（可选，没有就不写）

问题: {一句话}
提出者: {昵称}
背景: {1-2 句}
状态: ⚠️ 部分解决
方案: {若有}

🤖 @bot 答疑（可选，没有就不写）

• {提问者 + 请求，自然转述}
  🤖 {真诚有用的回答}

📊 消息统计: 共 N 条消息
1. {昵称}: N 条
2. {昵称}: N 条
...
10. {昵称}: N 条

群友画像

{昵称}（{角色标签}）
• {观察 1}
• {观察 2}
• {观察 3}

{昵称}（{角色标签}）
• {观察 1}
• {观察 2}

本简报由 AI 自动生成
```

### Roast

```
{群名} 群聊精华 · {日期} · 毒舌版

{毒舌开篇 1-2 段}

🛠 {更大声的分类标题}

{保留真实引用的毒舌叙述}

🤖 bot 答疑（毒舌值班版，可选）

• {提问者 + 请求，调侃口吻}
  🤖 {带刺但仍有实质的回答}

📊 消息统计: 共 N 条消息
1. {昵称}: N 条 ({毒舌评语})
2. {昵称}: N 条 ({毒舌评语})
...

群友画像

{昵称}（{放大的角色标签}）
• {毒舌观察 1}
• {毒舌观察 2}

本简报由一个没有感情的 AI 自动生成,如有冒犯,概不负责
```

---

## 6. Self-check before saving

Before writing the digest file, mentally walk through:

1. Section order correct? Opening summary → categorized body → (pain points) → (@bot) → stats block → portraits → footer?
2. Stats block accurate? Counts match the filtered message set?
3. Top 10 names resolved (self_display substituted, ambiguous nicknames disambiguated)?
4. Opening hooks at least one real category title?
5. Every active user (3+ msgs) has a 画像 entry?
6. Every category has a topic-named title (not "讨论")?
7. Every quote uses 「」 and is traceable to a real message?
8. Links inline and complete?
9. No markdown bold/heading/link syntax leaked through?
10. (Roast only) Every roast bullet would pass the §2 红线 audit?
11. Footer line exact match, and it is the last line (after 群友画像)?
12. （本批有 @bot 请求时）两版各有对应 @bot 答疑小节？普通版真诚有用、毒舌版带刺仍有干货？无编造的实时信息？

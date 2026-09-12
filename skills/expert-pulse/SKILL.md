---
name: expert-pulse
description: "把脉" — Expert Pulse Check for product decisions. Triggers in two ways: (1) AUTOMATIC — when Claude presents multiple options for a major product decision (product positioning, user experience model, data architecture, pricing strategy, go-to-market, feature prioritization), Claude must automatically enter expert review mode instead of simply asking the user to pick. (2) MANUAL — when the user says "把脉" anywhere in their message, Claude immediately runs an expert review on the current topic, even without predefined options. Use this skill whenever Claude is about to ask the user to choose between design/product alternatives, or when the user explicitly invokes "把脉". Do NOT trigger for routine implementation decisions (variable naming, component structure, minor refactors, library choices for well-understood problems).
---

# 把脉 — Expert Pulse Check

## Why This Skill Exists

When an AI presents options A/B/C, the user is anchored to that option space. A second pass through cross-disciplinary expert lenses often produces a superior option D that transcends the original framing. This skill automates that "second pass" so the user doesn't have to manually prompt for it every time.

## Trigger Conditions

### Automatic Trigger
When Claude is about to present multiple options for a **major product decision**, it should enter 把脉 mode instead of asking the user to choose directly. Major product decisions include:

- Product positioning or competitive strategy
- User experience models or interaction paradigms
- Data architecture with user-facing implications
- Pricing or monetization strategy
- Feature prioritization or roadmap direction
- Onboarding or activation flow design
- API/protocol design that shapes the developer experience

Do NOT auto-trigger for: implementation-level choices (which library, which pattern, variable naming, minor refactors), bug fixes, routine code structure, or decisions where the user has already expressed a clear preference.

### Manual Trigger
When the user says **"把脉"** — immediately enter expert review mode on whatever is currently being discussed. In manual mode, there may be no predefined options; Claude analyzes the current direction/approach directly.

## Execution Flow

### Step 1: Present the Landscape (if auto-triggered)
List the options as Claude normally would, with brief pros/cons. This preserves the user's ability to see the full picture. Skip this step if manually triggered and no options exist yet.

### Step 2: Select Expert Lenses (3–5 cross-disciplinary perspectives)
Based on the decision type, select 3–5 expert perspectives that are likely to reveal blind spots. State them explicitly at the start so the user knows which lenses are being applied — and can request a swap if desired.

**Perspective selection heuristics** (not exhaustive — use judgment):

| Decision Domain | Candidate Expert Lenses |
|---|---|
| UX / Interaction | Cognitive psychology, behavioral economics, accessibility, information architecture, game design |
| Product positioning | Jobs-to-be-done theory, blue ocean strategy, platform economics, behavioral psychology |
| Pricing / Monetization | Behavioral economics, SaaS metrics, price psychology, competitive dynamics |
| Data architecture | Systems thinking, data mesh/domain-driven design, privacy-by-design, developer experience |
| Onboarding / Activation | Motivation theory (Fogg, Self-Determination), progressive disclosure, habit formation |
| API / Protocol design | Developer experience, network effects, backwards compatibility, composability principles |

Also reference **real-world benchmark products or frameworks** when available — not vague appeals to authority, but specific, named design decisions from relevant products (e.g., "Notion's block architecture", "Stripe's progressive API disclosure", "Linear's opinionated defaults").

### Step 3: Expert Analysis
For each selected lens, briefly analyze the situation. This is the core value — the analysis should:

- Challenge assumptions embedded in the original options
- Surface trade-offs the original framing missed
- Identify which option (or new hybrid/alternative) best serves the user's actual goal
- Reference specific principles, frameworks, or product precedents where they sharpen the argument

Keep each lens to 2–4 sentences. Depth over breadth — don't pad.

### Step 4: Synthesized Recommendation
Deliver two things:

**A. Clear recommendation** — one specific path, which may be an original option, a modified version, or an entirely new option D that emerged from the analysis. State it directly with conviction. Explain the core reasoning in 2–3 sentences.

**B. Quick evaluation framework** — a concise rubric (3–5 criteria with one-line descriptions) that the user can apply to validate or override the recommendation based on context only they have. This respects the user's final authority while still giving a strong default.

### Step 5: Await Decision and Save to KnowMine
After the user confirms their final choice, save the decision to KnowMine with this structure:

**Tool:** `add_knowledge` (KnowMine MCP)
- **title:** `[决策日志] {decision topic summary}`
- **type:** `insight`
- **tags:** `["决策日志", "把脉", "{domain tag}", "{product tag}"]`
- **content:** Markdown with these sections:
  ```
  ## 决策主题
  {One-line description}

  ## 可选方案
  {Brief list of options considered, including any new option D}

  ## 专家视角
  {Which lenses were applied, key insight from each}

  ## 最终选择
  {What the user decided}

  ## 选择理由
  {Why — from the user's stated or implied reasoning}
  ```

Only save after the user has made an explicit choice. If the user moves on without choosing, do not save.

## Tone and Style

- Be direct and opinionated in the recommendation — the user invoked this mode because they want a strong expert take, not more hedging.
- Use concrete references (named products, specific frameworks, real patterns) over generic advice.
- Keep the total output concise. The expert analysis section is the longest part; everything else should be tight.
- In Chinese conversations, maintain the user's natural code-switching style (Chinese prose with English technical terms).

## Example

**User is building a knowledge product and asks about data source design for a "Soul" (user profile) feature. Claude auto-triggers:**

---

**专家视角选择：** 本次从认知心理学（约哈里窗模型）、平台设计（双边数据网络效应）、行为设计（Fogg 行为模型）、隐私架构（Privacy by Design）、以及标杆产品参考（Spotify Wrapped 的数据叙事）五个维度分析。

{... analysis per lens ...}

**推荐方案：** 选 B（双源加权）但增加一层 — 不只是静态加权，而是让用户看到 Soul 是如何被"两种声音"塑造的，把数据来源的双重性变成产品叙事...

**评估框架：**
| 标准 | 说明 |
|---|---|
| 数据丰富度 | Soul 画像是否能在用户早期就有足够信号？ |
| 用户感知 | 用户是否觉得 Soul "懂我"而不是"监视我"？ |
| 冷启动 | 新用户没有 AI 记忆时 Soul 是否仍有价值？ |
| 实现复杂度 | 加权逻辑是否可以在当前架构下 2 周内上线？ |

---

你选哪个方案？确认后我保存到 KnowMine。

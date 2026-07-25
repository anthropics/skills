# Xiaohongshu Content Analysis Framework

Deep analysis framework tailored for Xiaohongshu's unique engagement patterns.

## Purpose

Before creating infographics, thoroughly analyze the source material to:
- Maximize hook power and swipe motivation
- Identify save-worthy and share-worthy elements
- Plan the visual narrative arc
- Match content to optimal style/layout

## Platform Characteristics

Unlike other platforms, Xiaohongshu content must prioritize:
- **Hook Power**: First image decides 90% of engagement
- **Swipe Motivation**: Each image must compel users to continue
- **Save Value**: Content worth bookmarking for later
- **Share Triggers**: Emotional resonance that drives sharing

## Analysis Dimensions

### 1. Content Type Classification

| Type | Characteristics | Best Style | Best Layout |
|------|----------------|------------|-------------|
| 种草/安利 | Product recommendation, benefits focus | cute/fresh | balanced/list |
| 干货分享 | Knowledge, tips, how-to | notion | dense/list |
| 个人故事 | Personal experience, emotional | warm | balanced |
| 测评对比 | Review, comparison, pros/cons | bold/notion | comparison |
| 教程步骤 | Step-by-step guide | fresh/notion | flow/list |
| 避坑指南 | Warnings, mistakes to avoid | bold | list/comparison |
| 清单合集 | Collections, recommendations | cute/minimal | list/dense |

### 2. Hook Analysis (爆款标题潜力)

Evaluate title/hook potential using these patterns:

**Hook Types**:
- **数字钩子**: "5个方法", "3分钟学会", "99%的人不知道"
- **痛点钩子**: "踩过的坑", "后悔没早知道", "别再..."
- **好奇钩子**: "原来...", "竟然...", "没想到..."
- **利益钩子**: "省钱", "变美", "效率翻倍"
- **身份钩子**: "打工人必看", "学生党", "新手妈妈"

**Rating Scale**:
- ⭐⭐⭐⭐⭐ (5/5): Multiple strong hooks combined
- ⭐⭐⭐⭐ (4/5): Clear hook with room for enhancement
- ⭐⭐⭐ (3/5): Basic hook, needs strengthening
- ⭐⭐ (2/5): Weak hook, requires significant improvement
- ⭐ (1/5): No clear hook

### 3. Target Audience (用户画像)

| Audience | Interests | Preferred Style | Content Focus |
|----------|-----------|-----------------|---------------|
| 学生党 | 省钱、学习、校园 | cute/fresh | 平价、教程、学习方法 |
| 打工人 | 效率、职场、减压 | minimal/notion | 工具、技巧、摸鱼 |
| 宝妈 | 育儿、家居、省心 | warm/fresh | 实用、安全、经验 |
| 精致女孩 | 美妆、穿搭、仪式感 | cute/retro | 好看、氛围、品质 |
| 技术宅 | 工具、效率、极客 | notion/chalkboard | 深度、专业、新奇 |
| 美食爱好者 | 探店、食谱、测评 | warm/pop | 好吃、简单、颜值 |
| 旅行达人 | 攻略、打卡、小众 | fresh/retro | 省钱、避坑、拍照 |

### 4. Engagement Potential

**Save Value (收藏价值)**:
- Is it reference material? ✓ High save potential
- Is it a checklist or list? ✓ High save potential
- Is it a tutorial? ✓ High save potential
- Is it time-sensitive news? ✗ Low save potential

**Share Triggers (分享冲动)**:
- "我朋友也需要看这个" → High share potential
- "这说的就是我" → Identity resonance
- "太有用了必须分享" → Utility sharing
- "笑死，给朋友看看" → Entertainment sharing

**Comment Inducement (评论诱导)**:
- Open-ended questions: "你是哪种类型？"
- Experience sharing: "评论区说说你的经历"
- Debate triggers: "你觉得呢？"
- Help requests: "有更好的推荐吗？"

**Interaction Design (互动设计)**:
- Polls: "A还是B？"
- Challenges: "你能做到几个？"
- Tags: "@你那个需要的朋友"

### 5. Visual Opportunity Map

| Content Element | Visual Treatment | Example |
|-----------------|------------------|---------|
| 数据/统计 | Highlighted numbers, simple charts | "节省80%时间" 大字突出 |
| 对比 | Before/after, side-by-side | 左右分屏对比图 |
| 步骤 | Numbered flow, arrows | 1→2→3 流程图 |
| 清单 | Checklist with icons | ✓/✗ 列表配图标 |
| 情感 | Character expressions, scenes | 卡通人物表情包 |
| 产品 | Product showcase, lifestyle | 产品实拍+使用场景 |
| 引用 | Quote cards, speech bubbles | 金句卡片设计 |

### 6. Swipe Flow Design

Plan the narrative arc across images:

| Position | Purpose | Hook Strategy |
|----------|---------|---------------|
| **Cover (封面)** | Stop scrolling | 最强视觉冲击 + 核心标题 |
| **Setup (铺垫)** | Build context | 痛点共鸣 / 好奇心 |
| **Core (核心)** | Deliver value | 干货内容，每页1-2个要点 |
| **Payoff (收获)** | Practical takeaway | 可执行的行动建议 |
| **Ending (结尾)** | Drive action | CTA + 互动引导 |

**Swipe Motivation Between Images**:
- End each image with a hook for the next
- Use "下一页更精彩" type transitions
- Create information gaps that require swiping
- Build anticipation through numbering ("第3个最重要")

## Output Format

Analysis results should be saved to `analysis.md` with:

```yaml
---
title: "5个让你效率翻倍的AI工具"
topic: 干货分享
content_type: 工具推荐
source_language: zh
user_language: zh
recommended_image_count: 6
---

## Target Audience

- **Primary**: 打工人、自由职业者 - 追求效率提升
- **Secondary**: 学生党 - 写论文、做作业需要
- **Tertiary**: 内容创作者 - 需要AI辅助

## Hook Analysis

**标题钩子评分**: ⭐⭐⭐⭐ (4/5)
- ✓ 数字钩子: "5个"
- ✓ 利益钩子: "效率翻倍"
- △ 可增强: 加入身份标签 "打工人必看"

**建议优化**:
- 原标题: "5个让你效率翻倍的AI工具"
- 优化: "打工人必看！5个让我效率翻倍的AI神器"

## Value Proposition

**为什么用户要看？**
1. **实用价值**: 直接可用的工具推荐
2. **省时省力**: 不用自己筛选，直接抄作业
3. **FOMO**: 别人都在用，我不能落后

**收藏理由**: 工具清单，需要时可以回来查

## Engagement Design

- **互动点**: 结尾问"你最常用哪个？"
- **评论诱导**: "还有什么好用的工具评论区分享"
- **分享触发**: 打工人会转发给同事

## Content Signals

- "AI工具" → notion + dense
- "效率" → notion + list
- "干货" → minimal + dense

## Swipe Flow

| Image | Position | Purpose | Hook |
|-------|----------|---------|------|
| 1 | Cover | 吸引停留 | 标题+视觉冲击 |
| 2 | Setup | 建立共鸣 | 为什么需要AI工具 |
| 3-5 | Core | 核心价值 | 每页1-2个工具详解 |
| 6 | Ending | 行动引导 | 总结+互动引导 |

## Recommended Approaches

1. **Notion + Dense** - 知识卡片风格，适合干货分享 (recommended)
2. **Notion + List** - 清爽知识卡片风格
3. **Minimal + Balanced** - 简约高端，适合职场人群
```

## Analysis Checklist

Before proceeding to outline generation:

- [ ] Can I identify the content type?
- [ ] Is the hook strong enough? (≥3 stars)
- [ ] Do I know the primary audience?
- [ ] Have I identified save/share triggers?
- [ ] Are there clear visual opportunities?
- [ ] Is the swipe flow planned?
- [ ] Have I identified the best style+layout recommendation?

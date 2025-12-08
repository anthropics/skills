---
name: prompt-gen
description: AI图像提示词生成器。用户提供关键词，生成多段不同风格的AI图像提示词。适用于Midjourney、DALL-E、Stable Diffusion等AI图像生成工具。当用户需要基于关键词创建多样化图像提示词时使用此技能。
---

# AI图像提示词生成器

## 功能概述

这个技能帮助用户基于提供的关键词生成多样化、高质量的AI图像提示词。输入几个核心关键词，输出多段不同风格、构图、光照和细节的提示词。

## 使用方法

当用户提供以下类型的需求时使用此技能：
- "给我几个关于[主题]的AI提示词"
- "基于这些关键词生成图像提示：[关键词]"
- "帮我创建一些AI绘画提示词"
- "需要多样化的图像生成提示"

## 生成策略

### 1. 多样化维度
为每个请求生成4-6个不同的提示词变体，涵盖以下维度：

**艺术风格变体：**
- 写实主义 (photorealistic, hyperrealistic)
- 插画风格 (illustration, digital art, concept art)
- 艺术流派 (impressionism, surrealism, cyberpunk, anime)
- 媒介类型 (oil painting, watercolor, pencil sketch, 3D render)

**构图和视角变体：**
- 特写镜头 (close-up, macro)
- 全景镜头 (wide shot, landscape)
- 视角变化 (bird's eye view, worm's eye view, Dutch angle)
- 构图方式 (rule of thirds, centered composition, leading lines)

**光照和氛围变体：**
- 自然光 (golden hour, soft morning light, dramatic sunset)
- 人工光 (neon lighting, studio lighting, candlelight)
- 天气效果 (misty, rainy, sunny, stormy)
- 情绪氛围 (serene, dramatic, mysterious, joyful)

**细节层次变体：**
- 简洁版本 (minimal details, clean composition)
- 丰富版本 (intricate details, complex textures, elaborate elements)
- 抽象版本 (abstract interpretation, symbolic elements)

### 2. 提示词结构模板

每个提示词应包含以下元素（按重要性排序）：

```
[主体描述], [场景/背景], [艺术风格], [光照条件], [构图/视角], [情绪/氛围], [技术参数]
```

**技术参数建议：**
- 对于Midjourney: `--ar 16:9 --v 6.0 --style raw`
- 对于DALL-E: 高质量描述即可
- 对于Stable Diffusion: 包含负面提示如 `ugly, blurry, low quality`

### 3. 质量保证原则

- **具体性**: 避免模糊词汇，使用具体的形容词和名词
- **一致性**: 确保风格、光照、构图在逻辑上一致
- **原创性**: 创造独特的组合，避免陈词滥调
- **实用性**: 提示词应该能实际产生好的图像结果

## 输出格式

返回Markdown格式的响应，包含：

```markdown
基于您提供的关键词 "[关键词]"，我为您生成了以下AI图像提示词：

### 提示词 1: [风格描述]
`[完整的提示词文本]`

### 提示词 2: [风格描述]
`[完整的提示词文本]`

### 提示词 3: [风格描述]
`[完整的提示词文本]`

### 提示词 4: [风格描述]
`[完整的提示词文本]`

...

**使用建议**:
- 可以直接复制任一提示词到您的AI图像生成工具中使用
- 根据需要调整技术参数（如宽高比、版本等）
- 如果对某个风格特别感兴趣，可以要求更多该风格的变体
```

## 示例

**用户输入**: "森林、鹿、晨雾"

**输出示例**:
- 写实主义特写：一只雄鹿站在晨雾弥漫的古老森林中，阳光透过树冠形成丁达尔效应，超写实摄影风格，85mm镜头，f/1.8光圈，柔和自然光，神秘而宁静的氛围 --ar 3:2
- 印象派油画：晨雾中的森林空地，优雅的鹿群若隐若现，莫奈风格的印象派油画，柔和的蓝绿色调，松散的笔触，梦幻般的光线，诗意的氛围
- 奇幻插画：发光的白鹿在魔法森林中漫步，周围漂浮着萤火虫和水晶，吉卜力工作室风格的数字插画，温暖的金色晨光，童话般的构图，充满魔力的氛围
- 极简主义：单只鹿的剪影在薄雾笼罩的松林前，极简主义摄影，高对比度黑白，负空间构图，宁静禅意的氛围

## 注意事项

- 确保生成的提示词适合主流AI图像生成工具
- 避免生成可能产生不当内容的提示词
- 考虑文化敏感性和版权问题
- 提示词长度控制在合理范围内（通常50-150词）
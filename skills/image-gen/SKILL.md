---
name: image-gen
description: 生成多样的提示词，用户选择，通过 ModelScope API 生成图像，并将图像保存到某个地方目录。在用户需要生成图像时使用。
---

## 功能概述

这个技能帮助用户基于提供的关键词生成多样化、高质量的AI图像提示词。根据用户输入几个核心关键词，输出多段不同风格、构图、光照和细节的提示词。

## 生成策略

### 1. 多样化维度
为请求生成4-6个不同的提示词变体，涵盖以下维度：

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
[主体描述], [场景/背景], [艺术风格], [光照条件], [构图/视角], [情绪/氛围]
```

### 3. 将提示词以编号列表的形式呈现给用户。
### 4. 请用户选择一个或多个编号。

### 5：生成图像与下载
运行 ./generate.mjs 脚本来生成图像：
参数1 "一只猫" 提示词文本
参数2 "752x1280" 生成图像的大小 默认为752x1280 最小64x64 最大1440x1440
生成图像成功后会有图像的URL
使用curl命令下载图像

注意：./generate.mjs 脚本位于技能目录下
---
name: brand-guidelines
description: Applies Anthropic's official brand colors and typography to any sort of artifact that may benefit from having Anthropic's look-and-feel. Use it when brand colors or style guidelines, visual formatting, or company design standards apply.
license: Complete terms in LICENSE.txt
---

# Anthropic Brand Styling
# Anthropic 品牌样式

## Overview
概述

To access Anthropic's official brand identity and style resources, use this skill.
要访问 Anthropic 的官方品牌标识和风格资源，请使用此技能。

**Keywords**: branding, corporate identity, visual identity, post-processing, styling, brand colors, typography, Anthropic brand, visual formatting, visual design
**关键词** ：品牌、企业身份、视觉识别、后期处理、样式、品牌颜色、排版、Anthropic 品牌、视觉格式、视觉设计

## Brand Guidelines
品牌指南

### Colors
颜色

**Main Colors:**
**主要颜色：**

- Dark: `#141413` - Primary text and dark backgrounds
  深色：`#141413` - 主要文本和深色背景
- Light: `#faf9f5` - Light backgrounds and text on dark
  浅色：`#faf9f5` - 浅色背景和深色上的文本
- Mid Gray: `#b0aea5` - Secondary elements
  中灰色：`#b0aea5` - 辅助元素
- Light Gray: `#e8e6dc` - Subtle backgrounds
  浅灰色：`#e8e6dc` - 微妙背景

**Accent Colors:**
**强调颜色：**

- Orange: `#d97757` - Primary accent
  橙色：`#d97757` - 主要强调
- Blue: `#6a9bcc` - Secondary accent
  蓝色：`#6a9bcc` - 次要强调
- Green: `#788c5d` - Tertiary accent
  绿色：`#788c5d` - 三级强调

### Typography
排版

- **Headings**: Poppins (with Arial fallback)
  **标题**：Poppins（带 Arial 后备字体）
- **Body Text**: Lora (with Georgia fallback)
  **正文**：Lora（带 Georgia 后备字体）
- **Note**: Fonts should be pre-installed in your environment for best results
  **注意**：为获得最佳效果，字体应在您的环境中预先安装

## Features
特性

### Smart Font Application
智能字体应用

- Applies Poppins font to headings (24pt and larger)
  将 Poppins 字体应用于标题（24pt 及以上）
- Applies Lora font to body text
  将 Lora 字体应用于正文
- Automatically falls back to Arial/Georgia if custom fonts unavailable
  如果自定义字体不可用，自动回退到 Arial/Georgia
- Preserves readability across all systems
  保持所有系统的可读性

### Text Styling
文本样式

- Headings (24pt+): Poppins font
  标题（24pt+）：Poppins 字体
- Body text: Lora font
  正文：Lora 字体
- Smart color selection based on background
  基于背景的智能颜色选择
- Preserves text hierarchy and formatting
  保持文本层级和格式

### Shape and Accent Colors
形状和强调颜色

- Non-text shapes use accent colors
  非文本形状使用强调颜色
- Cycles through orange, blue, and green accents
  循环使用橙色、蓝色和绿色强调
- Maintains visual interest while staying on-brand
  保持视觉趣味同时保留品牌风格

## Technical Details
技术细节

### Font Management
字体管理

- Uses system-installed Poppins and Lora fonts when available
  在可用时使用系统安装的 Poppins 和 Lora 字体
- Provides automatic fallback to Arial (headings) and Georgia (body)
  提供自动回退到 Arial（标题）和 Georgia（正文）
- No font installation required - works with existing system fonts
  不需要字体安装 - 可与现有系统字体一起使用
- For best results, pre-install Poppins and Lora fonts in your environment
  为获得最佳效果，请在您的环境中预先安装 Poppins 和 Lora 字体

### Color Application
颜色应用

- Uses RGB color values for precise brand matching
  使用 RGB 颜色值进行精确的品牌匹配
- Applied via python-pptx's RGBColor class
  通过 python-pptx 的 RGBColor 类应用
- Maintains color fidelity across different systems
  保持跨不同系统的颜色保真度

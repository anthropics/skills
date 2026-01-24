# 中英双语转换 - 具体示例展示

## 示例 1: Canvas Design（最完整的转换）

### 转换前 (原始)
```markdown
---
name: canvas-design
description: Create beautiful visual art in .png and .pdf documents using design philosophy...
---

These are instructions for creating design philosophies - aesthetic movements that are then EXPRESSED VISUALLY.

Complete this in two steps:
1. Design Philosophy Creation (.md file)
2. Express by creating it on a canvas (.pdf file or .png file)

## DESIGN PHILOSOPHY CREATION

To begin, create a VISUAL PHILOSOPHY (not layouts or templates) that will be interpreted through:
- Form, space, color, composition
- Images, graphics, shapes, patterns
- Minimal text as visual accent
```

### 转换后 (中英双语)
```markdown
---
name: canvas-design
description: Create beautiful visual art in .png and .pdf documents using design philosophy...
---

These are instructions for creating design philosophies - aesthetic movements that are then EXPRESSED VISUALLY.
这些是创建设计理念的指导——美学运动，然后通过视觉表达。只输出.md 文件、.pdf 文件和.png 文件。

Complete this in two steps:
完成过程分为两个步骤：
1. Design Philosophy Creation (.md file)
   设计理念创建（.md 文件）
2. Express by creating it on a canvas (.pdf file or .png file)
   通过在画布（.pdf 文件或.png 文件）上创建来表达它

## DESIGN PHILOSOPHY CREATION
## 设计理念的创造

To begin, create a VISUAL PHILOSOPHY (not layouts or templates) that will be interpreted through:
首先，创建一个视觉哲学（不是版面或模板），通过以下方式来解读：
- Form, space, color, composition
  形态、空间、色彩、构图
- Images, graphics, shapes, patterns
  图像、图形、形状、图案
- Minimal text as visual accent
  简约文字作为视觉强调
```

**改进点：**
- ✓ 每个关键段落都有对应中文
- ✓ 列表项也添加了中文
- ✓ 中文放在英文下方，易于对应
- ✓ 保持原始格式和结构

---

## 示例 2: Brand Guidelines

### 转换前 (原始)
```markdown
# Anthropic Brand Styling

## Overview

To access Anthropic's official brand identity and style resources, use this skill.

### Colors

**Main Colors:**

- Dark: `#141413` - Primary text and dark backgrounds
- Light: `#faf9f5` - Light backgrounds and text on dark
```

### 转换后 (中英双语)
```markdown
# Anthropic Brand Styling
# Anthropic 品牌样式

## Overview
## 概述

To access Anthropic's official brand identity and style resources, use this skill.
要访问 Anthropic 的官方品牌标识和风格资源，请使用此技能。

### Colors
### 颜色

**Main Colors:**
**主要颜色：**

- Dark: `#141413` - Primary text and dark backgrounds
  深色：`#141413` - 主要文本和深色背景
- Light: `#faf9f5` - Light backgrounds and text on dark
  浅色：`#faf9f5` - 浅色背景和深色上的文本
```

**改进点：**
- ✓ 标题级别都添加了中文
- ✓ 描述性文本有对应翻译
- ✓ 列表项也进行了中文标注
- ✓ 颜色代码保持不变

---

## 示例 3: Web App Testing

### 转换前 (原始)
```markdown
# Web Application Testing

To test local web applications, write native Python Playwright scripts.

**Helper Scripts Available**:
- `scripts/with_server.py` - Manages server lifecycle
```

### 转换后 (中英双语)
```markdown
# Web Application Testing
# Web 应用程序测试

To test local web applications, write native Python Playwright scripts.
要测试本地 Web 应用程序，请编写本地 Python Playwright 脚本。

**Helper Scripts Available**:
**可用的辅助脚本**：
- `scripts/with_server.py` - Manages server lifecycle
  `scripts/with_server.py` - 管理服务器生命周期
```

**改进点：**
- ✓ 主标题添加中文
- ✓ 关键说明有中文翻译
- ✓ 脚本路径保持不变
- ✓ 简洁明了

---

## 示例 4: DOCX Skill

### 转换前 (原始)
```markdown
# DOCX creation, editing, and analysis

## Overview

A user may ask you to create, edit, or analyze the contents of a .docx file.
```

### 转换后 (中英双语)
```markdown
# DOCX creation, editing, and analysis
# DOCX 创建、编辑和分析

## Overview
## 概述

A user may ask you to create, edit, or analyze the contents of a .docx file.
用户可能会要求您创建、编辑或分析 .docx 文件的内容。
```

**改进点：**
- ✓ 标题有中文对应
- ✓ 核心说明进行了翻译
- ✓ 简洁有效

---

## 示例 5: Theme Factory

### 转换前 (原始)
```markdown
# Theme Factory Skill

This skill provides a curated collection of professional font and color themes, 
each with carefully selected color palettes and font pairings.

## Purpose

To apply consistent, professional styling to presentation slide decks, use this skill.
Each theme includes:
- A cohesive color palette with hex codes
- Complementary font pairings for headers and body text
- A distinct visual identity suitable for different contexts and audiences
```

### 转换后 (中英双语)
```markdown
# Theme Factory Skill
# 主题工厂技能

This skill provides a curated collection of professional font and color themes, 
each with carefully selected color palettes and font pairings.
此技能提供了精心策划的专业字体和颜色主题集合，
每种主题都包含精心选择的色调和字体配对。

## Purpose
## 目的

To apply consistent, professional styling to presentation slide decks, use this skill.
要将一致的专业样式应用于演示幻灯片组，请使用此技能。
Each theme includes:
每个主题包括：
- A cohesive color palette with hex codes
  具有十六进制代码的协调色调
- Complementary font pairings for headers and body text
  用于标题和正文的互补字体配对
- A distinct visual identity suitable for different contexts and audiences
  适合不同背景和受众的独特视觉身份
```

**改进点：**
- ✓ 全面的标题和内容翻译
- ✓ 列表项都有中文对应
- ✓ 长段落正确分段

---

## 翻译风格总结

### ✅ 推荐的翻译模式

#### 模式 1: 标题翻译
```markdown
# English Title
# 英文标题的中文翻译
```

#### 模式 2: 列表翻译
```markdown
- English item description
  英文项目说明的中文翻译
```

#### 模式 3: 段落翻译
```markdown
English paragraph text.
英文段落文本的中文翻译。
```

#### 模式 4: 混合翻译
```markdown
## English Section
## 英文部分的中文标题

English description.
英文描述的中文翻译。

- English item
  英文项目的中文翻译
```

---

## 为什么选择这种方式

### ✅ 直接添加中文的优势
1. **完全可见** - Claude 能同时看到英文和中文
2. **不被忽略** - 中文不会被注释方式隐藏
3. **完全理解** - 模型能用两种语言理解指令
4. **格式清晰** - Markdown 格式保持完整
5. **易于维护** - 后续可以轻松更新或调整

### ❌ HTML 注释方式的问题
```markdown
# Title
<!-- 中文标题 -->

Text here.
<!-- 中文翻译 -->
```
**问题：**
- Claude 倾向于忽略 HTML 注释
- 中文指令可能不被理解
- 格式复杂，难以维护
- 实际测试表明效果不佳

---

## 快速检查清单

使用这个清单验证转换质量：

- [ ] 所有主标题（H1）都有中文
- [ ] 主要章节（H2）都有中文标题
- [ ] 核心说明有对应的中文翻译
- [ ] 关键列表项都进行了翻译
- [ ] 没有 HTML 注释被使用
- [ ] Markdown 格式保持正确
- [ ] 代码块没有被修改
- [ ] 文件路径和命令保持不变
- [ ] 原始结构没有改变
- [ ] 中文和英文对应清晰

---

## 示例验证

### ✅ 好的转换示例
```markdown
## Core Principles
## 核心原则

This is the English text explaining the principles.
这是解释原则的英文文本的中文翻译。

- Principle 1: Description
  原则 1：说明
- Principle 2: Description  
  原则 2：说明
```

### ❌ 不好的转换示例
```markdown
## Core Principles
<!-- 核心原则 -->

<!-- This is the English text explaining the principles. -->
<!-- 这是解释原则的英文文本的中文翻译。 -->

- Principle 1: Description
  <!-- 原则 1：说明 -->
```

---

**总结：** 所有转换都采用**直接添加中文翻译**的方式，确保 Claude 能完整理解和执行中英双语指令！

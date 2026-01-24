# Bilingual Converter - Quick Reference Card
# 中英双语转换器 - 快速参考卡

A quick reference guide for common bilingual conversion scenarios and patterns.
常见双语转换场景和模式的快速参考指南。

---

## ⚡ 30-Second Quick Start
⚡ 30秒快速开始

### The One Rule
唯一规则
```markdown
English text here.
英文文本的中文翻译。
```

### What NOT to Do
不要做什么
```markdown
<!-- 不要这样做！HTML注释会被忽略 -->
```

### Result
结果
✅ Claude sees both languages  
✅ Claude 看到两种语言
✅ Both are understood  
✅ 两者都被理解

---

## 🎯 5 Most Common Patterns
🎯 5个最常见的模式

### Pattern 1: Section Headers
模式 1：章节标题

```markdown
## English Section Title
## 英文部分标题的中文翻译
```

### Pattern 2: Bullet Lists
模式 2：项目符号列表

```markdown
- Item one description
  项目一说明
- Item two description
  项目二说明
```

### Pattern 3: Numbered Steps
模式 3：编号步骤

```markdown
1. First step
   第一步
2. Second step
   第二步
```

### Pattern 4: Important Notes
模式 4：重要说明

```markdown
**Important**: Key information here.
**重要提示**：关键信息。
```

### Pattern 5: Paragraphs
模式 5：段落

```markdown
English paragraph explaining something important.
英文段落的中文翻译。
```

---

## ✅ Translation Checklist
✅ 翻译检查清单

Before submitting a bilingual-converted file:
提交双语转换文件前：

- [ ] Main title (H1) has Chinese
- [ ] Main sections (H2) have Chinese
- [ ] Core descriptions translated
- [ ] Key instructions translated
- [ ] Important warnings translated
- [ ] No HTML comments used
- [ ] Original content preserved
- [ ] Formatting looks clean
- [ ] Chinese reads naturally
- [ ] File opens without errors

---

## 🚫 Things to NEVER Do
🚫 永远不要做的事

| ❌ Don't | ✅ Do Instead |
|---------|------------|
| Use HTML comments | Add Chinese directly below |
| Delete English | Keep all English content |
| Translate code | Leave code unchanged |
| Change structure | Preserve document layout |
| Mix languages in one line | Keep each language on own line |
| Use auto-translator artifacts | Use professional translations |
| Forget to check formatting | Always verify in preview |
| Use simplified or informal Chinese | Use professional Chinese |

---

## 📊 Translation Priority Matrix
📊 翻译优先级矩阵

```
HIGH PRIORITY (Translate First)
高优先级（首先翻译）
├─ Main title (H1)
├─ All H2 section headings
├─ "Overview" / "Introduction"
├─ Usage instructions
└─ Important warnings

MEDIUM PRIORITY (Then Translate)
中等优先级（然后翻译）
├─ Descriptive paragraphs
├─ Feature lists
├─ Configuration options
└─ Common examples

LOW PRIORITY (May Leave Untranslated)
低优先级（可以不翻译）
├─ Detailed API reference
├─ Internal technical details
├─ Code comments
└─ Advanced use cases
```

---

## 🔄 Before & After Comparison
🔄 转换前后对比

### Original (English Only)
```markdown
# Web Server Setup

This guide explains how to configure a web server.

## Installation

1. Download the package
2. Extract files
3. Run installer

## Configuration

Edit the config file to set parameters.
```

### Converted (Bilingual)
```markdown
# Web Server Setup
# Web 服务器设置

This guide explains how to configure a web server.
本指南说明如何配置 web 服务器。

## Installation
## 安装

1. Download the package
   下载包
2. Extract files
   提取文件
3. Run installer
   运行安装程序

## Configuration
## 配置

Edit the config file to set parameters.
编辑配置文件以设置参数。
```

**What Changed:**
发生的变化：
- ✓ Every heading now has Chinese
- ✓ 每个标题现在都有中文
- ✓ Each step has Chinese translation
- ✓ 每个步骤都有中文翻译
- ✓ Descriptions translated
- ✓ 说明已翻译
- ✓ No content was removed
- ✓ 没有删除任何内容

---

## 💡 Common Scenarios
💡 常见场景

### Scenario 1: Converting a SKILL.md
场景 1：转换 SKILL.md

**What to translate:**
翻译什么：
- Title, description, all H2 headers
- Overview section
- When to use
- Core principles
- Key instructions
- Warning messages

**What to skip:**
跳过什么：
- Code examples
- File paths and URLs
- Command-line examples

### Scenario 2: Converting README.md
场景 2：转换 README.md

**What to translate:**
翻译什么：
- Main title
- Project description
- Getting started
- Feature list
- Basic installation
- Common usage

**What to skip:**
跳过什么：
- Detailed API reference
- Code snippets
- Advanced configuration

### Scenario 3: Converting Technical Reference
场景 3：转换技术参考

**What to translate:**
翻译什么：
- Section titles
- Parameter descriptions
- Return values explanation
- Error messages

**What to skip:**
跳过什么：
- Function signatures
- Code blocks
- Type definitions

---

## 🛠️ Tools and Commands
🛠️ 工具和命令

### Batch Conversion
批量转换

```bash
# Run the conversion script
python convert_skills_to_bilingual.py
```

### Manual Editing
手动编辑

1. Open the file in your markdown editor
2. Add Chinese translations following the patterns
3. Save with UTF-8 encoding
4. Verify in markdown preview

### Validation
验证

```bash
# Check encoding
file -b --mime-encoding SKILL.md

# Preview markdown
python -m markdown SKILL.md
```

---

## 📈 Quality Levels
📈 质量水平

### Level 1: Professional ⭐⭐⭐⭐⭐
第 1 级：专业级

- Natural, fluent Chinese
- Accurate technical terms
- Consistent terminology
- Perfect formatting
- All critical content translated

→ **Target this level for SKILL.md files**

### Level 2: Functional ⭐⭐⭐⭐
第 2 级：功能级

- Comprehensible Chinese
- Mostly accurate terms
- Some variation in phrasing
- Good formatting
- Main content translated

### Level 3: Minimal ⭐⭐⭐
第 3 级：最低级

- Basic Chinese
- Some inaccuracies
- Inconsistent terms
- Acceptable formatting
- Essential content only

---

## 🎓 Learning Resources
🎓 学习资源

| Resource | 位置 | 描述 |
|----------|------|------|
| Full Guide | SKILL.md | Complete conversion guide |
| Glossary | GLOSSARY.md | Technical terms reference |
| Examples | BEFORE_AFTER_EXAMPLES.md | Real conversion examples |
| Quick Card | This file | Quick reference (you are here) |

---

## ⚡ Emergency Quick Solutions
⚡ 紧急快速解决方案

**Problem: Text looks garbled**
问题：文本看起来乱码

→ Solution: Check UTF-8 encoding
→ 解决方案：检查 UTF-8 编码

**Problem: Formatting is broken**
问题：格式被破坏

→ Solution: Verify markdown syntax
→ 解决方案：验证 markdown 语法

**Problem: Chinese not appearing**
问题：中文不显示

→ Solution: Check file not using HTML comments
→ 解决方案：检查文件不使用 HTML 注释

**Problem: Inconsistent terminology**
问题：术语不一致

→ Solution: Check GLOSSARY.md
→ 解决方案：检查 GLOSSARY.md

**Problem: Lost original English**
问题：丢失原始英文

→ Solution: Restore from backup
→ 解决方案：从备份恢复

---

## 📋 Conversion Workflow
📋 转换工作流程

```
1. PREPARE
   准备
   ├─ Back up original file
   └─ Review what needs translation

2. TRANSLATE
   翻译
   ├─ Add Chinese to headings
   ├─ Translate descriptions
   └─ Add Chinese to instructions

3. FORMAT
   格式化
   ├─ Fix spacing
   ├─ Check alignment
   └─ Verify structure

4. VERIFY
   验证
   ├─ Check encoding
   ├─ Preview in markdown
   └─ Read through both languages

5. DONE
   完成
   ├─ Save file
   └─ Update documentation
```

---

## 🎯 Success Criteria
🎯 成功标准

A bilingual-converted file is considered complete when:
双语转换文件在以下情况下被认为是完整的：

✅ All main headings have English and Chinese  
✅ 所有主标题都有英文和中文

✅ Core content is translated to professional level  
✅ 核心内容已翻译为专业级

✅ No content was removed or changed  
✅ 没有删除或更改任何内容

✅ Formatting is clean and consistent  
✅ 格式干净一致

✅ File opens without errors  
✅ 文件打开没有错误

✅ Both languages read naturally  
✅ 两种语言都能自然阅读

✅ Terminology is consistent throughout  
✅ 术语全程一致

---

## 📞 Quick Help Matrix
📞 快速帮助矩阵

| Question | Answer |
|----------|--------|
| Should I use comments? | No, add Chinese directly |
| Should I remove English? | No, keep all English |
| Should I translate code? | No, leave code unchanged |
| What about file paths? | Leave them as-is |
| How formal should Chinese be? | Professional/formal |
| What if I'm unsure? | Check GLOSSARY.md |
| How do I batch convert? | Use the Python script |
| How do I verify quality? | Use checklist above |

---

**Quick Reference Version**: 1.0  
**Last Updated**: 2026-01-24  
**Print This**: Yes, keep on desk when translating!

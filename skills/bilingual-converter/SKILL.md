---
name: bilingual-converter
description: Convert English markdown files to bilingual Chinese-English format. Use this skill when you need to transform English .md files in skill folders into Chinese-English dual-language documentation. Creates professional bilingual content by adding Chinese translations directly below English text, ensuring both languages are fully visible and understood by AI models.
license: Complete terms in LICENSE.txt
---

# Bilingual Converter Skill
# 中英双语转换技能

This skill provides a structured approach to converting English markdown files into professional bilingual Chinese-English format. The conversions maintain full English content while adding Chinese translations directly (never using HTML comments), ensuring AI models can understand and execute instructions in both languages.
此技能提供了一个结构化的方法来将英文markdown文件转换为专业的中英双语格式。转换过程保留完整的英文内容，同时直接添加中文翻译（不使用HTML注释），确保AI模型能够理解和执行两种语言的指令。

---

## When to Use This Skill
何时使用此技能

Use this skill when:
使用此技能的情况：

- You have English .md documentation files that need Chinese translations
  您有需要中文翻译的英文 .md 文档文件
- Converting SKILL.md files in skill folders to bilingual format
  将技能文件夹中的 SKILL.md 文件转换为双语格式
- Creating multilingual support for AI documentation
  为 AI 文档创建多语言支持
- Ensuring both English and Chinese speakers can understand technical content
  确保英文和中文使用者都能理解技术内容
- Building professional dual-language reference materials
  构建专业的双语参考材料

---

## Core Principles
核心原则

### ✅ Recommended: Direct Chinese Addition
✅ 推荐方式：直接添加中文

```markdown
# English Title
# 英文标题的中文翻译

English description text.
英文描述文本的中文翻译。

- Point 1
  要点 1
- Point 2
  要点 2
```

**Advantages:**
优势：
- AI model sees both languages completely
  AI 模型能完整看到两种语言
- Chinese translations are not ignored
  中文翻译不会被忽略
- Both languages are properly understood
  两种语言都能被正确理解
- Clean, maintainable markdown format
  清洁、可维护的 markdown 格式

### ❌ Not Recommended: HTML Comments
❌ 不推荐方式：HTML 注释

```markdown
# Title
<!-- 中文标题 -->

Text here.
<!-- 中文翻译 -->
```

**Problems:**
问题：
- AI models often ignore HTML comments
  AI 模型通常忽略 HTML 注释
- Chinese instructions may not be understood
  中文指令可能无法被理解
- Content becomes hidden and unmaintainable
  内容变成隐藏和不可维护的
- Reduced effectiveness and accessibility
  降低有效性和可访问性

---

## Conversion Process
转换过程

### Step 1: Identify Content to Translate
步骤 1：识别需要翻译的内容

Prioritize for translation:
优先翻译的内容：

1. **Titles and Headings** (H1, H2, H3)
   标题和标题（H1、H2、H3）
   - All main section headings must have Chinese equivalents
     所有主要章节标题必须有中文等价物

2. **Core Descriptions and Overviews**
   核心说明和概述
   - Introduction paragraphs explaining what the document covers
     解释文档涵盖内容的介绍段落
   - Key purpose and usage instructions
     关键目的和使用说明

3. **Critical Instructions and Guidelines**
   关键指导和指令
   - Step-by-step processes
     分步过程
   - Important warnings and requirements
     重要警告和要求
   - Technical constraints and limitations
     技术约束和限制

4. **List Items and Bullet Points**
   列表项和项目符号
   - When items explain important concepts
     当项目解释重要概念时
   - Feature lists and capability descriptions
     特性列表和功能说明
   - Configuration options and parameters
     配置选项和参数

5. **Examples and Use Cases**
   示例和使用案例
   - Practical demonstrations of features
     特性的实际演示
   - Common workflows and scenarios
     常见工作流程和场景

### Step 2: Translate Content
步骤 2：翻译内容

Translation guidelines:
翻译指导原则：

**Accuracy First**
准确性优先
- Maintain technical accuracy in both languages
  保持两种语言的技术准确性
- Preserve original meaning completely
  完整保留原始含义
- Use professional terminology consistently
  一致地使用专业术语

**Natural Chinese**
自然中文
- Use fluent, professional Chinese language
  使用流畅、专业的中文语言
- Avoid literal word-for-word translation
  避免逐字逐句翻译
- Consider Chinese reading conventions
  考虑中文阅读习惯

**Preserve Code and Technical Elements**
保留代码和技术元素
- Never translate code examples
  不要翻译代码示例
- Keep file paths, URLs, and commands unchanged
  保持文件路径、URL 和命令不变
- Preserve technical abbreviations and acronyms
  保留技术缩写和首字母缩略词

### Step 3: Format Bilingual Content
步骤 3：格式化双语内容

Formatting rules:
格式化规则：

**Heading Format**
标题格式
```markdown
# English Heading
# 英文标题的中文翻译
```

**Paragraph Format**
段落格式
```markdown
English paragraph text that explains a concept.
英文段落文本的中文翻译，解释了一个概念。
```

**List Format**
列表格式
```markdown
- English item description
  英文项目说明的中文翻译
- Another point
  另一个要点
```

**Mixed Content Format**
混合内容格式
```markdown
## Section Title
## 部分标题

Introduction text in English.
英文介绍文本的中文翻译。

- Point 1: Description
  要点 1：说明
- Point 2: Description
  要点 2：说明

**Important**: English note here.
**重要提示**：英文注释的中文翻译。
```

### Step 4: Quality Assurance
步骤 4：质量保证

Verification checklist:
验证清单：

- [ ] All main headings (H1, H2) have Chinese equivalents
  所有主标题（H1、H2）都有中文等价物
- [ ] Core descriptions and instructions are translated
  核心说明和指令已翻译
- [ ] Chinese text is natural and professional
  中文文本自然且专业
- [ ] No HTML comments are used
  未使用 HTML 注释
- [ ] Original markdown structure is preserved
  原始 markdown 结构已保留
- [ ] Code blocks remain unchanged
  代码块保持不变
- [ ] Technical terms are consistent
  技术术语保持一致
- [ ] No formatting errors or encoding issues
  没有格式错误或编码问题
- [ ] Text alignment and spacing are correct
  文本对齐和间距正确
- [ ] Content is readable and maintainable
  内容可读且可维护

---

## Detailed Translation Examples
详细翻译示例

### Example 1: SKILL File Header
示例 1：SKILL 文件标题

**Before:**
```markdown
---
name: skill-name
description: Comprehensive description of what the skill does...
---

# Skill Title

This skill provides tools and guidance for specific tasks.

## Overview

To use this skill effectively, understand the following concepts.
```

**After:**
```markdown
---
name: skill-name
description: Comprehensive description of what the skill does...
---

# Skill Title
# 技能标题

This skill provides tools and guidance for specific tasks.
此技能为特定任务提供工具和指导。

## Overview
## 概述

To use this skill effectively, understand the following concepts.
要有效使用此技能，请理解以下概念。
```

### Example 2: Instructions with Steps
示例 2：带有步骤的指导

**Before:**
```markdown
## How to Use

1. Prepare your materials
2. Follow these steps in order
3. Verify the results
4. Document your findings

### Important Requirements

- Data must be validated first
- Follow the security guidelines
- Report any issues immediately
```

**After:**
```markdown
## How to Use
## 使用方法

1. Prepare your materials
   准备您的材料
2. Follow these steps in order
   按顺序遵循这些步骤
3. Verify the results
   验证结果
4. Document your findings
   记录您的发现

### Important Requirements
### 重要要求

- Data must be validated first
  数据必须首先经过验证
- Follow the security guidelines
  遵循安全指南
- Report any issues immediately
  立即报告任何问题
```

### Example 3: Technical Content
示例 3：技术内容

**Before:**
```markdown
## Configuration

The system accepts these parameters:

- `timeout`: Integer, milliseconds (default: 5000)
- `retries`: Integer, number of retry attempts
- `encoding`: String, file encoding format

## Installation

Run the following command:

```bash
pip install package-name
```

Verify installation with:

```bash
python -c "import module; print(module.__version__)"
```
```

**After:**
```markdown
## Configuration
## 配置

The system accepts these parameters:
系统接受这些参数：

- `timeout`: Integer, milliseconds (default: 5000)
  整数，毫秒（默认值：5000）
- `retries`: Integer, number of retry attempts
  整数，重试次数
- `encoding`: String, file encoding format
  字符串，文件编码格式

## Installation
## 安装

Run the following command:
运行以下命令：

```bash
pip install package-name
```

Verify installation with:
使用以下方式验证安装：

```bash
python -c "import module; print(module.__version__)"
```
```

---

## Conversion Strategy by Document Type
按文档类型的转换策略

### SKILL.md Files (Highest Priority)
SKILL.md 文件（最高优先级）

**Translate:**
翻译：
- Frontmatter description
- Main title and all H2 headings
- "When to use" section
- Core principles and guidelines
- Step-by-step instructions
- Important warnings and requirements
- Feature lists and capabilities

**May leave untranslated:**
可以不翻译：
- Detailed technical reference sections
- Large code block annotations
- Partner-specific implementation details

### README.md Files
README.md 文件

**Translate:**
翻译：
- Main title
- Project description
- Getting started section
- Key features overview
- Installation instructions
- Basic usage examples

**May leave untranslated:**
可以不翻译：
- Detailed API reference
- Advanced configuration examples
- Internal implementation notes

### Reference Documentation
参考文档

**Translate:**
翻译：
- Section headings
- Introduction paragraphs
- Parameter descriptions
- Error messages and warnings
- Common use cases

**May leave untranslated:**
可以不翻译：
- Complete function signatures
- Internal technical details
- Low-level implementation specifics

---

## Common Translation Patterns
常见翻译模式

### Pattern 1: Title + Description
模式 1：标题 + 描述

```markdown
# Feature Name
# 特性名称

Brief description of the feature.
特性的简要说明。
```

### Pattern 2: Bullet Point List
模式 2：项目符号列表

```markdown
- Item 1: Description
  项目 1：说明
- Item 2: Description
  项目 2：说明
```

### Pattern 3: Step-by-Step Process
模式 3：分步过程

```markdown
1. First step description
   第一步说明
2. Second step description
   第二步说明
```

### Pattern 4: Emphasized Sections
模式 4：强调部分

```markdown
**Important**: Key information here.
**重要提示**：关键信息在这里。

> Quoted text in English.
> 英文引文的中文翻译。
```

### Pattern 5: Code with Explanation
模式 5：代码与说明

```markdown
Example usage:
示例用法：

```python
# Code example - no translation needed
code_here()
```

This demonstrates how to use the feature.
这演示了如何使用该特性。
```

---

## Tools and Automation
工具和自动化

### Python Conversion Script
Python 转换脚本

Use the provided `convert_skills_to_bilingual.py` script for batch conversions:
使用提供的 `convert_skills_to_bilingual.py` 脚本进行批量转换：

```bash
python convert_skills_to_bilingual.py
```

**Features:**
特性：
- Automatic detection of English content
  自动检测英文内容
- Prevents duplicate translations
  防止重复翻译
- Batch processing multiple files
  批量处理多个文件
- Maintains file structure and formatting
  保持文件结构和格式化

### Manual Process
手动过程

For custom conversions or fine-tuning:
对于自定义转换或微调：

1. Open the English .md file
   打开英文 .md 文件
2. Identify sections needing translation
   识别需要翻译的部分
3. Add Chinese translations following the patterns above
   按照上述模式添加中文翻译
4. Verify formatting and quality
   验证格式和质量
5. Save and validate the bilingual file
   保存并验证双语文件

---

## Quality Standards
质量标准

### Translation Quality Levels
翻译质量水平

**Level 1: Professional** (推荐)
- Natural, fluent Chinese language
- Accurate technical terminology
- Consistent with established glossary
- Properly formatted bilingual layout
- All critical content translated

**Level 2: Functional**
- Comprehensible Chinese language
- Mostly accurate terminology
- Some terminology variations
- Acceptable bilingual format
- Main content translated

**Level 3: Minimal**
- Basic Chinese language
- Some technical inaccuracies
- Inconsistent terminology
- Simple bilingual format
- Essential content only

Aim for **Level 1 (Professional)** for skill files.
为技能文件力求达到**第 1 级（专业）**。

### Consistency Guidelines
一致性指导

- Create and maintain a terminology glossary
  创建并维护术语表
- Keep technical terms consistent across translations
  保持翻译中的技术术语一致
- Use the same Chinese equivalents for repeated English terms
  为重复出现的英文术语使用相同的中文等价物
- Review previous translations for consistency
  查看之前的翻译以确保一致性

---

## Best Practices
最佳实践

### Do ✅
做的事：

- ✓ Keep English content completely intact
  保持英文内容完全完整
- ✓ Add Chinese directly below English
  在英文下方直接添加中文
- ✓ Use professional, natural Chinese
  使用专业、自然的中文
- ✓ Maintain consistent terminology
  保持术语一致
- ✓ Preserve all markdown formatting
  保留所有 markdown 格式
- ✓ Test readability in both languages
  测试两种语言的可读性
- ✓ Document translation decisions
  记录翻译决定

### Don't ❌
不要做的事：

- ✗ Use HTML comments for Chinese
  不要用 HTML 注释表示中文
- ✗ Remove any English content
  不要删除任何英文内容
- ✗ Translate code or file paths
  不要翻译代码或文件路径
- ✗ Mix Chinese within English sentences
  不要在英文句子中混入中文
- ✗ Change the document structure
  不要改变文档结构
- ✗ Over-translate (leave technical terms as-is)
  不要过度翻译（保持技术术语原样）
- ✗ Forget to verify formatting
  不要忘记验证格式

---

## Troubleshooting
故障排除

### Issue: Chinese text not visible
问题：中文文本不可见

**Solution:**
解决方案：
- Check file encoding (should be UTF-8)
  检查文件编码（应为 UTF-8）
- Verify markdown is valid
  验证 markdown 有效
- Ensure no HTML comments are hiding content
  确保没有 HTML 注释隐藏内容

### Issue: Inconsistent terminology
问题：术语不一致

**Solution:**
解决方案：
- Review the terminology glossary
  查看术语表
- Update all instances to match
  更新所有实例以匹配
- Document the standard term
  记录标准术语

### Issue: Formatting broken after translation
问题：翻译后格式破裂

**Solution:**
解决方案：
- Check for special characters
  检查特殊字符
- Verify markdown syntax
  验证 markdown 语法
- Preview in markdown viewer
  在 markdown 查看器中预览

---

## File Organization
文件组织

```
skills/
├── bilingual-converter/
│   └── SKILL.md (this file)
├── {skill-name}/
│   └── SKILL.md (convert to bilingual)
├── {another-skill}/
│   └── SKILL.md (convert to bilingual)
└── convert_skills_to_bilingual.py
```

When converting:
转换时：

1. Back up original files
   备份原始文件
2. Use the conversion script
   使用转换脚本
3. Verify each converted file
   验证每个转换的文件
4. Update documentation as needed
   根据需要更新文档

---

## Summary Checklist
总结清单

Before considering a file bilingual-converted:
在认为文件已转换为双语之前：

- [ ] All H1 and H2 headings have Chinese
  所有 H1 和 H2 标题都有中文
- [ ] Core descriptions translated
  核心说明已翻译
- [ ] Steps and instructions translated
  步骤和指导已翻译
- [ ] Important warnings translated
  重要警告已翻译
- [ ] No HTML comments used
  未使用 HTML 注释
- [ ] Original content preserved
  原始内容已保留
- [ ] Formatting is clean and consistent
  格式干净一致
- [ ] Chinese is natural and professional
  中文自然专业
- [ ] File validated in markdown viewer
  在 markdown 查看器中验证了文件
- [ ] Terminology is consistent
  术语一致
- [ ] Quality reaches Level 1 (Professional)
  质量达到第 1 级（专业）

---

## Next Steps
后续步骤

After conversion:
转换后：

1. **Test**: Verify content works with AI models
   测试：验证内容与 AI 模型配合使用
2. **Document**: Update project documentation
   文档：更新项目文档
3. **Maintain**: Keep translations updated
   维护：保持翻译最新
4. **Expand**: Apply to more files
   扩展：应用于更多文件
5. **Refine**: Improve based on feedback
   改进：根据反馈改进

---

**Status**: Ready to use | **Version**: 1.0 | **Last Updated**: 2026-01-24

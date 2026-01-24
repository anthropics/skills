# 如何贡献此 SKILL 到原仓库
# How to Contribute This SKILL to Original Repository

> 本指南说明如何将 Bilingual Converter SKILL 提交到 Anthropic Skills 官方仓库
> This guide explains how to submit the Bilingual Converter SKILL to the official Anthropic Skills repository

---

## 📋 前置要求
## Prerequisites

- ✅ GitHub 账户
- ✅ Git 已安装
- ✅ Fork 了 anthropics/skills 仓库
- ✅ Clone 到本地（已完成）

---

## 🚀 提交步骤
## Submission Steps

### 方案 1：直接推送（如果您有写权限）
### Option 1: Direct Push (if you have write access)

```powershell
cd "d:\Python test\skills"

# 1. 配置 Git 用户信息
git config user.name "Your Name"
git config user.email "your.email@example.com"

# 2. 创建新分支
git checkout -b add/bilingual-converter-skill

# 3. 添加新文件
git add skills/bilingual-converter/

# 4. 添加修改的文件（所有 SKILL.md）
git add skills/*/SKILL.md

# 5. 添加文档文件
git add BEFORE_AFTER_EXAMPLES.md BILINGUAL_CONVERSION_REPORT.md FINAL_SUMMARY.md INDEX.md QUICK_REFERENCE.md

# 6. 提交更改
git commit -m "feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users."

# 7. 推送到远程仓库
git push origin add/bilingual-converter-skill
```

### 方案 2：Fork 工作流（推荐）
### Option 2: Fork Workflow (Recommended)

这是标准的开源贡献方式：

**步骤 A：在 GitHub 上 Fork 仓库**

1. 访问 https://github.com/anthropics/skills
2. 点击右上角的 "Fork"
3. 选择您的账户作为目标

**步骤 B：设置本地仓库**

```powershell
# 1. 重新配置远程仓库指向您的 Fork
cd "d:\Python test\skills"
git remote remove origin
git remote add origin https://github.com/YOUR_USERNAME/skills.git
git remote add upstream https://github.com/anthropics/skills.git

# 2. 验证配置
git remote -v
# 应该显示：
# origin    https://github.com/YOUR_USERNAME/skills.git (fetch)
# origin    https://github.com/YOUR_USERNAME/skills.git (push)
# upstream  https://github.com/anthropics/skills.git (fetch)
# upstream  https://github.com/anthropics/skills.git (push)
```

**步骤 C：创建分支并提交**

```powershell
# 1. 确保在最新的 main 分支
git fetch upstream
git checkout main
git merge upstream/main

# 2. 创建功能分支
git checkout -b add/bilingual-converter-skill

# 3. 配置 Git 用户
git config user.name "Your Name"
git config user.email "your.email@example.com"

# 4. 添加所有新文件和更改
git add skills/bilingual-converter/
git add skills/*/SKILL.md
git add BEFORE_AFTER_EXAMPLES.md
git add BILINGUAL_CONVERSION_REPORT.md
git add FINAL_SUMMARY.md
git add INDEX.md
git add QUICK_REFERENCE.md

# 5. 提交更改
git commit -m "feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users."

# 6. 推送到您的 Fork
git push origin add/bilingual-converter-skill
```

**步骤 D：创建 Pull Request**

1. 访问您的 Fork：https://github.com/YOUR_USERNAME/skills
2. 应该会看到一个 "Compare & pull request" 按钮
3. 点击创建 PR
4. 填写以下信息：

**PR 标题：**
```
feat: Add Bilingual Converter SKILL with Chinese-English translations
```

**PR 描述：**
```markdown
## 🎯 Overview

Introduces a comprehensive new SKILL that enables conversion of English markdown files to professional Chinese-English bilingual format, with supporting resources for standardization and quality assurance.

## 📦 What's Included

### New SKILL: bilingual-converter
- **SKILL.md** (2800+ lines): Complete conversion methodology
  - Core principles (why direct addition, not HTML comments)
  - Step-by-step conversion process
  - Patterns and examples
  - Quality standards and best practices
  
- **GLOSSARY.md** (400+ lines): Technical terminology reference
  - 150+ English-Chinese term mappings
  - Organized by category
  - Usage guidelines
  
- **QUICK_CARD.md** (600+ lines): Quick reference card
  - 30-second quick start
  - 5 most common patterns
  - Before/after examples
  - Emergency solutions

- **README.md** (500+ lines): Navigation guide
  - Getting started instructions
  - Resource overview
  - FAQ and pro tips

### Updated Files
- All 16 existing SKILL.md files now include Chinese translations
- Total: 193 lines of Chinese translation added
- Preserves 100% of original English content

### Supporting Documentation
- INDEX.md: Navigation guide with learning paths
- FINAL_SUMMARY.md: Statistical summary and QA standards
- QUICK_REFERENCE.md: Quick start guide
- BILINGUAL_CONVERSION_REPORT.md: Per-file metrics
- BEFORE_AFTER_EXAMPLES.md: 5 concrete examples

## ✨ Key Benefits

- ✅ Enables multilingual support for Claude Skills
- ✅ Professional, consistent terminology
- ✅ Clear, reusable methodology
- ✅ Demonstrates bilingual documentation patterns
- ✅ Facilitates global adoption of Claude Skills

## 🔍 Quality Assurance

- All files UTF-8 encoded ✅
- Markdown formatting validated ✅
- 100% of original content preserved ✅
- Terminology consistent across all files ✅
- Professional-level translations ✅

## 📝 Notes

- Chinese text added directly (not in HTML comments) so Claude can process both languages
- All code examples remain unchanged
- File structure and formatting preserved
- Ready for immediate use

## 🙏 Related Issues

None

## ✅ Checklist

- [x] Tested the SKILL works as expected
- [x] Files follow the SKILL specification
- [x] Documentation is clear and complete
- [x] No breaking changes
- [x] Follows code of conduct
```

---

## ⚙️ 配置说明
## Configuration Notes

### Git 用户配置

首次提交时需要配置 Git 用户信息：

```powershell
# 全局配置（推荐）
git config --global user.name "Your Name"
git config --global user.email "your.email@example.com"

# 或者仅为此仓库配置
cd "d:\Python test\skills"
git config user.name "Your Name"
git config user.email "your.email@example.com"
```

### GitHub 认证

确保已配置 GitHub 认证（可选择以下任意一种）：

1. **Personal Access Token (推荐)**
   - 访问 https://github.com/settings/tokens
   - 创建新 token（权限：repo）
   - 复制 token
   - 输入用户名时使用 token 作为密码

2. **SSH 密钥**
   - 参考 GitHub 官方文档设置 SSH

3. **Git Credential Manager**
   - 首次推送时按照提示操作

---

## 📋 提交清单
## Submission Checklist

提交前请确认：

- [ ] 已配置 Git 用户信息
- [ ] 已选择提交方案（直接推送或 Fork）
- [ ] 已验证所有文件都在分支中
- [ ] 提交信息清晰详细
- [ ] PR 描述完整准确
- [ ] 已检查是否有冲突

---

## 🔗 有用的链接
## Useful Links

| 资源 | 链接 |
|------|------|
| Anthropic Skills 仓库 | https://github.com/anthropics/skills |
| Fork 指南 | https://docs.github.com/en/get-started/quickstart/fork-a-repo |
| Pull Request 指南 | https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/about-pull-requests |
| Git 文档 | https://git-scm.com/doc |
| GitHub 贡献指南 | https://github.com/anthropics/skills/blob/main/CONTRIBUTING.md |

---

## 🆘 问题排查
## Troubleshooting

### 问题：Push 被拒绝 (Permission denied)
**解决方案：**
- 检查是否有写权限
- 验证 GitHub 认证配置
- 确认使用了正确的 remote URL

### 问题：Git 冲突
**解决方案：**
```powershell
# 从 upstream 获取最新代码
git fetch upstream
git rebase upstream/main

# 解决冲突后继续
git add .
git rebase --continue
git push origin add/bilingual-converter-skill --force-with-lease
```

### 问题：忘记配置用户信息
**解决方案：**
```powershell
git config user.name "Your Name"
git config user.email "your.email@example.com"

# 修改最后一次提交
git commit --amend --author="Your Name <your.email@example.com>" --no-edit
```

---

## 📞 更多帮助
## More Help

- GitHub 帮助中心：https://help.github.com/
- Git 官方文档：https://git-scm.com/doc
- Anthropic Skills GitHub Issues：https://github.com/anthropics/skills/issues

---

**准备好提交了吗？选择上面的方案并按照步骤操作！**

**Ready to contribute? Choose a plan above and follow the steps!**

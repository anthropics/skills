@echo off
REM 中英双语 SKILL 提交脚本
REM Bilingual Converter SKILL Submission Script

setlocal enabledelayedexpansion

echo.
echo =====================================================
echo 中英双语转换器 SKILL 提交助手
echo Bilingual Converter SKILL Submission Helper
echo =====================================================
echo.

REM 检查 Git 是否安装
git --version >nul 2>&1
if errorlevel 1 (
    echo ❌ Git 未安装！请先安装 Git
    echo.
    echo 下载地址: https://git-scm.com/download/win
    pause
    exit /b 1
)

REM 进入仓库目录
cd /d "d:\Python test\skills"

echo 📋 当前仓库状态：
echo.
git status --short
echo.

echo =====================================================
echo 请选择提交方案：
echo.
echo 1. 方案 A: 直接推送（需要写权限）
echo 2. 方案 B: Fork 工作流（推荐）
echo 3. 查看更多信息
echo 4. 退出
echo.
set /p choice="请输入选择 (1-4): "

if "%choice%"=="1" (
    call :direct_push
) else if "%choice%"=="2" (
    call :fork_workflow
) else if "%choice%"=="3" (
    call :show_info
) else if "%choice%"=="4" (
    echo.
    echo 再见！
    exit /b 0
) else (
    echo.
    echo ❌ 选择无效！
    pause
    exit /b 1
)

pause
exit /b 0

REM =====================================================
REM 直接推送函数
REM =====================================================
:direct_push
echo.
echo =====================================================
echo 方案 A：直接推送
echo =====================================================
echo.

echo 🔧 配置 Git 用户信息...
echo.
set /p username="输入您的名字: "
set /p useremail="输入您的邮箱: "

git config user.name "%username%"
git config user.email "%useremail%"

if errorlevel 1 (
    echo ❌ Git 配置失败！
    exit /b 1
)

echo ✅ Git 配置完成
echo.

echo 🌿 创建新分支...
git checkout -b add/bilingual-converter-skill
if errorlevel 1 (
    echo ❌ 分支创建失败！可能分支已存在
    git checkout add/bilingual-converter-skill
)

echo ✅ 分支创建/切换完成
echo.

echo 📦 添加所有更改...
git add skills/bilingual-converter/
git add skills/*/SKILL.md
git add BEFORE_AFTER_EXAMPLES.md
git add BILINGUAL_CONVERSION_REPORT.md
git add FINAL_SUMMARY.md
git add INDEX.md
git add QUICK_REFERENCE.md
echo ✅ 文件已添加
echo.

echo 📝 提交更改...
git commit -m "feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users."

if errorlevel 1 (
    echo ❌ 提交失败！
    exit /b 1
)

echo ✅ 提交完成
echo.

echo 🚀 推送到远程仓库...
git push origin add/bilingual-converter-skill
if errorlevel 1 (
    echo ❌ 推送失败！
    echo.
    echo 可能的原因：
    echo   1. 没有写权限
    echo   2. 未配置 GitHub 认证
    echo   3. 远程分支已存在
    echo.
    echo 请检查上述问题并重试
    exit /b 1
)

echo ✅ 推送成功！
echo.
echo 📌 下一步：
echo   1. 访问: https://github.com/anthropics/skills
echo   2. 创建 Pull Request
echo   3. 填写 PR 说明（参考 CONTRIBUTION_GUIDE.md）
echo   4. 等待审核
echo.

exit /b 0

REM =====================================================
REM Fork 工作流函数
REM =====================================================
:fork_workflow
echo.
echo =====================================================
echo 方案 B：Fork 工作流（推荐）
echo =====================================================
echo.

echo 📌 步骤 1：在 GitHub 上 Fork 仓库
echo.
echo   1. 访问: https://github.com/anthropics/skills
echo   2. 点击右上角的 "Fork"
echo   3. 等待 Fork 完成
echo.
set /p fork_ready="Fork 完成了吗？(y/n): "

if /i not "%fork_ready%"=="y" (
    echo ❌ 请先完成 Fork！
    exit /b 1
)

echo.
echo 🔧 步骤 2：配置本地仓库...
echo.
set /p github_username="输入您的 GitHub 用户名: "
set /p username="输入您的名字: "
set /p useremail="输入您的邮箱: "

git config user.name "%username%"
git config user.email "%useremail%"

git remote remove origin
git remote add origin https://github.com/%github_username%/skills.git
git remote add upstream https://github.com/anthropics/skills.git

echo ✅ 远程仓库已配置
echo.
echo 验证配置：
git remote -v
echo.

echo 🌿 步骤 3：创建分支...
git fetch upstream
git checkout main
git merge upstream/main
git checkout -b add/bilingual-converter-skill

echo ✅ 分支创建完成
echo.

echo 📦 步骤 4：添加所有更改...
git add skills/bilingual-converter/
git add skills/*/SKILL.md
git add BEFORE_AFTER_EXAMPLES.md
git add BILINGUAL_CONVERSION_REPORT.md
git add FINAL_SUMMARY.md
git add INDEX.md
git add QUICK_REFERENCE.md
echo ✅ 文件已添加
echo.

echo 📝 步骤 5：提交更改...
git commit -m "feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users."

if errorlevel 1 (
    echo ❌ 提交失败！
    exit /b 1
)

echo ✅ 提交完成
echo.

echo 🚀 步骤 6：推送到您的 Fork...
git push origin add/bilingual-converter-skill

if errorlevel 1 (
    echo ❌ 推送失败！
    echo.
    echo 可能的原因：
    echo   1. 未配置 GitHub 认证
    echo   2. 网络问题
    echo   3. 远程分支已存在
    echo.
    echo 请检查上述问题并重试
    exit /b 1
)

echo ✅ 推送成功！
echo.
echo 📌 下一步：
echo   1. 访问: https://github.com/%github_username%/skills
echo   2. 点击 "Compare & pull request" 按钮
echo   3. 填写 PR 说明（参考 CONTRIBUTION_GUIDE.md）
echo   4. 提交 PR
echo   5. 等待 Anthropic 团队审核
echo.

exit /b 0

REM =====================================================
REM 显示信息函数
REM =====================================================
:show_info
echo.
echo =====================================================
echo 📚 关于此 SKILL
echo =====================================================
echo.

echo 🎯 名称：
echo   中英双语转换器 SKILL
echo   Bilingual Converter SKILL
echo.

echo 📝 描述：
echo   将英文 markdown 文件转换为专业的中英双语格式
echo   Convert English markdown files to professional bilingual format
echo.

echo 📦 包含内容：
echo   1. SKILL.md (2800+ 行) - 完整的转换方法论
echo   2. GLOSSARY.md (400+ 行) - 术语标准化参考
echo   3. QUICK_CARD.md (600+ 行) - 快速查询卡片
echo   4. README.md (500+ 行) - 导航和快速开始
echo.

echo ✨ 主要特性：
echo   ✅ 确保 Claude 理解两种语言的指令
echo   ✅ 高质量的专业翻译
echo   ✅ 所有文档中的术语一致
echo   ✅ 清洁、可维护的双语格式
echo   ✅ 没有内容丢失或改变
echo.

echo 📊 统计数据：
echo   - 新增 SKILL：1 个
echo   - 更新的现有 SKILL 文件：16 个
echo   - 新增中文翻译：193 行
echo   - 支持文档：5 个
echo.

echo 🔗 原仓库：
echo   https://github.com/anthropics/skills
echo.

echo 📖 更多信息，请查看：
echo   CONTRIBUTION_GUIDE.md
echo.

exit /b 0

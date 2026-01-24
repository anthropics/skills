# 中英双语 SKILL 提交脚本 (PowerShell)
# Bilingual Converter SKILL Submission Script (PowerShell)

param(
    [ValidateSet('direct', 'fork', 'help', 'status')]
    [string]$Mode = 'help'
)

# 颜色定义
$Colors = @{
    Success = 'Green'
    Error = 'Red'
    Warning = 'Yellow'
    Info = 'Cyan'
    Normal = 'White'
}

# 辅助函数
function Write-Status {
    param(
        [string]$Message,
        [ValidateSet('success', 'error', 'warning', 'info', 'normal')]
        [string]$Type = 'normal'
    )
    
    $symbol = @{
        success = '✅'
        error = '❌'
        warning = '⚠️'
        info = 'ℹ️'
        normal = '•'
    }[$Type]
    
    $color = $Colors[$Type]
    Write-Host "$symbol $Message" -ForegroundColor $color
}

function Write-Section {
    param([string]$Title)
    Write-Host ""
    Write-Host "=====================================================" -ForegroundColor Cyan
    Write-Host $Title -ForegroundColor Cyan
    Write-Host "=====================================================" -ForegroundColor Cyan
    Write-Host ""
}

# 检查 Git 是否安装
function Test-GitInstalled {
    try {
        $version = git --version 2>$null
        return $true
    }
    catch {
        Write-Status "Git 未安装！" -Type error
        Write-Status "下载地址: https://git-scm.com/download/win" -Type info
        return $false
    }
}

# 显示仓库状态
function Show-RepositoryStatus {
    Write-Section "📋 仓库状态 Repository Status"
    
    Push-Location "d:\Python test\skills"
    
    Write-Host "分支状态 (Branch Status):" -ForegroundColor Yellow
    git branch -v
    
    Write-Host ""
    Write-Host "未提交的更改 (Uncommitted Changes):" -ForegroundColor Yellow
    git status --short
    
    Pop-Location
}

# 直接推送模式
function Submit-DirectPush {
    Write-Section "🚀 方案 A: 直接推送 Direct Push"
    
    Push-Location "d:\Python test\skills"
    
    # 获取用户信息
    $username = Read-Host "输入您的名字 Enter your name"
    $useremail = Read-Host "输入您的邮箱 Enter your email"
    
    # 配置 Git
    Write-Status "配置 Git 用户信息..." -Type info
    git config user.name $username
    git config user.email $useremail
    Write-Status "Git 配置完成" -Type success
    
    # 创建分支
    Write-Status "创建新分支..." -Type info
    git checkout -b add/bilingual-converter-skill 2>$null
    if ($LASTEXITCODE -ne 0) {
        git checkout add/bilingual-converter-skill
    }
    Write-Status "分支已准备" -Type success
    
    # 添加文件
    Write-Status "添加所有更改..." -Type info
    git add skills/bilingual-converter/
    git add skills/*/SKILL.md
    git add BEFORE_AFTER_EXAMPLES.md
    git add BILINGUAL_CONVERSION_REPORT.md
    git add FINAL_SUMMARY.md
    git add INDEX.md
    git add QUICK_REFERENCE.md
    Write-Status "文件已添加" -Type success
    
    # 提交更改
    Write-Status "提交更改..." -Type info
    $commitMessage = @"
feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users.
"@
    
    git commit -m $commitMessage
    if ($LASTEXITCODE -ne 0) {
        Write-Status "提交失败！" -Type error
        Pop-Location
        return
    }
    Write-Status "提交完成" -Type success
    
    # 推送
    Write-Status "推送到远程仓库..." -Type info
    git push origin add/bilingual-converter-skill
    
    if ($LASTEXITCODE -ne 0) {
        Write-Status "推送失败！" -Type error
        Write-Status "可能的原因：" -Type warning
        Write-Host "  1. 没有写权限"
        Write-Host "  2. 未配置 GitHub 认证"
        Write-Host "  3. 远程分支已存在"
        Pop-Location
        return
    }
    
    Write-Status "推送成功！" -Type success
    Write-Status "下一步：" -Type info
    Write-Host "  1. 访问: https://github.com/anthropics/skills"
    Write-Host "  2. 创建 Pull Request"
    Write-Host "  3. 填写 PR 说明（参考 CONTRIBUTION_GUIDE.md）"
    Write-Host "  4. 等待审核"
    
    Pop-Location
}

# Fork 工作流模式
function Submit-ForkWorkflow {
    Write-Section "🚀 方案 B: Fork 工作流 Fork Workflow (推荐 Recommended)"
    
    Push-Location "d:\Python test\skills"
    
    # 步骤 1: Fork
    Write-Host "步骤 1: 在 GitHub 上 Fork 仓库" -ForegroundColor Yellow
    Write-Host "  1. 访问: https://github.com/anthropics/skills"
    Write-Host "  2. 点击右上角的 'Fork'"
    Write-Host "  3. 等待 Fork 完成"
    Write-Host ""
    
    $forkReady = Read-Host "Fork 完成了吗？(y/n)"
    if ($forkReady -ne 'y' -and $forkReady -ne 'Y') {
        Write-Status "请先完成 Fork！" -Type error
        Pop-Location
        return
    }
    
    # 步骤 2: 配置
    Write-Section "步骤 2: 配置本地仓库 Configure Local Repository"
    
    $githubUsername = Read-Host "输入您的 GitHub 用户名 Enter your GitHub username"
    $username = Read-Host "输入您的名字 Enter your name"
    $useremail = Read-Host "输入您的邮箱 Enter your email"
    
    Write-Status "配置 Git 用户信息..." -Type info
    git config user.name $username
    git config user.email $useremail
    
    Write-Status "配置远程仓库..." -Type info
    git remote remove origin 2>$null
    git remote add origin "https://github.com/$githubUsername/skills.git"
    git remote add upstream https://github.com/anthropics/skills.git 2>$null
    
    Write-Status "远程仓库已配置：" -Type success
    git remote -v
    
    # 步骤 3: 创建分支
    Write-Section "步骤 3: 创建分支 Create Branch"
    
    Write-Status "获取最新代码..." -Type info
    git fetch upstream
    git checkout main
    git merge upstream/main
    
    Write-Status "创建功能分支..." -Type info
    git checkout -b add/bilingual-converter-skill
    Write-Status "分支已创建" -Type success
    
    # 步骤 4: 添加文件
    Write-Section "步骤 4: 添加更改 Stage Changes"
    
    Write-Status "添加所有文件和更改..." -Type info
    git add skills/bilingual-converter/
    git add skills/*/SKILL.md
    git add BEFORE_AFTER_EXAMPLES.md
    git add BILINGUAL_CONVERSION_REPORT.md
    git add FINAL_SUMMARY.md
    git add INDEX.md
    git add QUICK_REFERENCE.md
    Write-Status "文件已添加" -Type success
    
    # 步骤 5: 提交
    Write-Section "步骤 5: 提交更改 Commit Changes"
    
    Write-Status "提交更改..." -Type info
    $commitMessage = @"
feat: Add Bilingual Converter SKILL with Chinese-English translations

- Add new bilingual-converter SKILL for converting English .md files to Chinese-English bilingual format
- Includes comprehensive guide (SKILL.md), terminology glossary (GLOSSARY.md), and quick reference (QUICK_CARD.md)
- Update all existing SKILL.md files with Chinese translations
- Add supporting documentation with conversion guidelines and examples

This SKILL enables multilingual support for Claude Skills documentation, making resources accessible to both English and Chinese-speaking users.
"@
    
    git commit -m $commitMessage
    if ($LASTEXITCODE -ne 0) {
        Write-Status "提交失败！" -Type error
        Pop-Location
        return
    }
    Write-Status "提交完成" -Type success
    
    # 步骤 6: 推送
    Write-Section "步骤 6: 推送到 Fork Push to Fork"
    
    Write-Status "推送到您的 Fork..." -Type info
    git push origin add/bilingual-converter-skill
    
    if ($LASTEXITCODE -ne 0) {
        Write-Status "推送失败！" -Type error
        Write-Status "可能的原因：" -Type warning
        Write-Host "  1. 未配置 GitHub 认证"
        Write-Host "  2. 网络问题"
        Write-Host "  3. 远程分支已存在"
        Pop-Location
        return
    }
    
    Write-Status "推送成功！" -Type success
    
    # 完成提示
    Write-Section "✅ 提交几乎完成！ Almost Done!"
    
    Write-Status "下一步：" -Type info
    Write-Host "  1. 访问: https://github.com/$githubUsername/skills"
    Write-Host "  2. 点击 'Compare & pull request' 按钮"
    Write-Host "  3. 填写 PR 说明（参考 CONTRIBUTION_GUIDE.md）"
    Write-Host "  4. 点击 'Create pull request'"
    Write-Host "  5. 等待 Anthropic 团队审核"
    Write-Host ""
    Write-Status "感谢您的贡献！Thank you for contributing!" -Type success
    
    Pop-Location
}

# 显示帮助
function Show-Help {
    Write-Section "📚 中英双语 SKILL 提交助手 Submission Assistant"
    
    Write-Host "此脚本帮助您将 Bilingual Converter SKILL 提交到 Anthropic 官方仓库"
    Write-Host "This script helps you submit the Bilingual Converter SKILL to Anthropic's official repository"
    Write-Host ""
    
    Write-Host "使用方法 Usage:" -ForegroundColor Yellow
    Write-Host "  .\submit_skill.ps1 -Mode <mode>"
    Write-Host ""
    
    Write-Host "可用的模式 Available modes:" -ForegroundColor Yellow
    Write-Host "  direct    - 直接推送（需要写权限）Direct push (requires write access)"
    Write-Host "  fork      - Fork 工作流（推荐）Fork workflow (recommended)"
    Write-Host "  status    - 查看仓库状态 Show repository status"
    Write-Host "  help      - 显示此帮助信息 Show this help message"
    Write-Host ""
    
    Write-Host "示例 Examples:" -ForegroundColor Yellow
    Write-Host "  .\submit_skill.ps1 -Mode status"
    Write-Host "  .\submit_skill.ps1 -Mode fork"
    Write-Host "  .\submit_skill.ps1 -Mode direct"
    Write-Host ""
    
    Write-Host "📖 详细信息请查看 CONTRIBUTION_GUIDE.md" -ForegroundColor Cyan
    Write-Host ""
}

# 主程序
Write-Host ""
Write-Host "=================================================" -ForegroundColor Cyan
Write-Host "中英双语转换器 SKILL 提交助手" -ForegroundColor Cyan
Write-Host "Bilingual Converter SKILL Submission Assistant" -ForegroundColor Cyan
Write-Host "=================================================" -ForegroundColor Cyan
Write-Host ""

# 检查 Git
if (-not (Test-GitInstalled)) {
    exit 1
}

# 根据模式执行
switch ($Mode) {
    'direct' { Submit-DirectPush }
    'fork' { Submit-ForkWorkflow }
    'status' { Show-RepositoryStatus }
    'help' { Show-Help }
    default { Show-Help }
}

Write-Host ""

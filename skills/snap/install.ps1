# snap: installer
# This script sets everything up automatically.

$ErrorActionPreference = "Stop"

function Step($msg) { Write-Host $msg -NoNewline -ForegroundColor White }
function Ok { Write-Host " OK" -ForegroundColor Green }
function Fail($msg) {
    Write-Host " FAILED" -ForegroundColor Red
    Write-Host ""
    Write-Host $msg -ForegroundColor Yellow
    Write-Host ""
    Read-Host "Press Enter to close"
    exit 1
}

Clear-Host
Write-Host ""
Write-Host "  snap: installer" -ForegroundColor Cyan
Write-Host "  ----------------" -ForegroundColor DarkGray
Write-Host ""

# ── 1. Node.js ───────────────────────────────────────────────────────────────
Step "  Checking for Node.js..."
try {
    $v = (node --version 2>&1)
    if ($LASTEXITCODE -ne 0) { throw }
    Write-Host " found ($v)" -ForegroundColor Green
} catch {
    Write-Host " not found" -ForegroundColor Red
    Write-Host ""
    Write-Host "  Node.js is required. Opening the download page now." -ForegroundColor Yellow
    Write-Host "  -> Download the version marked LTS" -ForegroundColor Yellow
    Write-Host "  -> Run the installer (just click Next on everything)" -ForegroundColor Yellow
    Write-Host "  -> Come back and run this script again" -ForegroundColor Yellow
    Write-Host ""
    Start-Process "https://nodejs.org"
    Read-Host "  Press Enter to close"
    exit 1
}

# ── 2. Create ~/.snap and copy hook ──────────────────────────────────────────
Step "  Setting up snap folder..."
$snapDir = Join-Path $env:USERPROFILE ".snap"
New-Item -ItemType Directory -Force -Path $snapDir | Out-Null
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$hookSrc = Join-Path $scriptDir "hook.js"
if (-not (Test-Path $hookSrc)) { Fail "  Could not find hook.js next to install.ps1. Make sure you unzipped the whole folder." }
Copy-Item -Force $hookSrc (Join-Path $snapDir "hook.js")
Ok

# ── 3. Install the snap command globally ─────────────────────────────────────
Step "  Installing the snap command..."
Push-Location $scriptDir
$result = npm install -g . 2>&1
Pop-Location
if ($LASTEXITCODE -ne 0) { Fail "  npm install failed. Try running this script as Administrator (right-click -> Run as Administrator)." }
Ok

# ── 4. Wire up Claude Code hook ──────────────────────────────────────────────
Step "  Configuring Claude Code..."
$claudeDir = Join-Path $env:USERPROFILE ".claude"
$settingsPath = Join-Path $claudeDir "settings.json"
$hookCommand = "node " + (Join-Path $snapDir "hook.js").Replace("\", "/")

# Read existing settings or start fresh
if (Test-Path $settingsPath) {
    $raw = Get-Content $settingsPath -Raw
    try { $settings = $raw | ConvertFrom-Json } catch { $settings = [PSCustomObject]@{} }
} else {
    New-Item -ItemType Directory -Force -Path $claudeDir | Out-Null
    $settings = [PSCustomObject]@{}
}

# Ensure hooks.UserPromptSubmit exists
if (-not $settings.PSObject.Properties["hooks"]) {
    $settings | Add-Member -MemberType NoteProperty -Name "hooks" -Value ([PSCustomObject]@{})
}
if (-not $settings.hooks.PSObject.Properties["UserPromptSubmit"]) {
    $settings.hooks | Add-Member -MemberType NoteProperty -Name "UserPromptSubmit" -Value @()
}

# Check if our hook is already registered
$alreadyAdded = $false
foreach ($block in $settings.hooks.UserPromptSubmit) {
    if ($block.hooks | Where-Object { $_.command -like "*snap*hook.js" }) {
        $alreadyAdded = $true
        break
    }
}

if (-not $alreadyAdded) {
    $newBlock = [PSCustomObject]@{
        matcher = ""
        hooks   = @([PSCustomObject]@{ type = "command"; command = $hookCommand })
    }
    $settings.hooks.UserPromptSubmit = @($settings.hooks.UserPromptSubmit) + $newBlock
}

$settings | ConvertTo-Json -Depth 10 | Set-Content $settingsPath -Encoding UTF8
Ok

# ── Done ─────────────────────────────────────────────────────────────────────
Write-Host ""
Write-Host "  All done!" -ForegroundColor Green
Write-Host ""
Write-Host "  Next steps:" -ForegroundColor Cyan
Write-Host "    1. Restart Claude Code (or VS Code)" -ForegroundColor White
Write-Host "    2. In any terminal — type  snap  and hit Enter to test" -ForegroundColor White
Write-Host "    3. In Claude Code  — type  snap:  and hit Enter, then alt-tab to a window" -ForegroundColor White
Write-Host ""
Read-Host "  Press Enter to close"

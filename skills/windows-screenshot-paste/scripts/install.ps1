# install.ps1 — Installs ClaudeScreenshot.ahk and registers it for auto-start
# Usage: powershell -ExecutionPolicy Bypass -File install.ps1

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ahkSource = Join-Path $scriptDir "ClaudeScreenshot.ahk"
$ahkDest   = Join-Path $env:USERPROFILE "ClaudeScreenshot.ahk"
$startup   = [Environment]::GetFolderPath('Startup')
$startupLink = Join-Path $startup "ClaudeScreenshot.ahk"

# 1. Check for AutoHotkey v2
$ahkExe = Get-Command "AutoHotkey64.exe" -ErrorAction SilentlyContinue
if (-not $ahkExe) {
    Write-Host "AutoHotkey v2 not found. Installing via winget..."
    winget install AutoHotkey.AutoHotkey --accept-source-agreements --accept-package-agreements
}

# 2. Copy script to user home
Copy-Item $ahkSource $ahkDest -Force
Write-Host "Copied script to: $ahkDest"

# 3. Add to Windows startup
Copy-Item $ahkDest $startupLink -Force
Write-Host "Added to startup: $startupLink"

# 4. Kill any existing instance and launch
Stop-Process -Name "AutoHotkey64" -Force -ErrorAction SilentlyContinue
Start-Sleep -Milliseconds 500
Start-Process $ahkDest
Write-Host "Script is now running. Screenshots save to: $env:USERPROFILE\Pictures\Claude_Screenshots"

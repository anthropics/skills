param(
    [switch]$Apply
)

$ErrorActionPreference = "Stop"

$keyPath = Join-Path $env:USERPROFILE ".ssh\id_ed25519_trae_local_test"
$pubKeyPath = "$keyPath.pub"
$sshDir = Join-Path $env:USERPROFILE ".ssh"
$authorizedKeys = Join-Path $sshDir "authorized_keys"
$sshConfig = Join-Path $sshDir "config"
$hostBlockStart = "# >>> trae-localhost managed by vscode skill"
$hostBlockEnd = "# <<< trae-localhost managed by vscode skill"

function Test-IsAdmin {
    $identity = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($identity)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

function Get-OpenSshServerCapability {
    try {
        return Get-WindowsCapability -Online -Name OpenSSH.Server~~~~0.0.1.0 -ErrorAction Stop
    } catch {
        return $null
    }
}

function Write-State {
    $isAdmin = Test-IsAdmin
    $sshd = Get-Service -Name sshd -ErrorAction SilentlyContinue
    $agent = Get-Service -Name ssh-agent -ErrorAction SilentlyContinue
    $cap = Get-OpenSshServerCapability
    $port = Test-NetConnection localhost -Port 22 -WarningAction SilentlyContinue

    [pscustomobject]@{
        IsAdmin = $isAdmin
        OpenSshServerState = if ($cap) { $cap.State } else { "UnknownOrRequiresElevation" }
        SshdService = if ($sshd) { $sshd.Status } else { "Missing" }
        SshdStartType = if ($sshd) { $sshd.StartType } else { "Missing" }
        SshAgentService = if ($agent) { $agent.Status } else { "Missing" }
        Localhost22 = $port.TcpTestSucceeded
        TestKeyExists = (Test-Path -LiteralPath $keyPath)
        AuthorizedKeysExists = (Test-Path -LiteralPath $authorizedKeys)
        SshConfigExists = (Test-Path -LiteralPath $sshConfig)
    } | Format-List
}

function Ensure-Admin {
    if (-not (Test-IsAdmin)) {
        throw "setup-local-sshd.ps1 -Apply requires an elevated Administrator PowerShell. Re-run this script as Administrator."
    }
}

function Ensure-OpenSshServer {
    $cap = Get-OpenSshServerCapability
    if (-not $cap) {
        throw "Cannot inspect OpenSSH Server capability. Run from an elevated Administrator PowerShell."
    }
    if ($cap.State -ne "Installed") {
        Add-WindowsCapability -Online -Name OpenSSH.Server~~~~0.0.1.0 | Out-Null
    }

    $sshd = Get-Service -Name sshd -ErrorAction SilentlyContinue
    if (-not $sshd) {
        throw "OpenSSH Server capability install completed, but sshd service was not found."
    }
    Set-Service -Name sshd -StartupType Automatic
    Start-Service -Name sshd

    $rule = Get-NetFirewallRule -Name "OpenSSH-Server-In-TCP" -ErrorAction SilentlyContinue
    if (-not $rule) {
        New-NetFirewallRule -Name "OpenSSH-Server-In-TCP" -DisplayName "OpenSSH Server (sshd)" -Enabled True -Direction Inbound -Protocol TCP -Action Allow -LocalPort 22 | Out-Null
    } else {
        Enable-NetFirewallRule -Name "OpenSSH-Server-In-TCP" | Out-Null
    }
}

function Ensure-TestKey {
    New-Item -ItemType Directory -Path $sshDir -Force | Out-Null

    if (-not (Test-Path -LiteralPath $keyPath)) {
        ssh-keygen -t ed25519 -N "" -f $keyPath -C "trae-localhost-test" | Out-Null
    }

    if (-not (Test-Path -LiteralPath $pubKeyPath)) {
        throw "Public key was not created: $pubKeyPath"
    }
}

function Ensure-AuthorizedKey {
    $pub = Get-Content -LiteralPath $pubKeyPath -Encoding ASCII -Raw
    if ([string]::IsNullOrWhiteSpace($pub)) {
        throw "Public key is empty: $pubKeyPath"
    }

    if (-not (Test-Path -LiteralPath $authorizedKeys)) {
        New-Item -ItemType File -Path $authorizedKeys -Force | Out-Null
    }

    $existing = Get-Content -LiteralPath $authorizedKeys -Encoding ASCII -Raw -ErrorAction SilentlyContinue
    if ($existing -notmatch [regex]::Escape($pub.Trim())) {
        Add-Content -LiteralPath $authorizedKeys -Value $pub.Trim() -Encoding ASCII
    }
}

function Ensure-SshConfig {
    if (-not (Test-Path -LiteralPath $sshConfig)) {
        New-Item -ItemType File -Path $sshConfig -Force | Out-Null
    }

    $content = Get-Content -LiteralPath $sshConfig -Encoding UTF8 -Raw -ErrorAction SilentlyContinue
    if ($null -eq $content) {
        $content = ""
    }

    $block = @"
$hostBlockStart
Host trae-localhost
    HostName localhost
    Port 22
    User $env:USERNAME
    IdentityFile $keyPath
    IdentitiesOnly yes
    StrictHostKeyChecking accept-new
$hostBlockEnd
"@

    $pattern = "(?s)$([regex]::Escape($hostBlockStart)).*?$([regex]::Escape($hostBlockEnd))"
    if ($content -match $pattern) {
        $content = [regex]::Replace($content, $pattern, $block)
    } else {
        if (-not $content.EndsWith("`n") -and $content.Length -gt 0) {
            $content += "`r`n"
        }
        $content += $block + "`r`n"
    }

    Set-Content -LiteralPath $sshConfig -Value $content -Encoding UTF8
}

Write-Host "== Current state =="
Write-State

if (-not $Apply) {
    Write-Host ""
    Write-Host "Dry run only. Re-run with -Apply in an elevated Administrator PowerShell to enable local sshd."
    exit 0
}

Ensure-Admin
Ensure-OpenSshServer
Ensure-TestKey
Ensure-AuthorizedKey
Ensure-SshConfig

Write-Host ""
Write-Host "== After apply =="
Write-State

Write-Host ""
Write-Host "Run this to verify:"
Write-Host "ssh trae-localhost `"echo trae-ssh-ok`""

# init-config.ps1 - write a starter config file in the platform default location.
#
# Usage:
#   pwsh -File scripts/init-config.ps1                    # uses default location
#   pwsh -File scripts/init-config.ps1 -Path C:\path\to\config.json
#   pwsh -File scripts/init-config.ps1 -Force             # overwrite existing

[CmdletBinding()]
param(
    [string]$Path,
    [switch]$Force
)

$ErrorActionPreference = "Stop"

$scriptRoot = Split-Path -Parent $PSCommandPath
$examplePath = Join-Path $scriptRoot "..\config.example.json"

if (-not (Test-Path -LiteralPath $examplePath)) {
    throw "Cannot find example config at $examplePath. Run from the skill root or fix the script layout."
}

if (-not $Path) {
    if ($env:VSCODE_SKILL_CONFIG) {
        $Path = $env:VSCODE_SKILL_CONFIG
    } elseif ($env:APPDATA) {
        $Path = Join-Path $env:APPDATA "vscode-skill\config.json"
    } elseif ($env:XDG_CONFIG_HOME) {
        $Path = Join-Path $env:XDG_CONFIG_HOME "vscode-skill/config.json"
    } elseif ($env:HOME) {
        $Path = Join-Path $env:HOME ".config/vscode-skill/config.json"
    } else {
        throw "Cannot determine a default config path. Pass -Path explicitly."
    }
}

if ([System.IO.Path]::IsPathRooted($Path)) {
    $resolvedPath = [System.IO.Path]::GetFullPath($Path)
} else {
    $resolvedPath = [System.IO.Path]::GetFullPath((Join-Path (Get-Location) $Path))
}

if ((Test-Path -LiteralPath $resolvedPath) -and -not $Force) {
    Write-Host "Config already exists at $resolvedPath. Re-run with -Force to overwrite."
    return
}

$parent = Split-Path -Parent $resolvedPath
if ($parent) {
    New-Item -ItemType Directory -Path $parent -Force | Out-Null
}

Copy-Item -LiteralPath $examplePath -Destination $resolvedPath -Force
Write-Host "Wrote starter config to $resolvedPath"
Write-Host "Edit the file, then re-run any vscode-cli.ps1 command; the new paths will be picked up automatically."
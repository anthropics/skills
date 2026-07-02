# vscode-cli.ps1 - VS Code skill driver script.
#
# Areas: info, ext, settings, python, ssh, wsl, tasks, launch, extensions
# Products: vscode (default), vscode-insiders, or any name resolved via config.
#
# Path resolution order:
#   1. Explicit env vars: VSCODE_CODE_CLI / VSCODE_INSIDERS_CLI
#   2. config.products.<name>.cliPath (config file at $VSCODE_SKILL_CONFIG
#      or the platform default location)
#   3. Built-in defaults for vscode and vscode-insiders on Windows
#   4. Get-Command lookup on PATH
#
# Per-machine preferences (default product, ssh defaults, etc.) come from the
# same config file under the matching top-level keys.

[CmdletBinding()]
param(
    [Parameter(Position = 0)]
    [ValidateSet("info", "ext", "python", "ssh", "wsl", "settings", "tasks", "launch", "extensions", "settings-sync", "workspace", "profile")]
    [string]$Area = "info",

    [Parameter(Position = 1)]
    [string]$Action,

    [string]$Id,
    [string]$Path,
    [string]$ProjectPath,
    [string]$VenvName,
    [string]$ExpectedVenvName,
    [string]$HostName,
    [string]$Distro,
    [string]$LinuxPath,
    [string]$Command,
    [string]$Scope,
    [string]$FontFamily,
    [string]$FontSize,
    [string]$LineHeight,
    [string]$ColorTheme,
    [string]$IconTheme,
    [string]$ProductIconTheme,
    [string]$WordWrap,
    [string]$TabSize,
    [string]$FormatOnSave,
    [string]$AutoSave,
    [string]$Minimap,
    [string]$SettingKey,
    [string]$SettingValue,
    [string]$Template,
    [string]$Stack,
    [string]$Profile,
    [string]$Folder,
    [switch]$Force,
    [switch]$Apply,
    [switch]$ForceOpenVsx,
    [string]$Product,

    [Parameter(ValueFromRemainingArguments = $true)]
    [string[]]$Rest
)

$ErrorActionPreference = "Stop"

# === Argument normalization ==================================================

if ($Action -and $Action -match "^--") {
    $Rest = @($Action) + $Rest
    $Action = $null
}

for ($i = 0; $i -lt $Rest.Count; $i++) {
    $name = $Rest[$i]
    if ($name -notmatch "^--") {
        throw "Unexpected argument '$name'. Use named options such as --Id value."
    }

    $key = $name.Substring(2).ToLowerInvariant()
    if ($key -eq "force") { $Force = $true; continue }
    if ($key -eq "apply") { $Apply = $true; continue }
    if ($key -eq "forceopenvsx") { $ForceOpenVsx = $true; continue }

    if ($i + 1 -ge $Rest.Count) {
        throw "Missing value for argument '$name'."
    }

    $value = $Rest[++$i]

    switch ($key) {
        "id"               { $Id = $value }
        "path"             { $Path = $value }
        "projectpath"      { $ProjectPath = $value }
        "project-path"     { $ProjectPath = $value }
        "venvname"         { $VenvName = $value }
        "venv-name"        { $VenvName = $value }
        "expectedvenvname" { $ExpectedVenvName = $value }
        "expected-venv-name" { $ExpectedVenvName = $value }
        "hostname"         { $HostName = $value }
        "host-name"        { $HostName = $value }
        "distro"           { $Distro = $value }
        "linuxpath"        { $LinuxPath = $value }
        "linux-path"       { $LinuxPath = $value }
        "command"          { $Command = $value }
        "scope"            { $Scope = $value }
        "fontfamily"       { $FontFamily = $value }
        "font-family"      { $FontFamily = $value }
        "fontsize"         { $FontSize = $value }
        "font-size"        { $FontSize = $value }
        "lineheight"       { $LineHeight = $value }
        "line-height"      { $LineHeight = $value }
        "theme"            { $ColorTheme = $value }
        "colortheme"       { $ColorTheme = $value }
        "color-theme"      { $ColorTheme = $value }
        "icontheme"        { $IconTheme = $value }
        "icon-theme"       { $IconTheme = $value }
        "producticontheme" { $ProductIconTheme = $value }
        "product-icon-theme" { $ProductIconTheme = $value }
        "wordwrap"         { $WordWrap = $value }
        "word-wrap"        { $WordWrap = $value }
        "tabsize"          { $TabSize = $value }
        "tab-size"         { $TabSize = $value }
        "formatonsave"     { $FormatOnSave = $value }
        "format-on-save"   { $FormatOnSave = $value }
        "autosave"         { $AutoSave = $value }
        "auto-save"        { $AutoSave = $value }
        "minimap"          { $Minimap = $value }
        "settingkey"       { $SettingKey = $value }
        "setting-key"      { $SettingKey = $value }
        "key"              { $SettingKey = $value }
        "settingvalue"     { $SettingValue = $value }
        "setting-value"    { $SettingValue = $value }
        "value"            { $SettingValue = $value }
        "product"          { $Product = $value }
        "template"         { $Template = $value }
        "stack"            { $Stack = $value }
        "profile"          { $Profile = $value }
        "folder"           { $Folder = $value }
        default { throw "Unknown argument '$name'." }
    }
}

if (-not $Product) {
    $Product = "auto"
}

# === Configuration resolution ===============================================

function Get-DefaultConfigPath {
    if ($env:VSCODE_SKILL_CONFIG) {
        return $env:VSCODE_SKILL_CONFIG
    }
    if ($env:APPDATA) {
        return (Join-Path $env:APPDATA "vscode-skill\config.json")
    }
    $xdg = $env:XDG_CONFIG_HOME
    if ($xdg) {
        return (Join-Path $xdg "vscode-skill/config.json")
    }
    if ($env:HOME) {
        return (Join-Path $env:HOME ".config/vscode-skill/config.json")
    }
    return $null
}

function Read-SkillConfig {
    $path = Get-DefaultConfigPath
    if (-not $path) { return $null }
    if (-not (Test-Path -LiteralPath $path)) { return $null }
    try {
        $raw = Get-Content -LiteralPath $path -Encoding UTF8 -Raw
    } catch {
        return $null
    }
    if ([string]::IsNullOrWhiteSpace($raw)) { return $null }
    try {
        return ($raw | ConvertFrom-Json)
    } catch {
        Write-Warning "Config file at $path is not valid JSON; ignoring."
        return $null
    }
}

function Get-ConfigDefaultProduct {
    if ($env:VSCODE_SKILL_PRODUCT) {
        return $env:VSCODE_SKILL_PRODUCT.ToLowerInvariant()
    }
    $cfg = Read-SkillConfig
    if ($cfg -and $cfg.PSObject.Properties.Match('product').Count -and $cfg.product) {
        return ([string]$cfg.product).ToLowerInvariant()
    }
    return $null
}

function Get-ConfigProductCli {
    param([Parameter(Mandatory = $true)][string]$ProductName)
    $cfg = Read-SkillConfig
    if (-not $cfg) { return $null }
    if (-not $cfg.PSObject.Properties.Match('products').Count) { return $null }
    $products = $cfg.products
    if (-not $products.PSObject.Properties.Match($ProductName).Count) { return $null }
    $entry = $products.$ProductName
    if ($entry -and $entry.PSObject.Properties.Match('cliPath').Count -and $entry.cliPath) {
        return [string]$entry.cliPath
    }
    return $null
}

function Get-ConfigSshDefaults {
    $cfg = Read-SkillConfig
    if ($cfg -and $cfg.PSObject.Properties.Match('ssh').Count -and $cfg.ssh) {
        return $cfg.ssh
    }
    return $null
}

function Get-ConfigWslDefaults {
    $cfg = Read-SkillConfig
    if ($cfg -and $cfg.PSObject.Properties.Match('wsl').Count -and $cfg.wsl) {
        return $cfg.wsl
    }
    return $null
}

# === Product CLI resolution =================================================

function Resolve-VsCodeCli {
    if ($env:VSCODE_CODE_CLI -and (Test-Path -LiteralPath $env:VSCODE_CODE_CLI)) {
        return (Resolve-Path -LiteralPath $env:VSCODE_CODE_CLI).Path
    }
    $cfgPath = Get-ConfigProductCli -ProductName "vscode"
    if ($cfgPath -and (Test-Path -LiteralPath $cfgPath)) {
        return (Resolve-Path -LiteralPath $cfgPath).Path
    }
    $candidates = @()
    $cmd = Get-Command "code.cmd" -ErrorAction SilentlyContinue
    if ($cmd) { $candidates += $cmd.Source }
    $cmd = Get-Command "code" -ErrorAction SilentlyContinue
    if ($cmd) { $candidates += $cmd.Source }
    if ($env:LOCALAPPDATA) {
        $candidates += (Join-Path $env:LOCALAPPDATA "Programs\Microsoft VS Code\bin\code.cmd")
    }
    foreach ($candidate in ($candidates | Where-Object { $_ } | Select-Object -Unique)) {
        if (Test-Path -LiteralPath $candidate) {
            return (Resolve-Path -LiteralPath $candidate).Path
        }
    }
    throw "Cannot find VS Code CLI. Set VSCODE_CODE_CLI or add 'products.vscode.cliPath' to your config."
}

function Resolve-VsCodeInsidersCli {
    if ($env:VSCODE_INSIDERS_CLI -and (Test-Path -LiteralPath $env:VSCODE_INSIDERS_CLI)) {
        return (Resolve-Path -LiteralPath $env:VSCODE_INSIDERS_CLI).Path
    }
    $cfgPath = Get-ConfigProductCli -ProductName "vscode-insiders"
    if ($cfgPath -and (Test-Path -LiteralPath $cfgPath)) {
        return (Resolve-Path -LiteralPath $cfgPath).Path
    }
    $candidates = @()
    $cmd = Get-Command "code-insiders.cmd" -ErrorAction SilentlyContinue
    if ($cmd) { $candidates += $cmd.Source }
    $cmd = Get-Command "code-insiders" -ErrorAction SilentlyContinue
    if ($cmd) { $candidates += $cmd.Source }
    if ($env:LOCALAPPDATA) {
        $candidates += (Join-Path $env:LOCALAPPDATA "Programs\Microsoft VS Code Insiders\bin\code-insiders.cmd")
    }
    foreach ($candidate in ($candidates | Where-Object { $_ } | Select-Object -Unique)) {
        if (Test-Path -LiteralPath $candidate) {
            return (Resolve-Path -LiteralPath $candidate).Path
        }
    }
    throw "Cannot find VS Code Insiders CLI. Set VSCODE_INSIDERS_CLI or add 'products.vscode-insiders.cliPath' to your config."
}

function Resolve-GenericProductCli {
    param([Parameter(Mandatory = $true)][string]$ProductName)
    $cfgPath = Get-ConfigProductCli -ProductName $ProductName
    if (-not $cfgPath) {
        throw "Product '$ProductName' has no CLI path configured. Add 'products.$ProductName.cliPath' to your config file or set VSCODE_SKILL_CONFIG pointing at one that includes it."
    }
    if (-not (Test-Path -LiteralPath $cfgPath)) {
        throw "Configured CLI for '$ProductName' does not exist: $cfgPath"
    }
    return (Resolve-Path -LiteralPath $cfgPath).Path
}

function Resolve-ProductCli {
    $active = Get-ActiveProduct
    switch ($active) {
        "vscode" { return (Resolve-VsCodeCli) }
        "vscode-insiders" { return (Resolve-VsCodeInsidersCli) }
        default { return (Resolve-GenericProductCli -ProductName $active) }
    }
}

function Get-ActiveProduct {
    if ($Product -ne "auto") {
        return $Product
    }
    $default = Get-ConfigDefaultProduct
    if ($default -and $default -ne "auto") {
        return $default
    }
    try {
        $null = Resolve-VsCodeCli
        return "vscode"
    } catch {
    }
    try {
        $null = Resolve-VsCodeInsidersCli
        return "vscode-insiders"
    } catch {
    }
    throw "Cannot auto-detect a VS Code-family CLI. Pass --Product, set VSCODE_SKILL_PRODUCT, or configure cliPath in your config file."
}

function Get-ProductLabel {
    $active = Get-ActiveProduct
    switch ($active) {
        "vscode" { return "VS Code" }
        "vscode-insiders" { return "VS Code Insiders" }
        default { return $active }
    }
}

function Get-ProductUserDataPath {
    $active = Get-ActiveProduct
    if ($env:VSCODE_USER_DATA) {
        return $env:VSCODE_USER_DATA
    }
    switch ($active) {
        "vscode" {
            if ($env:APPDATA) { return (Join-Path $env:APPDATA "Code\User") }
            throw "VSCODE_USER_DATA not set and APPDATA unavailable."
        }
        "vscode-insiders" {
            if ($env:APPDATA) { return (Join-Path $env:APPDATA "Code - Insiders\User") }
            throw "VSCODE_USER_DATA not set and APPDATA unavailable."
        }
        default {
            $cfg = Read-SkillConfig
            if ($cfg -and $cfg.products -and $cfg.products.$active -and $cfg.products.$active.userDataPath) {
                return [string]$cfg.products.$active.userDataPath
            }
            throw "Product '$active' has no userDataPath configured. Set VSCODE_USER_DATA or add 'products.$active.userDataPath' to your config."
        }
    }
}

function Get-ProductExtensionDataPath {
    $active = Get-ActiveProduct
    if ($env:VSCODE_EXTENSIONS_DIR) {
        return $env:VSCODE_EXTENSIONS_DIR
    }
    $userHome = $env:USERPROFILE
    if (-not $userHome) { $userHome = $env:HOME }
    if (-not $userHome) { throw "USERPROFILE/HOME not set." }
    switch ($active) {
        "vscode" { return (Join-Path $userHome ".vscode\extensions") }
        "vscode-insiders" { return (Join-Path $userHome ".vscode-insiders\extensions") }
        default {
            $cfg = Read-SkillConfig
            if ($cfg -and $cfg.products -and $cfg.products.$active -and $cfg.products.$active.extensionsPath) {
                return [string]$cfg.products.$active.extensionsPath
            }
            return (Join-Path $userHome ".$active\extensions")
        }
    }
}

function Invoke-ProductCli {
    param([Parameter(ValueFromRemainingArguments = $true)][string[]]$CliArgs)
    $cli = Resolve-ProductCli
    & $cli @CliArgs
    $script:LastProductExitCode = $LASTEXITCODE
}

# === Output helpers =========================================================

function Write-Section {
    param([string]$Name)
    Write-Host ""
    Write-Host "== $Name =="
}

# === info ===================================================================

function Invoke-Info {
    $active = Get-ActiveProduct
    $label = Get-ProductLabel
    $cli = Resolve-ProductCli

    Write-Section "$label CLI"
    try {
        [pscustomobject]@{
            Product       = $active
            CliPath       = $cli
            UserSettings  = (Join-Path (Get-ProductUserDataPath) "settings.json")
            UserKeybindings = (Join-Path (Get-ProductUserDataPath) "keybindings.json")
            UserSnippets  = (Join-Path (Get-ProductUserDataPath) "snippets")
            Extensions    = (Get-ProductExtensionDataPath)
            ConfigFile    = (Get-DefaultConfigPath)
        } | Format-List
    } catch {
        Write-Warning "Could not resolve user data path: $($_.Exception.Message)"
    }

    Write-Section "Version"
    & $cli --version

    Write-Section "Paths"
    $paths = @()
    try { $paths += (Get-ProductUserDataPath) } catch { }
    try { $paths += (Get-ProductExtensionDataPath) } catch { }
    $pathRows = foreach ($p in ($paths | Where-Object { $_ } | Select-Object -Unique)) {
        [pscustomobject]@{ Path = $p; Exists = (Test-Path -LiteralPath $p) }
    }
    if ($pathRows) {
        $pathRows | Format-Table -AutoSize
    } else {
        Write-Host "(no path information available)"
    }
}

# === ext ====================================================================

function Get-ExtensionsJsonRows {
    $extensionsJson = Join-Path (Get-ProductExtensionDataPath) "extensions.json"
    if (-not (Test-Path -LiteralPath $extensionsJson)) {
        return @()
    }
    try {
        $raw = Get-Content -LiteralPath $extensionsJson -Encoding UTF8 -Raw
    } catch {
        return @()
    }
    if ([string]::IsNullOrWhiteSpace($raw)) {
        return @()
    }
    try {
        $items = $raw | ConvertFrom-Json
    } catch {
        return @()
    }
    if (-not $items) { return @() }
    return @($items)
}

function Find-InstalledExtensionPath {
    param([string]$ExtensionId)
    $extensionRoot = Get-ProductExtensionDataPath
    if (-not (Test-Path -LiteralPath $extensionRoot)) {
        return $null
    }
    $safeId = $ExtensionId.ToLowerInvariant()
    $candidates = Get-ChildItem -LiteralPath $extensionRoot -Directory -ErrorAction SilentlyContinue |
        Where-Object { $_.Name.ToLowerInvariant().StartsWith("$safeId-") -or $_.Name.ToLowerInvariant() -eq $safeId } |
        Sort-Object LastWriteTime -Descending
    if ($candidates) {
        return $candidates[0].FullName
    }
    return $null
}

function Test-ExtensionInJson {
    param([string]$ExtensionId)
    $rows = Get-ExtensionsJsonRows
    foreach ($row in $rows) {
        if ($row.identifier -and $row.identifier.id -eq $ExtensionId) {
            return $true
        }
    }
    return $false
}

function Save-OpenVsxVsix {
    param([string]$ExtensionId)
    $parts = $ExtensionId.Split(".")
    if ($parts.Count -lt 2) {
        throw "Open VSX fallback requires publisher.extension id (got '$ExtensionId')."
    }
    $publisher = $parts[0]
    $name = ($parts[1..($parts.Count - 1)] -join ".")
    $apiUrl = "https://open-vsx.org/api/$publisher/$name"
    $metadata = Invoke-RestMethod -Uri $apiUrl -Method Get
    $version = $metadata.version
    if (-not $version) {
        throw "Open VSX metadata did not include a version for $ExtensionId."
    }

    $fileName = "$publisher.$name-$version@win32-x64.vsix"
    $downloadUrl = "https://open-vsx.org/api/$publisher/$name/win32-x64/$version/file/$fileName"
    $downloadDir = if ($env:VSCODE_SKILL_TEMP) {
        (Join-Path $env:VSCODE_SKILL_TEMP "vsix")
    } elseif ($env:TEMP) {
        (Join-Path $env:TEMP "vscode-skill-vsix")
    } else {
        New-Item -ItemType Directory -Path "vscode-skill-vsix" -Force | Out-Null
        (Resolve-Path -LiteralPath "vscode-skill-vsix").Path
    }
    New-Item -ItemType Directory -Path $downloadDir -Force | Out-Null
    $outPath = Join-Path $downloadDir $fileName

    try {
        Invoke-WebRequest -Uri $downloadUrl -OutFile $outPath
    } catch {
        if ($metadata.files.download) {
            Invoke-WebRequest -Uri $metadata.files.download -OutFile $outPath
        } else {
            throw
        }
    }
    return $outPath
}

function Invoke-Ext {
    switch ($Action) {
        "list" {
            Invoke-ProductCli --list-extensions --show-versions
            if ($script:LastProductExitCode -ne 0) {
                throw "Failed to list extensions for $(Get-ProductLabel)."
            }
            return
        }
        "locate" {
            if (-not $Id) { throw "ext locate requires --Id." }
            $located = Find-InstalledExtensionPath -ExtensionId $Id
            if (-not $located) {
                throw "Extension $Id was not found under $(Get-ProductExtensionDataPath)."
            }
            [pscustomobject]@{ Extension = $Id; Path = $located } | Format-List
            return
        }
        "install" {
            if (-not $Id -and -not $Path) { throw "ext install requires --Id or --Path." }
            $target = if ($Path) { $Path } else { $Id }
            $args = @("--install-extension", $target)
            if ($Force) { $args += "--force" }

            Write-Section "Install via $(Get-ProductLabel) CLI"
            $cli = Resolve-ProductCli
            & $cli @args
            $exit = $LASTEXITCODE

            if ($exit -ne 0 -and $Id -and -not $Path -and $ForceOpenVsx) {
                Write-Warning "Direct gallery install failed. Retrying with Open VSX VSIX for $Id (--ForceOpenVsx)."
                $vsix = Save-OpenVsxVsix -ExtensionId $Id
                & $cli --install-extension $vsix
                $exit = $LASTEXITCODE
            } elseif ($exit -ne 0 -and $Id -and -not $Path) {
                Write-Warning "Install failed. Re-run with --ForceOpenVsx to fall back to open-vsx.org if your environment blocks the official gallery."
            }

            if ($exit -ne 0) {
                throw "Extension install failed for $target with exit code $exit."
            }

            if ($Id) {
                Write-Section "Verify"
                $locatedPath = Find-InstalledExtensionPath -ExtensionId $Id
                $inJson = Test-ExtensionInJson -ExtensionId $Id
                [pscustomobject]@{
                    Extension = $Id
                    LocatePath = $locatedPath
                    InExtensionsJson = $inJson
                } | Format-List
                if (-not $locatedPath) {
                    throw "Extension install verification failed for $Id."
                }
            }
            return
        }
        default {
            throw "Unknown ext action '$Action'. Use list, locate, or install."
        }
    }
}

# === settings ===============================================================

function Write-JsonFile {
    param([string]$Path, [object]$Object)
    $json = $Object | ConvertTo-Json -Depth 20
    Set-Content -LiteralPath $Path -Value $json -Encoding UTF8
}

function Get-JsonObjectAsOrderedMap {
    param([object]$Object)
    $map = [ordered]@{}
    if ($Object) {
        foreach ($property in $Object.PSObject.Properties) {
            $map[$property.Name] = $property.Value
        }
    }
    return $map
}

function Convert-SettingValue {
    param([string]$Value)
    if ($null -eq $Value) { return $null }
    $trimmed = $Value.Trim()
    if ($trimmed -eq "") { return "" }
    if ($trimmed -match "^(?i:true|false)$") { return [bool]::Parse($trimmed) }
    if ($trimmed -match "^-?\d+$") { return [int]$trimmed }
    if ($trimmed -match "^-?\d+\.\d+$") { return [double]$trimmed }
    if (($trimmed.StartsWith("{") -and $trimmed.EndsWith("}")) -or ($trimmed.StartsWith("[") -and $trimmed.EndsWith("]"))) {
        return ($trimmed | ConvertFrom-Json)
    }
    return $Value
}

function Get-SettingsTargetPath {
    if (-not $Scope) { $Scope = "user" }
    switch ($Scope.ToLowerInvariant()) {
        "user" {
            return (Join-Path (Get-ProductUserDataPath) "settings.json")
        }
        "project" {
            if (-not $ProjectPath) { throw "Project settings require --ProjectPath." }
            $resolvedProject = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            return (Join-Path $resolvedProject ".vscode\settings.json")
        }
        default {
            throw "Unknown settings scope '$Scope'. Use user or project."
        }
    }
}

function Read-SettingsMap {
    param([string]$SettingsPath)
    if (-not (Test-Path -LiteralPath $SettingsPath)) {
        return [ordered]@{}
    }
    $raw = Get-Content -LiteralPath $SettingsPath -Encoding UTF8 -Raw
    if ([string]::IsNullOrWhiteSpace($raw)) {
        return [ordered]@{}
    }
    return (Get-JsonObjectAsOrderedMap -Object ($raw | ConvertFrom-Json))
}

function Write-SettingsMap {
    param([string]$SettingsPath, [System.Collections.IDictionary]$Settings)
    $parent = Split-Path -Parent $SettingsPath
    if ($parent) {
        New-Item -ItemType Directory -Path $parent -Force | Out-Null
    }
    Write-JsonFile -Path $SettingsPath -Object $Settings
}

function Set-SettingEntry {
    param(
        [System.Collections.IDictionary]$Settings,
        [string]$Key,
        [object]$Value
    )
    if ([string]::IsNullOrWhiteSpace($Key)) { return }
    if ($null -eq $Value) { return }
    $Settings[$Key] = $Value
}

function Add-EditorSettingsFromParameters {
    param([System.Collections.IDictionary]$Settings)
    Set-SettingEntry -Settings $Settings -Key "editor.fontFamily" -Value $FontFamily
    if ($FontSize) { Set-SettingEntry -Settings $Settings -Key "editor.fontSize" -Value (Convert-SettingValue $FontSize) }
    if ($LineHeight) { Set-SettingEntry -Settings $Settings -Key "editor.lineHeight" -Value (Convert-SettingValue $LineHeight) }
    Set-SettingEntry -Settings $Settings -Key "workbench.colorTheme" -Value $ColorTheme
    Set-SettingEntry -Settings $Settings -Key "workbench.iconTheme" -Value $IconTheme
    Set-SettingEntry -Settings $Settings -Key "workbench.productIconTheme" -Value $ProductIconTheme
    Set-SettingEntry -Settings $Settings -Key "editor.wordWrap" -Value $WordWrap
    if ($TabSize) { Set-SettingEntry -Settings $Settings -Key "editor.tabSize" -Value (Convert-SettingValue $TabSize) }
    if ($FormatOnSave) { Set-SettingEntry -Settings $Settings -Key "editor.formatOnSave" -Value (Convert-SettingValue $FormatOnSave) }
    Set-SettingEntry -Settings $Settings -Key "files.autoSave" -Value $AutoSave
    if ($Minimap) { Set-SettingEntry -Settings $Settings -Key "editor.minimap.enabled" -Value (Convert-SettingValue $Minimap) }
    if ($SettingKey) { Set-SettingEntry -Settings $Settings -Key $SettingKey -Value (Convert-SettingValue $SettingValue) }
}

function Invoke-SettingsArea {
    switch ($Action) {
        "path" {
            $settingsPath = Get-SettingsTargetPath
            [pscustomobject]@{
                Scope = $(if ($Scope) { $Scope } else { "user" })
                Path = $settingsPath
                Exists = (Test-Path -LiteralPath $settingsPath)
            } | Format-List
            return
        }
        "get" {
            $settingsPath = Get-SettingsTargetPath
            $settings = Read-SettingsMap -SettingsPath $settingsPath
            Write-Section "Settings file"
            [pscustomobject]@{ Path = $settingsPath; Exists = (Test-Path -LiteralPath $settingsPath) } | Format-List
            Write-Section "Core editor settings"
            $keys = @(
                "editor.fontFamily",
                "editor.fontSize",
                "editor.lineHeight",
                "editor.fontWeight",
                "workbench.colorTheme",
                "workbench.iconTheme",
                "workbench.productIconTheme",
                "editor.wordWrap",
                "editor.tabSize",
                "editor.formatOnSave",
                "files.autoSave",
                "editor.minimap.enabled"
            )
            $rows = foreach ($key in $keys) {
                [pscustomobject]@{ Key = $key; Value = $settings[$key] }
            }
            $rows | Format-Table -AutoSize
            return
        }
        "set" {
            if (-not $Apply) { throw "settings set is a write operation. Pass --Apply." }
            $settingsPath = Get-SettingsTargetPath
            $settings = Read-SettingsMap -SettingsPath $settingsPath
            Add-EditorSettingsFromParameters -Settings $settings
            Write-SettingsMap -SettingsPath $settingsPath -Settings $settings
            [pscustomobject]@{ Path = $settingsPath; Written = $true } | Format-List
            return
        }
        "smoke" {
            $oldScope = $Scope
            $Scope = "user"
            $settingsPath = Get-SettingsTargetPath
            $parent = Split-Path -Parent $settingsPath
            New-Item -ItemType Directory -Path $parent -Force | Out-Null
            $existed = Test-Path -LiteralPath $settingsPath
            $original = if ($existed) { Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw } else { $null }

            try {
                $settings = Read-SettingsMap -SettingsPath $settingsPath
                $settings["editor.fontFamily"] = "Consolas, 'Courier New', monospace"
                $settings["editor.fontSize"] = 15
                $settings["editor.lineHeight"] = 22
                $settings["workbench.colorTheme"] = "Default Dark Modern"
                $settings["editor.wordWrap"] = "on"
                $settings["editor.tabSize"] = 2
                $settings["editor.formatOnSave"] = $false
                $settings["files.autoSave"] = "off"
                $settings["editor.minimap.enabled"] = $false
                Write-SettingsMap -SettingsPath $settingsPath -Settings $settings

                $verify = Read-SettingsMap -SettingsPath $settingsPath
                $ok = (
                    $verify["editor.fontFamily"] -eq "Consolas, 'Courier New', monospace" -and
                    [int]$verify["editor.fontSize"] -eq 15 -and
                    [int]$verify["editor.lineHeight"] -eq 22 -and
                    $verify["workbench.colorTheme"] -eq "Default Dark Modern" -and
                    $verify["editor.wordWrap"] -eq "on" -and
                    [int]$verify["editor.tabSize"] -eq 2 -and
                    [bool]$verify["editor.formatOnSave"] -eq $false -and
                    $verify["files.autoSave"] -eq "off" -and
                    [bool]$verify["editor.minimap.enabled"] -eq $false
                )
                if (-not $ok) {
                    throw "Settings smoke verification failed after write."
                }
                [pscustomobject]@{
                    Path = $settingsPath
                    TemporaryWriteVerified = $true
                    Restored = $false
                } | Format-List
            } finally {
                if ($existed) {
                    Set-Content -LiteralPath $settingsPath -Value $original -Encoding UTF8 -NoNewline
                } elseif (Test-Path -LiteralPath $settingsPath) {
                    Remove-Item -LiteralPath $settingsPath -Force
                }
                $Scope = $oldScope
            }

            $restored = if ($existed) {
                (Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw) -eq $original
            } else {
                -not (Test-Path -LiteralPath $settingsPath)
            }
            [pscustomobject]@{
                Path = $settingsPath
                RestoredOriginal = $restored
            } | Format-List
            if (-not $restored) {
                throw "Settings smoke failed to restore original settings.json."
            }
            return
        }
        default {
            throw "Unknown settings action '$Action'. Use path, get, set, or smoke."
        }
    }
}

# === python =================================================================

function Get-PythonExeForVenv {
    param([string]$ProjectPath, [string]$VenvName)
    $candidate = Join-Path $ProjectPath "$VenvName\Scripts\python.exe"
    if (-not (Test-Path -LiteralPath $candidate)) {
        throw "Python interpreter not found: $candidate"
    }
    return (Resolve-Path -LiteralPath $candidate).Path
}

function Invoke-PythonArea {
    if (-not $ProjectPath) { throw "python action requires --ProjectPath." }
    $ProjectPath = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)

    switch ($Action) {
        "make-venvs" {
            New-Item -ItemType Directory -Path $ProjectPath -Force | Out-Null
            New-Item -ItemType Directory -Path (Join-Path $ProjectPath ".vscode") -Force | Out-Null

            $probe = @'
import json
import os
import sys

print(json.dumps({
    "executable": sys.executable,
    "prefix": sys.prefix,
    "cwd": os.getcwd()
}, ensure_ascii=False))
'@
            Set-Content -LiteralPath (Join-Path $ProjectPath "probe.py") -Value $probe -Encoding UTF8

            foreach ($name in @(".venv-a", ".venv-b")) {
                $venvPath = Join-Path $ProjectPath $name
                if (-not (Test-Path -LiteralPath (Join-Path $venvPath "Scripts\python.exe"))) {
                    python -m venv $venvPath
                }
            }

            [pscustomobject]@{
                ProjectPath = $ProjectPath
                VenvA = (Get-PythonExeForVenv -ProjectPath $ProjectPath -VenvName ".venv-a")
                VenvB = (Get-PythonExeForVenv -ProjectPath $ProjectPath -VenvName ".venv-b")
                Probe = (Join-Path $ProjectPath "probe.py")
            } | Format-List
            return
        }
        "set-interpreter" {
            if (-not $VenvName) { throw "python set-interpreter requires --VenvName." }
            $pythonExe = Get-PythonExeForVenv -ProjectPath $ProjectPath -VenvName $VenvName
            $settingsPath = Join-Path $ProjectPath ".vscode\settings.json"
            New-Item -ItemType Directory -Path (Split-Path -Parent $settingsPath) -Force | Out-Null

            $settings = [ordered]@{}
            if (Test-Path -LiteralPath $settingsPath) {
                $raw = Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw
                if (-not [string]::IsNullOrWhiteSpace($raw)) {
                    $existing = $raw | ConvertFrom-Json
                    foreach ($property in $existing.PSObject.Properties) {
                        $settings[$property.Name] = $property.Value
                    }
                }
            }
            $settings["python.defaultInterpreterPath"] = $pythonExe
            Write-JsonFile -Path $settingsPath -Object $settings
            [pscustomobject]@{ Settings = $settingsPath; Interpreter = $pythonExe } | Format-List
            return
        }
        "verify" {
            if (-not $ExpectedVenvName) { throw "python verify requires --ExpectedVenvName." }
            $expected = Get-PythonExeForVenv -ProjectPath $ProjectPath -VenvName $ExpectedVenvName
            $settingsPath = Join-Path $ProjectPath ".vscode\settings.json"
            $probePath = Join-Path $ProjectPath "probe.py"
            if (-not (Test-Path -LiteralPath $settingsPath)) { throw "Missing settings.json at $settingsPath." }
            if (-not (Test-Path -LiteralPath $probePath)) { throw "Missing probe.py at $probePath." }

            $settings = Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw | ConvertFrom-Json
            $configured = $settings."python.defaultInterpreterPath"
            if ($configured -ne $expected) {
                throw "Configured interpreter '$configured' does not match expected '$expected'."
            }

            Push-Location $ProjectPath
            try {
                $output = & $configured $probePath
            } finally {
                Pop-Location
            }

            if ($output -notmatch [regex]::Escape($ExpectedVenvName)) {
                throw "Probe output does not contain expected venv '$ExpectedVenvName': $output"
            }

            [pscustomobject]@{
                ProjectPath = $ProjectPath
                ExpectedVenv = $ExpectedVenvName
                Interpreter = $configured
                ProbeOutput = $output
            } | Format-List
            return
        }
        default {
            throw "Unknown python action '$Action'. Use make-venvs, set-interpreter, or verify."
        }
    }
}

# === ssh ====================================================================

function ConvertTo-SshRemoteUri {
    param([string]$HostAlias, [string]$RemotePath)
    if (-not $HostAlias) { throw "SSH URI requires --HostName." }
    if (-not $RemotePath) { $RemotePath = "~" }
    if ($RemotePath -eq "~") {
        return "vscode-remote://ssh-remote+$HostAlias~"
    }
    if (-not $RemotePath.StartsWith("/")) {
        throw "LinuxPath for SSH must be '~' or an absolute remote path such as /home/user/project."
    }
    return "vscode-remote://ssh-remote+$HostAlias$RemotePath"
}

function Invoke-SshArea {
    if (-not $HostName) {
        $sshDefaults = Get-ConfigSshDefaults
        if ($sshDefaults -and $sshDefaults.PSObject.Properties.Match('defaultHost').Count -and $sshDefaults.defaultHost) {
            $HostName = [string]$sshDefaults.defaultHost
        } else {
            $HostName = "localhost"
        }
    }

    switch ($Action) {
        "open" {
            $uri = ConvertTo-SshRemoteUri -HostAlias $HostName -RemotePath $LinuxPath
            Write-Section "Open $(Get-ProductLabel) SSH remote"
            [pscustomobject]@{ Uri = $uri } | Format-List
            Invoke-ProductCli --folder-uri $uri
            if ($script:LastProductExitCode -ne 0) {
                throw "$(Get-ProductLabel) SSH open failed with exit code $script:LastProductExitCode."
            }
            return
        }
        "smoke" {
            Write-Section "ssh -V"
            ssh -V

            Write-Section "ssh -G $HostName"
            ssh -G $HostName | Select-Object -First 60

            Write-Section "Test-NetConnection"
            $port = 22
            $g = ssh -G $HostName 2>$null
            foreach ($line in $g) {
                if ($line -match "^port\s+(\d+)") {
                    $port = [int]$Matches[1]
                    break
                }
            }
            if (Get-Command Test-NetConnection -ErrorAction SilentlyContinue) {
                Test-NetConnection $HostName -Port $port |
                    Select-Object ComputerName, RemoteAddress, RemotePort, TcpTestSucceeded |
                    Format-List
            } else {
                Write-Host "(Test-NetConnection unavailable on this platform; skipping port probe.)"
            }

            if ($Command) {
                Write-Section "ssh command"
                ssh $HostName $Command
            }
            return
        }
        default {
            throw "Unknown ssh action '$Action'. Use open or smoke."
        }
    }
}

# === wsl ====================================================================

function ConvertTo-WslRemoteUri {
    param([string]$DistroName, [string]$RemotePath)
    if (-not $DistroName) { throw "WSL URI requires --Distro." }
    if (-not $RemotePath) { throw "WSL URI requires --LinuxPath." }
    if (-not $RemotePath.StartsWith("/")) {
        throw "LinuxPath must be an absolute Linux path such as /home/user/project."
    }
    return "vscode-remote://wsl+$DistroName$RemotePath"
}

function Invoke-WslCommand {
    param(
        [Parameter(Mandatory = $true)][string]$DistroName,
        [Parameter(Mandatory = $true)][string]$Script
    )
    $encoded = [Convert]::ToBase64String([System.Text.Encoding]::UTF8.GetBytes($Script))
    wsl -d $DistroName -- bash -lc "printf '%s' '$encoded' | base64 -d | bash" 2>&1 |
        ForEach-Object { $_ -replace "`0", "" }
    $script:LastWslExitCode = $LASTEXITCODE
}

function Show-WslList {
    wsl -l -v | ForEach-Object { $_ -replace "`0", "" }
}

function Invoke-WslArea {
    switch ($Action) {
        "list" {
            Write-Section "wsl -l -v"
            Show-WslList
            return
        }
        "open" {
            if (-not $Distro) {
                $wslDefaults = Get-ConfigWslDefaults
                if ($wslDefaults -and $wslDefaults.PSObject.Properties.Match('defaultDistro').Count -and $wslDefaults.defaultDistro) {
                    $Distro = [string]$wslDefaults.defaultDistro
                }
            }
            $uri = ConvertTo-WslRemoteUri -DistroName $Distro -RemotePath $LinuxPath
            Write-Section "Open $(Get-ProductLabel) WSL remote"
            [pscustomobject]@{ Uri = $uri } | Format-List
            Invoke-ProductCli --folder-uri $uri
            if ($script:LastProductExitCode -ne 0) {
                throw "$(Get-ProductLabel) WSL open failed with exit code $script:LastProductExitCode."
            }
            return
        }
        "smoke" {
            if (-not $Distro) { throw "wsl smoke requires --Distro." }
            if (-not $LinuxPath) { $LinuxPath = "~" }

            Write-Section "WSL distro"
            Show-WslList

            Write-Section "WSL command smoke"
            $quotedPath = $LinuxPath.Replace("'", "'\''")
            $scriptTemplate = @'
set -e
echo "distro=$WSL_DISTRO_NAME"
echo "user=$(whoami)"
echo "pwd=$(pwd)"
if [ -d '__WSL_PATH__' ]; then
  echo "project_exists=true"
  cd '__WSL_PATH__'
  echo "project_pwd=$(pwd)"
else
  echo "project_exists=false"
fi
if command -v python3 >/dev/null 2>&1; then
  echo "python3=$(command -v python3)"
else
  echo "python3=missing"
fi
'@
            $script = $scriptTemplate.Replace("__WSL_PATH__", $quotedPath)
            Invoke-WslCommand -DistroName $Distro -Script $script
            if ($script:LastWslExitCode -ne 0) {
                throw "WSL smoke failed for distro $Distro."
            }
            return
        }
        default {
            throw "Unknown wsl action '$Action'. Use list, open, or smoke."
        }
    }
}

# === tasks / launch / extensions =============================================

function Get-SkillRoot {
    return (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
}

function Get-TemplateDir {
    param([Parameter(Mandatory = $true)][string]$Kind)
    return (Join-Path (Get-SkillRoot) "references/templates/$Kind")
}

function Get-AvailableTemplates {
    param([Parameter(Mandatory = $true)][string]$Kind)
    $dir = Get-TemplateDir -Kind $Kind
    if (-not (Test-Path -LiteralPath $dir)) { return @() }
    return @(Get-ChildItem -LiteralPath $dir -Filter "*.json" | ForEach-Object { $_.BaseName } | Sort-Object)
}

function Get-ExtensionPacks {
    $packs = [ordered]@{}
    $file = Join-Path (Get-SkillRoot) "references/extension-packs.md"
    if (-not (Test-Path -LiteralPath $file)) { return $packs }

    $currentStack = $null
    $lines = Get-Content -LiteralPath $file -Encoding UTF8
    foreach ($line in $lines) {
        $headerMatch = [regex]::Match($line, '^### `([a-z0-9-]+)`')
        if ($headerMatch.Success) {
            $currentStack = $headerMatch.Groups[1].Value
            $packs[$currentStack] = [System.Collections.Generic.List[object]]::new()
            continue
        }
        if ($null -eq $currentStack) { continue }
        if (-not $line.StartsWith("|")) { continue }
        $stripped = $line.Trim().Trim('|')
        $rawCells = $stripped.Split('|')
        $cells = @()
        foreach ($c in $rawCells) { $cells += ,$c.Trim().Trim('`') }
        if ($cells.Count -lt 2) { continue }
        $first = $cells[0]
        if ($first -eq "ID" -or $first -eq "---") { continue }
        if ($first -match '^[a-zA-Z0-9_-]+\.[a-zA-Z0-9_.-]+$') {
            $packs[$currentStack].Add([pscustomobject]@{ id = $first; purpose = $cells[1] })
        }
    }
    return $packs
}

function Invoke-TasksArea {
    switch ($Action) {
        "list" {
            [pscustomobject]@{ templates = (Get-AvailableTemplates -Kind "tasks") } | ConvertTo-Json
            return
        }
        "init" {
            if (-not $Template) { throw "tasks init requires --Template." }
            if (-not $ProjectPath) { throw "tasks init requires --ProjectPath." }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $sourcePath = Join-Path (Get-TemplateDir -Kind "tasks") "$Template.json"
            if (-not (Test-Path -LiteralPath $sourcePath)) {
                throw "Template '$Template' not found. Available: $((Get-AvailableTemplates -Kind 'tasks') -join ', ')"
            }
            $targetDir = Join-Path $resolved ".vscode"
            $target = Join-Path $targetDir "tasks.json"
            if ((Test-Path -LiteralPath $target) -and -not $Force) {
                throw "$target already exists. Pass --Force to overwrite."
            }
            New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
            Copy-Item -LiteralPath $sourcePath -Destination $target -Force
            [pscustomobject]@{ Path = $target; Template = $Template; Written = $true } | ConvertTo-Json
            return
        }
        default { throw "Unknown tasks action '$Action'. Use list or init." }
    }
}

function Invoke-LaunchArea {
    switch ($Action) {
        "list" {
            [pscustomobject]@{ templates = (Get-AvailableTemplates -Kind "launch") } | ConvertTo-Json
            return
        }
        "init" {
            if (-not $Template) { throw "launch init requires --Template." }
            if (-not $ProjectPath) { throw "launch init requires --ProjectPath." }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $sourcePath = Join-Path (Get-TemplateDir -Kind "launch") "$Template.json"
            if (-not (Test-Path -LiteralPath $sourcePath)) {
                throw "Template '$Template' not found. Available: $((Get-AvailableTemplates -Kind 'launch') -join ', ')"
            }
            $targetDir = Join-Path $resolved ".vscode"
            $target = Join-Path $targetDir "launch.json"
            if ((Test-Path -LiteralPath $target) -and -not $Force) {
                throw "$target already exists. Pass --Force to overwrite."
            }
            New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
            Copy-Item -LiteralPath $sourcePath -Destination $target -Force
            [pscustomobject]@{ Path = $target; Template = $Template; Written = $true } | ConvertTo-Json
            return
        }
        default { throw "Unknown launch action '$Action'. Use list or init." }
    }
}

function Invoke-ExtensionsArea {
    switch ($Action) {
        "stacks" {
            $packs = Get-ExtensionPacks
            [pscustomobject]@{ stacks = @($packs.Keys | Sort-Object) } | ConvertTo-Json
            return
        }
        "recommend" {
            if (-not $Stack) { throw "extensions recommend requires --Stack." }
            $packs = Get-ExtensionPacks
            if (-not $packs.Contains($Stack)) {
                throw "Unknown stack '$Stack'. Available: $((@($packs.Keys) | Sort-Object) -join ', ')"
            }
            [pscustomobject]@{ stack = $Stack; extensions = $packs[$Stack] } | ConvertTo-Json -Depth 5
            return
        }
        "install" {
            if (-not $Stack) { throw "extensions install requires --Stack." }
            $packs = Get-ExtensionPacks
            if (-not $packs.Contains($Stack)) {
                throw "Unknown stack '$Stack'. Available: $((@($packs.Keys) | Sort-Object) -join ', ')"
            }
            $cli = Resolve-ProductCli
            $failures = @()
            foreach ($entry in $packs[$Stack]) {
                Write-Host "installing $($entry.id)..." -ForegroundColor DarkGray
                & $cli --install-extension $entry.id
                if ($LASTEXITCODE -ne 0) { $failures += $entry }
            }
            [pscustomobject]@{
                stack     = $Stack
                total     = $packs[$Stack].Count
                failures  = $failures
            } | ConvertTo-Json -Depth 5
            if ($failures.Count -gt 0) { exit 1 }
            return
        }
        "pin" {
            if (-not $Stack) { throw "extensions pin requires --Stack." }
            if (-not $ProjectPath) { throw "extensions pin requires --ProjectPath." }
            $packs = Get-ExtensionPacks
            if (-not $packs.Contains($Stack)) {
                throw "Unknown stack '$Stack'. Available: $((@($packs.Keys) | Sort-Object) -join ', ')"
            }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $targetDir = Join-Path $resolved ".vscode"
            $target = Join-Path $targetDir "extensions.json"
            $existing = [ordered]@{}
            if (Test-Path -LiteralPath $target) {
                $raw = Get-Content -LiteralPath $target -Encoding UTF8 -Raw
                if (-not [string]::IsNullOrWhiteSpace($raw)) {
                    try { $existing = Get-JsonObjectAsOrderedMap -Object ($raw | ConvertFrom-Json) } catch { $existing = [ordered]@{} }
                }
            }
            $recs = @()
            if ($existing.Contains("recommendations")) {
                $recs = @($existing["recommendations"])
            }
            foreach ($entry in $packs[$Stack]) {
                if ($entry.id -notin $recs) { $recs += $entry.id }
            }
            $existing["recommendations"] = $recs
            New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
            Write-JsonFile -Path $target -Object $existing
            [pscustomobject]@{ Path = $target; Stack = $Stack; Recommendations = $recs } | ConvertTo-Json -Depth 5
            return
        }
        default { throw "Unknown extensions action '$Action'. Use stacks, recommend, install, or pin." }
    }
}

function Invoke-SettingsSyncArea {
    switch ($Action) {
        "status" {
            $paths = @()
            $candidates = @(
                (Join-Path (Get-ProductUserDataPath) "sync"),
                (Join-Path (Join-Path $env:APPDATA "Code - Insiders\User") "sync")
            )
            foreach ($p in $candidates) {
                if (Test-Path -LiteralPath $p) { $paths += $p }
            }
            [pscustomobject]@{
                syncStorageFound = ($paths.Count -gt 0)
                locations        = $paths
                note             = "Settings sync is controlled via the VS Code UI (Accounts -> Backup and Sync Settings). The skill does not enable or disable sync programmatically to avoid accidental data leaks."
            } | ConvertTo-Json
            return
        }
        default { throw "Unknown settings-sync action '$Action'. Use status." }
    }
}

function Invoke-WorkspaceArea {
    switch ($Action) {
        "info" {
            if (-not $ProjectPath) { throw "workspace info requires --ProjectPath." }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $wsFile = Get-ChildItem -LiteralPath $resolved -Filter "*.code-workspace" -ErrorAction SilentlyContinue | Select-Object -First 1
            if (-not $wsFile) {
                [pscustomobject]@{
                    ProjectPath  = $resolved
                    IsMultiRoot  = $false
                    note         = "No .code-workspace file found. This is a single-root workspace; use 'settings set --Scope project'."
                } | ConvertTo-Json
                return
            }
            $data = Get-Content -LiteralPath $wsFile.FullName -Encoding UTF8 -Raw | ConvertFrom-Json
            $folders = @($data.folders)
            [pscustomobject]@{
                ProjectPath    = $resolved
                IsMultiRoot    = ($folders.Count -gt 1)
                WorkspaceFile  = $wsFile.FullName
                Folders        = @($folders | ForEach-Object { $_.path })
                FolderSettings = @($folders | Where-Object { $_.settings } | ForEach-Object {
                    [pscustomobject]@{ path = $_.path; settings = $_.settings }
                })
            } | ConvertTo-Json -Depth 10
            return
        }
        "folder-settings-get" {
            if (-not $ProjectPath -or -not $Folder) { throw "workspace folder-settings-get requires --ProjectPath and --Folder." }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $wsFile = Get-ChildItem -LiteralPath $resolved -Filter "*.code-workspace" -ErrorAction SilentlyContinue | Select-Object -First 1
            if (-not $wsFile) { throw "Not a multi-root workspace (no .code-workspace file)." }
            $data = Get-Content -LiteralPath $wsFile.FullName -Encoding UTF8 -Raw | ConvertFrom-Json
            $entry = @($data.folders) | Where-Object { $_.path -eq $Folder } | Select-Object -First 1
            if (-not $entry) { throw "Folder '$Folder' not found in workspace file." }
            $folderSettings = if ($entry.settings) { $entry.settings } else { @{} }
            if ($SettingKey) {
                [pscustomobject]@{ key = $SettingKey; value = $folderSettings.$SettingKey } | ConvertTo-Json
            } else {
                [pscustomobject]@{ folder = $Folder; settings = $folderSettings } | ConvertTo-Json
            }
            return
        }
        "folder-settings-set" {
            if (-not $ProjectPath -or -not $Folder -or -not $SettingKey) {
                throw "workspace folder-settings-set requires --ProjectPath, --Folder, --SettingKey."
            }
            if (-not $Apply) { throw "workspace folder-settings-set is a write operation. Pass --Apply." }
            $resolved = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($ProjectPath)
            $wsFile = Get-ChildItem -LiteralPath $resolved -Filter "*.code-workspace" -ErrorAction SilentlyContinue | Select-Object -First 1
            if (-not $wsFile) { throw "Not a multi-root workspace (no .code-workspace file)." }
            $data = Get-Content -LiteralPath $wsFile.FullName -Encoding UTF8 -Raw | ConvertFrom-Json
            $found = $false
            foreach ($f in @($data.folders)) {
                if ($f.path -eq $Folder) {
                    if (-not $f.settings) {
                        $f | Add-Member -NotePropertyName "settings" -NotePropertyValue ([ordered]@{}) -Force
                    }
                    $coerced = Convert-SettingValue $SettingValue
                    $f.settings.$SettingKey = $coerced
                    $found = $true
                    break
                }
            }
            if (-not $found) { throw "Folder '$Folder' not found in workspace file." }
            $data | ConvertTo-Json -Depth 20 | Set-Content -LiteralPath $wsFile.FullName -Encoding UTF8
            [pscustomobject]@{
                WorkspaceFile = $wsFile.FullName
                Folder        = $Folder
                Key           = $SettingKey
                Value         = $coerced
            } | ConvertTo-Json
            return
        }
        default { throw "Unknown workspace action '$Action'. Use info, folder-settings-get, or folder-settings-set." }
    }
}

function Invoke-ProfileArea {
    switch ($Action) {
        "list" {
            $profilesDir = Join-Path (Get-ProductUserDataPath) "profiles"
            if (-not (Test-Path -LiteralPath $profilesDir)) {
                [pscustomobject]@{ profiles = @(); note = "No profiles directory found; no profiles defined." } | ConvertTo-Json
                return
            }
            $entries = @()
            foreach ($child in (Get-ChildItem -LiteralPath $profilesDir -Directory | Sort-Object Name)) {
                $entry = [ordered]@{
                    name               = $child.Name
                    settingsFileExists = (Test-Path -LiteralPath (Join-Path $child.FullName "settings.json"))
                }
                $settingsPath = Join-Path $child.FullName "settings.json"
                if (Test-Path -LiteralPath $settingsPath) {
                    try {
                        $settings = Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw | ConvertFrom-Json
                        $entry["settingCount"] = @($settings.PSObject.Properties).Count
                        $entry["sampleKeys"] = @($settings.PSObject.Properties | Select-Object -First 5 -ExpandProperty Name)
                    } catch {
                        $entry["parseError"] = "settings.json is not valid JSON"
                    }
                }
                $entries += [pscustomobject]$entry
            }
            [pscustomobject]@{ profilesDir = $profilesDir; profiles = $entries } | ConvertTo-Json
            return
        }
        "show" {
            if (-not $Profile) { throw "profile show requires --Profile." }
            $profilesDir = Join-Path (Get-ProductUserDataPath) "profiles"
            $settingsPath = Join-Path (Join-Path $profilesDir $Profile) "settings.json"
            if (-not (Test-Path -LiteralPath $settingsPath)) {
                throw "Profile '$Profile' not found or has no settings.json."
            }
            $settings = Get-Content -LiteralPath $settingsPath -Encoding UTF8 -Raw | ConvertFrom-Json
            [pscustomobject]@{
                profile      = $Profile
                settingsFile = $settingsPath
                settings     = $settings
            } | ConvertTo-Json -Depth 10
            return
        }
        default { throw "Unknown profile action '$Action'. Use list or show." }
    }
}

# === dispatch ===============================================================

switch ($Area) {
    "info"         { Invoke-Info }
    "ext"          { Invoke-Ext }
    "python"       { Invoke-PythonArea }
    "ssh"          { Invoke-SshArea }
    "wsl"          { Invoke-WslArea }
    "settings"     { Invoke-SettingsArea }
    "tasks"        { Invoke-TasksArea }
    "launch"       { Invoke-LaunchArea }
    "extensions"   { Invoke-ExtensionsArea }
    "settings-sync" { Invoke-SettingsSyncArea }
    "workspace"    { Invoke-WorkspaceArea }
    "profile"      { Invoke-ProfileArea }
    default        { throw "Unknown area '$Area'. Use info, ext, python, ssh, wsl, settings, tasks, launch, extensions, settings-sync, workspace, or profile." }
}
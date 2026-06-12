#requires -Version 7
<#
.SYNOPSIS
PII scrub and audit for files about to be shared externally.

.DESCRIPTION
Applies user-provided context-token substitutions plus a baseline library of
PII regex patterns from patterns.json. Audits the result; exits non-zero if any
pattern still matches after substitution.

The skill that owns this script lives at ~/.claude/skills/pii-scrub/.
See SKILL.md in the same directory for the full procedure and gotchas.

.PARAMETER Files
Absolute paths to the files to scrub. Pass an array.

.PARAMETER Substitutions
Hashtable of literal-string -> replacement-string. Matched case-insensitively
as literals (regex-escaped). Applied BEFORE baseline patterns.

For tokens that risk substring matches in legitimate words (e.g., a 6-letter
employer name that appears inside common English words), prefer adding them
to -SubstitutionsRegex instead with explicit \b word boundaries.

.PARAMETER SubstitutionsRegex
Hashtable of regex-pattern -> replacement-string. Use when you need word
boundaries, case sensitivity, or other regex features.

.PARAMETER PatternsPath
Path to patterns.json. Defaults to the file next to this script.

.PARAMETER AuditOnly
Skip substitution. Only run the audit pass and report what matches. Useful
for surveying a file before deciding what to redact.

.PARAMETER ExtraAuditPatterns
Additional regex patterns to audit for (won't be substituted, just reported).
Pass an array of hashtables: @(@{name='foo';pattern='bar'}, ...).

.EXAMPLE
& "$env:USERPROFILE\.claude\skills\pii-scrub\scrub.ps1" `
    -Files @('C:\out\report.txt','C:\out\log.json') `
    -Substitutions @{ 'alice'='<user>'; 'lab-host'='<hostname>' }

.EXAMPLE
$files = (Get-ChildItem 'C:\artifacts' -File -Recurse).FullName
& "$env:USERPROFILE\.claude\skills\pii-scrub\scrub.ps1" -Files $files -AuditOnly

.EXAMPLE
# Word-bounded substitution (avoids a short token matching inside a longer word)
& "$env:USERPROFILE\.claude\skills\pii-scrub\scrub.ps1" `
    -Files $files `
    -SubstitutionsRegex @{ '\bshorttoken\b' = '<redacted>' }
#>

[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string[]]$Files,

    [hashtable]$Substitutions = @{},

    [hashtable]$SubstitutionsRegex = @{},

    [string]$PatternsPath,

    [switch]$AuditOnly,

    [hashtable[]]$ExtraAuditPatterns = @()
)

$ErrorActionPreference = 'Stop'

if (-not $PatternsPath) {
    $PatternsPath = Join-Path $PSScriptRoot 'patterns.json'
}
if (-not (Test-Path -LiteralPath $PatternsPath)) {
    throw "patterns.json not found at: $PatternsPath"
}

$patternsConfig = Get-Content -LiteralPath $PatternsPath -Raw | ConvertFrom-Json
$baselinePatterns = $patternsConfig.baseline
$auditOnlyPatterns = if ($patternsConfig.PSObject.Properties.Name -contains 'audit_only') {
    $patternsConfig.audit_only
} else { @() }

function Test-FileTextual {
    param([string]$Path)
    # Heuristic: if first 8KB has > 1% null bytes, treat as binary.
    if (-not (Test-Path -LiteralPath $Path)) { return $false }
    $size = (Get-Item -LiteralPath $Path).Length
    if ($size -eq 0) { return $false }
    $sample = [System.IO.File]::ReadAllBytes($Path) | Select-Object -First ([Math]::Min($size, 8192))
    if ($sample.Count -eq 0) { return $false }
    $nullCount = ($sample | Where-Object { $_ -eq 0 }).Count
    return ($nullCount / $sample.Count) -lt 0.01
}

function Invoke-Substitution {
    param([string]$Content, [hashtable]$Subs, [hashtable]$RegexSubs)
    foreach ($key in $Subs.Keys) {
        if ([string]::IsNullOrEmpty($key)) {
            Write-Warning "skipping empty key in -Substitutions"
            continue
        }
        $regex = '(?i)' + [regex]::Escape($key)
        $Content = $Content -replace $regex, $Subs[$key]
    }
    foreach ($key in $RegexSubs.Keys) {
        if ([string]::IsNullOrEmpty($key)) {
            Write-Warning "skipping empty key in -SubstitutionsRegex"
            continue
        }
        $Content = $Content -replace $key, $RegexSubs[$key]
    }
    return $Content
}

function Invoke-Audit {
    param(
        [string]$Path,
        [object[]]$Patterns,
        [hashtable]$ContextSubs,
        [hashtable]$ContextRegexSubs,
        [hashtable[]]$Extra
    )
    $hits = @()
    if (-not (Test-FileTextual -Path $Path)) { return $hits }
    $c = Get-Content -LiteralPath $Path -Raw -ErrorAction SilentlyContinue
    if (-not $c) { return $hits }

    foreach ($p in $Patterns) {
        $m = [regex]::Matches($c, $p.pattern)
        if ($m.Count -gt 0) {
            $hits += [PSCustomObject]@{
                File = $Path
                Pattern = $p.name
                Count = $m.Count
                Sample = $m[0].Value
            }
        }
    }
    foreach ($key in $ContextSubs.Keys) {
        if ([string]::IsNullOrEmpty($key)) { continue }
        $m = [regex]::Matches($c, '(?i)' + [regex]::Escape($key))
        if ($m.Count -gt 0) {
            $hits += [PSCustomObject]@{
                File = $Path
                Pattern = "context-literal: $key"
                Count = $m.Count
                Sample = $m[0].Value
            }
        }
    }
    foreach ($key in $ContextRegexSubs.Keys) {
        if ([string]::IsNullOrEmpty($key)) { continue }
        $m = [regex]::Matches($c, $key)
        if ($m.Count -gt 0) {
            $hits += [PSCustomObject]@{
                File = $Path
                Pattern = "context-regex: $key"
                Count = $m.Count
                Sample = $m[0].Value
            }
        }
    }
    foreach ($p in $Extra) {
        $m = [regex]::Matches($c, $p.pattern)
        if ($m.Count -gt 0) {
            $hits += [PSCustomObject]@{
                File = $Path
                Pattern = "extra: $($p.name)"
                Count = $m.Count
                Sample = $m[0].Value
            }
        }
    }
    return $hits
}

# === Substitution pass ===
if (-not $AuditOnly) {
    foreach ($f in $Files) {
        if (-not (Test-Path -LiteralPath $f)) {
            Write-Warning "skipping (not found): $f"
            continue
        }
        if ((Get-Item -LiteralPath $f).Length -eq 0) {
            Write-Warning "skipping (empty): $f"
            continue
        }
        if (-not (Test-FileTextual -Path $f)) {
            Write-Warning "skipping (binary): $f"
            continue
        }
        $orig = Get-Content -LiteralPath $f -Raw
        if (-not $orig) { continue }

        $new = Invoke-Substitution -Content $orig -Subs $Substitutions -RegexSubs $SubstitutionsRegex
        foreach ($p in $baselinePatterns) {
            $new = $new -replace $p.pattern, $p.replacement
        }

        if ($new -ne $orig) {
            Set-Content -LiteralPath $f -Value $new -Encoding utf8 -NoNewline
            Write-Host "scrubbed: $f"
        } else {
            Write-Host "unchanged: $f"
        }
    }
}

# === Audit pass ===
Write-Host ""
Write-Host "=== Audit pass ==="
$allHits = @()
$skipped = @()  # files we couldn't audit (binary / missing / etc.)
$auditPatterns = @($baselinePatterns) + @($auditOnlyPatterns)
foreach ($f in $Files) {
    if (-not (Test-Path -LiteralPath $f)) {
        $skipped += [PSCustomObject]@{ File = $f; Reason = 'not found' }
        continue
    }
    if ((Get-Item -LiteralPath $f).Length -eq 0) {
        $skipped += [PSCustomObject]@{ File = $f; Reason = 'empty file' }
        continue
    }
    if (-not (Test-FileTextual -Path $f)) {
        # Common case on Windows: PowerShell's default Out-File / > / Export-*
        # cmdlets emit UTF-16 LE, which Test-FileTextual classifies as binary.
        # Captured PS session logs land here.
        $skipped += [PSCustomObject]@{ File = $f; Reason = 'binary or non-UTF-8 (UTF-16 / encoded)' }
        continue
    }
    $hits = Invoke-Audit -Path $f -Patterns $auditPatterns -ContextSubs $Substitutions -ContextRegexSubs $SubstitutionsRegex -Extra $ExtraAuditPatterns
    $allHits += $hits
}

$auditedCount = $Files.Count - $skipped.Count
if ($allHits.Count -eq 0 -and $skipped.Count -eq 0) {
    $patternCount = $baselinePatterns.Count + $auditOnlyPatterns.Count + $Substitutions.Count + $SubstitutionsRegex.Count + $ExtraAuditPatterns.Count
    Write-Host "VERDICT: CLEAN. Zero hits across $patternCount patterns in $($Files.Count) file(s)."
} elseif ($allHits.Count -eq 0 -and $skipped.Count -gt 0) {
    Write-Host "VERDICT: AUDITED $auditedCount of $($Files.Count) files; $($skipped.Count) skipped (could not safely scan as text). Cannot certify CLEAN."
    foreach ($s in $skipped) { Write-Host "  skipped: $($s.File) ($($s.Reason))" }
    Write-Host ""
    Write-Host "If any skipped file may contain PII, either re-encode it as UTF-8 first or scrub it by hand. The audit cannot inspect files it cannot decode as text."
    exit 1
} else {
    Write-Host "VERDICT: $($allHits.Count) hit(s) remaining. Review:"
    $allHits | Format-Table File, Pattern, Count, Sample -AutoSize -Wrap
    if ($skipped.Count -gt 0) {
        Write-Host ""
        Write-Host "ALSO: $($skipped.Count) file(s) skipped (could not safely scan as text):"
        foreach ($s in $skipped) { Write-Host "  skipped: $($s.File) ($($s.Reason))" }
    }
    Write-Host ""
    Write-Host "NOTE: audit_only patterns (e.g., private-key-block, long-base64-blob) are flagged for review, not auto-substituted."
    exit 1
}

# === Manual review prompt ===
$textualFiles = $Files | Where-Object { Test-FileTextual -Path $_ }
if ($textualFiles.Count -gt 0) {
    Write-Host ""
    Write-Host "MANUAL REVIEW recommended for the two largest files:"
    Get-Item $textualFiles | Sort-Object Length -Descending | Select-Object -First 2 | ForEach-Object {
        Write-Host "  - $($_.FullName) ($($_.Length) bytes)"
    }
    Write-Host ""
    Write-Host "Pattern matching catches structured PII. It does NOT catch identifying free-form text."
    Write-Host "Skim these two files before sharing externally."
}

exit 0

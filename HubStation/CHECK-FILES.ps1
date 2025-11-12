# ==============================================================================
# HubStation File Mapping and Syntax Check Script
# Lists all files, checks for key components, and scans for syntax errors
# ==============================================================================

param(
    [string]$BasePath = $PSScriptRoot
)

# If $PSScriptRoot is empty (running in console), use current directory
if (-not $BasePath) {
    $BasePath = Get-Location
    Write-Host "[WARN] Running from console, using current directory: $BasePath" -ForegroundColor Yellow
}

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "HubStation File Checker" -ForegroundColor Cyan
Write-Host "Scanning: $BasePath" -ForegroundColor Cyan
Write-Host "========================================`n" -ForegroundColor Cyan

# ==============================================================================
# List all files and folders
# ==============================================================================

Write-Host "[1/3] Listing all files and folders..." -ForegroundColor Yellow
try {
    $allItems = Get-ChildItem -Path $BasePath -Recurse -ErrorAction Stop | Where-Object { $_.PSIsContainer -eq $false }
    Write-Host "Total files found: $($allItems.Count)" -ForegroundColor Green
    foreach ($item in $allItems) {
        $relativePath = $item.FullName.Replace($BasePath, ".")
        Write-Host "  $relativePath" -ForegroundColor Gray
    }
} catch {
    Write-Host "[ERROR] Failed to list files: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# ==============================================================================
# Check for key files/components
# ==============================================================================

Write-Host "`n[2/3] Checking for required files/components..." -ForegroundColor Yellow

$keyFiles = @(
    "index.html",
    "GeminiService.ps1",
    "OllamaRunner",
    "Reflections.psm1",
    "HubStation.ps1",
    "hub_config.json",
    "shared_bus",
    "START.bat",
    "Start-HubStation.ps1",
    "test-hubstation.ps1",
    "auto-monitor.ps1"
)

$foundCount = 0
$missingCount = 0

foreach ($file in $keyFiles) {
    try {
        $found = Get-ChildItem -Path $BasePath -Recurse -Force -ErrorAction Stop |
                 Where-Object { $_.Name -eq $file }

        if ($found) {
            $relativePath = $found.FullName.Replace($BasePath, ".")
            Write-Host "  [OK] Found: $file at $relativePath" -ForegroundColor Green
            $foundCount++
        } else {
            Write-Host "  [MISS] Missing: $file" -ForegroundColor Red
            $missingCount++
        }
    } catch {
        Write-Host "  [ERROR] Error checking $file : $($_.Exception.Message)" -ForegroundColor Red
        $missingCount++
    }
}

Write-Host "`nSummary: $foundCount found, $missingCount missing" -ForegroundColor $(if ($missingCount -eq 0) { "Green" } else { "Yellow" })

# ==============================================================================
# Scan PowerShell scripts for syntax errors
# ==============================================================================

Write-Host "`n[3/3] Scanning PowerShell scripts for syntax errors..." -ForegroundColor Yellow

try {
    $scriptFiles = Get-ChildItem -Path $BasePath -Recurse -Include *.ps1,*.psm1 -ErrorAction Stop
    Write-Host "Found $($scriptFiles.Count) PowerShell scripts to check`n" -ForegroundColor Cyan

    $okCount = 0
    $errorCount = 0

    foreach ($script in $scriptFiles) {
        $relativePath = $script.FullName.Replace($BasePath, ".")
        Write-Host "Checking: $relativePath" -ForegroundColor Gray

        try {
            # Read file content
            $content = Get-Content -Path $script.FullName -Raw -ErrorAction Stop

            if (-not $content) {
                Write-Host "  [WARN] Empty file" -ForegroundColor Yellow
                continue
            }

            # Use modern parser (not deprecated PSParser)
            $errors = $null
            $tokens = $null
            $ast = [System.Management.Automation.Language.Parser]::ParseInput(
                $content,
                [ref]$tokens,
                [ref]$errors
            )

            if ($errors -and $errors.Count -gt 0) {
                Write-Host "  [FAIL] Syntax Errors Found:" -ForegroundColor Red
                foreach ($err in $errors) {
                    Write-Host "    Line $($err.Extent.StartLineNumber): $($err.Message)" -ForegroundColor Red
                }
                $errorCount++
            } else {
                Write-Host "  [PASS] Syntax OK" -ForegroundColor Green
                $okCount++
            }

        } catch {
            Write-Host "  [ERROR] Error reading/parsing: $($_.Exception.Message)" -ForegroundColor Red
            $errorCount++
        }
    }

    Write-Host "`nSyntax Check Summary: $okCount OK, $errorCount errors" -ForegroundColor $(if ($errorCount -eq 0) { "Green" } else { "Yellow" })

} catch {
    Write-Host "[ERROR] Failed to scan scripts: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# ==============================================================================
# Final Summary
# ==============================================================================

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "File check complete!" -ForegroundColor Cyan
Write-Host "Files: $foundCount/$($keyFiles.Count) found" -ForegroundColor $(if ($missingCount -eq 0) { "Green" } else { "Yellow" })
Write-Host "Scripts: $okCount/$($scriptFiles.Count) valid" -ForegroundColor $(if ($errorCount -eq 0) { "Green" } else { "Yellow" })
Write-Host "========================================`n" -ForegroundColor Cyan

if ($missingCount -gt 0 -or $errorCount -gt 0) {
    exit 1
}

exit 0

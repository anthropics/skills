# ==============================================================================
# HubStation Test Script - Diagnose what's working and what's not
# Run this while HubStation is running
# ==============================================================================

param([switch]$NoSound)

function Speak {
    param([string]$Message)
    Write-Host $Message -ForegroundColor Cyan
    if (-not $NoSound) {
        try {
            Add-Type -AssemblyName System.Speech
            $synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
            $synth.Rate = 1
            $synth.Speak($Message)
            $synth.Dispose()
        } catch {}
    }
}

function Test-Endpoint {
    param(
        [string]$Name,
        [string]$Url,
        [string]$Method = "GET",
        [hashtable]$Body = $null
    )

    Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Yellow
    Write-Host "Testing: $Name" -ForegroundColor Yellow
    Write-Host "URL: $Url" -ForegroundColor Gray
    Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Yellow

    try {
        if ($Method -eq "GET") {
            $response = Invoke-RestMethod -Uri $Url -Method Get -TimeoutSec 5 -ErrorAction Stop
        } else {
            $bodyJson = $Body | ConvertTo-Json -Depth 5
            $response = Invoke-RestMethod -Uri $Url -Method Post -Body $bodyJson -ContentType "application/json" -TimeoutSec 5 -ErrorAction Stop
        }

        Write-Host "[SUCCESS]" -ForegroundColor Green
        Write-Host "Response:" -ForegroundColor White
        $response | ConvertTo-Json -Depth 3 | Write-Host

        return @{ success = $true; response = $response }
    } catch {
        Write-Host "[FAILED]" -ForegroundColor Red
        Write-Host "Error: $($_.Exception.Message)" -ForegroundColor Red

        if ($_.Exception.Response) {
            $statusCode = $_.Exception.Response.StatusCode.value__
            Write-Host "Status Code: $statusCode" -ForegroundColor Red
        }

        return @{ success = $false; error = $_.Exception.Message }
    }
}

# ==============================================================================
# Main Test Suite
# ==============================================================================

Clear-Host

Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  HubStation Test Suite" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

Speak "Starting HubStation test suite"

$baseUrl = "http://localhost:9199"
$results = @{}

# ==============================================================================
# Test 1: Basic Status
# ==============================================================================

$results.status = Test-Endpoint -Name "Status Endpoint" -Url "$baseUrl/status"

# ==============================================================================
# Test 2: Reflection - CSV Tail
# ==============================================================================

$results.csvTail = Test-Endpoint -Name "CSV Tail (Reflection System)" -Url "$baseUrl/logs/csv/tail?rows=5"

# ==============================================================================
# Test 3: Reflection - Window
# ==============================================================================

$results.reflectWindow = Test-Endpoint -Name "Reflection Window" -Url "$baseUrl/reflect/window?rows=10"

# ==============================================================================
# Test 4: Reflection - Submit
# ==============================================================================

$reflectionBody = @{
    title = "Test Reflection"
    goal = "Test the reflection submission endpoint"
    summary = "Testing if reflection submission works"
    source_model = "test-script"
    meta_tags = "test,diagnostic"
}

$results.reflectSubmit = Test-Endpoint -Name "Reflection Submit" -Url "$baseUrl/reflect/submit" -Method "POST" -Body $reflectionBody

# ==============================================================================
# Test 5: Static Files (index.html)
# ==============================================================================

Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Yellow
Write-Host "Testing: Static File Serving" -ForegroundColor Yellow
Write-Host "URL: $baseUrl/web" -ForegroundColor Gray
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Yellow

try {
    $webResponse = Invoke-WebRequest -Uri "$baseUrl/web" -TimeoutSec 5 -ErrorAction Stop
    Write-Host "[SUCCESS]" -ForegroundColor Green
    Write-Host "Status: $($webResponse.StatusCode)" -ForegroundColor White
    Write-Host "Content Length: $($webResponse.Content.Length) bytes" -ForegroundColor White
    $results.staticFiles = @{ success = $true }
} catch {
    Write-Host "[FAILED]" -ForegroundColor Red
    Write-Host "Error: $($_.Exception.Message)" -ForegroundColor Red
    $results.staticFiles = @{ success = $false; error = $_.Exception.Message }
}

# ==============================================================================
# Test 6: Gemini Endpoint (will fail if GeminiService not loaded)
# ==============================================================================

$geminiBody = @{
    description = "Test evidence description"
    quote = "Test quote"
    context = "Test context"
}

$results.gemini = Test-Endpoint -Name "Gemini Analyze (Optional)" -Url "$baseUrl/api/gemini/analyze" -Method "POST" -Body $geminiBody

# ==============================================================================
# Test 7: Runner Endpoint (will fail if OllamaRunner not loaded)
# ==============================================================================

$runnerBody = @{
    prompt = "Test prompt"
    context = "Test context"
}

$results.runner = Test-Endpoint -Name "Runner Prompt (Optional)" -Url "$baseUrl/api/runner/prompt" -Method "POST" -Body $runnerBody

# ==============================================================================
# Test 8: Logs
# ==============================================================================

$results.logs = Test-Endpoint -Name "Logs Endpoint" -Url "$baseUrl/logs?n=10"

# ==============================================================================
# Summary
# ==============================================================================

Write-Host "`n`n════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  TEST SUMMARY" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

$totalTests = 0
$passedTests = 0
$failedTests = 0
$optionalFailed = 0

foreach ($test in $results.Keys) {
    $totalTests++
    $testName = $test
    $testResult = $results[$test]

    if ($testResult.success) {
        $passedTests++
        Write-Host "[PASS] $testName" -ForegroundColor Green
    } else {
        # Check if it's an optional test
        if ($test -eq "gemini" -or $test -eq "runner") {
            $optionalFailed++
            Write-Host "[SKIP] $testName (optional - module not loaded)" -ForegroundColor Yellow
        } else {
            $failedTests++
            Write-Host "[FAIL] $testName - $($testResult.error)" -ForegroundColor Red
        }
    }
}

Write-Host ""
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor White
Write-Host "Total Tests: $totalTests" -ForegroundColor White
Write-Host "Passed: $passedTests" -ForegroundColor Green
Write-Host "Failed: $failedTests" -ForegroundColor Red
Write-Host "Optional (not loaded): $optionalFailed" -ForegroundColor Yellow
Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor White
Write-Host ""

# ==============================================================================
# Recommendations
# ==============================================================================

Write-Host "RECOMMENDATIONS:" -ForegroundColor Cyan
Write-Host ""

if ($failedTests -eq 0 -and $passedTests -gt 0) {
    Speak "All core tests passed"
    Write-Host "[OK] Core functionality is working!" -ForegroundColor Green
    Write-Host ""
}

if ($results.gemini.success -eq $false) {
    Write-Host "• GeminiService.ps1 is not loaded" -ForegroundColor Yellow
    Write-Host "  → Evidence card generation via Gemini won't work" -ForegroundColor Gray
    Write-Host "  → This is optional" -ForegroundColor Gray
    Write-Host ""
}

if ($results.runner.success -eq $false) {
    Write-Host "• OllamaRunner is not loaded" -ForegroundColor Yellow
    Write-Host "  → AI model routing (6 routes) won't work" -ForegroundColor Gray
    Write-Host "  → This is optional" -ForegroundColor Gray
    Write-Host ""
}

if ($results.status.success) {
    Write-Host "[OK] You can access the web interface at:" -ForegroundColor Green
    Write-Host "  http://localhost:9199/web" -ForegroundColor Cyan
    Write-Host ""
}

if ($results.reflectSubmit.success) {
    Write-Host "[OK] Check your reflection was saved:" -ForegroundColor Green
    Write-Host "  Get-Content HubStation\shared_bus\logs\hub_events.csv" -ForegroundColor Cyan
    Write-Host "  Get-ChildItem HubStation\shared_bus\reflections\" -ForegroundColor Cyan
    Write-Host ""
}

# ==============================================================================
# Browser Test
# ==============================================================================

Write-Host "BROWSER TEST:" -ForegroundColor Cyan
Write-Host "Open your browser and go to:" -ForegroundColor White
Write-Host "  http://localhost:9199/web" -ForegroundColor Yellow
Write-Host ""
Write-Host "If you see your index.html page, static files are working!" -ForegroundColor White
Write-Host ""

$openBrowser = Read-Host "Open browser now? (y/n)"
if ($openBrowser -eq 'y') {
    Start-Process "http://localhost:9199/web"
    Speak "Opening browser"
}

Write-Host ""
Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  Test Complete" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan

Speak "Test complete"

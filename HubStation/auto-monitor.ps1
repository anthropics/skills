# ==============================================================================
# HubStation Auto-Monitor with Claude AI Feedback Loop
# Monitors HubStation, sends state to Claude, applies fixes automatically
# ==============================================================================

param(
    [int]$IntervalMinutes = 5,
    [string]$ClaudeApiKey = $env:ANTHROPIC_API_KEY,
    [switch]$AutoApplyFixes,
    [switch]$NoSound
)

# ==============================================================================
# Configuration
# ==============================================================================

$script:HubStationUrl = "http://localhost:9199"
$script:LogPath = ".\monitor-log.txt"
$script:StateHistoryPath = ".\state-history.json"
$script:FixesAppliedPath = ".\fixes-applied.json"

# ==============================================================================
# Functions
# ==============================================================================

function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logLine = "[$timestamp] [$Level] $Message"
    Add-Content -Path $script:LogPath -Value $logLine

    $color = switch ($Level) {
        "ERROR" { "Red" }
        "WARN" { "Yellow" }
        "SUCCESS" { "Green" }
        default { "White" }
    }
    Write-Host $logLine -ForegroundColor $color
}

function Speak {
    param([string]$Message)
    if (-not $NoSound) {
        try {
            Add-Type -AssemblyName System.Speech
            $synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
            $synth.Rate = 1
            $synth.SpeakAsync($Message) | Out-Null
        } catch {}
    }
}

function Get-HubStationState {
    Write-Log "Capturing HubStation state..." "INFO"

    $state = @{
        timestamp = (Get-Date -Format "o")
        endpoints = @{}
        logs = @()
        errors = @()
        files_missing = @()
        config = $null
    }

    # Test status endpoint
    try {
        $status = Invoke-RestMethod -Uri "$script:HubStationUrl/status" -TimeoutSec 5 -ErrorAction Stop
        $state.endpoints.status = @{ working = $true; response = $status }
    } catch {
        $state.endpoints.status = @{ working = $false; error = $_.Exception.Message }
        $state.errors += "Status endpoint failed: $($_.Exception.Message)"
    }

    # Test reflection endpoints
    try {
        $reflectWindow = Invoke-RestMethod -Uri "$script:HubStationUrl/reflect/window?rows=5" -TimeoutSec 5 -ErrorAction Stop
        $state.endpoints.reflect = @{ working = $true; response = $reflectWindow }
    } catch {
        $state.endpoints.reflect = @{ working = $false; error = $_.Exception.Message }
        $state.errors += "Reflection endpoint failed: $($_.Exception.Message)"
    }

    # Check for missing files
    $requiredFiles = @(
        "HubStation\GeminiService.ps1",
        "HubStation\OllamaRunner\Router.ps1",
        "HubStation\OllamaRunner\Config.ps1",
        "HubStation\Reflections.psm1",
        "HubStation\HubStation.ps1"
    )

    foreach ($file in $requiredFiles) {
        if (-not (Test-Path $file)) {
            $state.files_missing += $file
            $state.errors += "Missing file: $file"
        }
    }

    # Get recent logs (last 10 lines)
    if (Test-Path "HubStation\shared_bus\logs\hub_events.csv") {
        try {
            $logs = Get-Content "HubStation\shared_bus\logs\hub_events.csv" -Tail 10 -ErrorAction Stop
            $state.logs = $logs
        } catch {}
    }

    # Check config
    if (Test-Path "HubStation\hub_config.json") {
        try {
            $config = Get-Content "HubStation\hub_config.json" -Raw | ConvertFrom-Json
            $state.config = $config
        } catch {}
    }

    # Check if Ollama is running
    try {
        $ollama = Invoke-RestMethod -Uri "http://localhost:11434/api/tags" -TimeoutSec 3 -ErrorAction Stop
        $state.ollama_running = $true
    } catch {
        $state.ollama_running = $false
        $state.errors += "Ollama is not running"
    }

    return $state
}

function Send-ToClaude {
    param(
        [hashtable]$State,
        [string]$ApiKey
    )

    Write-Log "Sending state to Claude for analysis..." "INFO"

    $prompt = @"
You are monitoring a HubStation server. Analyze this state and provide:
1. What's working
2. What's broken
3. Specific fixes (PowerShell commands if possible)
4. Priority (critical/high/medium/low)

Current State:
```json
$($State | ConvertTo-Json -Depth 10)
```

Respond with JSON in this format:
{
  "status": "healthy|degraded|critical",
  "working": ["list of working features"],
  "broken": ["list of broken features"],
  "fixes": [
    {
      "issue": "description",
      "priority": "critical|high|medium|low",
      "fix_type": "powershell|manual|config",
      "command": "powershell command to run",
      "description": "what this fix does"
    }
  ],
  "recommendations": ["general recommendations"]
}
"@

    try {
        $headers = @{
            "x-api-key" = $ApiKey
            "Content-Type" = "application/json"
            "anthropic-version" = "2023-06-01"
        }

        $body = @{
            model = "claude-sonnet-4-5-20250929"
            max_tokens = 2000
            messages = @(
                @{
                    role = "user"
                    content = $prompt
                }
            )
        } | ConvertTo-Json -Depth 10

        $response = Invoke-RestMethod -Uri "https://api.anthropic.com/v1/messages" `
                                      -Method Post `
                                      -Headers $headers `
                                      -Body $body `
                                      -TimeoutSec 30 `
                                      -ErrorAction Stop

        # Extract JSON from response
        $claudeResponse = $response.content[0].text

        # Try to parse as JSON
        try {
            # Remove markdown code blocks if present
            $claudeResponse = $claudeResponse -replace '```json\s*', '' -replace '```\s*$', ''
            $analysis = $claudeResponse | ConvertFrom-Json
            return $analysis
        } catch {
            Write-Log "Claude response wasn't valid JSON, returning raw response" "WARN"
            return @{
                status = "unknown"
                raw_response = $claudeResponse
            }
        }

    } catch {
        Write-Log "Failed to contact Claude API: $($_.Exception.Message)" "ERROR"
        return $null
    }
}

function Apply-Fix {
    param(
        [object]$Fix,
        [switch]$AutoApply
    )

    Write-Log "Fix suggested: $($Fix.issue)" "INFO"
    Write-Log "  Priority: $($Fix.priority)" "INFO"
    Write-Log "  Command: $($Fix.command)" "INFO"

    if ($Fix.fix_type -ne "powershell") {
        Write-Log "  Skipping (not PowerShell fix)" "WARN"
        return @{ applied = $false; reason = "Not a PowerShell fix" }
    }

    if (-not $AutoApply) {
        Write-Log "  Skipping (AutoApply not enabled)" "WARN"
        return @{ applied = $false; reason = "AutoApply disabled" }
    }

    try {
        Write-Log "  Applying fix..." "INFO"
        Speak "Applying fix for $($Fix.issue)"

        $result = Invoke-Expression $Fix.command

        Write-Log "  ✓ Fix applied successfully" "SUCCESS"
        Speak "Fix applied successfully"

        return @{
            applied = $true
            result = $result
            timestamp = (Get-Date -Format "o")
        }
    } catch {
        Write-Log "  ✗ Fix failed: $($_.Exception.Message)" "ERROR"
        Speak "Fix failed"

        return @{
            applied = $false
            error = $_.Exception.Message
            timestamp = (Get-Date -Format "o")
        }
    }
}

function Save-FixHistory {
    param([object]$Fix, [object]$Result)

    $history = @()
    if (Test-Path $script:FixesAppliedPath) {
        $history = Get-Content $script:FixesAppliedPath -Raw | ConvertFrom-Json
    }

    $history += @{
        fix = $Fix
        result = $Result
        timestamp = (Get-Date -Format "o")
    }

    $history | ConvertTo-Json -Depth 10 | Out-File $script:FixesAppliedPath -Encoding UTF8
}

# ==============================================================================
# Main Monitoring Loop
# ==============================================================================

Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "  HubStation Auto-Monitor with Claude AI" -ForegroundColor Cyan
Write-Host "════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""
Write-Host "Interval: $IntervalMinutes minutes" -ForegroundColor White
Write-Host "Auto-Apply Fixes: $AutoApplyFixes" -ForegroundColor White
Write-Host "Log File: $script:LogPath" -ForegroundColor White
Write-Host ""

if (-not $ClaudeApiKey) {
    Write-Host "ERROR: Claude API key not set!" -ForegroundColor Red
    Write-Host "Set environment variable: `$env:ANTHROPIC_API_KEY = 'your-key'" -ForegroundColor Yellow
    Write-Host "Or pass -ClaudeApiKey parameter" -ForegroundColor Yellow
    exit 1
}

Speak "Starting auto monitor"

$iteration = 0

while ($true) {
    $iteration++

    Write-Host "`n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
    Write-Host "  Iteration #$iteration - $(Get-Date -Format 'HH:mm:ss')" -ForegroundColor Cyan
    Write-Host "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" -ForegroundColor Cyan
    Write-Host ""

    # Capture state
    $state = Get-HubStationState

    # Send to Claude
    $analysis = Send-ToClaude -State $state -ApiKey $ClaudeApiKey

    if ($analysis) {
        Write-Host ""
        Write-Host "Claude Analysis:" -ForegroundColor Yellow
        Write-Host "  Status: $($analysis.status)" -ForegroundColor White

        if ($analysis.working) {
            Write-Host "  Working: $($analysis.working -join ', ')" -ForegroundColor Green
        }

        if ($analysis.broken) {
            Write-Host "  Broken: $($analysis.broken -join ', ')" -ForegroundColor Red
            Speak "Found $($analysis.broken.Count) issues"
        }

        # Apply fixes
        if ($analysis.fixes) {
            Write-Host ""
            Write-Host "Fixes suggested: $($analysis.fixes.Count)" -ForegroundColor Yellow

            foreach ($fix in $analysis.fixes) {
                $result = Apply-Fix -Fix $fix -AutoApply:$AutoApplyFixes
                Save-FixHistory -Fix $fix -Result $result
            }
        }

        # Show recommendations
        if ($analysis.recommendations) {
            Write-Host ""
            Write-Host "Recommendations:" -ForegroundColor Cyan
            foreach ($rec in $analysis.recommendations) {
                Write-Host "  • $rec" -ForegroundColor White
            }
        }
    } else {
        Write-Log "No analysis received from Claude" "WARN"
    }

    # Wait for next iteration
    Write-Host ""
    Write-Host "Next check in $IntervalMinutes minutes..." -ForegroundColor Gray
    Write-Host "Press Ctrl+C to stop" -ForegroundColor Gray

    Start-Sleep -Seconds ($IntervalMinutes * 60)
}

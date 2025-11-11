# ==============================================================================
# Start HubStation - Simple Startup with Audio Feedback
# Just double-click this file!
# ==============================================================================

param(
    [switch]$NoSound
)

# Function to speak and write
function Speak-Status {
    param(
        [string]$Message,
        [string]$Color = "Cyan"
    )

    Write-Host $Message -ForegroundColor $Color

    if (-not $NoSound) {
        try {
            Add-Type -AssemblyName System.Speech
            $synth = New-Object System.Speech.Synthesis.SpeechSynthesizer
            $synth.SelectVoiceByHints('Male') # or 'Female'
            $synth.Speak($Message)
            $synth.Dispose()
        } catch {
            # Silent fail if TTS not available
        }
    }
}

# ==============================================================================
# STEP 1: Check if we're in the right directory
# ==============================================================================

Speak-Status "Starting HubStation setup" "Cyan"

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

if (-not (Test-Path (Join-Path $scriptDir "HubStation.ps1"))) {
    Speak-Status "ERROR: Cannot find HubStation.ps1. Please run this script from the HubStation directory." "Red"
    Read-Host "Press Enter to exit"
    exit 1
}

Set-Location $scriptDir
Speak-Status "Directory check passed" "Green"

# ==============================================================================
# STEP 2: Check for Ollama
# ==============================================================================

Speak-Status "Checking for Ollama" "Cyan"

try {
    $ollamaCheck = Invoke-RestMethod -Uri "http://localhost:11434/api/tags" -Method Get -TimeoutSec 5 -ErrorAction Stop
    Speak-Status "Ollama is running" "Green"
} catch {
    Speak-Status "WARNING: Ollama is not running. Please start Ollama first." "Yellow"
    Speak-Status "You can start Ollama by running: ollama serve" "Yellow"

    $response = Read-Host "Do you want to continue anyway? (y/n)"
    if ($response -ne 'y') {
        Speak-Status "Exiting. Please start Ollama and try again." "Red"
        Read-Host "Press Enter to exit"
        exit 1
    }
}

# ==============================================================================
# STEP 3: Check for Gemini API Key
# ==============================================================================

Speak-Status "Checking for Gemini API key" "Cyan"

if (-not $env:GEMINI_API_KEY) {
    Speak-Status "WARNING: GEMINI_API_KEY environment variable is not set." "Yellow"
    Speak-Status "Gemini evidence card generation will not work without it." "Yellow"

    $key = Read-Host "Enter your Gemini API key (or press Enter to skip)"
    if ($key) {
        $env:GEMINI_API_KEY = $key
        Speak-Status "Gemini API key set for this session" "Green"
    } else {
        Speak-Status "Skipping Gemini API key. You can set it later." "Yellow"
    }
} else {
    Speak-Status "Gemini API key found" "Green"
}

# ==============================================================================
# STEP 4: Check port availability
# ==============================================================================

Speak-Status "Checking if port 9199 is available" "Cyan"

try {
    $portCheck = Test-NetConnection -ComputerName localhost -Port 9199 -InformationLevel Quiet -WarningAction SilentlyContinue
    if ($portCheck) {
        Speak-Status "WARNING: Port 9199 is already in use. HubStation may fail to start." "Yellow"

        $response = Read-Host "Do you want to continue anyway? (y/n)"
        if ($response -ne 'y') {
            Speak-Status "Exiting. Please close the application using port 9199." "Red"
            Read-Host "Press Enter to exit"
            exit 1
        }
    } else {
        Speak-Status "Port 9199 is available" "Green"
    }
} catch {
    # Port is available (Test-NetConnection fails when nothing is listening)
    Speak-Status "Port 9199 is available" "Green"
}

# ==============================================================================
# STEP 5: Start HubStation
# ==============================================================================

Speak-Status "All checks passed. Starting HubStation now." "Green"
Speak-Status "You should hear module loading messages in a moment." "Cyan"

Start-Sleep -Seconds 2

# Start HubStation.ps1
& (Join-Path $scriptDir "HubStation.ps1")

@echo off
REM ==============================================================================
REM HubStation Startup - Just double-click this file!
REM ==============================================================================

echo.
echo ========================================
echo   Starting HubStation...
echo ========================================
echo.

REM Change to the directory where this batch file is located
cd /d "%~dp0"

REM Run the PowerShell startup script
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "Start-HubStation.ps1"

REM If PowerShell exits with an error, pause so you can see the error message
if errorlevel 1 (
    echo.
    echo ========================================
    echo   HubStation failed to start
    echo ========================================
    echo.
    pause
)

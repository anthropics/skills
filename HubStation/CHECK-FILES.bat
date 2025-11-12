@echo off
cd /d "%~dp0"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "CHECK-FILES.ps1"
if errorlevel 1 (
    echo.
    echo File check found issues
    pause
) else (
    echo.
    echo All checks passed!
    pause
)

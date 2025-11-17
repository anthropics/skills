@echo off
cd /d "%~dp0"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "test-hubstation.ps1"
if errorlevel 1 (
    echo Test script failed
    pause
)

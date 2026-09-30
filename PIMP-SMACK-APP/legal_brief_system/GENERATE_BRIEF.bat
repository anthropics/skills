@echo off
echo ============================================================
echo NINTH CIRCUIT BRIEF GENERATOR
echo ============================================================
echo.
cd /d "%~dp0"
python generate_brief.py
echo.
pause

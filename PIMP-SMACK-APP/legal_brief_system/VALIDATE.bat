@echo off
echo ============================================================
echo BRIEF VALIDATOR
echo ============================================================
echo.
echo Checking all data files for compliance...
echo.
cd /d "%~dp0"
python validate_brief.py
echo.
pause

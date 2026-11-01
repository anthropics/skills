@echo off
echo ============================================================
echo COMPLETE FILING PACKAGE GENERATOR
echo ============================================================
echo.
echo This will generate:
echo   - Cover page
echo   - Brief body (all sections)
echo   - Filing checklist
echo.
cd /d "%~dp0"
python generate_filing_package.py
echo.
pause

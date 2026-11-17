@echo off
echo ============================================================
echo BUILD BRIEF FROM EVIDENCE POOL
echo ============================================================
echo.
echo Building brief sections from linked evidence...
echo.
cd /d "%~dp0"
python build_from_evidence.py
echo.
pause

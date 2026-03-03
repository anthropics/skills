@echo off
REM 盘后复盘一键运行脚本（Windows）
REM 建议运行时间：每个交易日 15:30 后
cd /d "%~dp0"

echo ========================================
echo 盘后复盘 - 一键采集并生成报告
echo ========================================
echo.

python -c "import akshare" 2>nul
if errorlevel 1 (
    echo 未检测到 akshare，请先安装：pip install -r requirements.txt
    pause
    exit /b 1
)

python fetch_market_data.py
echo.
python fetch_fund_flow.py
echo.
python fetch_etf_shares.py
echo.
python generate_report.py

echo.
echo 全部完成！
pause

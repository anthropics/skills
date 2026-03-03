#!/bin/bash
# 盘后复盘一键运行脚本（Mac/Linux）
# 建议运行时间：每个交易日 15:30 后
set -e
cd "$(dirname "$0")"

echo "========================================"
echo "🌙 盘后复盘 - 一键采集并生成报告"
echo "========================================"
echo ""

# 检查 akshare 是否已安装
if ! python3 -c "import akshare" 2>/dev/null; then
    echo "❌ 未检测到 akshare，请先安装依赖："
    echo "   pip install -r requirements.txt"
    echo ""
    echo "如遇 SSL/安装问题，可尝试："
    echo "   - 使用 conda: conda install -c conda-forge akshare"
    echo "   - 或在 Windows 下运行 run.bat"
    exit 1
fi

python3 fetch_market_data.py
echo ""
python3 fetch_fund_flow.py
echo ""
python3 fetch_etf_shares.py
echo ""
python3 generate_report.py

echo ""
echo "✅ 全部完成！"

#!/bin/bash
# 盘后复盘一键运行脚本（Mac/Linux）
# 建议运行时间：每个交易日 15:30 后
set -e
cd "$(dirname "$0")"

echo "========================================"
echo "🌙 盘后复盘 - 一键采集并生成报告"
echo "========================================"
echo ""

python3 fetch_market_data.py
echo ""
python3 fetch_fund_flow.py
echo ""
python3 fetch_etf_shares.py
echo ""
python3 generate_report.py

echo ""
echo "✅ 全部完成！"

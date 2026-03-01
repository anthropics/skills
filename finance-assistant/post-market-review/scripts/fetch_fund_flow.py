"""
fetch_fund_flow.py - 采集主力资金净流向数据
运行时间：每个交易日 16:00 后
数据源：akshare 东方财富资金流向接口
"""
import akshare as ak
import pandas as pd
import json
import os
from datetime import datetime, date
from config import WATCHLIST_ETFS, ETF_NAME_MAP, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    return date.today().strftime("%Y-%m-%d")


def ensure_output_dir(date_str: str) -> str:
    path = os.path.join(OUTPUT_DIR, date_str)
    os.makedirs(path, exist_ok=True)
    return path


def fetch_sector_fund_flow() -> list:
    """采集板块资金流向排行（前10名净流入/流出）"""
    print("💰 采集板块主力资金流向...")
    result = []

    try:
        df = ak.stock_sector_fund_flow_rank(symbol="今日")
        if df is not None and not df.empty:
            # 取净流入最多的前10个板块
            key_col = [c for c in df.columns if "净额" in c or "净流入" in c]
            if key_col:
                df = df.sort_values(key_col[0], ascending=False)

            for _, row in df.head(10).iterrows():
                result.append({
                    "rank": _ + 1,
                    "sector": str(row.get("板块名称", row.iloc[0])),
                    "net_flow": str(row.get(key_col[0], "") if key_col else ""),
                    "change_pct": str(row.get("涨跌幅", "")),
                })

            print(f"  ✅ 板块资金流向采集完成，共{len(df)}个板块")
            print(f"  🥇 净流入最多: {result[0]['sector'] if result else '无数据'}")
            print(f"  📋 净流出最多: {result[-1]['sector'] if len(result) > 1 else '无数据'}")
    except Exception as e:
        print(f"  ⚠️ 板块资金流向获取失败: {e}")

    return result


def fetch_etf_fund_flow(etf_code: str) -> dict:
    """采集单只ETF的资金流向"""
    name = ETF_NAME_MAP.get(etf_code, etf_code)
    result = {
        "code": etf_code,
        "name": name,
        "net_flow_million": None,
        "signal": "数据不可用"
    }

    try:
        df = ak.fund_etf_flow_daily_em(symbol=etf_code)
        if df is not None and not df.empty:
            latest = df.iloc[-1]
            net_flow = float(latest.get("主力净流入", latest.get("净流入", 0)))
            result["net_flow_million"] = round(net_flow / 1e6, 2)

            threshold = THRESHOLDS["fund_flow_billion"] * 100  # 转为百万
            if net_flow >= threshold * 1e6:
                result["signal"] = f"🟢 主力大幅净流入 {result['net_flow_million']:+.1f}百万"
            elif net_flow >= 0:
                result["signal"] = f"💚 主力净流入 {result['net_flow_million']:+.1f}百万"
            elif net_flow >= -threshold * 1e6:
                result["signal"] = f"🟠 主力净流出 {result['net_flow_million']:+.1f}百万"
            else:
                result["signal"] = f"🔴 主力大幅净流出 {result['net_flow_million']:+.1f}百万"
    except Exception as e:
        result["error"] = str(e)

    return result


def fetch_market_total_flow() -> dict:
    """采集全市场今日主力资金总体净流向"""
    print("💰 采集全市场主力资金总流向...")
    result = {}

    try:
        df = ak.stock_market_fund_flow()
        if df is not None and not df.empty:
            latest = df.iloc[-1]
            result = {
                "date": str(latest.get("日期", "")),
                "main_net_flow": str(latest.get("主力净流入", "")),
                "retail_net_flow": str(latest.get("散户净流入", "")),
                "total_amount": str(latest.get("成交额", "")),
            }
            print(f"  ✅ 全市场主力净流向: {result.get('main_net_flow', '未知')}")
    except Exception as e:
        print(f"  ⚠️ 全市场资金流向获取失败: {e}")

    return result


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"💰 主力资金流向采集 - {today}")
    print(f"{'='*50}\n")

    sector_flow = fetch_sector_fund_flow()
    market_total = fetch_market_total_flow()

    print(f"\n📦 采集各ETF资金流向...")
    etf_flows = []
    for code in WATCHLIST_ETFS:
        name = ETF_NAME_MAP.get(code, code)
        print(f"  采集 {name}({code})...")
        data = fetch_etf_fund_flow(code)
        etf_flows.append(data)
        if "error" not in data:
            print(f"  → {data['signal']}")

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "market_total_flow": market_total,
        "sector_top10": sector_flow,
        "etf_flows": etf_flows,
        "summary": {
            "hottest_sectors": [s["sector"] for s in sector_flow[:3]] if sector_flow else [],
            "coldest_sectors": [s["sector"] for s in sector_flow[-3:]] if len(sector_flow) >= 3 else [],
            "etf_inflow": [e["name"] for e in etf_flows if (e.get("net_flow_million") or 0) > 0],
            "etf_outflow": [e["name"] for e in etf_flows if (e.get("net_flow_million") or 0) < 0],
        }
    }

    output_file = os.path.join(output_path, "fund_flow.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"\n✅ 主力资金数据已保存至: {output_file}")
    print(f"\n📈 今日资金净流入板块 TOP3: {', '.join(result['summary']['hottest_sectors'])}")
    if result["summary"]["etf_inflow"]:
        print(f"💚 持仓ETF净流入: {', '.join(result['summary']['etf_inflow'])}")
    if result["summary"]["etf_outflow"]:
        print(f"🟠 持仓ETF净流出: {', '.join(result['summary']['etf_outflow'])}")

    return result


if __name__ == "__main__":
    run()

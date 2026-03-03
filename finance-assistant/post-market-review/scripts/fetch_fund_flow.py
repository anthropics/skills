# -*- coding: utf-8 -*-
"""
fetch_fund_flow.py - 采集主力资金净流向数据
运行时间：每个交易日 16:00 后
数据源：akshare  新浪/东方财富
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import akshare as ak
import warnings
warnings.filterwarnings('ignore')

import json
import os
from datetime import datetime, date
from config import WATCHLIST_ETFS, ETF_NAME_MAP, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    """支持 --date YYYY-MM-DD 命令行参数覆盖今日日期"""
    import sys
    if "--date" in sys.argv:
        idx = sys.argv.index("--date")
        if idx + 1 < len(sys.argv):
            return sys.argv[idx + 1]
    return date.today().strftime("%Y-%m-%d")


def ensure_output_dir(date_str: str) -> str:
    path = os.path.join(OUTPUT_DIR, date_str)
    os.makedirs(path, exist_ok=True)
    return path


def get_market(code: str) -> str:
    """根据ETF代码判断市场：5开头→沪市sh，1开头→深市sz"""
    return "sh" if code.startswith("5") else "sz"


def fmt_yuan(val) -> str:
    """将元转换为亿元字符串"""
    try:
        v = float(val)
        return f"{v/1e8:+.2f}亿"
    except Exception:
        return str(val)


def _retry(fn, retries=3, delay=2):
    """简单重试装饰器（顺序调用时防止东方财富限速）"""
    import time
    last_err = None
    for i in range(retries):
        try:
            return fn()
        except Exception as e:
            last_err = e
            if i < retries - 1:
                time.sleep(delay * (i + 1))
    raise last_err


def fetch_etf_fund_flow(etf_code: str) -> dict:
    """
    采集单只ETF的二级市场主力资金净流向。
    使用 stock_individual_fund_flow(stock, market) 替代已废弃的 fund_etf_flow_daily_em。
    返回今日最新一行数据。
    """
    name = ETF_NAME_MAP.get(etf_code, etf_code)
    market = get_market(etf_code)
    result = {
        "code": etf_code,
        "name": name,
        "close": None,
        "change_pct_day": None,
        "main_net_flow": None,       # 主力净流入额（元）
        "main_net_flow_pct": None,   # 主力净流入占比%
        "super_large_net": None,     # 超大单净额（元）
        "large_net": None,           # 大单净额（元）
        "signal": "数据不可用",
    }

    try:
        df = _retry(lambda: ak.stock_individual_fund_flow(stock=etf_code, market=market))
        if df is None or df.empty:
            raise ValueError("无数据返回")

        cols = list(df.columns)
        # 列序: 日期(0) 收盘价(1) 涨跌幅(2) 主力净流入-净额(3) 主力净流入-净占比(4)
        #        超大单净流入-净额(5) 超大单净流入-净占比(6) 大单净流入-净额(7) 大单净流入-净占比(8)
        today_str = get_today_str()
        today_rows = df[df[cols[0]].astype(str) == today_str]
        # 若无今日行，取最新一行（允许T+0延迟）
        latest = today_rows.iloc[0] if not today_rows.empty else df.iloc[-1]
        latest_date = str(latest[cols[0]])

        if latest_date != today_str:
            # 超过2个自然日则认为数据过期
            from datetime import datetime as _dt
            diff = (_dt.strptime(today_str, "%Y-%m-%d") - _dt.strptime(latest_date, "%Y-%m-%d")).days
            if diff > 2:
                result["signal"] = f"⚠️ 数据过期（最新: {latest_date}）"
                return result
            # 否则使用最新可用数据（如当日数据尚未更新）
            result["_data_date"] = latest_date

        close = float(latest[cols[1]])
        chg_pct = float(latest[cols[2]])
        main_net = float(latest[cols[3]])
        main_net_pct = float(latest[cols[4]])
        super_net = float(latest[cols[5]])
        large_net = float(latest[cols[7]])

        result.update({
            "close": close,
            "change_pct_day": chg_pct,
            "main_net_flow": main_net,
            "main_net_flow_pct": main_net_pct,
            "super_large_net": super_net,
            "large_net": large_net,
        })

        threshold_yuan = THRESHOLDS["fund_flow_billion"] * 1e8
        if main_net >= threshold_yuan:
            result["signal"] = f"🟢 主力大幅净流入 {fmt_yuan(main_net)} ({main_net_pct:+.1f}%)"
        elif main_net >= 0:
            result["signal"] = f"💚 主力净流入 {fmt_yuan(main_net)} ({main_net_pct:+.1f}%)"
        elif main_net >= -threshold_yuan:
            result["signal"] = f"🟠 主力净流出 {fmt_yuan(main_net)} ({main_net_pct:+.1f}%)"
        else:
            result["signal"] = f"🔴 主力大幅净流出 {fmt_yuan(main_net)} ({main_net_pct:+.1f}%)"

    except Exception as e:
        result["error"] = str(e)

    return result


def fetch_industry_fund_flow() -> list:
    """
    采集行业资金流向排行（今日净流入 TOP/BOTTOM）。
    使用 stock_fund_flow_industry(symbol='即时')。
    """
    print("💰 采集行业主力资金流向...")
    result = []
    try:
        df = ak.stock_fund_flow_industry(symbol='即时')
        if df is None or df.empty:
            raise ValueError("无数据")

        cols = list(df.columns)
        # 列序: 序号(0) 行业(1) 行业指数(2) 行业-涨跌幅(3) 流入资金(4) 流出资金(5) 净额(6) 公司家数(7) 领涨股(8) 领涨股-涨跌幅(9) 当前价(10)
        # 按净额排序（已有序，正在从大到小）
        col_sector = cols[1]
        col_chg = cols[3]
        col_inflow = cols[4]
        col_outflow = cols[5]
        col_net = cols[6]
        col_leader = cols[8] if len(cols) > 8 else None
        col_leader_chg = cols[9] if len(cols) > 9 else None

        for _, row in df.iterrows():
            entry = {
                "sector": str(row[col_sector]),
                "change_pct": float(row[col_chg]) if row[col_chg] else 0,
                "inflow_billion": round(float(row[col_inflow]) / 1e2, 2) if row[col_inflow] else 0,
                "outflow_billion": round(float(row[col_outflow]) / 1e2, 2) if row[col_outflow] else 0,
                "net_billion": round(float(row[col_net]) / 1e2, 2) if row[col_net] else 0,
                "leader_stock": str(row[col_leader]) if col_leader else "",
                "leader_change": float(row[col_leader_chg]) if col_leader_chg and row[col_leader_chg] else 0,
            }
            result.append(entry)

        # 排序：net 从大到小
        result.sort(key=lambda x: x["net_billion"], reverse=True)
        top3 = [s["sector"] for s in result[:3]]
        bot3 = [s["sector"] for s in result[-3:]]
        print(f"  ✅ 净流入TOP3: {' / '.join(top3)}")
        print(f"  📉 净流出TOP3: {' / '.join(bot3)}")

    except Exception as e:
        print(f"  ⚠️ 行业资金流向获取失败: {e}")

    return result


def fetch_market_total_flow() -> dict:
    """采集全市场今日主力资金总体净流向"""
    print("💰 采集全市场主力资金总流向...")
    result = {}
    try:
        df = _retry(lambda: ak.stock_market_fund_flow())
        if df is None or df.empty:
            raise ValueError("无数据")

        cols = list(df.columns)
        # 列：日期(0) 上证-收盘价(1) 上证-涨跌幅(2) 深证-收盘价(3) 深证-涨跌幅(4)
        #      主力净流入-净额(5) 主力净流入-净占比(6) 超大单净流入-净额(7) 超大单净流入-净占比(8)
        #      大单净流入-净额(9) 大单净流入-净占比(10) 中单净流入-净额(11) 中单净流入-净占比(12)
        #      小单净流入-净额(13) 小单净流入-净占比(14)
        today_str = get_today_str()
        today_rows = df[df[cols[0]].astype(str) == today_str]
        latest = today_rows.iloc[0] if not today_rows.empty else df.iloc[-1]

        result = {
            "date": str(latest[cols[0]]),
            "sh_close": float(latest[cols[1]]) if latest[cols[1]] else None,
            "sh_change_pct": float(latest[cols[2]]) if latest[cols[2]] else None,
            "sz_close": float(latest[cols[3]]) if latest[cols[3]] else None,
            "sz_change_pct": float(latest[cols[4]]) if latest[cols[4]] else None,
            "main_net_flow": float(latest[cols[5]]) if latest[cols[5]] else None,
            "main_net_flow_pct": float(latest[cols[6]]) if latest[cols[6]] else None,
            "super_large_net": float(latest[cols[7]]) if latest[cols[7]] else None,
            "large_net": float(latest[cols[9]]) if latest[cols[9]] else None,
            "small_net": float(latest[cols[13]]) if latest[cols[13]] else None,
        }

        main = result.get("main_net_flow") or 0
        pct = result.get("main_net_flow_pct") or 0
        sign = "净流入" if main >= 0 else "净流出"
        print(f"  ✅ 全市场主力{sign}: {fmt_yuan(main)} ({pct:+.2f}%)")
        if result.get("small_net") is not None:
            small = result["small_net"]
            print(f"  📊 散户资金{'净买入' if small >= 0 else '净卖出'}: {fmt_yuan(small)}")

    except Exception as e:
        print(f"  ⚠️ 全市场资金流向获取失败: {e}")

    return result


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"💰 主力资金流向采集 - {today}")
    print(f"{'='*50}\n")

    market_total = fetch_market_total_flow()
    industry_flow = fetch_industry_fund_flow()

    import time as _time
    print(f"\n📦 采集各持仓ETF二级市场资金流向...")
    etf_flows = []
    for i, code in enumerate(WATCHLIST_ETFS):
        name = ETF_NAME_MAP.get(code, code)
        print(f"  采集 {name}({code})...", end=" ")
        data = fetch_etf_fund_flow(code)
        etf_flows.append(data)
        if i < len(WATCHLIST_ETFS) - 1:
            _time.sleep(0.8)  # 防止东方财富限速
        if "error" not in data and data.get("main_net_flow") is not None:
            print(f"涨跌{data['change_pct_day']:+.2f}%  {data['signal']}")
        elif "signal" in data:
            print(data["signal"])
        else:
            print(f"❌ {data.get('error', '未知错误')}")

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "market_total_flow": market_total,
        "industry_top10": industry_flow[:10],
        "industry_bottom5": industry_flow[-5:] if len(industry_flow) >= 5 else industry_flow,
        "etf_flows": etf_flows,
        "summary": {
            "market_main_net_billion": round(market_total.get("main_net_flow", 0) / 1e8, 2) if market_total.get("main_net_flow") else None,
            "top_inflow_sectors": [s["sector"] for s in industry_flow[:5]] if industry_flow else [],
            "top_outflow_sectors": [s["sector"] for s in industry_flow[-5:]] if industry_flow else [],
            "etf_inflow": [e["name"] for e in etf_flows if (e.get("main_net_flow") or 0) > 0],
            "etf_outflow": [e["name"] for e in etf_flows if (e.get("main_net_flow") or 0) < 0],
        }
    }

    output_file = os.path.join(output_path, "fund_flow.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"\n✅ 主力资金数据已保存至: {output_file}")
    net = result["summary"].get("market_main_net_billion")
    if net is not None:
        label = "净流入" if net >= 0 else "净流出"
        print(f"📊 今日全市场主力{label}: {abs(net):.2f}亿")

    return result


if __name__ == "__main__":
    run()

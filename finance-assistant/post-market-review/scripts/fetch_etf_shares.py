"""
fetch_etf_shares.py - 采集ETF份额变化数据
运行时间：每个交易日 17:00 后（等份额公告发布完成）
数据源：akshare ETF份额接口
"""
import akshare as ak
import pandas as pd
import json
import os
from datetime import datetime, date, timedelta
from config import WATCHLIST_ETFS, ETF_NAME_MAP, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    return date.today().strftime("%Y-%m-%d")


def get_prev_trading_day(today_str: str) -> str:
    """简单获取前一个日期（非精确交易日）"""
    d = datetime.strptime(today_str, "%Y-%m-%d")
    delta = 1
    prev = d - timedelta(days=delta)
    # 跳过周末
    while prev.weekday() >= 5:
        delta += 1
        prev = d - timedelta(days=delta)
    return prev.strftime("%Y-%m-%d")


def ensure_output_dir(date_str: str) -> str:
    path = os.path.join(OUTPUT_DIR, date_str)
    os.makedirs(path, exist_ok=True)
    return path


def fetch_single_etf_share(etf_code: str) -> dict:
    """获取单只ETF的最新份额数据"""
    result = {
        "code": etf_code,
        "name": ETF_NAME_MAP.get(etf_code, etf_code),
        "today_share": None,
        "yesterday_share": None,
        "change": None,
        "change_pct": None,
        "signal": "中性",
        "score_impact": 0
    }

    try:
        # akshare ETF份额历史数据
        df = ak.fund_etf_hist_em(symbol=etf_code, period="daily", adjust="")
        if df is None or df.empty:
            raise ValueError("无数据返回")

        df = df.sort_values("日期", ascending=False).reset_index(drop=True)

        today_share = float(df.iloc[0].get("持有份数", df.iloc[0].get("成交量", 0)))
        yesterday_share = float(df.iloc[1].get("持有份数", df.iloc[1].get("成交量", 0))) if len(df) > 1 else today_share

        change = today_share - yesterday_share
        change_pct = (change / yesterday_share * 100) if yesterday_share != 0 else 0

        result.update({
            "today_share": today_share,
            "yesterday_share": yesterday_share,
            "change": change,
            "change_pct": round(change_pct, 2),
        })

        # 信号判断
        threshold = THRESHOLDS["etf_shares_change_pct"]
        if change_pct >= threshold:
            result["signal"] = f"🟢 大幅净申购 (+{change_pct:.1f}%)"
            result["score_impact"] = +15
        elif change_pct >= threshold / 2:
            result["signal"] = f"💚 小幅净申购 (+{change_pct:.1f}%)"
            result["score_impact"] = +8
        elif change_pct <= -threshold:
            result["signal"] = f"🔴 大幅净赎回 ({change_pct:.1f}%)"
            result["score_impact"] = -15
        elif change_pct <= -threshold / 2:
            result["signal"] = f"🟠 小幅净赎回 ({change_pct:.1f}%)"
            result["score_impact"] = -8
        else:
            result["signal"] = f"⚪ 份额基本不变 ({change_pct:+.1f}%)"
            result["score_impact"] = 0

    except Exception as e:
        result["error"] = str(e)
        print(f"  ⚠️ {etf_code} 份额数据获取失败: {e}")

    return result


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"📦 ETF份额变化采集 - {today}")
    print(f"{'='*50}\n")
    print(f"关注ETF列表: {WATCHLIST_ETFS}\n")

    shares_data = []
    alerts = []

    for etf_code in WATCHLIST_ETFS:
        name = ETF_NAME_MAP.get(etf_code, etf_code)
        print(f"采集 {name}({etf_code})...")
        data = fetch_single_etf_share(etf_code)
        shares_data.append(data)

        # 打印结果
        if "error" not in data:
            print(f"  → 今日份额: {data['today_share']:,.0f}")
            print(f"  → 变化: {data['change_pct']:+.2f}%  信号: {data['signal']}")
            print(f"  → 评分影响: {data['score_impact']:+d}分\n")

            # 生成预警
            if abs(data.get("change_pct", 0)) >= THRESHOLDS["etf_shares_change_pct"]:
                alerts.append({
                    "etf": name,
                    "signal": data["signal"],
                    "score_impact": data["score_impact"]
                })
        else:
            print(f"  ❌ 获取失败: {data['error']}\n")

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "etf_shares": shares_data,
        "alerts": alerts,
        "summary": {
            "strong_buy_signal": [d["name"] for d in shares_data if d.get("score_impact", 0) >= 15],
            "strong_sell_signal": [d["name"] for d in shares_data if d.get("score_impact", 0) <= -15],
        }
    }

    # 保存 JSON
    output_file = os.path.join(output_path, "etf_shares.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"✅ ETF份额数据已保存至: {output_file}")

    if alerts:
        print(f"\n⚠️ 重要信号 ({len(alerts)}条):")
        for a in alerts:
            print(f"  {a['etf']}: {a['signal']}  评分{a['score_impact']:+d}分")

    if result["summary"]["strong_buy_signal"]:
        print(f"\n🟢 机构大幅申购（明日关注加仓）: {', '.join(result['summary']['strong_buy_signal'])}")
    if result["summary"]["strong_sell_signal"]:
        print(f"🔴 机构大幅赎回（关注风险）: {', '.join(result['summary']['strong_sell_signal'])}")

    return result


if __name__ == "__main__":
    run()

# -*- coding: utf-8 -*-
"""
fetch_etf_shares.py - 采集ETF份额/成交量变化数据
运行时间：每个交易日 17:00 后
数据源：akshare fund_etf_hist_em

说明：当"持有份数"字段不可用时，以成交量变化作为机构活跃度代理指标。
评分规则：根据变化幅度差异化给分，幅度越大分值越高，不再固定+15。
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import akshare as ak
import warnings
warnings.filterwarnings('ignore')

import json
import os
from datetime import datetime, date, timedelta
from config import WATCHLIST_ETFS, ETF_NAME_MAP, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    """支持 --date YYYY-MM-DD 命令行参数"""
    import sys
    if "--date" in sys.argv:
        idx = sys.argv.index("--date")
        if idx + 1 < len(sys.argv):
            return sys.argv[idx + 1]
    return date.today().strftime("%Y-%m-%d")


def get_prev_trading_day(today_str: str) -> str:
    """获取前一个交易日（跳过周末）"""
    d = datetime.strptime(today_str, "%Y-%m-%d")
    delta = 1
    prev = d - timedelta(days=delta)
    while prev.weekday() >= 5:
        delta += 1
        prev = d - timedelta(days=delta)
    return prev.strftime("%Y-%m-%d")


def ensure_output_dir(date_str: str) -> str:
    path = os.path.join(OUTPUT_DIR, date_str)
    os.makedirs(path, exist_ok=True)
    return path


def calc_score(change_pct: float) -> int:
    """
    差异化评分：根据份额/成交量变化幅度计算评分影响。
    正向（申购/活跃）：
      >= 100% → +20  极强（翻倍以上，机构大举进场）
      >= 50%  → +17
      >= 20%  → +14
      >= 10%  → +11
      >= 5%   → +8
      >= 2%   → +5
    负向（赎回/萎缩）：
      <= -50% → -17
      <= -20% → -14
      <= -10% → -11
      <= -5%  → -8
      <= -2%  → -5
    中性：±2% → 0
    """
    if change_pct >= 100:
        return +20
    elif change_pct >= 50:
        return +17
    elif change_pct >= 20:
        return +14
    elif change_pct >= 10:
        return +11
    elif change_pct >= 5:
        return +8
    elif change_pct >= 2:
        return +5
    elif change_pct > -2:
        return 0
    elif change_pct > -5:
        return -5
    elif change_pct > -10:
        return -8
    elif change_pct > -20:
        return -11
    elif change_pct > -50:
        return -14
    else:
        return -17


def signal_label(change_pct: float, score: int) -> str:
    """生成信号标签"""
    if score >= 17:
        return f"🔥 极强申购 (+{change_pct:.1f}%)"
    elif score >= 11:
        return f"🟢 大幅申购 (+{change_pct:.1f}%)"
    elif score >= 5:
        return f"💚 小幅申购 (+{change_pct:.1f}%)"
    elif score > 0:
        return f"🟩 轻微申购 (+{change_pct:.1f}%)"
    elif score == 0:
        return f"⚪ 基本持平 ({change_pct:+.1f}%)"
    elif score > -8:
        return f"🟠 小幅赎回 ({change_pct:.1f}%)"
    elif score > -14:
        return f"🔴 大幅赎回 ({change_pct:.1f}%)"
    else:
        return f"🚨 极强赎回 ({change_pct:.1f}%)"


def fetch_single_etf_share(etf_code: str) -> dict:
    """获取单只ETF的最新份额/成交量数据"""
    result = {
        "code": etf_code,
        "name": ETF_NAME_MAP.get(etf_code, etf_code),
        "today_share": None,
        "yesterday_share": None,
        "change": None,
        "change_pct": None,
        "signal": "中性",
        "score_impact": 0,
        "data_type": "unknown",  # 'shares' or 'volume'
    }

    try:
        df = ak.fund_etf_hist_em(symbol=etf_code, period="daily", adjust="")
        if df is None or df.empty:
            raise ValueError("无数据返回")

        df = df.sort_values("日期", ascending=False).reset_index(drop=True)
        cols = list(df.columns)

        # 优先取"持有份数"，无则取"成交量"
        share_col = None
        for c in cols:
            if "份" in str(c):
                share_col = c
                data_type = "shares"
                break
        if share_col is None:
            for c in cols:
                if "成交量" in str(c) or "量" in str(c)[-2:]:
                    share_col = c
                    data_type = "volume"
                    break
        if share_col is None:
            share_col = cols[5] if len(cols) > 5 else cols[-1]
            data_type = "volume"

        result["data_type"] = data_type

        today_share = float(df.iloc[0][share_col]) if df.iloc[0][share_col] else 0
        yesterday_share = float(df.iloc[1][share_col]) if len(df) > 1 and df.iloc[1][share_col] else today_share

        change = today_share - yesterday_share
        change_pct = (change / yesterday_share * 100) if yesterday_share != 0 else 0

        score = calc_score(change_pct)
        label = signal_label(change_pct, score)

        result.update({
            "today_share": round(today_share, 0),
            "yesterday_share": round(yesterday_share, 0),
            "change": round(change, 0),
            "change_pct": round(change_pct, 2),
            "signal": label,
            "score_impact": score,
        })

    except Exception as e:
        result["error"] = str(e)
        result["signal"] = "数据不可用"
        print(f"  ⚠️ {etf_code} 数据获取失败: {e}")

    return result


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"📦 ETF份额变化采集 - {today}")
    print(f"{'='*50}\n")

    shares_data = []
    alerts = []

    for etf_code in WATCHLIST_ETFS:
        name = ETF_NAME_MAP.get(etf_code, etf_code)
        print(f"采集 {name}({etf_code})...", end=" ")
        data = fetch_single_etf_share(etf_code)
        shares_data.append(data)

        if "error" not in data and data.get("change_pct") is not None:
            print(f"变化{data['change_pct']:+.1f}%  评分{data['score_impact']:+d}  {data['signal']}")
            if abs(data["change_pct"]) >= THRESHOLDS["etf_shares_change_pct"]:
                alerts.append({
                    "etf": name,
                    "signal": data["signal"],
                    "score_impact": data["score_impact"]
                })
        else:
            print(f"❌ {data.get('error', '未知')}")

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "etf_shares": shares_data,
        "alerts": alerts,
        "summary": {
            "extreme_buy": [d["name"] for d in shares_data if d.get("score_impact", 0) >= 17],
            "strong_buy": [d["name"] for d in shares_data if 11 <= d.get("score_impact", 0) < 17],
            "moderate_buy": [d["name"] for d in shares_data if 5 <= d.get("score_impact", 0) < 11],
            "strong_sell": [d["name"] for d in shares_data if d.get("score_impact", 0) <= -11],
            "moderate_sell": [d["name"] for d in shares_data if -11 < d.get("score_impact", 0) <= -5],
        }
    }

    output_file = os.path.join(output_path, "etf_shares.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"\n✅ ETF份额数据已保存至: {output_file}")
    if result["summary"]["extreme_buy"]:
        print(f"🔥 极强申购: {', '.join(result['summary']['extreme_buy'])}")
    if result["summary"]["strong_buy"]:
        print(f"🟢 大幅申购: {', '.join(result['summary']['strong_buy'])}")
    if result["summary"]["strong_sell"]:
        print(f"🔴 大幅赎回: {', '.join(result['summary']['strong_sell'])}")

    return result


if __name__ == "__main__":
    run()

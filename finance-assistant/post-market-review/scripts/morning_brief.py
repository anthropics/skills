"""
morning_brief.py - 早盘定性判断脚本（盘前定调）
运行时间：每个交易日 8:00-9:25
功能：输出早盘定性判断清单，可选拉取期货升贴水等预判信号
依赖：akshare（可选，无则仅输出模板）
"""
import sys
from datetime import datetime, date

try:
    import akshare as ak
    HAS_AK = True
except ImportError:
    HAS_AK = False

from config import WATCHLIST_ETFS, ETF_NAME_MAP


def fetch_futures_basis() -> dict:
    """获取股指期货主力合约升贴水（若有）"""
    if not HAS_AK:
        return {}
    result = {}
    try:
        # IF沪深300、IC中证500 主力合约
        for code, name in [("IF", "沪深300期货"), ("IC", "中证500期货")]:
            df = ak.stock_zh_futures_daily(symbol=code)
            if df is not None and not df.empty:
                latest = df.iloc[-1]
                # 升贴水 = 期货-现货，需结合现货指数；此处简化为展示期货涨跌
                result[code] = {
                    "name": name,
                    "close": float(latest.get("收盘", latest.get("收盘价", 0))),
                    "change_pct": float(latest.get("涨跌幅", 0)),
                }
    except Exception:
        pass
    return result


def run():
    now = datetime.now().strftime("%H:%M")
    today = date.today().strftime("%Y-%m-%d")

    print(f"\n{'='*55}")
    print(f"📋 早盘定性判断 — {today} {now}")
    print(f"{'='*55}\n")

    # 1. 期货信号（若有）
    if HAS_AK:
        futures = fetch_futures_basis()
        if futures:
            print("📊 股指期货（主力合约）")
            for code, d in futures.items():
                pct = d.get("change_pct", 0)
                pct_str = f"{pct:+.2f}%" if pct else "-"
                hint = "机构偏多" if pct > 0.3 else ("机构偏空" if pct < -0.3 else "中性")
                print(f"  {d['name']}: {pct_str}  → {hint}")
            print()
    else:
        print("  （安装 akshare 可获取期货升贴水信号）\n")

    # 2. 早盘定性判断框架
    print("─" * 55)
    print("📋 早盘定性判断清单（手动填写）")
    print("─" * 55)
    print()
    print("【隔夜消息】")
    print("  □ 政策：有无凌晨/昨夜新政？利好/利空/中性")
    print("  □ 美股：纳指涨跌 ___%  → 科技情绪")
    print("  □ 汇率：离岸人民币 ___  → 北向资金压力")
    print()
    print("【竞价观察 9:15-9:25】")
    print("  □ 沪深300竞价：高开/平开/低开 ___%")
    print("  □ 竞价量：放量/缩量/持平")
    print("  □ 与期货方向是否一致？")
    print()
    print("【今日定调】")
    print("  综合评分（0-100）: ___  → 偏强(>60) / 震荡(40-60) / 偏弱(<40)")
    print("  情绪温度: 极冷 / 偏冷 / 中性 / 偏热 / 过热")
    print()
    print("【操作计划】")
    print("  计划买入：")
    for code in WATCHLIST_ETFS:
        print(f"    - {ETF_NAME_MAP.get(code, code)}({code})  触发条件___  仓位___%")
    print("  计划止损：")
    print("    - 跌破止损位 ___  → 无条件执行")
    print()
    print("【最大风险】")
    print("  今日需警惕：___")
    print()
    print("原则: 9:25前完成决策，9:30后只执行不临时改方向")
    print()


if __name__ == "__main__":
    run()

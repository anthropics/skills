"""
intraday_check.py - 午盘一键检查脚本（盘中监控）
运行时间：交易日 13:00-15:00 任意时刻
功能：拉取当前大盘、涨跌停、ETF折溢价，输出午盘操作清单
依赖：akshare（与 fetch_market_data 相同）
"""
import os
import sys
from datetime import datetime, date

try:
    import akshare as ak
except ImportError:
    print("❌ 请先安装 akshare: pip install akshare")
    sys.exit(1)

from config import (
    WATCHLIST_ETFS,
    ETF_NAME_MAP,
    INDEX_LIST,
    THRESHOLDS,
)


def get_index_spot() -> dict:
    """获取主要指数实时行情"""
    result = {}
    try:
        df = ak.stock_zh_index_spot_em()
        for symbol, name in INDEX_LIST.items():
            code = symbol.replace("sh", "").replace("sz", "")
            row = df[df["代码"] == code]
            if not row.empty:
                result[symbol] = {
                    "name": name,
                    "price": float(row["最新价"].values[0]),
                    "change_pct": float(row["涨跌幅"].values[0]),
                    "amount": float(row["成交额"].values[0]) / 1e8,
                }
    except Exception as e:
        print(f"  ⚠️ 指数数据获取失败: {e}")
    return result


def get_limit_up_down() -> dict:
    """获取涨跌停统计"""
    result = {"limit_up": 0, "limit_down": 0, "ratio": 0.0}
    try:
        today_str = date.today().strftime("%Y%m%d")
        df_up = ak.stock_zt_pool_em(date=today_str)
        df_down = ak.stock_zt_pool_dtgc_em(date=today_str)
        result["limit_up"] = len(df_up)
        result["limit_down"] = len(df_down)
        if result["limit_down"] > 0:
            result["ratio"] = round(result["limit_up"] / result["limit_down"], 2)
        else:
            result["ratio"] = float(result["limit_up"]) if result["limit_up"] > 0 else 1.0
    except Exception as e:
        print(f"  ⚠️ 涨跌停数据获取失败: {e}")
    return result


def get_etf_spot(etf_codes: list) -> list:
    """获取关注ETF实时行情（含折溢价，若接口支持）"""
    result = []
    try:
        df = ak.fund_etf_spot_em()
        premium_col = None
        for c in ["溢折率", "折溢价率", "折溢价"]:
            if c in df.columns:
                premium_col = c
                break
        for code in etf_codes:
            name = ETF_NAME_MAP.get(code, code)
            row = df[df["代码"] == code]
            item = {"code": code, "name": name, "price": None, "change_pct": None, "premium_pct": None, "alert": ""}
            if not row.empty:
                item["price"] = float(row["最新价"].values[0])
                item["change_pct"] = float(row["涨跌幅"].values[0])
                if premium_col:
                    try:
                        item["premium_pct"] = float(row[premium_col].values[0])
                        thresh = THRESHOLDS["etf_premium_pct"]
                        if item["premium_pct"] > thresh:
                            item["alert"] = f"⚠️ 溢价>{thresh}% 停止买入"
                        elif item["premium_pct"] < -thresh:
                            item["alert"] = f"⚠️ 折价>{thresh}% 谨慎买入"
                    except (ValueError, TypeError):
                        pass
            result.append(item)
    except Exception as e:
        print(f"  ⚠️ ETF行情获取失败: {e}")
        for code in etf_codes:
            result.append({"code": code, "name": ETF_NAME_MAP.get(code, code), "alert": "数据不可用"})
    return result


def check_alerts(index_data: dict, limit_data: dict) -> list:
    """生成预警"""
    alerts = []
    for sym, d in index_data.items():
        if d.get("change_pct") is not None and d["change_pct"] <= -THRESHOLDS["index_drop_pct"]:
            alerts.append(f"🔴 {d['name']} 跌 {d['change_pct']:.2f}% 超阈值 → 检查止损，暂停新仓")
    if limit_data.get("ratio", 1) > 3.0:
        alerts.append(f"🟠 涨跌停比 {limit_data['ratio']} 情绪偏热 → 不追高")
    elif limit_data.get("ratio", 1) < 0.5 and limit_data.get("limit_up", 0) > 0:
        alerts.append(f"🟢 涨跌停比 {limit_data['ratio']} 市场极冷 → 关注政策催化")
    return alerts


def run():
    now = datetime.now().strftime("%H:%M")
    today = date.today().strftime("%Y-%m-%d")

    print(f"\n{'='*55}")
    print(f"📡 午盘一键检查 — {today} {now}")
    print(f"{'='*55}\n")

    # 1. 指数
    print("📊 大盘实时")
    index_data = get_index_spot()
    if index_data:
        for sym, d in index_data.items():
            pct = d.get("change_pct")
            amt = d.get("amount", 0)
            pct_str = f"{pct:+.2f}%" if pct is not None else "-"
            print(f"  {d['name']}: {pct_str}  成交额 {amt:.0f}亿")
    else:
        print("  数据获取失败")
    print()

    # 2. 涨跌停
    print("📈 涨跌停")
    limit_data = get_limit_up_down()
    print(f"  涨停: {limit_data['limit_up']}  跌停: {limit_data['limit_down']}  比值: {limit_data['ratio']}")
    print()

    # 3. 关注ETF
    print("📦 关注ETF")
    etf_list = get_etf_spot(WATCHLIST_ETFS)
    for e in etf_list:
        pct = e.get("change_pct")
        prem = e.get("premium_pct")
        pct_str = f"{pct:+.2f}%" if pct is not None else "-"
        prem_str = f"{prem:+.2f}%" if prem is not None else "-"
        alert = e.get("alert", "")
        print(f"  {e['name']}({e['code']}): {pct_str}  折溢价 {prem_str}  {alert}")
    print()

    # 4. 预警
    alerts = check_alerts(index_data, limit_data)
    if alerts:
        print("⚠️ 预警")
        for a in alerts:
            print(f"  {a}")
        print()

    # 5. 午盘操作清单
    print("─" * 55)
    print("📋 午盘操作清单（参考 intraday-monitor）")
    print("─" * 55)
    print("  □ 大盘是否延续早盘方向？")
    print("  □ ETF折溢价 >1.5%？→ 停止买入")
    print("  □ 指数单日跌>2%？→ 检查止损，暂停新仓")
    print("  □ 必须止损的ETF？→ 14:50前完成")
    print("  □ 计划买入未执行？→ 评估今日尾盘 vs 明日")
    print("  □ 动态止盈是否触发？→ 按3段式执行")
    print()
    print("原则: 午盘不做新决策，只执行盘前计划；波动±1%无需操作")
    print()


if __name__ == "__main__":
    run()

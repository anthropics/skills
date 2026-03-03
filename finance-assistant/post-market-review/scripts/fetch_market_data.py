# -*- coding: utf-8 -*-
"""
fetch_market_data.py - 采集A股大盘总览数据
运行时间：每个交易日 15:30 后
数据来源：akshare 新浪/东方财富
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import akshare as ak
import warnings
warnings.filterwarnings('ignore')

import json
import os
from datetime import datetime, date
from config import INDEX_LIST, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    """支持 --date YYYY-MM-DD 命令行参数"""
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


def fetch_index_data() -> dict:
    """
    采集主要指数收盘数据。
    策略：stock_zh_index_spot_sina() 一次调用获全量，再按代码过滤。
    配置中 INDEX_LIST 的键格式为 'sh000300'、'sz399006'，与新浪返回的 '代码' 列一致。
    """
    result = {}
    print("📊 采集指数数据（新浪源）...")

    try:
        df = ak.stock_zh_index_spot_sina()
        cols = list(df.columns)
        # 列序：代码(0) 名称(1) 最新价(2) 涨跌额(3) 涨跌幅(4) 昨收(5) 今开(6) 最高(7) 最低(8) 成交量(9) 成交额(10)
        col_code = cols[0]
        col_name = cols[1]
        col_close = cols[2]
        col_chg_pct = cols[4]
        col_vol = cols[9]
        col_amt = cols[10]

        for symbol in INDEX_LIST:
            name = INDEX_LIST[symbol]
            row = df[df[col_code] == symbol]
            if not row.empty:
                r = row.iloc[0]
                result[symbol] = {
                    "name": name,
                    "close": float(r[col_close]),
                    "change_pct": float(r[col_chg_pct]),
                    "volume": float(r[col_vol]) if r[col_vol] else 0,
                    "amount": float(r[col_amt]) if r[col_amt] else 0,
                }
                sign = "+" if result[symbol]["change_pct"] >= 0 else ""
                print(f"  ✅ {name}: {sign}{result[symbol]['change_pct']:.2f}%  "
                      f"收盘{result[symbol]['close']}")
            else:
                print(f"  ⚠️ {name}({symbol}) 未找到")
                result[symbol] = {"name": name, "error": "未找到"}

    except Exception as e:
        print(f"  ❌ 指数数据采集失败: {e}")
        for symbol, name in INDEX_LIST.items():
            result[symbol] = {"name": name, "error": str(e)}

    return result


def fetch_limit_up_down() -> dict:
    """采集涨跌停统计"""
    print("📊 采集涨跌停数据...")
    result = {"limit_up": 0, "limit_down": 0, "ratio": 0.0}

    try:
        today_str = date.today().strftime("%Y%m%d")
        df_up = ak.stock_zt_pool_em(date=today_str)
        result["limit_up"] = len(df_up)
        df_down = ak.stock_zt_pool_dtgc_em(date=today_str)
        result["limit_down"] = len(df_down)
        if result["limit_down"] > 0:
            result["ratio"] = round(result["limit_up"] / result["limit_down"], 2)
        print(f"  ✅ 涨停: {result['limit_up']} | 跌停: {result['limit_down']} | 比值: {result['ratio']}")
    except Exception as e:
        print(f"  ⚠️ 涨跌停数据获取失败: {e}")

    return result


def fetch_market_breadth() -> dict:
    """采集市场情绪宽度数据"""
    print("📊 采集市场宽度数据...")
    result = {}
    try:
        df = ak.stock_market_activity_legu()
        for _, row in df.iterrows():
            result[str(row.iloc[0])] = str(row.iloc[1])
        print(f"  ✅ 市场宽度数据采集完成，共{len(result)}项")
    except Exception as e:
        print(f"  ⚠️ 市场宽度数据获取失败（非关键项，跳过）: {e}")
    return result


def classify_emotion(ratio: float) -> dict:
    """根据涨跌停比对市场情绪评级"""
    if ratio >= 10:
        return {"label": "🔥 极热", "desc": "涨停数量是跌停10倍以上，短期追高风险极大，注意回调", "action": "止盈优先，不追高"}
    elif ratio >= 5:
        return {"label": "🟠 过热", "desc": "情绪火热，赚钱效应强，但追高风险大", "action": "减仓止盈，设置移动止盈"}
    elif ratio >= 2:
        return {"label": "🟡 偏热", "desc": "多方占优，市场活跃，可持仓不追高", "action": "持仓观望，不加仓追高"}
    elif ratio >= 0.8:
        return {"label": "⚪ 中性", "desc": "多空均衡，震荡行情为主", "action": "正常操作，关注个股分化"}
    elif ratio >= 0.4:
        return {"label": "🔵 偏冷", "desc": "空方占优，市场谨慎", "action": "轻仓或观望，等待企稳信号"}
    else:
        return {"label": "🟢 极冷", "desc": "恐慌情绪高，通常是逆向布局窗口", "action": "关注政策信号，分批建仓"}


def check_alerts(index_data: dict, limit_data: dict) -> list:
    """检查是否触发预警条件"""
    alerts = []
    for symbol, data in index_data.items():
        if "change_pct" in data:
            if data["change_pct"] <= -THRESHOLDS["index_drop_pct"]:
                alerts.append({
                    "level": "🔴 高风险",
                    "msg": f"{data['name']} 今日下跌 {data['change_pct']:.2f}%，超过预警阈值",
                    "action": "检查止损位，暂停新建仓"
                })

    ratio = limit_data.get("ratio", 1.0)
    emotion = classify_emotion(ratio)
    if ratio >= 5 or ratio <= 0.4:
        alerts.append({
            "level": emotion["label"],
            "msg": f"涨跌停比 {ratio}，{emotion['desc']}",
            "action": emotion["action"]
        })

    return alerts


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"🌙 盘后大盘数据采集 - {today}")
    print(f"{'='*50}\n")

    index_data = fetch_index_data()
    limit_data = fetch_limit_up_down()
    breadth_data = fetch_market_breadth()

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "index_data": index_data,
        "limit_data": limit_data,
        "market_breadth": breadth_data,
        "alerts": check_alerts(index_data, limit_data),
        "emotion": classify_emotion(limit_data.get("ratio", 1.0)),
    }

    output_file = os.path.join(output_path, "market_data.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"\n✅ 大盘数据已保存至: {output_file}")
    if result["alerts"]:
        print(f"\n⚠️ 今日预警 ({len(result['alerts'])}条):")
        for a in result["alerts"]:
            print(f"  {a['level']}: {a['msg']}")
            print(f"  → {a['action']}")

    return result


if __name__ == "__main__":
    run()

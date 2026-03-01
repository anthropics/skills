"""
fetch_market_data.py - 采集A股大盘总览数据
运行时间：每个交易日 15:30 后
数据来源：akshare（免费A股数据库）
"""
import akshare as ak
import pandas as pd
import json
import os
from datetime import datetime, date
from config import INDEX_LIST, OUTPUT_DIR, THRESHOLDS


def get_today_str():
    return date.today().strftime("%Y-%m-%d")


def ensure_output_dir(date_str: str) -> str:
    path = os.path.join(OUTPUT_DIR, date_str)
    os.makedirs(path, exist_ok=True)
    return path


def fetch_index_data() -> dict:
    """采集主要指数收盘数据"""
    result = {}
    print("📊 采集指数数据...")

    for symbol, name in INDEX_LIST.items():
        try:
            # 使用 akshare 获取指数实时行情
            df = ak.stock_zh_index_spot_em()
            row = df[df["代码"] == symbol.replace("sh", "").replace("sz", "")]
            if not row.empty:
                result[symbol] = {
                    "name": name,
                    "close": float(row["最新价"].values[0]),
                    "change_pct": float(row["涨跌幅"].values[0]),
                    "volume": float(row["成交量"].values[0]),
                    "amount": float(row["成交额"].values[0]),
                }
                print(f"  ✅ {name}: {result[symbol]['change_pct']:+.2f}%")
        except Exception as e:
            print(f"  ⚠️ {name} 获取失败: {e}")
            result[symbol] = {"name": name, "error": str(e)}

    return result


def fetch_limit_up_down() -> dict:
    """采集涨跌停统计"""
    print("📊 采集涨跌停数据...")
    result = {"limit_up": 0, "limit_down": 0, "ratio": 0.0}

    try:
        # 涨停股池
        df_up = ak.stock_zt_pool_em(date=date.today().strftime("%Y%m%d"))
        result["limit_up"] = len(df_up)

        # 跌停股池
        df_down = ak.stock_zt_pool_dtgc_em(date=date.today().strftime("%Y%m%d"))
        result["limit_down"] = len(df_down)

        if result["limit_down"] > 0:
            result["ratio"] = round(result["limit_up"] / result["limit_down"], 2)

        print(f"  ✅ 涨停: {result['limit_up']} | 跌停: {result['limit_down']} | 比值: {result['ratio']}")
    except Exception as e:
        print(f"  ⚠️ 涨跌停数据获取失败: {e}")

    return result


def fetch_market_breadth() -> dict:
    """采集市场情绪宽度数据（上涨/下跌家数、换手率等）"""
    print("📊 采集市场宽度数据...")
    result = {}

    try:
        df = ak.stock_market_activity_legu()
        # 提取关键字段
        for _, row in df.iterrows():
            result[row.get("指标", "")] = row.get("数值", "")
        print(f"  ✅ 市场宽度数据采集完成，共{len(result)}项")
    except Exception as e:
        print(f"  ⚠️ 市场宽度数据获取失败: {e}")

    return result


def check_alerts(index_data: dict, limit_data: dict) -> list:
    """检查是否触发预警条件"""
    alerts = []

    # 检查指数大幅下跌
    for symbol, data in index_data.items():
        if "change_pct" in data:
            if data["change_pct"] <= -THRESHOLDS["index_drop_pct"]:
                alerts.append({
                    "level": "🔴 高风险",
                    "msg": f"{data['name']} 今日下跌 {data['change_pct']:.2f}%，超过预警阈值！",
                    "action": "检查止损位，暂停新建仓"
                })

    # 检查涨跌停比（情绪过热/过冷）
    if limit_data.get("ratio", 0) > 3.0:
        alerts.append({
            "level": "🟠 情绪过热",
            "msg": f"涨跌停比 {limit_data['ratio']}，情绪偏热，追高需谨慎",
            "action": "减仓止盈，不追高"
        })
    elif limit_data.get("ratio", 1) < 0.5 and limit_data.get("limit_up", 0) > 0:
        alerts.append({
            "level": "🟢 建仓机会",
            "msg": f"涨跌停比 {limit_data['ratio']}，市场极冷，关注政策催化后的建仓机会",
            "action": "关注政策信号，等待买点"
        })

    return alerts


def run():
    today = get_today_str()
    output_path = ensure_output_dir(today)

    print(f"\n{'='*50}")
    print(f"🌙 盘后大盘数据采集 - {today}")
    print(f"{'='*50}\n")

    result = {
        "date": today,
        "timestamp": datetime.now().isoformat(),
        "index_data": fetch_index_data(),
        "limit_data": fetch_limit_up_down(),
        "market_breadth": fetch_market_breadth(),
    }

    # 生成预警
    result["alerts"] = check_alerts(result["index_data"], result["limit_data"])

    # 保存 JSON
    output_file = os.path.join(output_path, "market_data.json")
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(f"\n✅ 大盘数据已保存至: {output_file}")

    if result["alerts"]:
        print(f"\n⚠️ 今日预警 ({len(result['alerts'])}条):")
        for alert in result["alerts"]:
            print(f"  {alert['level']}: {alert['msg']}")
            print(f"  → 建议操作: {alert['action']}")

    return result


if __name__ == "__main__":
    run()

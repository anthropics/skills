"""
generate_report.py - 汇总所有盘后数据，生成 Markdown 复盘报告
运行时间：每个交易日 18:00（在所有采集脚本运行完后执行）
也可以单独运行（会先触发各采集脚本）
"""
import json
import os
import sys
from datetime import datetime, date

from config import OUTPUT_DIR, WATCHLIST_ETFS, ETF_NAME_MAP


def get_today_str():
    return date.today().strftime("%Y-%m-%d")


def load_json(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"  ⚠️ 无法读取 {path}: {e}")
        return {}


def run_collectors():
    """运行所有数据采集脚本"""
    print("🔄 开始运行所有数据采集脚本...\n")
    import fetch_market_data
    import fetch_fund_flow
    import fetch_etf_shares

    fetch_market_data.run()
    fetch_fund_flow.run()
    fetch_etf_shares.run()
    print("\n✅ 所有数据采集完成\n")


def format_change_pct(val) -> str:
    try:
        v = float(val)
        prefix = "+" if v >= 0 else ""
        return f"{prefix}{v:.2f}%"
    except Exception:
        return str(val)


def generate_markdown(today: str, market: dict, fund: dict, shares: dict) -> str:
    lines = []
    now = datetime.now().strftime("%Y-%m-%d %H:%M")

    lines.append(f"# 🌙 盘后复盘报告 — {today}")
    lines.append(f"\n> 报告生成时间：{now}\n")
    lines.append("---\n")

    # ── 一、大盘总览 ──────────────────────────────────────────────────
    lines.append("## 📊 一、今日大盘总览\n")

    index_data = market.get("index_data", {})
    if index_data:
        lines.append("| 指数 | 涨跌幅 | 成交额 |")
        lines.append("|------|--------|--------|")
        for sym, d in index_data.items():
            if "change_pct" in d:
                pct = format_change_pct(d["change_pct"])
                amt = f'{d.get("amount", 0) / 1e8:.0f}亿' if d.get("amount") else "-"
                lines.append(f"| {d['name']} | {pct} | {amt} |")
        lines.append("")

    limit = market.get("limit_data", {})
    if limit:
        lines.append(f"- **涨停板**：{limit.get('limit_up', '-')} 只")
        lines.append(f"- **跌停板**：{limit.get('limit_down', '-')} 只")
        lines.append(f"- **涨跌停比**：{limit.get('ratio', '-')}")
        lines.append("")

    # 情绪判断
    ratio = limit.get("ratio", 1.0) if limit else 1.0
    if ratio > 2.0:
        emotion = "🟠 **偏热** — 涨停板数量显著多于跌停板，追高风险加大"
    elif ratio > 1.4:
        emotion = "🟡 **偏多** — 多方占优，可适度持仓"
    elif ratio > 0.6:
        emotion = "⚪ **中性** — 多空均衡，震荡行情"
    elif ratio > 0.3:
        emotion = "🔵 **偏冷** — 空方略占优，谨慎操作"
    else:
        emotion = "🟢 **极冷** — 恐慌情绪高，逆向布局机会关注政策信号"
    lines.append(f"**市场情绪评级**：{emotion}\n")

    # 预警
    alerts = market.get("alerts", [])
    if alerts:
        lines.append("### ⚠️ 自动预警\n")
        for a in alerts:
            lines.append(f"- {a.get('level', '')}：{a.get('msg', '')}")
            lines.append(f"  - 建议操作：{a.get('action', '')}")
        lines.append("")

    lines.append("---\n")

    # ── 二、资金流向 ───────────────────────────────────────────────────
    lines.append("## 💰 二、主力资金流向\n")

    sector_top = fund.get("sector_top10", [])
    if sector_top:
        lines.append("### 板块资金 TOP 5 净流入\n")
        lines.append("| 排名 | 板块 | 净流入 | 涨跌幅 |")
        lines.append("|------|------|--------|--------|")
        for s in sector_top[:5]:
            lines.append(f"| {s.get('rank', '-')} | {s.get('sector', '-')} | {s.get('net_flow', '-')} | {s.get('change_pct', '-')} |")
        lines.append("")

        summary = fund.get("summary", {})
        hot = summary.get("hottest_sectors", [])
        cold = summary.get("coldest_sectors", [])
        if hot:
            lines.append(f"📈 **今日资金主线**：{' / '.join(hot)}")
        if cold:
            lines.append(f"📉 **今日资金回避**：{' / '.join(cold)}")
        lines.append("")

    lines.append("---\n")

    # ── 三、持仓ETF份额变化 ────────────────────────────────────────────
    lines.append("## 📦 三、持仓ETF份额变化（机构行为）\n")

    etf_shares_list = shares.get("etf_shares", [])
    if etf_shares_list:
        lines.append("| ETF | 份额变化% | 信号 | 评分影响 |")
        lines.append("|-----|---------|------|---------|")
        for e in etf_shares_list:
            name = e.get("name", e.get("code", "-"))
            chg = f"{e.get('change_pct', 0):+.2f}%" if e.get("change_pct") is not None else "数据不可用"
            signal = e.get("signal", "-")
            score = e.get("score_impact", 0)
            score_str = f"{score:+d}分" if score != 0 else "0"
            lines.append(f"| {name} | {chg} | {signal} | {score_str} |")
        lines.append("")

    # 强信号汇总
    buy_signals = shares.get("summary", {}).get("strong_buy_signal", [])
    sell_signals = shares.get("summary", {}).get("strong_sell_signal", [])
    if buy_signals:
        lines.append(f"🟢 **机构大幅申购（看多信号）**：{', '.join(buy_signals)}")
    if sell_signals:
        lines.append(f"🔴 **机构大幅赎回（看空信号）**：{', '.join(sell_signals)}")
    lines.append("")
    lines.append("---\n")

    # ── 四、操作日志（手动填写区）─────────────────────────────────────
    lines.append("## 📝 四、今日操作日志（手动填写）\n")
    lines.append("| ETF | 计划操作 | 实际操作 | 执行价 | 结果 |")
    lines.append("|-----|---------|---------|-------|------|")
    for code in WATCHLIST_ETFS:
        name = ETF_NAME_MAP.get(code, code)
        lines.append(f"| {name}({code}) | - | - | - | - |")
    lines.append("")
    lines.append("**今日做对了**：\n\n1. \n\n**今日做错了**：\n\n1. \n")
    lines.append("---\n")

    # ── 五、明日操作计划（手动填写区）────────────────────────────────
    lines.append("## 📅 五、明日操作计划（手动填写）\n")
    lines.append("**市场预判**：【偏强/震荡/偏弱】\n")
    lines.append("**最重要信号**：\n")
    lines.append("| ETF | 触发条件 | 计划仓位 | 止损位 |")
    lines.append("|-----|---------|---------|-------|")
    lines.append("| - | - | - | - |")
    lines.append("")
    lines.append("---\n")

    # ── 六、评分更新记录 ───────────────────────────────────────────────
    lines.append("## 🔄 六、评分更新记录\n")
    lines.append("| ETF | 原评分 | 新评分 | 变化原因 |")
    lines.append("|-----|--------|--------|---------|")
    for code in WATCHLIST_ETFS:
        name = ETF_NAME_MAP.get(code, code)
        lines.append(f"| {name} | - | - | - |")
    lines.append("")
    lines.append("---\n")

    lines.append("## ⚖️ 免责声明\n")
    lines.append("本报告基于公开数据自动生成，仅供个人投资研究参考，不构成投资建议。\n")

    return "\n".join(lines)


def run(force_collect: bool = False):
    today = get_today_str()
    today_dir = os.path.join(OUTPUT_DIR, today)
    os.makedirs(today_dir, exist_ok=True)

    # 检查是否需要先运行采集脚本
    market_file = os.path.join(today_dir, "market_data.json")
    fund_file = os.path.join(today_dir, "fund_flow.json")
    shares_file = os.path.join(today_dir, "etf_shares.json")

    if force_collect or not all(os.path.exists(f) for f in [market_file, fund_file, shares_file]):
        run_collectors()

    print(f"\n{'='*50}")
    print(f"📋 生成复盘报告 - {today}")
    print(f"{'='*50}\n")

    # 加载数据
    market = load_json(market_file)
    fund = load_json(fund_file)
    shares = load_json(shares_file)

    # 生成 Markdown
    md_content = generate_markdown(today, market, fund, shares)

    output_file = os.path.join(today_dir, f"review_{today}.md")
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(md_content)

    print(f"✅ 复盘报告已生成: {output_file}")
    print(f"\n📂 今日数据目录: {today_dir}")
    print("   ├── market_data.json   （大盘数据）")
    print("   ├── fund_flow.json      （资金流向）")
    print("   ├── etf_shares.json     （ETF份额）")
    print(f"   └── review_{today}.md  （复盘报告）")

    return output_file


if __name__ == "__main__":
    force = "--force" in sys.argv
    run(force_collect=force)

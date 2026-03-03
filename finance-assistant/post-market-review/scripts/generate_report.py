# -*- coding: utf-8 -*-
"""
generate_report.py - 汇总所有盘后数据，生成专业 Markdown 复盘报告
运行时间：每个交易日 18:00（在所有采集脚本运行完后执行）
也可以单独运行（会先触发各采集脚本）
"""
import sys
sys.stdout.reconfigure(encoding='utf-8')

import json
import os
import glob
from datetime import datetime, date
from config import OUTPUT_DIR, REPORTS_DIR, WATCHLIST_ETFS, ETF_NAME_MAP, BASE_DIR


def get_today_str():
    return date.today().strftime("%Y-%m-%d")


def load_json(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"  ⚠️ 无法读取 {path}: {e}")
        return {}


def load_holdings_snapshot(today: str) -> dict:
    """加载今日持仓快照（由 sync_holdings.py 生成）"""
    snap_path = os.path.join(REPORTS_DIR, f"{today}-holdings-snapshot.json")
    if os.path.exists(snap_path):
        return load_json(snap_path)
    return {}


def load_operations_log(today: str) -> list:
    """加载今日操作记录（由 agent 交互引导后写入）"""
    ops_path = os.path.join(OUTPUT_DIR, today, "operations.json")
    if os.path.exists(ops_path):
        return load_json(ops_path).get("operations", [])
    return []


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


def fmt_pct(val, plus=True) -> str:
    try:
        v = float(val)
        prefix = "+" if plus and v >= 0 else ""
        return f"{prefix}{v:.2f}%"
    except Exception:
        return "-"


def fmt_yuan_billion(val) -> str:
    """元 → 亿元"""
    try:
        v = float(val)
        return f"{v/1e8:+.1f}亿"
    except Exception:
        return "-"


def fmt_amount(val) -> str:
    """大数字显示为亿"""
    try:
        v = abs(float(val))
        if v >= 1e8:
            return f"{v/1e8:.0f}亿"
        elif v >= 1e4:
            return f"{v/1e4:.0f}万"
        return str(int(v))
    except Exception:
        return "-"


def score_badge(score: int) -> str:
    if score >= 17:
        return f"**+{score}** 🔥"
    elif score >= 11:
        return f"**+{score}** 🟢"
    elif score >= 5:
        return f"+{score} 💚"
    elif score > 0:
        return f"+{score}"
    elif score == 0:
        return "0"
    elif score > -8:
        return f"{score} 🟠"
    elif score > -14:
        return f"**{score}** 🔴"
    else:
        return f"**{score}** 🚨"


def build_index_section(market: dict) -> list:
    lines = []
    lines.append("## 一、今日大盘总览\n")

    index_data = market.get("index_data", {})
    if index_data:
        lines.append("| 指数 | 收盘价 | 涨跌幅 | 成交额 |")
        lines.append("|------|--------|--------|--------|")
        for sym, d in index_data.items():
            if "change_pct" in d:
                pct = fmt_pct(d["change_pct"])
                amt = fmt_amount(d.get("amount", 0)) if d.get("amount") else "-"
                close = f"{d.get('close', 0):.2f}"
                emoji = "🟢" if d["change_pct"] >= 0 else "🔴"
                lines.append(f"| {emoji} {d['name']} | {close} | {pct} | {amt} |")
            else:
                lines.append(f"| ⚠️ {d.get('name', sym)} | - | 获取失败 | - |")
        lines.append("")

    limit = market.get("limit_data", {})
    if limit:
        ratio = limit.get("ratio", 0)
        lines.append(f"- **涨停板**：{limit.get('limit_up', '-')} 只  |  **跌停板**：{limit.get('limit_down', '-')} 只  |  **涨跌停比**：{ratio}")
        lines.append("")

    emotion = market.get("emotion", {})
    if emotion:
        lines.append(f"> **市场情绪**：{emotion.get('label', '-')}  — {emotion.get('desc', '')}")
        lines.append(f"> **建议操作方向**：{emotion.get('action', '-')}")
        lines.append("")

    return lines


def build_fund_flow_section(fund: dict) -> list:
    lines = []
    lines.append("## 二、今日主力资金流向\n")

    # 全市场
    mkt = fund.get("market_total_flow", {})
    main_raw = mkt.get("main_net_flow")
    if mkt and main_raw not in (None, "", "None"):
        try:
            main = float(main_raw)
        except (ValueError, TypeError):
            main = None
    else:
        main = None
    if mkt and main is not None:
        pct = float(mkt.get("main_net_flow_pct") or 0)
        small_raw = mkt.get("small_net")
        small = float(small_raw) if small_raw not in (None, "", "None") else 0
        sh_pct = float(mkt.get("sh_change_pct") or 0)
        sz_pct = float(mkt.get("sz_change_pct") or 0)
        direction = "🟢 净流入" if main >= 0 else "🔴 净流出"
        lines.append(f"**全市场主力资金**：{direction} {fmt_yuan_billion(main)} ({pct:+.2f}%)")
        lines.append(f"**散户资金**：{'净买入' if small >= 0 else '净卖出'} {fmt_yuan_billion(abs(small))}"
                     f"  |  上证: {fmt_pct(sh_pct)}  深证: {fmt_pct(sz_pct)}")
        lines.append("")

        # 智能解读
        if main < -1e10:  # 流出超过100亿
            lines.append("> ⚠️ 主力今日大幅净流出，主力在出货或调仓，短期需谨慎追高。")
        elif main < 0 and small > 0:
            lines.append("> 📌 主力净流出、散户净买入 → 典型「主力出货、散户接盘」格局，注意风险。")
        elif main > 0 and small < 0:
            lines.append("> ✅ 主力净流入、散户净卖出 → 主力在低吸，信号偏正面。")
        lines.append("")

    # 行业资金 TOP5
    industry_top = fund.get("industry_top10", [])
    industry_bot = fund.get("industry_bottom5", [])
    if industry_top:
        lines.append("### 行业资金 TOP 5 净流入\n")
        lines.append("| 行业 | 涨跌幅 | 净流入 | 领涨股 |")
        lines.append("|------|--------|--------|--------|")
        for s in industry_top[:5]:
            leader = f"{s.get('leader_stock', '-')} ({s.get('leader_change', 0):+.1f}%)" if s.get('leader_stock') else "-"
            lines.append(f"| 🟢 {s['sector']} | {fmt_pct(s.get('change_pct', 0))} | {s['net_billion']:+.1f}亿 | {leader} |")
        lines.append("")

    if industry_bot and len(industry_bot) > 0:
        lines.append("### 行业资金 TOP 5 净流出\n")
        lines.append("| 行业 | 涨跌幅 | 净流出 |")
        lines.append("|------|--------|--------|")
        for s in industry_bot:
            lines.append(f"| 🔴 {s['sector']} | {fmt_pct(s.get('change_pct', 0))} | {s['net_billion']:+.1f}亿 |")
        lines.append("")

    # 持仓ETF二级市场资金流向
    etf_flows = fund.get("etf_flows", [])
    valid_flows = [e for e in etf_flows if e.get("main_net_flow") is not None]
    if valid_flows:
        lines.append("### 持仓ETF · 二级市场主力资金\n")
        lines.append("| ETF | 今日涨跌 | 主力净流向 | 净占比 | 信号 |")
        lines.append("|-----|---------|-----------|--------|------|")
        for e in valid_flows:
            chg = fmt_pct(e.get("change_pct_day", 0))
            net = fmt_yuan_billion(e.get("main_net_flow", 0))
            net_pct = f"{e.get('main_net_flow_pct', 0):+.1f}%"
            lines.append(f"| {e['name']} | {chg} | {net} | {net_pct} | {e['signal']} |")
        lines.append("")

    return lines


def build_etf_shares_section(shares: dict) -> list:
    lines = []
    lines.append("## 三、机构行为 · ETF份额/活跃度变化\n")
    lines.append("> 份额变化幅度越大，机构行为越明显。评分按幅度差异化给分（非固定值）。\n")

    etf_list = shares.get("etf_shares", [])
    if etf_list:
        lines.append("| ETF | 变化幅度 | 信号 | 评分影响 |")
        lines.append("|-----|---------|------|---------|")
        for e in etf_list:
            name = e.get("name", e.get("code", "-"))
            if e.get("change_pct") is not None:
                chg = f"{e['change_pct']:+.1f}%"
            else:
                chg = "不可用"
            signal = e.get("signal", "-")
            score = e.get("score_impact", 0)
            lines.append(f"| {name} | {chg} | {signal} | {score_badge(score)} |")
        lines.append("")

    summary = shares.get("summary", {})
    extreme = summary.get("extreme_buy", [])
    strong_buy = summary.get("strong_buy", [])
    strong_sell = summary.get("strong_sell", [])
    moderate_sell = summary.get("moderate_sell", [])

    if extreme:
        lines.append(f"🔥 **极强申购（变化100%+）**：{', '.join(extreme)}")
    if strong_buy:
        lines.append(f"🟢 **大幅申购（变化20%+）**：{', '.join(strong_buy)}")
    if strong_sell:
        lines.append(f"🔴 **大幅赎回（需警惕）**：{', '.join(strong_sell)}")
    if moderate_sell:
        lines.append(f"🟠 **小幅赎回**：{', '.join(moderate_sell)}")
    lines.append("")

    return lines


def build_holdings_section(holdings: dict, fund: dict) -> list:
    lines = []
    if not holdings:
        return lines

    lines.append("## 四、持仓盈亏快照\n")

    fund_info = holdings.get("fund_info", {})
    if fund_info:
        total = fund_info.get("总资产", "-")
        mval = fund_info.get("证券市值", "-")
        avail = fund_info.get("可用资金", "-")
        day_pnl = fund_info.get("当日盈亏参考", "-")
        cum_pnl = fund_info.get("持仓盈亏", "-")
        export_time = fund_info.get("导出时间", "-")

        try:
            day_v = float(day_pnl)
            day_str = f"{'🟢' if day_v >= 0 else '🔴'} **{day_v:+.2f}元**"
        except Exception:
            day_str = day_pnl

        try:
            cum_v = float(cum_pnl)
            cum_str = f"{'🟢' if cum_v >= 0 else '🔴'} {cum_v:+.2f}元"
        except Exception:
            cum_str = cum_pnl

        lines.append(f"| 指标 | 数值 |")
        lines.append(f"|------|------|")
        lines.append(f"| 总资产 | {total}元 |")
        lines.append(f"| 证券市值 | {mval}元 |")
        lines.append(f"| 可用资金 | {avail}元 |")
        lines.append(f"| 当日盈亏 | {day_str} |")
        lines.append(f"| 累计盈亏 | {cum_str} |")
        lines.append(f"| 快照时间 | {export_time} |")
        lines.append("")

    # 持仓明细：与ETF资金流向数据结合，显示今日涨跌
    etf_flow_map = {}
    for e in fund.get("etf_flows", []):
        etf_flow_map[e["code"]] = e

    positions = sorted(holdings.get("holdings", []), key=lambda x: x.get("profit_pct", 0), reverse=True)
    if positions:
        lines.append("| ETF | 持仓量 | 均价 | 今收价 | 今涨跌 | 累计盈亏% | 市值 | 仓位 |")
        lines.append("|-----|------|------|--------|--------|---------|------|------|")
        for p in positions:
            code = p.get("code", "")
            name = p.get("name", code)
            qty = int(p.get("quantity", 0))
            avg = p.get("avg_buy", p.get("cost", 0))
            price = p.get("price", 0)
            pnl_pct = p.get("profit_pct", 0)
            mval = p.get("market_val", 0)
            pos_pct = p.get("position_pct", 0)

            # 今日涨跌从fund_flow取
            flow = etf_flow_map.get(code, {})
            day_chg = flow.get("change_pct_day")
            day_str = fmt_pct(day_chg) if day_chg is not None else "-"

            pnl_emoji = "🟢" if pnl_pct >= 0 else "🔴"
            day_emoji = ""
            if day_chg is not None:
                day_emoji = "↑" if day_chg > 0 else ("↓" if day_chg < 0 else "→")

            lines.append(f"| {name} | {qty:,} | {avg:.3f} | {price:.3f} | {day_emoji}{day_str} | {pnl_emoji}{pnl_pct:+.2f}% | {mval:.0f}元 | {pos_pct:.1f}% |")

        lines.append("")

    return lines


def build_signal_analysis(market: dict, fund: dict, shares: dict, holdings: dict) -> list:
    """核心模块：AI信号分析与解读"""
    lines = []
    lines.append("## 五、AI信号综合解读\n")

    # 收集关键信号
    signals = []
    warnings_list = []
    opportunities = []

    # 1. 大盘信号
    index_data = market.get("index_data", {})
    for sym, d in index_data.items():
        if "change_pct" in d:
            if d["change_pct"] <= -1.5:
                warnings_list.append(f"{d['name']}今日跌{d['change_pct']:.2f}%，宽基指数走弱")
            elif d["change_pct"] >= 1.5:
                opportunities.append(f"{d['name']}今日涨{d['change_pct']:.2f}%，板块机会增多")

    # 2. 情绪信号
    ratio = market.get("limit_data", {}).get("ratio", 1.0)
    if ratio >= 10:
        warnings_list.append(f"涨跌停比{ratio}，情绪极度过热，历史回测显示次日回调概率>60%")
    elif ratio <= 0.3:
        opportunities.append(f"涨跌停比仅{ratio}，市场极度悲观，可能是左侧布局窗口")

    # 3. 主力资金信号
    mkt_flow = fund.get("market_total_flow", {})
    main_flow = mkt_flow.get("main_net_flow")
    small_flow = mkt_flow.get("small_net")
    if main_flow is not None:
        if main_flow < -5e9:  # 流出50亿以上
            warnings_list.append(f"全市场主力净流出{abs(main_flow)/1e8:.0f}亿，机构在减仓")
        elif main_flow > 5e9:
            opportunities.append(f"全市场主力净流入{main_flow/1e8:.0f}亿，机构在积极增仓")
        # 主力vs散户背离
        if main_flow is not None and small_flow is not None:
            if main_flow < 0 and small_flow > 0:
                warnings_list.append("主力流出+散户流入 = 典型分歧格局，主力或在借散户接盘出货")

    # 4. ETF份额信号
    shares_list = shares.get("etf_shares", [])
    contradictions = []
    for e in shares_list:
        if e.get("score_impact") is None:
            continue
        score = e["score_impact"]
        # 找机构行为与价格的背离
        flow = {}
        for f in fund.get("etf_flows", []):
            if f["code"] == e["code"]:
                flow = f
                break
        day_chg = flow.get("change_pct_day")
        main_net = flow.get("main_net_flow")

        # 极强申购但二级市场主力净流出 → 背离
        if score >= 14 and main_net is not None and main_net < -1e7:
            contradictions.append(
                f"**{e['name']}**：份额+{e['change_pct']:.0f}%（机构一级市场大申购）"
                f"但二级市场主力净流出{abs(main_net)/1e8:.2f}亿 → "
                f"新资金通过ETF申购入场，但二级市场主力在借机减仓，短期谨慎"
            )

        # 大幅赎回但价格上涨 → 出货信号
        if score <= -11 and day_chg is not None and day_chg > 0.5:
            warnings_list.append(
                f"⚠️ **{e['name']}**：份额-{abs(e['change_pct']):.0f}%（机构赎回）但价格涨{day_chg:.1f}% → "
                f"机构借涨出货，小心追高"
            )

    # 5. 持仓风险信号
    positions = holdings.get("holdings", [])
    for p in positions:
        pnl = p.get("profit_pct", 0)
        pos = p.get("position_pct", 0)
        if pnl <= -10 and pos >= 3:
            warnings_list.append(f"**{p['name']}**：亏损{pnl:.1f}%，仓位{pos:.1f}%，已达止损考虑区间")
        elif pos >= 8:
            warnings_list.append(f"**{p['name']}**：仓位{pos:.1f}%，集中度较高，注意分散风险")

    # 组装输出
    if signals or opportunities or warnings_list or contradictions:
        if opportunities:
            lines.append("### ✅ 今日正面信号\n")
            for s in opportunities:
                lines.append(f"- {s}")
            lines.append("")

        if contradictions:
            lines.append("### 🔄 今日关键背离（需深度理解）\n")
            for c in contradictions:
                lines.append(f"- {c}")
            lines.append("")

        if warnings_list:
            lines.append("### ⚠️ 今日风险信号\n")
            for w in warnings_list:
                lines.append(f"- {w}")
            lines.append("")
    else:
        lines.append("*今日无显著异常信号，市场运行平稳。*\n")

    return lines


def build_operations_section(operations: list, today: str) -> list:
    lines = []
    lines.append("## 六、今日操作记录\n")

    if operations:
        lines.append("| ETF | 操作类型 | 数量 | 执行价 | 金额 | 备注 |")
        lines.append("|-----|---------|------|--------|------|------|")
        for op in operations:
            lines.append(
                f"| {op.get('name', op.get('code', '-'))} "
                f"| {op.get('type', '-')} "
                f"| {op.get('qty', '-')} "
                f"| {op.get('price', '-')} "
                f"| {op.get('amount', '-')} "
                f"| {op.get('note', '-')} |"
            )
        lines.append("")
    else:
        lines.append("*（今日无操作记录，或尚未通过导入命令更新）*\n")
        lines.append("> 💡 如有操作，可将东方财富导出的CSV发给Agent，指令：「导入今日操作记录」\n")

    lines.append("**今日做对了**：\n\n1. （填写）\n\n**今日做错了/漏执行**：\n\n1. （填写）\n")

    return lines


def build_tomorrow_plan(market: dict, fund: dict, shares: dict, holdings: dict) -> list:
    """基于今日数据自动生成明日操作建议框架"""
    lines = []
    lines.append("## 七、明日操作计划\n")

    # 自动推断市场倾向
    ratio = market.get("limit_data", {}).get("ratio", 1.0)
    main_flow = fund.get("market_total_flow", {}).get("main_net_flow", 0) or 0
    if ratio >= 5 and main_flow > 0:
        outlook = "偏强（情绪热+主力流入）"
    elif ratio >= 2 and main_flow >= 0:
        outlook = "震荡偏强"
    elif ratio >= 5 and main_flow < 0:
        outlook = "震荡（情绪热但主力流出，需警惕）"
    elif ratio <= 0.5:
        outlook = "偏弱（情绪冷）"
    else:
        outlook = "震荡（中性）"

    lines.append(f"**明日市场倾向预判**：{outlook}\n")

    # 自动生成关注列表：基于份额极强申购的ETF
    watch_buy = []
    watch_sell = []
    etf_flow_map = {e["code"]: e for e in fund.get("etf_flows", [])}

    for e in shares.get("etf_shares", []):
        score = e.get("score_impact", 0)
        code = e.get("code", "")
        name = e.get("name", code)
        flow = etf_flow_map.get(code, {})
        day_chg = flow.get("change_pct_day")

        # 极强申购+今日上涨 → 明日观察是否延续
        if score >= 14 and day_chg is not None and day_chg > 0:
            watch_buy.append({
                "name": name, "code": code,
                "reason": f"份额+{e['change_pct']:.0f}%，今日涨{day_chg:.1f}%，机构持续入场",
                "condition": "开盘后高开低走不超-1%则持有，低开需观察量能"
            })

        # 大幅赎回 → 关注止损
        if score <= -11:
            watch_sell.append({
                "name": name, "code": code,
                "reason": f"份额-{abs(e['change_pct']):.0f}%，机构减仓信号",
                "condition": "若明日继续跌>1%或放量下跌则减仓"
            })

    # 仓位重+亏损大的持仓 → 止损关注
    for p in holdings.get("holdings", []):
        if p.get("profit_pct", 0) <= -8 and p.get("position_pct", 0) >= 2:
            name = p.get("name", p.get("code", ""))
            code = p.get("code", "")
            if not any(w["code"] == code for w in watch_sell):
                watch_sell.append({
                    "name": name, "code": code,
                    "reason": f"累计亏损{p['profit_pct']:.1f}%，仓位{p['position_pct']:.1f}%",
                    "condition": f"止损线参考: {p.get('avg_buy',0)*0.92:.3f}（亏损8%止损）"
                })

    if watch_buy:
        lines.append("### 计划关注（持有/加仓条件）\n")
        lines.append("| ETF | 代码 | 信号依据 | 触发条件 |")
        lines.append("|-----|------|---------|---------|")
        for w in watch_buy[:5]:
            lines.append(f"| {w['name']} | {w['code']} | {w['reason']} | {w['condition']} |")
        lines.append("")

    if watch_sell:
        lines.append("### 计划止损/减仓关注\n")
        lines.append("| ETF | 代码 | 风险依据 | 触发条件 |")
        lines.append("|-----|------|---------|---------|")
        for w in watch_sell[:5]:
            lines.append(f"| {w['name']} | {w['code']} | {w['reason']} | {w['condition']} |")
        lines.append("")

    lines.append("**重点观察事项**（手动补充）：\n\n- \n\n**季节性/事件风险**：\n\n- \n")

    return lines


def generate_markdown(today: str, market: dict, fund: dict, shares: dict,
                      holdings: dict, operations: list) -> str:
    now = datetime.now().strftime("%Y-%m-%d %H:%M")
    lines = []

    lines.append(f"# 🌙 盘后复盘报告 · {today}\n")
    lines.append(f"> 生成时间：{now}  |  数据源：新浪财经 · 东方财富 · 持仓快照\n")
    lines.append("---\n")

    lines.extend(build_index_section(market))
    lines.append("---\n")
    lines.extend(build_fund_flow_section(fund))
    lines.append("---\n")
    lines.extend(build_etf_shares_section(shares))
    lines.append("---\n")
    lines.extend(build_holdings_section(holdings, fund))
    lines.append("---\n")
    lines.extend(build_signal_analysis(market, fund, shares, holdings))
    lines.append("---\n")
    lines.extend(build_operations_section(operations, today))
    lines.append("---\n")
    lines.extend(build_tomorrow_plan(market, fund, shares, holdings))
    lines.append("---\n")
    lines.append("*本报告基于公开数据自动生成，仅供个人研究参考，不构成投资建议。*\n")

    return "\n".join(lines)


def run(force_collect: bool = False, target_date: str = None):
    today = target_date if target_date else get_today_str()
    today_dir = os.path.join(OUTPUT_DIR, today)
    os.makedirs(today_dir, exist_ok=True)

    market_file = os.path.join(today_dir, "market_data.json")
    fund_file = os.path.join(today_dir, "fund_flow.json")
    shares_file = os.path.join(today_dir, "etf_shares.json")

    if force_collect or not all(os.path.exists(f) for f in [market_file, fund_file, shares_file]):
        run_collectors()

    print(f"\n{'='*50}")
    print(f"📋 生成复盘报告 - {today}")
    print(f"{'='*50}\n")

    market = load_json(market_file)
    fund = load_json(fund_file)
    shares = load_json(shares_file)
    holdings = load_holdings_snapshot(today)
    operations = load_operations_log(today)

    if not holdings:
        print("  ℹ️ 未找到持仓快照，盈亏部分将跳过（可运行 sync_holdings.py 更新）")

    md_content = generate_markdown(today, market, fund, shares, holdings, operations)

    # 同时写入 output 目录和 reports 目录
    output_file = os.path.join(today_dir, f"review_{today}.md")
    report_file = os.path.join(REPORTS_DIR, f"{today}-post-market.md")
    os.makedirs(REPORTS_DIR, exist_ok=True)

    for path in [output_file, report_file]:
        with open(path, "w", encoding="utf-8") as f:
            f.write(md_content)

    print(f"✅ 复盘报告已生成:")
    print(f"   · 脚本输出: {output_file}")
    print(f"   · 归档报告: {report_file}")

    return report_file


if __name__ == "__main__":
    import sys as _sys
    force = "--force" in _sys.argv
    # 支持 --date YYYY-MM-DD 参数指定复盘日期
    target = None
    if "--date" in _sys.argv:
        idx = _sys.argv.index("--date")
        if idx + 1 < len(_sys.argv):
            target = _sys.argv[idx + 1]
    run(force_collect=force, target_date=target)

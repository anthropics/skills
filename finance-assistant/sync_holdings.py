from __future__ import annotations
"""
sync_holdings.py - 东方财富导出文件 → 同步持仓到全局 config.py
==========================================================================

支持格式：
  [A] 东方财富账户持仓 CSV（首选）
      结构：第0行=资金字段名, 第1行=资金数值, 第2行=持仓表头, 第3行起=持仓数据

  [B] 东方财富自选股行情表 (.xls Tab分隔)
      结构：第0行=表头, 第1行起=行情数据（仅含价格/涨跌，无成本/市值）

使用方法：
  python sync_holdings.py                           # 自动搜索 holdings/ 最新文件
  python sync_holdings.py --file holdings/20260302.csv
  python sync_holdings.py --preview                 # 仅预览，不修改 config.py
==========================================================================
"""
import os
import re
import sys
import json
import glob
import argparse
from datetime import datetime

_ROOT        = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH  = os.path.join(_ROOT, "config.py")
SNAPSHOT_DIR = os.path.join(_ROOT, "reports")
HOLDINGS_DIR = os.path.join(_ROOT, "holdings")

# ── 持仓 CSV 字段别名（东方财富账户持仓 CSV）────────────────────────────────
POSITION_COLS = {
    "code":        ["证券代码", "股票代码", "基金代码"],
    "name":        ["证券名称", "股票名称", "基金名称"],
    "quantity":    ["持仓数量", "持有份额", "数量"],
    "avail_qty":   ["可用数量", "可用份额"],
    "cost":        ["成本价", "持仓成本", "成本"],
    "price":       ["最新价", "现价"],
    "profit_pct":  ["持仓盈亏比例", "盈亏比例", "盈亏%"],
    "day_profit":  ["当日盈亏", "当日盈亏参考"],
    "avg_buy":     ["买入均价"],
    "position_pct":["个股仓位"],
    "market_val":  ["最新市值", "参考市值", "市值"],
    "market":      ["交易市场"],
    "account":     ["股东账号"],
    "currency":    ["币种"],
}

# ── 自选股行情表字段别名（Tab XLS）────────────────────────────────────────
QUOTE_COLS = {
    "code":       ["代码", "证券代码"],
    "name":       ["名称", "证券名称"],
    "price":      ["最新", "最新价"],
    "change_pct": ["涨幅%", "涨跌幅"],
}


def detect_encoding(path: str) -> str:
    for enc in ["gbk", "gb2312", "utf-8-sig", "utf-8"]:
        try:
            with open(path, encoding=enc) as f:
                f.read(512)
            return enc
        except Exception:
            continue
    return "gbk"


def clean_code(raw: str) -> str:
    """提取6位纯数字代码，去掉 = "XXXXXX" 等 Excel 公式包装"""
    raw = str(raw).strip()
    m = re.search(r'"(\d{6})\s*"', raw)
    if m:
        return m.group(1)
    digits = re.sub(r"\D", "", raw)
    return digits if len(digits) == 6 else ""


def clean_float(raw) -> float | None:
    try:
        s = str(raw).replace(",", "").replace("亿", "").replace("万", "").strip()
        s = s.rstrip("%")
        if s in ("—", "-", "", "None", "/"):
            return None
        return float(s)
    except Exception:
        return None


def find_col_idx(headers: list, aliases: list) -> int | None:
    for alias in aliases:
        for i, h in enumerate(headers):
            if alias in str(h).strip():
                return i
    return None


# ─────────────────────────────────────────────────────────────────────────────
# 账户持仓 CSV 解析
# ─────────────────────────────────────────────────────────────────────────────

def parse_position_csv(path: str) -> tuple[list[dict], dict]:
    """
    解析东方财富账户持仓 CSV。
    返回 (holdings_list, fund_info)
      holdings_list: 每只ETF的持仓字典
      fund_info: 账户资金概览（总资产、可用资金等）
    """
    enc = detect_encoding(path)
    with open(path, encoding=enc, errors="replace") as f:
        lines = f.read().split("\n")

    # ── 第0行 = 资金字段名，第1行 = 资金数值 ──────────────────────────────
    fund_info = {}
    if len(lines) >= 2:
        fund_keys   = [k.strip() for k in lines[0].split(",")]
        fund_values = [v.strip() for v in lines[1].split(",")]
        for k, v in zip(fund_keys, fund_values):
            if k:
                fund_info[k] = v

    # ── 第2行 = 持仓表头，第3行起 = 持仓数据 ─────────────────────────────
    header_line_idx = 2   # 固定结构
    # 容错：如果第2行不包含"证券代码"，往后扫
    for i in range(2, min(6, len(lines))):
        if any(kw in lines[i] for kw in ["证券代码", "股票代码", "基金代码", "证券名称"]):
            header_line_idx = i
            break

    headers = [h.strip() for h in lines[header_line_idx].split(",")]
    col = {k: find_col_idx(headers, v) for k, v in POSITION_COLS.items()}

    if col["code"] is None:
        raise ValueError(f"找不到证券代码列。表头={headers}")

    holdings = []
    for raw_line in lines[header_line_idx + 1:]:
        raw_line = raw_line.strip()
        if not raw_line:
            continue
        parts = [p.strip() for p in raw_line.split(",")]

        code = clean_code(parts[col["code"]] if col["code"] < len(parts) else "")
        if not code:
            continue

        name = parts[col["name"]].strip() if col["name"] is not None and col["name"] < len(parts) else code

        def get(key: str) -> float | None:
            idx = col.get(key)
            if idx is None or idx >= len(parts):
                return None
            return clean_float(parts[idx])

        def get_str(key: str) -> str:
            idx = col.get(key)
            if idx is None or idx >= len(parts):
                return ""
            return parts[idx].strip()

        holdings.append({
            "code":         code,
            "name":         name,
            "quantity":     get("quantity"),
            "avail_qty":    get("avail_qty"),
            "cost":         get("cost"),
            "price":        get("price"),
            "profit_pct":   get("profit_pct"),
            "day_profit":   get("day_profit"),
            "avg_buy":      get("avg_buy"),
            "position_pct": get("position_pct"),
            "market_val":   get("market_val"),
            "market":       get_str("market"),
            "currency":     get_str("currency"),
        })

    return holdings, fund_info


# ─────────────────────────────────────────────────────────────────────────────
# 自选股行情 XLS 解析（Tab分隔）
# ─────────────────────────────────────────────────────────────────────────────

def parse_quote_xls(path: str) -> tuple[list[dict], dict]:
    """解析东方财富自选股导出的 Tab 分隔伪 XLS 行情表"""
    enc = detect_encoding(path)
    with open(path, encoding=enc, errors="replace") as f:
        lines = [l.rstrip("\n\r") for l in f.readlines()]

    header_idx = None
    for i, line in enumerate(lines):
        if any(kw in line for kw in ["代码", "证券代码"]):
            header_idx = i
            break
    if header_idx is None:
        raise ValueError("找不到表头行")

    headers = [h.strip() for h in lines[header_idx].split("\t")]
    col = {k: find_col_idx(headers, v) for k, v in QUOTE_COLS.items()}

    holdings = []
    for line in lines[header_idx + 1:]:
        if not line.strip():
            continue
        parts = [p.strip() for p in line.split("\t")]
        code = clean_code(parts[col["code"]] if col["code"] is not None and col["code"] < len(parts) else "")
        if not code:
            continue
        name = parts[col["name"]].strip() if col["name"] is not None and col["name"] < len(parts) else code

        def get(key: str) -> float | None:
            idx = col.get(key)
            if idx is None or idx >= len(parts):
                return None
            return clean_float(parts[idx])

        holdings.append({
            "code":         code,
            "name":         name,
            "quantity":     None,
            "avail_qty":    None,
            "cost":         None,
            "price":        get("price"),
            "profit_pct":   None,
            "day_profit":   None,
            "avg_buy":      None,
            "position_pct": None,
            "market_val":   None,
            "change_pct":   get("change_pct"),
        })

    return holdings, {}


# ─────────────────────────────────────────────────────────────────────────────
# 文件格式自动判断
# ─────────────────────────────────────────────────────────────────────────────

def parse_file(path: str) -> tuple[list[dict], dict, str]:
    """
    自动识别文件格式并解析。
    返回 (holdings, fund_info, table_type)
    """
    ext = os.path.splitext(path)[1].lower()
    enc = detect_encoding(path)
    with open(path, encoding=enc, errors="replace") as f:
        first_line = f.readline()

    # 判断分隔符：Tab = 行情XLS；逗号 = 账户持仓CSV
    sep = "\t" if "\t" in first_line else ","

    if sep == "\t":
        holdings, fund_info = parse_quote_xls(path)
        table_type = "自选股行情表（XLS）"
    else:
        holdings, fund_info = parse_position_csv(path)
        has_cost = any(h.get("cost") for h in holdings)
        table_type = "账户持仓表（CSV）" if has_cost else "持仓代码表（CSV，无成本数据）"

    return holdings, fund_info, table_type


# ─────────────────────────────────────────────────────────────────────────────
# 打印表格
# ─────────────────────────────────────────────────────────────────────────────

def print_table(holdings: list[dict], fund_info: dict, table_type: str):
    total_val = sum(h.get("market_val") or 0 for h in holdings)
    total_asset = fund_info.get("总资产", "—")
    avail_cash  = fund_info.get("可用资金", "—")

    print(f"\n{'='*75}")
    print(f"  📊 {table_type}  |  共 {len(holdings)} 只ETF")
    if fund_info:
        print(f"  💰 总资产: {total_asset}   可用资金: {avail_cash}")
    if total_val:
        print(f"  📦 持仓市值合计: ¥{total_val:>12,.2f}")
    print(f"{'='*75}")

    has_cost = any(h.get("cost") for h in holdings)

    if has_cost:
        print(f"  {'代码':<8}{'名称':<14}{'持仓数量':>10}{'成本价':>8}{'现价':>8}{'市值':>12}{'盈亏%':>9}{'仓位%':>7}")
        print(f"  {'-'*73}")
        for h in sorted(holdings, key=lambda x: x.get("market_val") or 0, reverse=True):
            qty   = f"{h['quantity']:>10,.0f}" if h.get("quantity")   else f"{'—':>10}"
            cost  = f"{h['cost']:>8.3f}"       if h.get("cost")       else f"{'—':>8}"
            price = f"{h['price']:>8.3f}"      if h.get("price")      else f"{'—':>8}"
            val   = f"¥{h['market_val']:>10,.2f}" if h.get("market_val") else f"{'—':>11}"
            pct   = f"{h['profit_pct']:>+8.2f}%" if h.get("profit_pct") is not None else f"{'—':>9}"
            pos   = f"{h['position_pct']:>6.2f}%" if h.get("position_pct") is not None else f"{'—':>7}"
            print(f"  {h['code']:<8}{h['name']:<14}{qty}{cost}{price}{val}{pct}{pos}")
    else:
        print(f"  {'代码':<8}{'名称':<16}{'现价':>8}{'今日涨幅':>10}")
        print(f"  {'-'*45}")
        for h in holdings:
            price = f"{h['price']:>8.3f}"      if h.get("price")      else f"{'—':>8}"
            pct   = f"{h.get('change_pct',0):>+9.2f}%" if h.get("change_pct") is not None else f"{'—':>10}"
            print(f"  {h['code']:<8}{h['name']:<16}{price}{pct}")

        print(f"\n  ⚠️  此文件为【自选股行情表】，无成本/市值/持仓数量")
        print(f'  💡  完整持仓数据请从东方财富"交易→持仓"页面右键导出 CSV')

    print(f"{'='*75}\n")


# ─────────────────────────────────────────────────────────────────────────────
# 更新 config.py
# ─────────────────────────────────────────────────────────────────────────────

def update_config(holdings: list[dict], dry_run: bool = False):
    with open(CONFIG_PATH, encoding="utf-8") as f:
        content = f.read()

    watchlist_lines = "\n".join(
        f'    "{h["code"]}",   # {h["name"]}'
        for h in holdings
    )
    namemap_lines = "\n".join(
        f'    "{h["code"]}": "{h["name"]}",'
        for h in holdings
    )

    new_watchlist = f"WATCHLIST_ETFS = [\n{watchlist_lines}\n]"
    new_namemap   = f"ETF_NAME_MAP = {{\n{namemap_lines}\n}}"

    if dry_run:
        print("[预览] WATCHLIST_ETFS：")
        print(new_watchlist)
        print("\n[预览] ETF_NAME_MAP：")
        print(new_namemap)
        return

    content = re.sub(r"WATCHLIST_ETFS\s*=\s*\[.*?\]", new_watchlist, content, flags=re.DOTALL)
    content = re.sub(r"ETF_NAME_MAP\s*=\s*\{.*?\}",   new_namemap,   content, flags=re.DOTALL)

    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        f.write(content)


# ─────────────────────────────────────────────────────────────────────────────
# 保存快照
# ─────────────────────────────────────────────────────────────────────────────

def save_snapshot(holdings: list[dict], fund_info: dict, table_type: str) -> str:
    os.makedirs(SNAPSHOT_DIR, exist_ok=True)
    today = datetime.now().strftime("%Y-%m-%d")
    path  = os.path.join(SNAPSHOT_DIR, f"{today}-holdings-snapshot.json")

    total_val = sum(h.get("market_val") or 0 for h in holdings)
    snapshot = {
        "date":               today,
        "synced_at":          datetime.now().isoformat(),
        "source":             "eastmoney_export",
        "table_type":         table_type,
        "total_market_value": round(total_val, 2) if total_val else None,
        "fund_info":          fund_info,
        "holdings":           holdings,
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(snapshot, f, ensure_ascii=False, indent=2)
    return path


# ─────────────────────────────────────────────────────────────────────────────
# 自动搜索最新导出文件
# ─────────────────────────────────────────────────────────────────────────────

def find_latest_export() -> str | None:
    search_dirs = [
        HOLDINGS_DIR,
        os.path.expanduser("~/Downloads"),
        os.path.expanduser("~/Desktop"),
        "C:/Users/Administrator/Downloads",
    ]
    candidates = []
    for d in search_dirs:
        if not os.path.isdir(d):
            continue
        for pat in ["*.csv", "*.xls", "*.xlsx"]:
            candidates.extend(glob.glob(os.path.join(d, pat)))
    if not candidates:
        return None
    return max(candidates, key=os.path.getmtime)


# ─────────────────────────────────────────────────────────────────────────────
# 主程序
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="东方财富持仓导出 → config.py 同步")
    parser.add_argument("--file",    "-f", help="导出文件路径")
    parser.add_argument("--preview", "-p", action="store_true", help="仅预览，不写入")
    args = parser.parse_args()

    print("\n🔄 东方财富持仓同步工具")
    print("=" * 50)

    path = args.file or find_latest_export()
    if not path:
        print("❌ 未找到文件，请用 --file 指定")
        sys.exit(1)

    print(f"✅ 文件：{path}")
    mtime = datetime.fromtimestamp(os.path.getmtime(path)).strftime("%Y-%m-%d %H:%M")
    print(f"   修改时间：{mtime}")

    print("\n⚙️  解析中...")
    try:
        holdings, fund_info, table_type = parse_file(path)
    except Exception as e:
        print(f"❌ 解析失败：{e}")
        sys.exit(1)

    if not holdings:
        print("⚠️  未解析到任何 ETF 数据")
        sys.exit(1)

    print(f"✅ 识别为：【{table_type}】，共 {len(holdings)} 只 ETF")

    print_table(holdings, fund_info, table_type)

    if args.preview:
        update_config(holdings, dry_run=True)
        print("\n[预览模式] config.py 未修改")
    else:
        update_config(holdings)
        snap = save_snapshot(holdings, fund_info, table_type)
        print(f"✅ config.py 已更新（WATCHLIST_ETFS + ETF_NAME_MAP）")
        print(f"✅ 快照已保存：{snap}")

    print()


if __name__ == "__main__":
    main()

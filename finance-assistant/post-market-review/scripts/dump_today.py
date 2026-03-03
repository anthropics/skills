import json

with open('output/2026-03-02/market_data.json', encoding='utf-8') as f:
    m = json.load(f)
with open('output/2026-03-02/fund_flow.json', encoding='utf-8') as f:
    fund = json.load(f)
with open('output/2026-03-02/etf_shares.json', encoding='utf-8') as f:
    shares = json.load(f)

print("=== 指数 ===")
for sym, d in m.get("index_data", {}).items():
    print(f'{d["name"]}: {float(d["change_pct"]):+.2f}%  成交{d.get("amount",0)/1e8:.0f}亿')

lim = m.get("limit_data", {})
print(f'\n涨停:{lim.get("limit_up")}  跌停:{lim.get("limit_down")}  比值:{lim.get("ratio")}')
for a in m.get("alerts", []):
    print(f'预警: {a.get("msg","")}')

print("\n=== 板块资金 ===")
for s in fund.get("sector_top10", []):
    print(f'{s["rank"]:>2}. {s["sector"]:<12}  净:{str(s["net_flow"]):<12}  涨:{s["change_pct"]}')

print("\n=== ETF份额变化 ===")
for e in shares.get("etf_shares", []):
    chg = e.get("change_pct", 0) or 0
    print(f'{e["name"]:<14}({e["code"]}): {float(chg):+6.1f}%  {e.get("signal",""):<20}  {e.get("score_impact",0):+d}分')

summ = shares.get("summary", {})
print(f'\n机构大申购: {summ.get("strong_buy_signal",[])}')
print(f'机构大赎回: {summ.get("strong_sell_signal",[])}')

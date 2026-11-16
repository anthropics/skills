# -*- coding: utf-8 -*-
"""离线自测：不碰浏览器，验证「录制产物 → 推断 → 人工确认 → 定稿」整条数据链。
用法：python -I test/run_offline_test.py   （在 skill-forge 目录下跑）
断言点：唯一键候选、直贴映射、分列映射、公式映射、确认定稿、链路就绪标记。
"""
import csv, json, os, subprocess, sys, zipfile
sys.stdout.reconfigure(encoding='utf-8', errors='replace')  # git-bash 下走 utf-8，别让 GBK 控制台炸在 ✓/✗ 上

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
FIX = os.path.join(HERE, '_fixture')
OUT = os.path.join(HERE, '草稿')  # 不放 _fixture 下面：test/_fixture/草稿/x 是 4 段路径，上传平台违规
os.makedirs(OUT, exist_ok=True)

# ---------- 样例源表：日期+视频id 可当唯一键；名称列藏分列；消耗/展示可算 CPM ----------
rows = [
    ('日期', '视频id', '名称', '消耗', '展示次数'),
    ('2026-10-30', '7698940123456789012', '品牌A-品类甲', '1200.50', '30000'),
    ('2026-10-30', '7698940123456789013', '品牌B-品类乙', '830.00', '15000'),
    ('2026-10-30', '7698940123456789014', '品牌C-品类丙', '95.20', '8000'),
    ('2026-10-31', '7698940123456789015', '品牌D-洗烘节', '460.80', '20000'),
]
with open(os.path.join(FIX, '源表.csv'), 'w', encoding='utf-8-sig', newline='') as f:
    csv.writer(f).writerows(rows)

# 用户实际贴进在线表格的三列：名称前段（分列）、消耗（直贴）、CPM（公式=消耗/展示*100）
paste_lines = ['\t'.join(['品牌', '花费(元)', 'CPM'])]
for r in rows[1:]:
    cost, imp = float(r[3]), int(r[4])
    paste_lines.append('\t'.join([r[2].split('-')[0], r[3], '%.2f' % (cost / imp * 100)]))
paste_tsv = '\n'.join(paste_lines)

# ---------- 样例录制：一次粘贴动作 + 一次复制动作（顺带验证 copy 也能当源） ----------
rec = {
    'meta': {'name': 'fixture'},
    'actions': [
        {'seq': 1, 'type': 'fill', 'label': '日期', 'value': '2026-10-30', 'url': 'https://agent.example.com/list',
         'locator': {'best': '#date-start', 'L1_id': '#date-start', 'L4_text': None}},
        {'seq': 2, 'type': 'download', 'value': '', 'filename': '源表.csv', 'href': '/export.csv',
         'url': 'https://agent.example.com/list', 'locator': {'best': 'a[href="/export.csv"]'}},
        {'seq': 3, 'type': 'paste', 'value': paste_tsv, 'rows': 5, 'cols': 3,
         'grid': {'host': 'docs.qq.com', 'docTitle': '投放日报-共享表', 'header': ''},
         'url': 'https://docs.qq.com/sheet/abc', 'locator': {'best': None}},
    ],
    'downloads': [], 'network': []
}
rec_path = os.path.join(FIX, 'fixture.rec.json')
json.dump(rec, open(rec_path, 'w', encoding='utf8'), ensure_ascii=False)

def run(*args):
    # 子进程在 Windows 控制台按 GBK 打中文，先收字节再自己解（utf-8 优先、gbk 兜底）
    r = subprocess.run([sys.executable, '-I', os.path.join(ROOT, 'scripts', 'analyze.py')] + list(args),
                       capture_output=True)
    out = (r.stdout or b'').decode('utf-8', errors='replace')
    err = (r.stderr or b'').decode('utf-8', errors='replace')
    if r.returncode != 0:
        open(os.path.join(FIX, 'analyze_error.log'), 'w', encoding='utf-8').write(out + '\n---\n' + err)
        raise SystemExit('analyze.py 跑挂了，输出在 test/_fixture/analyze_error.log')
    return out

# ---------- ① 推断 ----------
run('--recording', rec_path, '--source', os.path.join(FIX, '源表.csv'), '--out', OUT, '--link', 'fixture')

draft = list(csv.reader(open(os.path.join(OUT, '映射字典.csv'), encoding='utf-8-sig')))
body = '\n'.join(','.join(r) for r in draft)
checks = [
    ('直贴映射（消耗→花费列）', '消耗' in body and '花费(元)' in body and '逐行命中' in body),
    ('分列映射（名称→品牌列）', '分列' in body and '名称' in body and '品牌' in body),
    ('公式映射（CPM=消耗/展示×100）', '公式' in body and 'CPM' in body and '展示次数' in body),
]
key_csv = open(os.path.join(OUT, '唯一键.csv'), encoding='utf-8-sig').read()
checks.append(('唯一键候选含日期+视频id', '日期' in key_csv and '视频id' in key_csv))
html = open(os.path.join(OUT, '映射核对表.html'), encoding='utf-8').read()
checks.append(('核对表可导出确认csv', '映射核对_确认.csv' in html))

# ---------- ② 定稿（模拟用户全选"是"） ----------
mp = {r[1]: True for r in draft[1:]}
confirm_path = os.path.join(OUT, '映射核对_确认.csv')
with open(confirm_path, 'w', encoding='utf-8-sig', newline='') as f:
    w = csv.writer(f)
    w.writerow(['KEY', '日期,视频id'])
    for r in draft[1:]:
        w.writerow(['MAP', r[1], r[4], '是', ''])
run('--confirm', confirm_path, '--out', OUT)

final = list(csv.reader(open(os.path.join(OUT, '映射字典.csv'), encoding='utf-8-sig')))
checks.append(('定稿后全部=已确认', all(r[9] == '已确认' for r in final[1:]) and len(final) == 4))
checks.append(('链路就绪标记', os.path.exists(os.path.join(OUT, '链路就绪.json'))))

# ---------- 结果 ----------
bad = [name for name, ok in checks if not ok]
for name, ok in checks:
    print(('✓ ' if ok else '✗ ') + name)
if bad:
    raise SystemExit('offline test 失败：%s' % bad)
print('\noffline test 全过（%d/%d）' % (len(checks), len(checks)))

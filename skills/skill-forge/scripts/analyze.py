# -*- coding: utf-8 -*-
"""analyze.py — 录制产物 → 链路配置草稿 + 人工核对表（纯标准库，-I 隔离模式可跑）

两步用法：
  1) 推断：  python -I analyze.py --recording X.rec.json --source 源表.xlsx[,源表2.csv] --out <草稿目录> [--link 名称] [--key 日期,视频id]
  2) 定稿：  python -I analyze.py --confirm <草稿目录>/映射核对_确认.csv --out <草稿目录>

推断原则（和用户 2026-10-31 对齐的口径）：
  - 映射第一依据是"值"，不是列名：源列的值集合和粘贴块某列对得上 = 映射成立；列名相同只是加分项
  - 唯一键不写死：自动给候选（整列唯一 + 长ID/日期型），拿不准就列出来让用户选
  - 一切推断结果必须过人工核对表，确认了才变成"已确认"
"""
import argparse, csv, io, json, os, re, sys, zipfile
import xml.etree.ElementTree as ET

NS = '{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'


# ---------- 表格读取（csv: utf-8-sig/gbk 兜底；xlsx: zipfile+ElementTree） ----------

def col_key(col):
    n = 0
    for ch in col:
        n = n * 26 + (ord(ch) - 64)
    return n


def read_xlsx(path):
    z = zipfile.ZipFile(path)
    shared = []
    if 'xl/sharedStrings.xml' in z.namelist():
        for si in ET.fromstring(z.read('xl/sharedStrings.xml')).iter(NS + 'si'):
            shared.append(''.join(t.text or '' for t in si.iter(NS + 't')))
    wb = ET.fromstring(z.read('xl/workbook.xml'))
    names = [s.get('name') for s in wb.iter(NS + 'sheet')]
    for idx, sheet_name in enumerate(names, 1):
        fn = 'xl/worksheets/sheet%d.xml' % idx
        if fn not in z.namelist():
            continue
        rows = []
        for row in ET.fromstring(z.read(fn)).iter(NS + 'row'):
            vals = {}
            for c in row.findall(NS + 'c'):
                col = ''.join(ch for ch in (c.get('r') or '') if ch.isalpha())
                v, isel = c.find(NS + 'v'), c.find(NS + 'is')
                if c.get('t') == 's' and v is not None:
                    val = shared[int(v.text)]
                elif isel is not None:
                    val = ''.join(x.text or '' for x in isel.iter(NS + 't'))
                elif v is not None:
                    val = v.text
                else:
                    val = ''
                if col:
                    vals[col] = val
            rows.append(vals)
        if not rows:
            continue
        cols = sorted({k for r in rows for k in r}, key=col_key)
        header = [str(rows[0].get(c, '')).strip() for c in cols]
        data = [{header[i]: rows[r].get(cols[i], '') for i in range(len(cols))} for r in range(1, len(rows))]
        return {'name': sheet_name, 'headers': header, 'rows': data, 'from': os.path.basename(path)}
    return None


def read_csv(path):
    raw = open(path, 'rb').read()
    for enc in ('utf-8-sig', 'gbk', 'utf-8'):
        try:
            text = raw.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    else:
        raise SystemExit('读不了 %s：编码不是 utf-8/gbk' % path)
    rows = list(csv.reader(io.StringIO(text)))
    rows = [r for r in rows if any(str(c).strip() for c in r)]
    if not rows:
        return None
    header = [str(c).strip() for c in rows[0]]
    data = [{header[i]: (r[i] if i < len(r) else '') for i in range(len(header))} for r in rows[1:]]
    return {'name': os.path.basename(path), 'headers': header, 'rows': data, 'from': os.path.basename(path)}


def read_table(path):
    return read_xlsx(path) if path.lower().endswith(('.xlsx', '.xlsm')) else read_csv(path)


# ---------- 数值/类型工具 ----------

def norm(v):
    s = str(v if v is not None else '').strip()
    for ch in (',', '，', '￥', '¥', ' ', '"'):
        s = s.replace(ch, '')
    return s


def num(v):
    s = norm(v)
    if s == '':
        return None
    try:
        return float(s.rstrip('%'))
    except ValueError:
        return None


def same(a, b):
    na, nb = num(a), num(b)
    if na is not None and nb is not None:
        return abs(na - nb) < 0.005
    return norm(a) == norm(b) and norm(a) != ''


DATE_RE = re.compile(r'^\d{4}[-/.年]\d{1,2}[-/.月]\d{1,2}日?$|^\d{8}$')


def col_kind(values):
    nonempty = [v for v in values if norm(v) != '']
    if not nonempty:
        return '空'
    if all(num(v) is not None for v in nonempty):
        s = [str(int(num(v))) for v in nonempty if abs(num(v)) < 1e15]
        if all(len(x) >= 8 for x in s):
            return '长ID'
        return '数值'
    if all(DATE_RE.match(norm(v)) for v in nonempty):
        return '日期'
    return '文本'


def unique_ratio(values):
    vals = [norm(v) for v in values if norm(v) != '']
    if not vals:
        return 0
    return len(set(vals)) / len(vals)


# ---------- 粘贴块 ----------

def parse_block(text):
    """剪贴板文本 → 二维表（tab 分列、换行分行），去掉整行空行"""
    grid = []
    for line in str(text).replace('\r\n', '\n').replace('\r', '\n').split('\n'):
        cells = line.split('\t')
        if any(c.strip() for c in cells):
            grid.append(cells)
    return grid


def target_label(paste_action, col_idx):
    g = paste_action.get('grid') or {}
    host = g.get('host', '')
    title = (g.get('docTitle') or '').strip()
    header = (g.get('header') or '').strip()
    # 目标表格标识：在线文档的标题就是文档名；列先给"表头名或第N列"，核对表里可改
    doc = (title or host or '未知目标') + ' [' + host + ']'
    col = header if header else '第%d列' % (col_idx + 1)
    sheet = '待确认（录制时落点标题=%s）' % title
    return doc, sheet, col


# ---------- 主流程：推断 ----------

def analyze(rec_path, sources, out_dir, link_name, key_override):
    rec = json.load(open(rec_path, encoding='utf-8'))
    actions = rec.get('actions', [])

    # 复制块也算"源表"：平台页选中→复制→贴在线表，没有下载文件也照样推断
    tables = []
    for s in sources:
        t = read_table(s)
        if t:
            tables.append(t)
        else:
            print('[!] 读不了源表：%s' % s)
    for a in actions:
        if a.get('type') == 'copy' and a.get('value'):
            grid = parse_block(a['value'])
            if len(grid) >= 2 and len(grid[0]) >= 2:
                header = [norm(c) for c in grid[0]]
                tables.append({
                    'name': '页面复制@' + (a.get('url') or '')[:40],
                    'headers': header,
                    'rows': [{header[i]: r[i] if i < len(r) else '' for i in range(len(header))} for r in grid[1:]],
                    'from': 'copy'
                })

    pastes = [a for a in actions if a.get('type') == 'paste' and a.get('value')]
    if not pastes:
        print('[!] 录制里没有粘贴动作——这次录的不是"搬运"链路，只出定位库/参数位')
    if not tables:
        raise SystemExit('没有可用的源表：--source 给下载的导出文件，或录制里要有 copy 动作')

    mappings = []       # 每行 = 一条 源列→目标列 映射候选
    unresolved = []     # 值对不上、要人看的

    for pi, p in enumerate(pastes):
        grid = parse_block(p['value'])
        if len(grid) < 2:
            continue
        doc, sheet, _ = target_label(p, 0)
        # 找行数对得上的源表（默认用户按原顺序整块贴）
        src = None
        for t in tables:
            if len(t['rows']) == len(grid) - 1 or len(t['rows']) == len(grid):
                src = t
                break
        if src is None:
            src = tables[0]
            unresolved.append({'目标': doc, '问题': '粘贴行数(%d)和源表行数对不上，按第一张源表试' % (len(grid) - 1)})
        # 粘贴块可能带目标侧表头（首行是"品牌/花费"这种新叫法），也可能纯数据。
        # 两种对齐都试：优先按"首行是表头"（更常见），每种对齐依次跑 直贴→分列→公式，先命中先停；
        # 带表头时目标列名直接用表头文字（比"第N列"可读，也正好落进同义字典）
        variants = []
        if len(grid) >= 2:
            variants.append((grid[1:], grid[0]))
        variants.append((grid, None))
        ncols = max(len(r) for r in grid)
        for j in range(ncols):
            doc, sheet, colname = target_label(p, j)
            fallback = ''
            for rows_i, head_row in variants:
                pv = [r[j] if j < len(r) else '' for r in rows_i]
                cn = colname
                if head_row is not None and j < len(head_row) and str(head_row[j]).strip():
                    cn = str(head_row[j]).strip()
                # ① 直贴：逐行值对上就算
                best, best_score = None, 0
                for h in src['headers']:
                    svals = [r.get(h, '') for r in src['rows'][:len(pv)]]
                    hits = sum(1 for a, b in zip(pv, svals) if same(a, b))
                    score = hits / max(1, len(pv))
                    if score > best_score:
                        best, best_score = h, score
                if best_score >= 0.85:
                    mappings.append({'源表': src['from'], '源列': best, '目标表格': doc, 'sheet': sheet,
                                     '目标列': cn, '依据': '数值/文本逐行命中', '规则': '', '命中率': '%.0f%%' % (best_score * 100),
                                     '样例': '%s → %s' % (pv[0], src['rows'][0].get(best, ''))})
                    break
                if not fallback:
                    fallback = '没找到对应源列（命中率最高 %.0f%%：%s）' % (best_score * 100, best or '无')
                # ② 分列：源某列按分隔符拆开，第 k 段 == 粘贴列（整列一致才算）
                split_hit = detect_split(pv, src)
                if split_hit:
                    mappings.append({'源表': src['from'], '源列': split_hit[0], '目标表格': doc, 'sheet': sheet,
                                     '目标列': cn, '依据': '分列', '规则': split_hit[1], '命中率': split_hit[2],
                                     '样例': split_hit[3]})
                    break
                # ③ 公式：源两列四则运算 == 粘贴列（CPM=消耗/展示×100 这类）
                f_hit = detect_formula(pv, src)
                if f_hit:
                    mappings.append({'源表': src['from'], '源列': f_hit[0], '目标表格': doc, 'sheet': sheet,
                                     '目标列': cn, '依据': '公式', '规则': f_hit[1], '命中率': '≥95%行成立',
                                     '样例': f_hit[2]})
                    break
            else:
                unresolved.append({'目标': doc + ' / ' + colname, '问题': fallback or '没找到对应源列'})

    # 唯一键候选：日期列一天多行很常见，不要求单独唯一（拿来和ID组合）；长ID要整列唯一
    main_src = tables[0]
    key_candidates = []
    for h in main_src['headers']:
        vals = [r.get(h, '') for r in main_src['rows']]
        kind = col_kind(vals)
        if kind == '日期':
            key_candidates.append((h, kind))
        elif kind == '长ID' and unique_ratio(vals) == 1.0:
            key_candidates.append((h, kind))
    chosen_key = key_override or suggest_key(key_candidates)

    write_draft(out_dir, link_name, rec, actions, main_src, key_candidates, chosen_key, mappings, unresolved)
    print('[OK] 草稿已出 → %s' % out_dir)
    print('     打开 映射核对表.html 勾选确认 → 导出 映射核对_确认.csv → 跑 --confirm 定稿')
    if unresolved:
        print('[!] %d 条对不上，去核对表里看' % len(unresolved))


def suggest_key(cands):
    dates = [c for c, k in cands if k == '日期']
    ids = [c for c, k in cands if k == '长ID']
    if len(dates) >= 1 and len(ids) == 1:
        return '%s,%s' % (dates[0], ids[0])
    if len(ids) == 1 and not dates:
        return ids[0]
    return ''


def detect_split(pvals, src):
    for h in src['headers']:
        svals = [r.get(h, '') for r in src['rows'][:len(pvals)]]
        for sep in ('-', '/', ' ', '·', '：', ':', '|'):
            for part in (0, 1, -1):
                ok, hit = 0, 0
                for pv, sv in zip(pvals, svals):
                    if norm(pv) == '':
                        continue
                    segs = [s for s in re.split(re.escape(sep), norm(sv)) if s != '']
                    if segs and part < len(segs) and same(pv, segs[part]):
                        ok += 1
                    hit += 1
                if hit >= 3 and ok / hit >= 0.95:
                    return h, '按"%s"分列取第%s段' % (sep, {'0': '1', '1': '2', '-1': '末'}[str(part)]), '%d/%d行' % (ok, hit), '%s → %s' % (svals[0], pvals[0])
    return None


def detect_formula(pvals, src):
    nums = [h for h in src['headers'] if all(num(r.get(h, '')) is not None for r in src['rows'][:len(pvals)])]
    for a in nums:
        for b in nums:
            if a == b:
                continue
            for fn, label in (
                (lambda x, y: x / y if y else None, '%s ÷ %s'),
                (lambda x, y: x / y * 100 if y else None, '(%s ÷ %s) × 100'),
                (lambda x, y: x * y, '%s × %s'),
                (lambda x, y: x + y, '%s + %s'),
                (lambda x, y: x - y, '%s − %s'),
            ):
                ok, hit = 0, 0
                for pv, r in zip(pvals, src['rows']):
                    x, y, target = num(r.get(a, '')), num(r.get(b, '')), num(pv)
                    if target is None or x is None or y is None:
                        continue
                    want = fn(x, y)
                    if want is not None and abs(want - target) <= max(0.05, abs(want) * 0.005):
                        ok += 1
                    hit += 1
                if hit >= 3 and ok / hit >= 0.95:
                    return '%s,%s' % (a, b), label % (a, b), '%s %s = %s' % (a, src['rows'][0].get(a, ''), pvals[0])
    return None


# ---------- 落盘 ----------

def write_csv(path, header, rows):
    with open(path, 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)


def write_draft(out_dir, link_name, rec, actions, main_src, key_candidates, chosen_key, mappings, unresolved):
    os.makedirs(out_dir, exist_ok=True)
    write_csv(os.path.join(out_dir, '映射字典.csv'),
              ['源表', '源列', '目标表格', '目标sheet', '目标列', '依据', '公式/分列规则', '命中率', '样例', '状态'],
              [[m['源表'], m['源列'], m['目标表格'], m['sheet'], m['目标列'], m['依据'], m['规则'], m['命中率'], m['样例'], '待确认'] for m in mappings])

    with open(os.path.join(out_dir, '唯一键.csv'), 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.writer(f)
        # 两行格式（和 templates/配置夹 一致）：表头一行、键值一行，run.mjs 按这个读
        w.writerow(['列名'])
        if chosen_key:
            w.writerow([chosen_key])
        w.writerow(['# 候选'] + [('%s(%s)' % (c, k)) for c, k in key_candidates])
        w.writerow(['# 说明'] + ['多个候选/没候选时，在核对表里选一个'])

    write_csv(os.path.join(out_dir, '同义字典.csv'), ['标准名(源列)', '同义名(目标侧见过)'],
              [[m['源列'], m['目标列'].replace('第', '').replace('列', '') if m['目标列'].startswith('第') else m['目标列']] for m in mappings if m['目标列'] != m['源列']])

    docs = sorted({m['目标表格'] for m in mappings})
    write_csv(os.path.join(out_dir, '路由表.csv'), ['账户', '目标表格', 'sheet', '启用'],
              [['待填', d, '待确认', '是'] for d in docs])

    ui = [a for a in actions if a.get('type') in ('click', 'fill', 'select', 'check', 'download', 'nav')]
    write_csv(os.path.join(out_dir, '定位库.csv'),
              ['步骤', '动作', '标签', '值', 'best定位', 'L1_id', 'L4_text', '页面'],
              [[i + 1, a['type'], a.get('label', ''), a.get('value', a.get('filename', ''))[:80],
                (a.get('locator') or {}).get('best', ''), (a.get('locator') or {}).get('L1_id', ''),
                (a.get('locator') or {}).get('L4_text', ''), (a.get('url') or '')[:120]] for i, a in enumerate(ui)])

    kw = ('日期', 'date', '时间', '账户', '账号', '渠道', '平台', 'ID', 'id')
    params = [a for a in actions if a.get('type') in ('fill', 'select') and any(k in (a.get('label') or '') for k in kw)]
    with open(os.path.join(out_dir, '参数位.md'), 'w', encoding='utf-8') as f:
        f.write('# 参数位（后台里可选的维度：日期/账户/渠道…）\n\n录制时看到这些控件动过，列为参数候选：\n\n')
        for a in params:
            f.write('- **%s**：%s = `%s`\n' % (a.get('label', '未命名'), (a.get('locator') or {}).get('best', ''), str(a.get('value', ''))[:60]))
        f.write('\n机器可读版在 参数.json（执行器读它填参数）。\n')
    with open(os.path.join(out_dir, '参数.json'), 'w', encoding='utf-8') as f:
        json.dump([{'label': a.get('label', ''), 'best': (a.get('locator') or {}).get('best', ''), 'value': str(a.get('value', ''))[:80]} for a in params], f, ensure_ascii=False, indent=1)

    write_review_html(out_dir, link_name, mappings, unresolved, key_candidates, chosen_key)


def write_review_html(out_dir, link_name, mappings, unresolved, key_candidates, chosen_key):
    rows_html = []
    for i, m in enumerate(mappings):
        rows_html.append(
            '<tr><td><input type="radio" name="m%d" value="是" checked>是 <input type="radio" name="m%d" value="否">否</td>'
            '<td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td>'
            '<td><input name="note%d" size="24"></td></tr>'
            % (i, i, m['源列'], m['源表'], m['目标表格'], m['目标列'], m['依据'], m['规则'], m['命中率'], i))
    for u in unresolved:
        rows_html.append('<tr style="background:#fff3f3"><td><input type="radio" name="u%d" value="是">是 <input type="radio" name="u%d" value="否" checked>否</td><td>?</td><td></td><td>%s</td><td></td><td>未匹配</td><td></td><td>%s</td><td><input name="unote%d" size="24"></td></tr>' % (len(rows_html), len(rows_html), u['目标'], u['问题'], len(rows_html)))
    # 选项 = 各单列候选 + 组合键（若有）；checked 只按精确相等，避免 radio 双选中
    key_names = [c for c, _ in key_candidates]
    if chosen_key and ',' in chosen_key and chosen_key not in key_names:
        key_names.append(chosen_key)
    key_opts = ''.join('<label><input type="radio" name="key" value="%s"%s> %s</label> '
                       % (c, ' checked' if c == chosen_key else '', c) for c in key_names) or '<input name="key" placeholder="手填列名，逗号分隔">'

    html = """<!doctype html><html><head><meta charset="utf-8"><title>映射核对表 — %s</title>
<style>body{font-family:system-ui;margin:24px;font-size:14px}table{border-collapse:collapse;width:100%%}td,th{border:1px solid #ccc;padding:5px 8px;text-align:left}th{background:#f5f5f5}button{font-size:16px;padding:8px 24px;margin-top:16px}</style></head><body>
<h2>映射核对表 — %s</h2>
<p><b>唯一键</b>（这条链路的"身份证"列，可用逗号组合）：%s</p>
<table id="t"><tr><th>确认</th><th>源列</th><th>源表</th><th>目标表格</th><th>目标列</th><th>依据</th><th>规则</th><th>命中率</th><th>备注/改列名</th></tr>%s</table>
<button onclick="exp()">✓ 确认完毕，导出 映射核对_确认.csv</button>
<p id="msg"></p>
<script>
function exp(){
 var rows=[['KEY',document.querySelector('input[name=key]:checked')?document.querySelector('input[name=key]:checked').value:document.querySelector('input[name=key]').value||'%s']];
 document.querySelectorAll('#t tr').forEach(function(tr,i){
  if(i===0)return;
  var r=tr.querySelector('input[type=radio]:checked'); if(!r)return;
  var tds=tr.querySelectorAll('td');
  rows.push(['MAP',tds[1].innerText,tds[4].innerText,r.value,tr.querySelector('input[type=text]')?tr.querySelector('input[type=text]').value:'']);
 });
 var csv='\\ufeff'+rows.map(function(r){return r.map(function(c){return '"'+String(c).replace(/"/g,'""')+'"'}).join(',')}).join('\\r\\n');
 var a=document.createElement('a');a.href=URL.createObjectURL(new Blob([csv],{type:'text/csv'}));a.download='映射核对_确认.csv';a.click();
 document.getElementById('msg').innerText='已导出，把它放回草稿目录，然后跑 python -I scripts/analyze.py --confirm 映射核对_确认.csv --out 本目录';
}
</script></body></html>""" % (link_name, link_name, key_opts, '\n'.join(rows_html), chosen_key)
    with open(os.path.join(out_dir, '映射核对表.html'), 'w', encoding='utf-8') as f:
        f.write(html)


# ---------- 定稿 ----------

def confirm(confirm_csv, out_dir):
    rows = list(csv.reader(open(confirm_csv, encoding='utf-8-sig')))
    key, kept = '', []
    for r in rows:
        if not r or r[0] == 'KEY':
            key = r[1] if len(r) > 1 else key
        elif r[0] == 'MAP' and len(r) > 4 and r[3] == '是':
            kept.append((r[1], r[2], r[4]))
    if not kept:
        raise SystemExit('确认文件里一条"是"都没有，没法定稿')
    draft_path = os.path.join(out_dir, '映射字典.csv')
    draft = list(csv.reader(open(draft_path, encoding='utf-8-sig')))
    final = []
    for row in draft[1:]:
        # 核对表里被否掉/改名的行：源列或目标列对得上才保留，备注列可改目标列名
        hit = next((k for k in kept if k[0] == row[1] and (k[1] == row[4] or k[1] == '')), None)
        if hit is None:
            continue
        row[4] = hit[2] if hit[2] else row[4]
        row[9] = '已确认'
        final.append(row)
    write_csv(draft_path, draft[0], final)
    with open(os.path.join(out_dir, '唯一键.csv'), 'w', encoding='utf-8-sig', newline='') as f:
        w = csv.writer(f)
        w.writerow(['列名'])
        w.writerow([key])
    with open(os.path.join(out_dir, '链路就绪.json'), 'w', encoding='utf-8') as f:
        json.dump({'ready': True, 'key': key, 'mappings': len(final), 'at': __import__('time').strftime('%Y-%m-%d %H:%M:%S')}, f, ensure_ascii=False)
    print('[OK] 定稿完成：%d 条映射，唯一键=%s。下一步 build_skill.mjs 生成子技能' % (len(final), key))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--recording')
    ap.add_argument('--source', help='下载的源表，逗号分隔可多张')
    ap.add_argument('--out', required=True)
    ap.add_argument('--link', default='未命名链路')
    ap.add_argument('--key', help='直接指定唯一键（逗号分隔列名），跳过候选')
    ap.add_argument('--confirm', help='核对表导出的确认csv，走定稿')
    a = ap.parse_args()
    if a.confirm:
        confirm(a.confirm, a.out)
        return
    if not a.recording or not a.source:
        ap.error('推断要 --recording 和 --source；定稿只要 --confirm 和 --out')
    analyze(a.recording, [s.strip() for s in a.source.split(',') if s.strip()], a.out, a.link, a.key)


if __name__ == '__main__':
    main()

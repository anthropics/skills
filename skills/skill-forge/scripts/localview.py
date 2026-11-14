# -*- coding: utf-8 -*-
"""localview.py — 看浏览器之外的东西：把下载下来的表格/文件读出来给人看，或直接打开给人看

为什么要有：链路跑完，人第一反应是「表下到哪了？里面是不是我要的数据？」
CDP 只管浏览器，管不了本地文件。这个脚本补这一块，零第三方依赖（xlsx 用标准库解 zip+xml）。

用法：
  python scripts/localview.py --file <路径>                  # 读摘要：类型/大小/行数/列名/前几行
  python scripts/localview.py --file <路径> --rows 10        # 多看几行
  python scripts/localview.py --file <路径> --open           # 用系统默认程序打开（Excel/WPS/记事本）
  python scripts/localview.py --dir <下载目录> --latest 3    # 看目录里最新的几个文件（找刚下载的那份）
退出码：0 正常；4 文件不存在/类型不支持
支持：.xlsx .csv .tsv .txt .json
"""
import argparse
import csv
import json
import os
import sys
import zipfile
import xml.etree.ElementTree as ET
from datetime import datetime

# 输出锁 UTF-8：Windows 控制台默认 GBK，调用方（agent/测试）按 UTF-8 读会拿到乱码
for _stream in (sys.stdout, sys.stderr):
    if hasattr(_stream, "reconfigure"):
        _stream.reconfigure(encoding="utf-8")


def _local(tag):
    """去掉命名空间：真实 xlsx 带 xmlns，测试样例可能不带，两种都要认。"""
    return tag.rsplit('}', 1)[-1]


def _col_index(ref):
    """A1 -> 0, B7 -> 1（按字母部分算列号），用于补齐空列。"""
    letters = ''.join(ch for ch in (ref or '') if ch.isalpha())
    n = 0
    for ch in letters:
        n = n * 26 + (ord(ch.upper()) - 64)
    return max(n - 1, 0)


def read_xlsx(path, max_rows=5):
    """读 xlsx：返回 [{sheet, rows_total, headers, sample}]，纯标准库，带/不带命名空间都认。"""
    out = []
    with zipfile.ZipFile(path) as z:
        names = z.namelist()
        shared = []
        if 'xl/sharedStrings.xml' in names:
            root = ET.fromstring(z.read('xl/sharedStrings.xml'))
            for si in root.iter():
                if _local(si.tag) != 'si':
                    continue
                shared.append(''.join(t.text or '' for t in si.iter() if _local(t.tag) == 't'))
        sheet_names = []
        if 'xl/workbook.xml' in names:
            wb = ET.fromstring(z.read('xl/workbook.xml'))
            sheet_names = [s.get('name') for s in wb.iter() if _local(s.tag) == 'sheet']
        sheets = sorted(n for n in names if n.startswith('xl/worksheets/sheet') and n.endswith('.xml'))
        for idx, sp in enumerate(sheets):
            root = ET.fromstring(z.read(sp))
            rows = []
            for r in root.iter():
                if _local(r.tag) != 'row':
                    continue
                vals = {}
                for c in r:
                    if _local(c.tag) != 'c':
                        continue
                    ci = _col_index(c.get('r'))
                    t = c.get('t')
                    text = None
                    for ch in c:
                        lt = _local(ch.tag)
                        if lt == 'v' and ch.text is not None:
                            text = ch.text
                        elif lt == 'is':
                            text = ''.join(x.text or '' for x in ch.iter() if _local(x.tag) == 't')
                    if t == 's' and text is not None:
                        i = int(text)
                        text = shared[i] if i < len(shared) else ''
                    vals[ci] = text if text is not None else ''
                if vals:
                    width = max(vals) + 1
                    rows.append([vals.get(i, '') for i in range(width)])
            headers = rows[0] if rows else []
            out.append({
                'sheet': sheet_names[idx] if idx < len(sheet_names) else 'sheet%d' % (idx + 1),
                'rows_total': max(len(rows) - 1, 0),
                'headers': headers,
                'sample': rows[1:1 + max_rows],
            })
    return out


def summarize(path, max_rows=5):
    ext = os.path.splitext(path)[1].lower()
    size = os.path.getsize(path)
    info = {'file': path, 'type': ext.lstrip('.'), 'size_kb': round(size / 1024, 1),
            'mtime': datetime.fromtimestamp(os.path.getmtime(path)).strftime('%Y-%m-%d %H:%M:%S')}
    if ext == '.xlsx':
        info['sheets'] = read_xlsx(path, max_rows)
    elif ext in ('.csv', '.tsv', '.txt'):
        delim = '\t' if ext == '.tsv' else ','
        with open(path, encoding='utf-8-sig', errors='replace', newline='') as f:
            rows = list(csv.reader(f, delimiter=delim))
        info['rows_total'] = max(len(rows) - 1, 0)
        info['headers'] = rows[0] if rows else []
        info['sample'] = rows[1:1 + max_rows]
    elif ext == '.json':
        with open(path, encoding='utf-8', errors='replace') as f:
            data = json.load(f)
        if isinstance(data, list):
            info['rows_total'] = len(data)
            info['headers'] = list(data[0].keys()) if data and isinstance(data[0], dict) else []
            info['sample'] = data[:max_rows]
        else:
            info['keys'] = list(data.keys())
            info['sample'] = data
    else:
        return None
    return info


def show(info):
    print(f"文件：{info['file']}")
    print(f"类型：{info['type']}｜大小：{info['size_kb']} KB｜改于：{info['mtime']}")
    if 'sheets' in info:
        for s in info['sheets']:
            print(f"工作表「{s['sheet']}」：数据 {s['rows_total']} 行，列 {len(s['headers'])} 列")
            print(f"  列名：{' | '.join(str(h) for h in s['headers'])}")
            for r in s['sample']:
                print(f"  · {' | '.join(str(x) for x in r)}")
            if s['rows_total'] > len(s['sample']):
                print(f"  …（还有 {s['rows_total'] - len(s['sample'])} 行）")
    elif 'rows_total' in info:
        print(f"数据 {info['rows_total']} 行，列 {len(info['headers'])} 列")
        print(f"列名：{' | '.join(str(h) for h in info['headers'])}")
        for r in info['sample']:
            print(f"  · {' | '.join(str(x) for x in r) if isinstance(r, list) else r}")
    else:
        print(f"键：{', '.join(map(str, info.get('keys', [])))}")
        print(f"内容：{json.dumps(info['sample'], ensure_ascii=False)[:500]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--file')
    ap.add_argument('--dir')
    ap.add_argument('--latest', type=int, default=0)
    ap.add_argument('--rows', type=int, default=5)
    ap.add_argument('--open', action='store_true')
    ap.add_argument('--json', action='store_true')
    a = ap.parse_args()

    if a.file:
        if not os.path.isfile(a.file):
            print(f'文件不存在：{a.file}', file=sys.stderr)
            sys.exit(4)
        targets = [a.file]
    elif a.dir:
        if not os.path.isdir(a.dir):
            print(f'目录不存在：{a.dir}', file=sys.stderr)
            sys.exit(4)
        files = [os.path.join(a.dir, f) for f in os.listdir(a.dir)
                 if os.path.isfile(os.path.join(a.dir, f))]
        files.sort(key=os.path.getmtime, reverse=True)
        targets = files[:max(a.latest, 1)]
        print('最近的文件：')
        for f in targets:
            print(f"  {os.path.basename(f)}  {datetime.fromtimestamp(os.path.getmtime(f)):%Y-%m-%d %H:%M}")
    else:
        print('用法：python scripts/localview.py --file <路径> | --dir <目录> --latest 3', file=sys.stderr)
        sys.exit(4)

    for t in targets:
        info = summarize(t, a.rows)
        if info is None:
            print(f'（{os.path.basename(t)}：类型不支持预览，只能 --open 打开）')
            continue
        if a.json:
            print(json.dumps(info, ensure_ascii=False, indent=1))
        else:
            show(info)
        if a.open:
            if sys.platform.startswith('win'):
                os.startfile(t)  # noqa: 只给本机用户看，不参与自动化判断
                print('（已用系统默认程序打开）')
            else:
                print('（当前系统不支持自动打开，请手动打开）')


if __name__ == '__main__':
    main()

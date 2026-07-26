"""Ujian keteguhan bagi dapatan komoditi, dan pengesanan percanggahan aritmetik."""
import json, itertools
import numpy as np
from scipy import stats
import openpyxl

panel = json.load(open('panel.json'))
ZONES = ["BARAT DAYA","SELATAN","TENGAH","TENGGARA","TIMUR","TIMUR LAUT","UTARA"]
YEARS = [2021, 2022, 2023, 2024, 2025]


def ols(y, X):
    X = np.column_stack([np.ones(len(y))] + list(X))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ b
    n, k = X.shape
    df = n - k
    ssr = float(r @ r)
    sst = float(((y - y.mean()) ** 2).sum())
    XtXi = np.linalg.pinv(X.T @ X)
    se = np.sqrt(np.diag(XtXi) * (ssr / df))
    p = 2 * (1 - stats.t.cdf(np.abs(b / se), df))
    return dict(b=b, p=p, r2=1 - ssr / sst, ssr=ssr, df=df)


def ftest(r_, f_, q):
    F = ((r_['ssr'] - f_['ssr']) / q) / (f_['ssr'] / f_['df'])
    return F, 1 - stats.f.cdf(F, q, f_['df'])


def run(rows, tag):
    zs = sorted({r['zon'] for r in rows})
    v = lambda k: np.array([float(r[k]) for r in rows])
    zd = [np.array([1.0 if r['zon'] == z else 0.0 for r in rows]) for z in zs[1:]]
    y, peg, pen = v('out'), v('peg'), v('pen')
    kom = [v('s_kecil'), v('s_tenusu'), v('pelbagai')]

    b0 = ols(y, [peg] + zd)
    b1 = ols(y, [peg] + zd + kom)
    F, p = ftest(b0, b1, 3)

    i0 = ols(y / pen, [peg] + zd)
    i1 = ols(y / pen, [peg] + zd + kom)
    Fi, pi = ftest(i0, i1, 3)
    b_div = i1['b'][-1]
    p_div = i1['p'][-1]

    print(f"  {tag:<34} n={len(rows):>3}  "
          f"OUTPUT F={F:5.2f} p={p:.3f}   |   "
          f"OUT/PENTERNAK F={Fi:5.2f} p={pi:.3f}  b(pelbagai)={b_div:+8.0f} p={p_div:.4f}")


print("=" * 100)
print("KETEGUHAN — blok komoditi selepas zon + pegawai dikawal")
print()
run(panel, "panel penuh 2021-2025")
run([r for r in panel if r['tahun'] != 2025], "tanpa 2025 (tahun anomali)")
run([r for r in panel if r['zon'] not in ('TENGGARA', 'TIMUR LAUT')],
    "tanpa TENGGARA & TIMUR LAUT")
run([r for r in panel if r['tahun'] != 2025 and
     r['zon'] not in ('TENGGARA', 'TIMUR LAUT')], "tanpa kedua-duanya")
print()
print("  Gugur-satu-zon:")
for z in ZONES:
    run([r for r in panel if r['zon'] != z], f"    tanpa {z}")

print()
print("=" * 100)
print("DALAM-ZON: perubahan campuran komoditi lawan perubahan output (min zon ditolak)")
print()
def demean(rows, key):
    a = np.array([float(r[key]) for r in rows])
    for z in {r['zon'] for r in rows}:
        idx = [i for i, r in enumerate(rows) if r['zon'] == z]
        a[idx] -= a[idx].mean()
    return a
for tag, rows in [("panel penuh", panel), ("tanpa 2025", [r for r in panel if r['tahun'] != 2025])]:
    print(f"  {tag}:")
    for lbl, k in [("bahagian ruminan kecil", 's_kecil'), ("bahagian tenusu", 's_tenusu'),
                   ("kepelbagaian", 'pelbagai'), ("ladang dilawat", 'lad'),
                   ("bilangan pegawai", 'peg')]:
        r_, p_ = stats.pearsonr(demean(rows, k), demean(rows, 'out'))
        print(f"    {lbl:<24} r={r_:+.3f}  p={p_:.4f}"
              f"{'   <-- signifikan' if p_ < 0.05 else ''}")

print()
print("=" * 100)
print("CIRI KOMODITI SETIAP ZON, 2025 — dan intensiti perkhidmatan")
print()
print(f"  {'ZON':<12}{'kecil%':>8}{'tenusu%':>9}{'pelbagai':>10}{'penternak':>11}"
      f"{'output':>9}{'out/penternak':>15}")
for r in sorted([r for r in panel if r['tahun'] == 2025],
                key=lambda r: -r['out'] / r['pen']):
    print(f"  {r['zon']:<12}{r['s_kecil']*100:>8.1f}{r['s_tenusu']*100:>9.1f}"
          f"{r['pelbagai']:>10.3f}{r['pen']:>11,}{r['out']:>9,}"
          f"{r['out']/r['pen']:>15.1f}")
rho, prho = stats.spearmanr([r['pelbagai'] for r in panel if r['tahun'] == 2025],
                            [r['out'] / r['pen'] for r in panel if r['tahun'] == 2025])
print(f"\n  Spearman kepelbagaian lawan output setiap penternak (2025, n=7): "
      f"rho={rho:+.3f}  p={prho:.4f}")

print()
print("=" * 100)
print("PENGESANAN PERCANGGAHAN ARITMETIK 2024")
wb = openpyxl.load_workbook('logteknikal.xlsx', data_only=True)
ws = wb['2024']
rows = [[('' if c is None else str(c).strip()) for c in r] for r in ws.iter_rows(values_only=True)]
hdr = next(i for i, r in enumerate(rows) if 'BARAT DAYA' in r)
zi = [rows[hdr].index(z) for z in ZONES]
ji = rows[hdr].index('JUMLAH')
for r in rows[hdr + 1:]:
    lbl = (r[1] or r[0]).strip()
    if not lbl:
        continue
    try:
        vals = [int(float(r[i])) for i in zi]
        tot = int(float(r[ji]))
    except (ValueError, IndexError):
        continue
    if sum(vals) != tot:
        print(f"  {lbl:<38} hasil tambah zon = {sum(vals):>7,}   "
              f"lajur JUMLAH = {tot:>7,}   beza = {sum(vals)-tot:+,}")

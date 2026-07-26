"""Analisis tren setiap VetEC 2021-2025 dan pengesanan tahun outlier.
Sumber: LAPORAN LOG TEKNIKAL 2021-2026 (lembaran tahunan)."""
import openpyxl, json
import numpy as np
from scipy import stats

wb = openpyxl.load_workbook('logteknikal_v2.xlsx', data_only=True)
ZONES = ["UTARA", "TENGAH", "BARAT DAYA", "SELATAN", "TENGGARA", "TIMUR", "TIMUR LAUT"]
YEARS = [2021, 2022, 2023, 2024, 2025]

AKT = [("KHIDMAT NASIHAT", "Khidmat nasihat"),
       ("KESIHATAN GEROMPOK (BIL PENTERNAK)", "Kesihatan gerompok"),
       ("RAWATAN BIASA (BIL KES)", "Kes rawatan"),
       ("PEMBIAKAN (BIL PENTERNAK)", "Pembiakbakaan"),
       ("LAWAT SIASAT", "Lawat siasat"),
       ("AUDIT/VERIFIKASI", "Regulatori"),
       ("PERSAMPELAN", "Pensampelan"),
       ("VAKSINASI", "Vaksinasi"),
       ("UJIAN LAPANGAN", "Ujian lapangan"),
       ("MESYUARAT", "Mesyuarat")]
ALIAS = {"BEBIRI": "BEBIRI PEDAGING"}


def read_year(sheet):
    ws = wb[sheet]
    rows = [[('' if c is None else str(c).strip()) for c in r]
            for r in ws.iter_rows(values_only=True)]
    hdr = next(i for i, r in enumerate(rows) if 'BARAT DAYA' in r)
    ci = {z: rows[hdr].index(z) for z in ZONES}
    out = {}
    for r in rows[hdr + 1:]:
        lab = (r[1] or r[0]).strip().upper()
        lab = ALIAS.get(lab, lab)
        if not lab:
            continue
        try:
            out[lab] = {z: int(float(r[ci[z]])) for z in ZONES}
        except (ValueError, IndexError):
            continue
    return out


D = {y: read_year(str(y)) for y in YEARS}

# ---------- bina siri ----------
S = {}                                   # S[metrik][zon] = senarai 5 tahun
for key, name in AKT:
    S[name] = {z: [D[y][key][z] for y in YEARS] for z in ZONES}
S["Output teknikal"] = {z: [sum(D[y][k][z] for k, _ in AKT) for y in YEARS] for z in ZONES}
S["Bilangan pegawai"] = {z: [D[y]['PEGAWAI TEKNIKAL'][z] for y in YEARS] for z in ZONES}
S["Program PPV"] = {z: [D[y]['BILANGAN PPV'][z] for y in YEARS] for z in ZONES}
S["Ladang dilawat"] = {z: [D[y]['BIL PENTERNAK DILAWAT'][z] for y in YEARS] for z in ZONES}
KOM = ["LEMBU TENUSU", "LEMBU PEDAGING", "KERBAU PEDAGING", "KERBAU TENUSU",
       "BEBIRI PEDAGING", "KAMBING PEDAGING", "KAMBING TENUSU"]
S["Penternak data asas"] = {z: [sum(D[y][k][z] for k in KOM) for y in YEARS] for z in ZONES}

UTAMA = ["Output teknikal", "Ladang dilawat", "Penternak data asas",
         "Program PPV", "Bilangan pegawai"]

res = {"zon": {}, "tahun": {}, "outlier": [], "aktiviti": {}, "meta": {}}

# ---------- A. profil tren setiap zon ----------
print("=" * 100)
print("A. TREN SETIAP ZON, 2021-2025")
for m in UTAMA:
    print(f"\n{m}")
    print(f"  {'ZON':<12}{'2021':>9}{'2025':>9}{'Δ%':>9}{'CAGR':>8}"
          f"{'CV%':>8}{'kecerunan':>12}{'p':>8}  bentuk")
    for z in ZONES:
        v = np.array(S[m][z], float)
        x = np.arange(5.0)
        sl, ic, r, p, se = stats.linregress(x, v)
        cagr = (v[4] / v[0]) ** 0.25 - 1 if v[0] > 0 else float('nan')
        cv = v.std(ddof=1) / v.mean() * 100
        # bentuk: monotonik naik/turun, puncak, palung, atau tidak menentu
        d = np.diff(v)
        if all(d > 0):
            bentuk = "menaik tekal"
        elif all(d < 0):
            bentuk = "menurun tekal"
        elif v.argmax() in (1, 2, 3) and v[v.argmax()] > v[0] and v[v.argmax()] > v[4]:
            bentuk = f"puncak {YEARS[v.argmax()]}"
        elif v.argmin() in (1, 2, 3) and v[v.argmin()] < v[0] and v[v.argmin()] < v[4]:
            bentuk = f"palung {YEARS[v.argmin()]}"
        else:
            bentuk = "tidak menentu"
        print(f"  {z:<12}{v[0]:>9,.0f}{v[4]:>9,.0f}{(v[4]/v[0]-1)*100:>8.1f}%"
              f"{cagr*100:>7.1f}%{cv:>7.1f}%{sl:>12,.0f}{p:>8.3f}  {bentuk}")
        res["zon"].setdefault(m, {})[z] = dict(
            v=[float(a) for a in v], d=float(v[4]/v[0]-1), cagr=float(cagr),
            cv=float(cv), slope=float(sl), p=float(p), bentuk=bentuk)

# ---------- B. adakah tahun penting? ANOVA dua hala ----------
print()
print("=" * 100)
print("B. KESAN TAHUN SELEPAS ZON DIKAWAL (log-output, model tambahan)")
print(f"  {'metrik':<22}{'F tahun':>10}{'p tahun':>10}{'F zon':>10}{'p zon':>10}"
      f"{'R² penuh':>10}")


def ols(y, X):
    X = np.column_stack([np.ones(len(y))] + list(X))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ b
    n, k = X.shape
    ssr = float(r @ r)
    sst = float(((y - y.mean()) ** 2).sum())
    return dict(b=b, ssr=ssr, df=n - k, r2=1 - ssr / sst, resid=r, X=X)


def ftest(r_, f_, q):
    F = ((r_['ssr'] - f_['ssr']) / q) / (f_['ssr'] / f_['df'])
    return F, 1 - stats.f.cdf(F, q, f_['df'])


cells = [(z, y) for z in ZONES for y in YEARS]
zd = [np.array([1.0 if z == zz else 0.0 for zz, _ in cells]) for zz in ZONES[1:]]
td = [np.array([1.0 if y == tt else 0.0 for _, y in cells]) for tt in YEARS[1:]]

for m in UTAMA:
    y = np.array([S[m][z][YEARS.index(t)] for z, t in cells], float)
    ly = np.log(np.maximum(y, 1))
    full = ols(ly, zd + td)
    noT = ols(ly, zd)
    noZ = ols(ly, td)
    Ft, pt = ftest(noT, full, 4)
    Fz, pz = ftest(noZ, full, 6)
    print(f"  {m:<22}{Ft:>10.2f}{pt:>10.4f}{Fz:>10.2f}{pz:>10.4f}{full['r2']:>10.3f}")
    res["tahun"][m] = dict(Ft=float(Ft), pt=float(pt), Fz=float(Fz), pz=float(pz),
                           r2=float(full['r2']),
                           kesan_tahun=[0.0] + [float(v) for v in full['b'][1 + len(zd):]])

# ---------- C. kesan setiap tahun (output teknikal) ----------
print()
print("Kesan setiap tahun ke atas output teknikal (log, 2021 = rujukan)")
y = np.array([S["Output teknikal"][z][YEARS.index(t)] for z, t in cells], float)
full = ols(np.log(y), zd + td)
eff = [0.0] + list(full['b'][1 + len(zd):])
for t, e in zip(YEARS, eff):
    print(f"  {t}   {e:+.3f} log  ≈ {(np.exp(e)-1)*100:+6.1f}% berbanding 2021")

# ---------- D. pengesanan outlier zon x tahun ----------
print()
print("=" * 100)
print("D. SEL ZON × TAHUN YANG TERKELUAR DARIPADA CORAK (baki piawai)")
for m in UTAMA:
    y = np.array([S[m][z][YEARS.index(t)] for z, t in cells], float)
    ly = np.log(np.maximum(y, 1))
    f = ols(ly, zd + td)
    r = f['resid']
    s = r.std(ddof=len(f['b']))
    zsc = r / s if s > 0 else r * 0
    flag = [(abs(v), cells[i], v) for i, v in enumerate(zsc) if abs(v) > 1.9]
    if not flag:
        continue
    print(f"\n{m}")
    for _, (zz, tt), v in sorted(flag, reverse=True):
        obs = S[m][zz][YEARS.index(tt)]
        fitted = float(np.exp(f['X'][cells.index((zz, tt))] @ f['b']))
        print(f"  {zz:<12}{tt}   cerapan {obs:>8,}   jangkaan {fitted:>8,.0f}   "
              f"baki {v:+.2f} sisihan piawai")
        res["outlier"].append(dict(metrik=m, zon=zz, tahun=tt, obs=float(obs),
                                   jangka=fitted, z=float(v)))

# ---------- E. apa yang memacu setiap outlier output ----------
print()
print("=" * 100)
print("E. PECAHAN ALIRAN AKTIVITI BAGI SEL OUTLIER OUTPUT TEKNIKAL")
outs = [o for o in res["outlier"] if o["metrik"] == "Output teknikal"]
for o in outs:
    zz, tt = o["zon"], o["tahun"]
    i = YEARS.index(tt)
    print(f"\n{zz} {tt} — output {o['obs']:,.0f} berbanding jangkaan {o['jangka']:,.0f}")
    base = {n: np.median([S[n][zz][j] for j in range(5) if j != i]) for _, n in AKT}
    rows = []
    for _, n in AKT:
        cur = S[n][zz][i]
        rows.append((cur - base[n], n, cur, base[n]))
    for dv, n, cur, b in sorted(rows, key=lambda r: -abs(r[0]))[:4]:
        pctv = (cur / b - 1) * 100 if b else float('inf')
        print(f"    {n:<20}{cur:>8,}  median tahun lain {b:>8,.0f}   {dv:+9,.0f}"
              f"  ({pctv:+.0f}%)")
        res["aktiviti"].setdefault(f"{zz} {tt}", []).append(
            dict(aliran=n, nilai=float(cur), median=float(b), delta=float(dv)))

# ---------- F. kestabilan setiap zon ----------
print()
print("=" * 100)
print("F. KESTABILAN ZON — pekali variasi output teknikal, 2021-2025")
cvs = sorted(((np.std(S["Output teknikal"][z], ddof=1) /
               np.mean(S["Output teknikal"][z]) * 100), z) for z in ZONES)
for cv, z in cvs:
    v = S["Output teknikal"][z]
    print(f"  {z:<12}CV {cv:>5.1f}%   min {min(v):>7,}   maks {max(v):>7,}   "
          f"nisbah maks/min {max(v)/min(v):>4.1f}×")
    res["meta"].setdefault("cv", {})[z] = float(cv)

json.dump(res, open('tren.json', 'w'), indent=1)
json.dump({m: S[m] for m in S}, open('siri.json', 'w'), indent=1)
print("\n\nDisimpan: tren.json, siri.json")

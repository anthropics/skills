"""Bina panel zon x tahun daripada LAPORAN LOG TEKNIKAL 2021-2026, dan uji sama ada
campuran komoditi mempengaruhi output perkhidmatan."""
import openpyxl, json, itertools
import numpy as np
from scipy import stats

wb = openpyxl.load_workbook('logteknikal.xlsx', data_only=True)
ZONES = ["BARAT DAYA","SELATAN","TENGAH","TENGGARA","TIMUR","TIMUR LAUT","UTARA"]
YEARS = [2021, 2022, 2023, 2024, 2025]          # 2026 dikecualikan: hanya 4 bulan

KOM = ["LEMBU TENUSU","LEMBU PEDAGING","KERBAU PEDAGING","KERBAU TENUSU",
       "BEBIRI PEDAGING","KAMBING PEDAGING","KAMBING TENUSU"]
# 2022 melabel bebiri sebagai "BEBIRI" sahaja
ALIAS = {"BEBIRI": "BEBIRI PEDAGING"}

# sepuluh aliran yang menjumlahkan kepada JUMLAH OUTPUT dalam lembaran RUMUSAN
AKT = ["KHIDMAT NASIHAT","KESIHATAN GEROMPOK (BIL PENTERNAK)","RAWATAN BIASA (BIL KES)",
       "PEMBIAKAN (BIL PENTERNAK)","LAWAT SIASAT","AUDIT/VERIFIKASI","PERSAMPELAN",
       "VAKSINASI","UJIAN LAPANGAN","MESYUARAT"]
AKT_SHORT = {"KHIDMAT NASIHAT":"nasihat","KESIHATAN GEROMPOK (BIL PENTERNAK)":"gerompok",
    "RAWATAN BIASA (BIL KES)":"rawatan","PEMBIAKAN (BIL PENTERNAK)":"pembiakan",
    "LAWAT SIASAT":"siasat","AUDIT/VERIFIKASI":"regulatori","PERSAMPELAN":"sampel",
    "VAKSINASI":"vaksin","UJIAN LAPANGAN":"ujian","MESYUARAT":"mesyuarat"}


def read_year(sheet):
    """Kembalikan {label: {zon: nilai}} bagi satu lembaran tahun."""
    ws = wb[sheet]
    rows = [[('' if c is None else str(c).strip()) for c in r]
            for r in ws.iter_rows(values_only=True)]
    hdr = next(i for i, r in enumerate(rows) if 'BARAT DAYA' in r)
    cols = {r: rows[hdr].index(r) for r in ZONES}
    out = {}
    for r in rows[hdr + 1:]:
        label = (r[1] or r[0]).strip().upper()
        label = ALIAS.get(label, label)
        if not label:
            continue
        try:
            out[label] = {z: int(float(r[cols[z]])) for z in ZONES}
        except (ValueError, IndexError):
            continue
    return out


data = {y: read_year(str(y)) for y in YEARS}

# ---------- bina panel ----------
panel = []
for y in YEARS:
    d = data[y]
    for z in ZONES:
        kom = {k: d[k][z] for k in KOM}
        pen = sum(kom.values())
        akt = {AKT_SHORT[a]: d[a][z] for a in AKT}
        out = sum(akt.values())
        row = dict(zon=z, tahun=y, out=out, pen=pen,
                   peg=d['PEGAWAI TEKNIKAL'][z], ppv=d['BILANGAN PPV'][z],
                   lad=d['BIL PENTERNAK DILAWAT'][z], **akt)
        # bahagian komoditi
        for k in KOM:
            row['s_' + k.lower().replace(' ', '_')] = kom[k] / pen if pen else 0
        row['s_tenusu'] = (kom['LEMBU TENUSU'] + kom['KERBAU TENUSU'] +
                           kom['KAMBING TENUSU']) / pen if pen else 0
        row['s_kecil'] = (kom['BEBIRI PEDAGING'] + kom['KAMBING PEDAGING'] +
                          kom['KAMBING TENUSU']) / pen if pen else 0
        row['s_besar'] = 1 - row['s_kecil']
        # kepelbagaian Herfindahl terbalik: 1 = sangat pelbagai, 0 = satu komoditi
        row['hhi'] = sum((v / pen) ** 2 for v in kom.values()) if pen else 1
        row['pelbagai'] = 1 - row['hhi']
        row['kom'] = kom
        panel.append(row)

# ---------- semakan integriti ----------
print("=" * 76)
print("SEMAKAN: jumlah zon berbanding lembaran RUMUSAN")
ws = wb['RUMUSAN']
rum = {}
for r in ws.iter_rows(values_only=True):
    if r[1] and isinstance(r[2], (int, float)):
        rum[str(r[1]).strip()] = [r[2 + i] for i in range(5)]
chk = [('Jumlah Pegawai/Kakitangan Teknikal', 'peg'),
       ('Jumlah Bilangan Penternak Data Asas Ruminan VetEC', 'pen'),
       ('Bilangan Program Pengembangan Veterinar (PPV)', 'ppv'),
       ('Bil Ladang dilawat', 'lad')]
for lbl, key in chk:
    got = [sum(r[key] for r in panel if r['tahun'] == y) for y in YEARS]
    exp = [int(v) for v in rum[lbl]]
    print(f"  {key:5} panel={got}  rumusan={exp}  {'OK' if got == exp else '<-- BEZA'}")
got = [sum(r['out'] for r in panel if r['tahun'] == y) for y in YEARS]
print(f"  out   panel={got}  rumusan=[293812, 274700, 250983, 234476, 266605]")

json.dump([{k: v for k, v in r.items() if k != 'kom'} for r in panel],
          open('panel.json', 'w'), indent=0)


# ---------- alat regresi ----------
def ols(y, X, names):
    """OLS dengan pintasan; kembalikan pekali, ralat piawai, nilai-p, R2, ssr, df."""
    X = np.column_stack([np.ones(len(y))] + list(X))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    resid = y - X @ b
    n, k = X.shape
    df = n - k
    ssr = float(resid @ resid)
    sst = float(((y - y.mean()) ** 2).sum())
    s2 = ssr / df
    XtXi = np.linalg.pinv(X.T @ X)
    se = np.sqrt(np.diag(XtXi) * s2)
    t = b / se
    p = 2 * (1 - stats.t.cdf(np.abs(t), df))
    return dict(b=b, se=se, p=p, r2=1 - ssr / sst,
                adj=1 - (ssr / df) / (sst / (n - 1)), ssr=ssr, df=df,
                names=['const'] + names)


def ftest(restricted, full, q):
    """Ujian-F blok: adakah q pemboleh ubah tambahan menyumbang?"""
    num = (restricted['ssr'] - full['ssr']) / q
    den = full['ssr'] / full['df']
    F = num / den
    return F, 1 - stats.f.cdf(F, q, full['df'])


zon_d = [np.array([1.0 if r['zon'] == z else 0.0 for r in panel]) for z in ZONES[1:]]
thn_d = [np.array([1.0 if r['tahun'] == t else 0.0 for r in panel]) for t in YEARS[1:]]
v = lambda k: np.array([float(r[k]) for r in panel])

print()
print("=" * 76)
print("SOALAN 1 — ADAKAH CAMPURAN KOMODITI BERBEZA MENGIKUT ZON?")
print()
print("Bahagian ruminan kecil (kambing + bebiri) daripada asas penternak, %")
print(f"  {'ZON':<12}" + "".join(f"{y:>8}" for y in YEARS) + "     Δ")
for z in ZONES:
    s = [next(r for r in panel if r['zon'] == z and r['tahun'] == y)['s_kecil'] for y in YEARS]
    print(f"  {z:<12}" + "".join(f"{x*100:>8.1f}" for x in s) +
          f"  {(s[-1]-s[0])*100:+6.1f}")
nat = []
for y in YEARS:
    rs = [r for r in panel if r['tahun'] == y]
    nat.append(sum(r['s_kecil'] * r['pen'] for r in rs) / sum(r['pen'] for r in rs))
print(f"  {'KEBANGSAAN':<12}" + "".join(f"{x*100:>8.1f}" for x in nat) +
      f"  {(nat[-1]-nat[0])*100:+6.1f}")

print()
print("Bahagian tenusu (lembu + kerbau + kambing tenusu), %")
print(f"  {'ZON':<12}" + "".join(f"{y:>8}" for y in YEARS) + "     Δ")
for z in ZONES:
    s = [next(r for r in panel if r['zon'] == z and r['tahun'] == y)['s_tenusu'] for y in YEARS]
    print(f"  {z:<12}" + "".join(f"{x*100:>8.1f}" for x in s) +
          f"  {(s[-1]-s[0])*100:+6.1f}")

# berapa banyak variasi campuran komoditi adalah antara-zon vs dalam-zon?
print()
print("Penguraian varians bahagian komoditi: antara-zon berbanding dalam-zon")
for lbl, key in [("ruminan kecil", 's_kecil'), ("tenusu", 's_tenusu'),
                 ("lembu pedaging", 's_lembu_pedaging'), ("kepelbagaian", 'pelbagai')]:
    x = v(key)
    zmean = np.array([np.mean([r[key] for r in panel if r['zon'] == r2['zon']])
                      for r2 in panel])
    between = ((zmean - x.mean()) ** 2).sum()
    within = ((x - zmean) ** 2).sum()
    print(f"  {lbl:<16} antara-zon {between/(between+within)*100:5.1f}%   "
          f"dalam-zon {within/(between+within)*100:5.1f}%")

print()
print("=" * 76)
print("SOALAN 2 — ADAKAH CAMPURAN KOMODITI MEMPENGARUHI OUTPUT?")
print()
y = v('out')
peg = v('peg')
kecil, tenusu, pelbagai = v('s_kecil'), v('s_tenusu'), v('pelbagai')
pen, lad = v('pen'), v('lad')

m_kom = ols(y, [kecil, tenusu, pelbagai], ['s_kecil', 's_tenusu', 'pelbagai'])
print("Model K — komoditi sahaja")
for n_, b_, p_ in zip(m_kom['names'], m_kom['b'], m_kom['p']):
    print(f"    {n_:<12} b={b_:>12,.0f}  p={p_:.4f}")
print(f"    R2={m_kom['r2']:.4f}  adj={m_kom['adj']:.4f}")

m_base = ols(y, [peg] + zon_d, ['peg'] + [f'z_{z}' for z in ZONES[1:]])
m_full = ols(y, [peg] + zon_d + [kecil, tenusu, pelbagai],
             ['peg'] + [f'z_{z}' for z in ZONES[1:]] + ['s_kecil', 's_tenusu', 'pelbagai'])
F, p = ftest(m_base, m_full, 3)
print()
print("Model B  — pegawai + kesan tetap zon           "
      f"R2={m_base['r2']:.4f}  adj={m_base['adj']:.4f}")
print("Model B+K— pegawai + zon + 3 pemboleh ubah komoditi "
      f"R2={m_full['r2']:.4f}  adj={m_full['adj']:.4f}")
print(f"    Ujian-F blok komoditi:  F(3,{m_full['df']}) = {F:.3f}   p = {p:.4f}")

m_bt = ols(y, [peg] + zon_d + thn_d, ['peg'] + [f'z_{z}' for z in ZONES[1:]] +
           [f't_{t}' for t in YEARS[1:]])
m_btk = ols(y, [peg] + zon_d + thn_d + [kecil, tenusu, pelbagai],
            ['peg'] + [f'z_{z}' for z in ZONES[1:]] + [f't_{t}' for t in YEARS[1:]] +
            ['s_kecil', 's_tenusu', 'pelbagai'])
F2, p2 = ftest(m_bt, m_btk, 3)
print()
print("Model BT  — pegawai + zon + tahun              "
      f"R2={m_bt['r2']:.4f}  adj={m_bt['adj']:.4f}")
print("Model BT+K— tambah komoditi                    "
      f"R2={m_btk['r2']:.4f}  adj={m_btk['adj']:.4f}")
print(f"    Ujian-F blok komoditi:  F(3,{m_btk['df']}) = {F2:.3f}   p = {p2:.4f}")

# ujian dalam-zon: adakah perubahan campuran komoditi seiring perubahan output?
print()
print("Ujian dalam-zon (min zon ditolak) — korelasi perubahan")
def demean(a):
    out = np.array(a, float)
    for z in ZONES:
        idx = [i for i, r in enumerate(panel) if r['zon'] == z]
        out[idx] -= out[idx].mean()
    return out
for lbl, key in [("ruminan kecil", 's_kecil'), ("tenusu", 's_tenusu'),
                 ("kepelbagaian", 'pelbagai'), ("penternak", 'pen'),
                 ("ladang dilawat", 'lad'), ("pegawai", 'peg')]:
    r_, p_ = stats.pearsonr(demean(v(key)), demean(y))
    flag = "  <-- signifikan" if p_ < 0.05 else ""
    print(f"    {lbl:<16} r={r_:+.3f}  p={p_:.4f}{flag}")

print()
print("=" * 76)
print("SOALAN 2b — ADAKAH KOMODITI MEMPENGARUHI *JENIS* KERJA, BUKAN JUMLAHNYA?")
print()
print("Bahagian setiap aliran aktiviti dijelaskan oleh komoditi, selepas zon dikawal")
print(f"  {'aliran':<12}{'R2 zon+peg':>12}{'+komoditi':>11}{'F':>8}{'p':>9}")
res_akt = []
for a in AKT:
    k = AKT_SHORT[a]
    share = v(k) / v('out')
    b0 = ols(share, [peg] + zon_d, ['peg'] + [f'z_{z}' for z in ZONES[1:]])
    b1 = ols(share, [peg] + zon_d + [kecil, tenusu, pelbagai],
             ['peg'] + [f'z_{z}' for z in ZONES[1:]] + ['s_kecil', 's_tenusu', 'pelbagai'])
    F3, p3 = ftest(b0, b1, 3)
    res_akt.append((k, b0['r2'], b1['r2'], F3, p3))
for k, r0, r1, F3, p3 in sorted(res_akt, key=lambda x: x[4]):
    flag = "  <-- signifikan" if p3 < 0.05 else ""
    print(f"  {k:<12}{r0:>12.3f}{r1:>11.3f}{F3:>8.2f}{p3:>9.4f}{flag}")

print()
print("Korelasi mudah: bahagian komoditi lawan bahagian aliran aktiviti (n=35)")
print(f"  {'aliran':<12}{'ruminan kecil':>15}{'tenusu':>15}{'lembu pedaging':>17}")
for a in AKT:
    k = AKT_SHORT[a]
    share = v(k) / v('out')
    cells = []
    for key in ['s_kecil', 's_tenusu', 's_lembu_pedaging']:
        r_, p_ = stats.pearsonr(v(key), share)
        cells.append(f"{r_:+.2f}{'*' if p_ < 0.05 else ' '}")
    print(f"  {k:<12}{cells[0]:>15}{cells[1]:>15}{cells[2]:>17}")
print("  * p < 0.05")

print()
print("=" * 76)
print("KESAN KE ATAS INTENSITI: output setiap penternak")
inten = y / pen
m0 = ols(inten, [peg] + zon_d, ['peg'] + [f'z_{z}' for z in ZONES[1:]])
m1 = ols(inten, [peg] + zon_d + [kecil, tenusu, pelbagai],
         ['peg'] + [f'z_{z}' for z in ZONES[1:]] + ['s_kecil', 's_tenusu', 'pelbagai'])
F4, p4 = ftest(m0, m1, 3)
print(f"  zon+pegawai R2={m0['r2']:.3f}   +komoditi R2={m1['r2']:.3f}   "
      f"F(3,{m1['df']})={F4:.2f}  p={p4:.4f}")
for n_, b_, p_ in zip(m1['names'], m1['b'], m1['p']):
    if n_.startswith('s_') or n_ == 'pelbagai':
        print(f"    {n_:<12} b={b_:>10.1f}  p={p_:.4f}")

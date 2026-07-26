"""Ujian lanjutan: dari mana pekali lawatan datang, dan adakah ia sebab atau
produk bersama. Susulan kepada lawatan.py."""
import openpyxl, json
import numpy as np
from scipy import stats

rng = np.random.default_rng(7)
wb = openpyxl.load_workbook('lt_v3.xlsx', data_only=True)
Z = ["UTARA", "TENGAH", "BARAT DAYA", "SELATAN", "TENGGARA", "TIMUR", "TIMUR LAUT"]
Y = [2021, 2022, 2023, 2024, 2025]
AKT = ["KHIDMAT NASIHAT", "KESIHATAN GEROMPOK (BIL PENTERNAK)", "RAWATAN BIASA (BIL KES)",
       "PEMBIAKAN (BIL PENTERNAK)", "LAWAT SIASAT", "AUDIT/VERIFIKASI", "PERSAMPELAN",
       "VAKSINASI", "UJIAN LAPANGAN", "MESYUARAT"]
AKTLAB = ["Khidmat nasihat", "Kesihatan gerompok", "Kes rawatan", "Pembiakbakaan",
          "Lawat siasat", "Regulatori", "Pensampelan", "Vaksinasi",
          "Ujian lapangan", "Mesyuarat"]
KAMPEN = ["Pensampelan", "Vaksinasi", "Ujian lapangan"]
KOM = ["LEMBU TENUSU", "LEMBU PEDAGING", "KERBAU PEDAGING", "KERBAU TENUSU",
       "BEBIRI PEDAGING", "KAMBING PEDAGING", "KAMBING TENUSU"]
ALIAS = {"BEBIRI": "BEBIRI PEDAGING"}


def read_year(sheet):
    ws = wb[sheet]
    rows = [[('' if c is None else str(c).strip()) for c in r]
            for r in ws.iter_rows(values_only=True)]
    h = next(i for i, r in enumerate(rows) if 'BARAT DAYA' in r)
    ci = {z: rows[h].index(z) for z in Z}
    o = {}
    for r in rows[h + 1:]:
        lab = (r[1] or r[0]).strip().upper()
        lab = ALIAS.get(lab, lab)
        if not lab:
            continue
        try:
            o[lab] = {z: int(float(r[ci[z]])) for z in Z}
        except (ValueError, IndexError):
            pass
    return o


D = {y: read_year(str(y)) for y in Y}
cells = [(z, y) for z in Z for y in Y]
def col(f): return np.array([f(z, y) for z, y in cells], float)

akt = {lab: col(lambda z, y, k=k: D[y][k][z]) for k, lab in zip(AKT, AKTLAB)}
out = sum(akt.values())
kamp = sum(akt[l] for l in KAMPEN)
lain = out - kamp
lad = col(lambda z, y: D[y]['BIL PENTERNAK DILAWAT'][z])
peg = col(lambda z, y: D[y]['PEGAWAI TEKNIKAL'][z])
pen = col(lambda z, y: sum(D[y][k][z] for k in KOM))
zi = np.array([Z.index(z) for z, _ in cells])
yi = np.array([Y.index(y) for _, y in cells])
zd = [(zi == j).astype(float) for j in range(1, 7)]
td = [(yi == j).astype(float) for j in range(1, 5)]
R = {}


def ols(y, cols, names):
    X = np.column_stack([np.ones(len(y))] + list(cols))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ b
    df = len(y) - X.shape[1]
    s2 = float(r @ r) / df
    se = np.sqrt(np.diag(np.linalg.pinv(X.T @ X)) * s2)
    t = b / se
    p = 2 * (1 - stats.t.cdf(np.abs(t), df))
    sst = float(((y - y.mean()) ** 2).sum())
    return dict(b=b, se=se, p=p, df=df, r2=1 - float(r @ r) / sst,
                names=['const'] + names)


def fe(y, l_, sel=None, extra=(), enames=()):
    s = np.ones(len(y), bool) if sel is None else sel
    zk = [(zi[s] == k).astype(float) for k in sorted(set(zi[s]))[1:]]
    tk = [(yi[s] == k).astype(float) for k in sorted(set(yi[s]))[1:]]
    m = ols(y[s], [l_[s], peg[s]] + [e[s] for e in extra] + zk + tk,
            ['lawatan', 'pegawai'] + list(enames) +
            [f'z{j}' for j in range(len(zk))] + [f't{j}' for j in range(len(tk))])
    i = m['names'].index('lawatan')
    return float(m['b'][i]), float(m['se'][i]), float(m['p'][i]), m['df']


print("=" * 100)
print("J. ADAKAH KESAN INI HANYA KERJA KEMPEN? Pecahkan output kepada dua bahagian")
print(f"  {'sasaran':<40}{'b':>10}{'SE':>9}{'p':>9}{'% output':>10}")
for lab, v in [("Output penuh (10 aliran)", out),
               ("Aliran kempen (sampel+vaksin+ujian)", kamp),
               ("Aliran bukan kempen (7 lain)", lain)]:
    b, se, p, _ = fe(v, lad)
    print(f"  {lab:<40}{b:>+10.2f}{se:>9.2f}{p:>9.4f}{v.sum()/out.sum()*100:>9.1f}%")
    R.setdefault('kempen', {})[lab] = dict(b=b, se=se, p=p)

print("\n  Nisbah: kerja kempen ialah "
      f"{kamp.sum()/out.sum()*100:.1f}% output tetapi "
      f"{R['kempen']['Aliran kempen (sampel+vaksin+ujian)']['b']/R['kempen']['Output penuh (10 aliran)']['b']*100:.0f}% "
      "pekali lawatan.")

print()
print("=" * 100)
print("K. LEVERAJ 2021 — mengapa menggugurkan satu tahun memusnahkan pekali")
print(f"  {'tahun':<10}{'lawatan':>10}{'output':>10}{'output/lawatan':>16}"
      f"{'pegawai':>10}")
for j, y in enumerate(Y):
    s = yi == j
    print(f"  {y:<10}{lad[s].sum():>10,.0f}{out[s].sum():>10,.0f}"
          f"{out[s].sum()/lad[s].sum():>15.1f}{peg[s].sum():>10,.0f}")
R['tahunan'] = {int(y): dict(lawatan=float(lad[yi == j].sum()),
                            output=float(out[yi == j].sum()))
                for j, y in enumerate(Y)}

print("\n  Kedudukan 2021 dalam setiap zon (baki daripada model tanpa lawatan):")
m0 = ols(out, [peg] + zd + td, ['pegawai'] + [f'z{j}' for j in range(1, 7)] +
         [f't{j}' for j in range(1, 5)])
X0 = np.column_stack([np.ones(35), peg] + zd + td)
r_out = out - X0 @ m0['b']
ml = ols(lad, [peg] + zd + td, ['pegawai'] + [f'z{j}' for j in range(1, 7)] +
         [f't{j}' for j in range(1, 5)])
r_lad = lad - X0 @ ml['b']
print(f"  {'zon':<12}" + "".join(f"{y:>16}" for y in Y))
print(f"  {'':12}" + "".join(f"{'baki L / baki O':>16}" for _ in Y)[:16 * 5])
for j, z in enumerate(Z):
    s = np.where(zi == j)[0]
    print(f"  {z:<12}" + "".join(f"{r_lad[i]:>+7.0f}/{r_out[i]:>+8.0f}" for i in s))
kontrib = r_lad * r_out
print(f"\n  Sumbangan setiap tahun kepada kovarians baki (pengangka pekali):")
tot = kontrib.sum()
for j, y in enumerate(Y):
    s = yi == j
    print(f"    {y}   {kontrib[s].sum()/tot*100:>6.1f}% "
          f"{'█' * max(0, int(abs(kontrib[s].sum()/tot*40)))}")
R['sumbangan_tahun'] = {int(y): float(kontrib[yi == j].sum() / tot)
                        for j, y in enumerate(Y)}

top = np.argsort(-np.abs(kontrib))[:5]
print("\n  Lima sel paling berpengaruh:")
for i in top:
    print(f"    {cells[i][0]:<12}{cells[i][1]}   baki lawatan {r_lad[i]:>+7.0f}   "
          f"baki output {r_out[i]:>+8.0f}   {kontrib[i]/tot*100:>+6.1f}% pekali")
R['sel_berpengaruh'] = [dict(zon=cells[i][0], tahun=cells[i][1],
                            bahagian=float(kontrib[i] / tot)) for i in top]

print()
print("=" * 100)
print("L. UJIAN GUGUR-SATU-SEL — adakah satu cerapan memacu keseluruhan dapatan?")
res = []
for i in range(35):
    s = np.ones(35, bool); s[i] = False
    b, se, p, _ = fe(out, lad, s)
    res.append((p, b, cells[i]))
res.sort(reverse=True)
print(f"  {'sel digugurkan':<24}{'b':>10}{'p':>10}")
for p, b, c in res[:4]:
    print(f"  {c[0] + ' ' + str(c[1]):<24}{b:>+10.2f}{p:>10.4f}")
print(f"  {'...':<24}")
print(f"  {'julat 35 ujian':<24}"
      f"{min(r[1] for r in res):>+6.1f} … {max(r[1] for r in res):<+6.1f}"
      f"{min(r[0] for r in res):>6.4f} … {max(r[0] for r in res):.4f}")
n_sig = sum(1 for r in res if r[0] < .05)
print(f"  Kekal signifikan dalam {n_sig} daripada 35 ujian gugur-satu-sel")
R['gugur_sel'] = dict(n_sig=int(n_sig),
                      b_min=float(min(r[1] for r in res)),
                      b_max=float(max(r[1] for r in res)),
                      p_max=float(max(r[0] for r in res)))

print()
print("=" * 100)
print("M. ARAH KESEPADANAN — ujian tanda ke atas 28 perubahan tahunan")
d_out, d_lad = [], []
for j in range(7):
    s = zi == j
    d_out += list(np.diff(out[s])); d_lad += list(np.diff(lad[s]))
d_out, d_lad = np.array(d_out), np.array(d_lad)
k = int(np.sum(np.sign(d_out) == np.sign(d_lad)))
pb = float(stats.binomtest(k, len(d_out), 0.5).pvalue)
print(f"  Sepadan {k}/{len(d_out)} ({k/len(d_out)*100:.0f}%), ujian binomial p = {pb:.4f}")
naik = d_lad > 0
print(f"  Apabila lawatan NAIK  (n={naik.sum():2d}): output naik "
      f"{int((d_out[naik] > 0).sum())} kali, purata Δoutput {d_out[naik].mean():+,.0f}")
print(f"  Apabila lawatan TURUN (n={(~naik).sum():2d}): output naik "
      f"{int((d_out[~naik] > 0).sum())} kali, purata Δoutput {d_out[~naik].mean():+,.0f}")
R['tanda'] = dict(k=k, n=int(len(d_out)), p=pb)

print()
print("=" * 100)
print("N. KAWALAN PEMBOHONG — adakah lawatan 'meramal' perkara yang ia tidak boleh sebabkan?")
for lab, v in [("Bilangan pegawai (ditetapkan pusat)", peg),
               ("Bilangan penternak dalam pangkalan data", pen),
               ("Program PPV (sasaran kebangsaan)", col(
                   lambda z, y: D[y]['BILANGAN PPV'][z]))]:
    zk = [(zi == k).astype(float) for k in range(1, 7)]
    tk = [(yi == k).astype(float) for k in range(1, 5)]
    m = ols(v, [lad] + zk + tk, ['lawatan'] + [f'z{j}' for j in range(1, 7)] +
            [f't{j}' for j in range(1, 5)])
    i = m['names'].index('lawatan')
    flag = '  ← sepatutnya nol' if m['p'][i] < .05 else ''
    print(f"  {lab:<44}b = {m['b'][i]:>+9.4f}  p = {m['p'][i]:.4f}{flag}")
    R.setdefault('pembohong', {})[lab] = dict(b=float(m['b'][i]), p=float(m['p'][i]))

print()
print("=" * 100)
print("O. LIPUTAN DAN PULANGAN — adakah kesan bergantung pada liputan sedia ada?")
lb = lad / pen
med = np.median([lb[zi == j].mean() for j in range(7)])
tinggi = np.array([lb[zi == j].mean() > med for j in zi])
print(f"  Ambang liputan zon: {med:.2f} lawatan setiap penternak")
for lab, s in [("Zon liputan RENDAH", ~tinggi), ("Zon liputan TINGGI", tinggi)]:
    b, se, p, df = fe(out, lad, s)
    zs = sorted({Z[j] for j in zi[s]})
    print(f"  {lab:<22}b = {b:>+8.2f}  SE {se:>6.2f}  p = {p:.4f}  "
          f"(n = {int(s.sum())})")
    print(f"    {', '.join(zs)}")
    R.setdefault('liputan', {})[lab] = dict(b=b, se=se, p=p)

inter = lad * tinggi.astype(float)
zk = [(zi == k).astype(float) for k in range(1, 7)]
tk = [(yi == k).astype(float) for k in range(1, 5)]
m = ols(out, [lad, inter, peg] + zk + tk,
        ['lawatan', 'inter', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
        [f't{j}' for j in range(1, 5)])
i = m['names'].index('inter')
print(f"  Sebutan interaksi (liputan tinggi × lawatan): {m['b'][i]:+.2f}, "
      f"p = {m['p'][i]:.4f}")
R['liputan_interaksi'] = dict(b=float(m['b'][i]), p=float(m['p'][i]))

json.dump(R, open('lawatan2.json', 'w'), indent=1)
print("\nDisimpan: lawatan2.json")

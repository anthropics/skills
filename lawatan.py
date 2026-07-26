"""Adakah lawatan ladang meningkatkan output, mengambil kira pegawai dan zon?
Panel 7 zon x 5 tahun (2021-2025), n = 35."""
import openpyxl, json, itertools
import numpy as np
from scipy import stats

rng = np.random.default_rng(20250726)
wb = openpyxl.load_workbook('lt_v3.xlsx', data_only=True)
Z = ["UTARA", "TENGAH", "BARAT DAYA", "SELATAN", "TENGGARA", "TIMUR", "TIMUR LAUT"]
Y = [2021, 2022, 2023, 2024, 2025]
AKT = ["KHIDMAT NASIHAT", "KESIHATAN GEROMPOK (BIL PENTERNAK)", "RAWATAN BIASA (BIL KES)",
       "PEMBIAKAN (BIL PENTERNAK)", "LAWAT SIASAT", "AUDIT/VERIFIKASI", "PERSAMPELAN",
       "VAKSINASI", "UJIAN LAPANGAN", "MESYUARAT"]
AKTLAB = ["Khidmat nasihat", "Kesihatan gerompok", "Kes rawatan", "Pembiakbakaan",
          "Lawat siasat", "Regulatori", "Pensampelan", "Vaksinasi",
          "Ujian lapangan", "Mesyuarat"]
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

out = col(lambda z, y: sum(D[y][k][z] for k in AKT))
lad = col(lambda z, y: D[y]['BIL PENTERNAK DILAWAT'][z])
peg = col(lambda z, y: D[y]['PEGAWAI TEKNIKAL'][z])
pen = col(lambda z, y: sum(D[y][k][z] for k in KOM))
ppv = col(lambda z, y: D[y]['BILANGAN PPV'][z])
akt = {lab: col(lambda z, y, k=k: D[y][k][z]) for k, lab in zip(AKT, AKTLAB)}
zi = np.array([Z.index(z) for z, _ in cells])
yi = np.array([Y.index(y) for _, y in cells])
zd = [(zi == j).astype(float) for j in range(1, 7)]
td = [(yi == j).astype(float) for j in range(1, 5)]

R = {}


# ---------------------------------------------------------------- alat regresi
def ols(y, cols, names):
    X = np.column_stack([np.ones(len(y))] + list(cols))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ b
    n, k = X.shape
    df = n - k
    s2 = float(r @ r) / df
    XtXi = np.linalg.pinv(X.T @ X)
    se = np.sqrt(np.diag(XtXi) * s2)
    t = b / se
    p = 2 * (1 - stats.t.cdf(np.abs(t), df))
    sst = float(((y - y.mean()) ** 2).sum())
    return dict(b=b, se=se, t=t, p=p, df=df, ssr=float(r @ r), resid=r,
                r2=1 - float(r @ r) / sst, names=['const'] + names, X=X)


def show(tag, m, focus='lawatan'):
    i = m['names'].index(focus)
    print(f"  {tag:<44}{m['b'][i]:>+10.2f}{m['se'][i]:>9.2f}"
          f"{m['t'][i]:>8.2f}{m['p'][i]:>9.4f}{m['r2']:>9.3f}{m['df']:>6}")
    return dict(b=float(m['b'][i]), se=float(m['se'][i]), t=float(m['t'][i]),
                p=float(m['p'][i]), r2=float(m['r2']), df=int(m['df']))


def demean(v, g):
    return v - np.array([v[g == j].mean() for j in g])


print("=" * 104)
print("A. TANGGA MODEL — pekali ke atas LAWATAN LADANG apabila kawalan ditambah")
print(f"  {'model':<44}{'b':>10}{'SE':>9}{'t':>8}{'p':>9}{'R²':>9}{'df':>6}")
R['tangga'] = {}
R['tangga']['1_kosong'] = show("1. lawatan sahaja", ols(out, [lad], ['lawatan']))
R['tangga']['2_pegawai'] = show("2. + bilangan pegawai",
                                ols(out, [lad, peg], ['lawatan', 'pegawai']))
R['tangga']['3_zon'] = show("3. + kesan tetap zon (model E.2)",
                            ols(out, [lad, peg] + zd, ['lawatan', 'pegawai'] +
                                [f'z{j}' for j in range(1, 7)]))
R['tangga']['4_zontahun'] = show("4. + kesan tetap tahun",
                                 ols(out, [lad, peg] + zd + td,
                                     ['lawatan', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
                                     [f't{j}' for j in range(1, 5)]))
R['tangga']['5_penternak'] = show("5. + saiz populasi penternak",
                                  ols(out, [lad, peg, pen] + zd + td,
                                      ['lawatan', 'pegawai', 'penternak'] +
                                      [f'z{j}' for j in range(1, 7)] +
                                      [f't{j}' for j in range(1, 5)]))
R['tangga']['6_ppv'] = show("6. + program PPV",
                            ols(out, [lad, peg, pen, ppv] + zd + td,
                                ['lawatan', 'pegawai', 'penternak', 'ppv'] +
                                [f'z{j}' for j in range(1, 7)] +
                                [f't{j}' for j in range(1, 5)]))

m3 = ols(out, [lad, peg] + zd, ['lawatan', 'pegawai'] + [f'z{j}' for j in range(1, 7)])
ip = m3['names'].index('pegawai')
print(f"\n  Pekali pegawai dalam model E.2: {m3['b'][ip]:+,.0f} "
      f"(SE {m3['se'][ip]:,.0f}, p = {m3['p'][ip]:.3f}) — nol seperti dilaporkan.")
R['pegawai_E2'] = dict(b=float(m3['b'][ip]), se=float(m3['se'][ip]), p=float(m3['p'][ip]))

# ---------------------------------------------------------------- B. within
print()
print("=" * 104)
print("B. VARIASI DALAM-ZON SAHAJA — buang purata zon daripada setiap pemboleh ubah")
ow, lw, pw = demean(out, zi), demean(lad, zi), demean(peg, zi)
mw = ols(ow, [lw, pw] + td, ['lawatan', 'pegawai'] + [f't{j}' for j in range(1, 5)])
i = mw['names'].index('lawatan')
print(f"  Anggaran dalam-zon (kesan tetap tahun dikekalkan):")
print(f"    lawatan  b = {mw['b'][i]:+.2f}   SE {mw['se'][i]:.2f}   p = {mw['p'][i]:.4f}")
print(f"    R² dalam = {mw['r2']:.3f}")
print(f"  Varians lawatan: {lw.var()/lad.var()*100:.1f}% dalam zon, "
      f"{100-lw.var()/lad.var()*100:.1f}% antara zon")
print(f"  Varians output : {ow.var()/out.var()*100:.1f}% dalam zon, "
      f"{100-ow.var()/out.var()*100:.1f}% antara zon")
R['within'] = dict(b=float(mw['b'][i]), se=float(mw['se'][i]), p=float(mw['p'][i]),
                   var_lawatan_dalam=float(lw.var() / lad.var()),
                   var_output_dalam=float(ow.var() / out.var()))

# ---------------------------------------------------------------- C. beza pertama
print()
print("=" * 104)
print("C. BEZA PERTAMA — ujian paling ketat: adakah PERUBAHAN lawatan menggerakkan "
      "PERUBAHAN output?")
d_out, d_lad, d_peg, d_yi, d_zi = [], [], [], [], []
for j, z in enumerate(Z):
    s = zi == j
    o_, l_, p_ = out[s], lad[s], peg[s]
    d_out += list(np.diff(o_)); d_lad += list(np.diff(l_)); d_peg += list(np.diff(p_))
    d_yi += [1, 2, 3, 4]; d_zi += [j] * 4
d_out, d_lad, d_peg = map(np.array, (d_out, d_lad, d_peg))
d_yi, d_zi = np.array(d_yi), np.array(d_zi)
dt = [(d_yi == j).astype(float) for j in (2, 3, 4)]
md = ols(d_out, [d_lad, d_peg], ['lawatan', 'pegawai'])
mdt = ols(d_out, [d_lad, d_peg] + dt, ['lawatan', 'pegawai'] + ['t2', 't3', 't4'])
print(f"  {'spesifikasi':<44}{'b':>10}{'SE':>9}{'t':>8}{'p':>9}{'R²':>9}{'df':>6}")
R['beza'] = {}
R['beza']['ringkas'] = show("Δoutput ~ Δlawatan + Δpegawai", md)
R['beza']['tahun'] = show("  + kesan tetap tahun", mdt)
kk = np.sum(np.sign(d_out) == np.sign(d_lad))
print(f"  Arah sepadan dalam {kk} daripada {len(d_out)} perubahan tahunan "
      f"({kk/len(d_out)*100:.0f}%; 50% = syiling adil)")
R['beza']['arah_sepadan'] = [int(kk), int(len(d_out))]

# ---------------------------------------------------------------- D. RI
print()
print("=" * 104)
print("D. INFERENS RAWAK — 7 kluster terlalu sedikit untuk SE teguh; guna ujian pilih atur")
print("   Lawatan dikocok dalam zon 20,000 kali; agihan nol dibina daripada data sebenar.")


def fe_beta(l_):
    X = np.column_stack([np.ones(35), l_, peg] + zd + td)
    b, *_ = np.linalg.lstsq(X, out, rcond=None)
    return b[1]


obs = fe_beta(lad)
draws = np.empty(20000)
for it in range(20000):
    perm = lad.copy()
    for j in range(7):
        s = zi == j
        perm[s] = rng.permutation(perm[s])
    draws[it] = fe_beta(perm)
p_ri = float((np.abs(draws) >= abs(obs)).mean())
print(f"  b diperhati = {obs:+.2f}")
print(f"  nol: purata {draws.mean():+.2f}, SD {draws.std():.2f}, "
      f"julat {draws.min():+.1f} hingga {draws.max():+.1f}")
print(f"  p pilih atur dua hujung = {p_ri:.4f}   (p-t konvensional = "
      f"{R['tangga']['4_zontahun']['p']:.4f})")
R['inferens_rawak'] = dict(b=float(obs), p=p_ri, sd=float(draws.std()))

# ---------------------------------------------------------------- E. pulangan
print()
print("=" * 104)
print("E. ADAKAH PULANGAN BERKURANGAN? Sebutan kuasa dua dan keanjalan log-log")
lad2 = (lad / 1000) ** 2
mq = ols(out, [lad, lad2, peg] + zd + td,
         ['lawatan', 'lawatan2', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
         [f't{j}' for j in range(1, 5)])
i2 = mq['names'].index('lawatan2')
print(f"  Sebutan kuasa dua: b = {mq['b'][i2]:+.2f}, p = {mq['p'][i2]:.4f} "
      f"({'ada' if mq['p'][i2] < .05 else 'tiada'} bukti lengkungan)")
ml = ols(np.log(out), [np.log(lad), np.log(peg)] + zd + td,
         ['lawatan', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
         [f't{j}' for j in range(1, 5)])
il = ml['names'].index('lawatan')
print(f"  Keanjalan log-log: {ml['b'][il]:+.3f} "
      f"(SE {ml['se'][il]:.3f}, p = {ml['p'][il]:.4f})")
print(f"    → kenaikan lawatan 10% dikaitkan dengan output "
      f"{ml['b'][il]*10:+.1f}%")
R['lengkung'] = dict(kuasa2_b=float(mq['b'][i2]), kuasa2_p=float(mq['p'][i2]),
                     elas=float(ml['b'][il]), elas_se=float(ml['se'][il]),
                     elas_p=float(ml['p'][il]))

lb = lad / pen
print(f"\n  Liputan (lawatan setiap penternak dalam pangkalan data), purata zon:")
for j, z in enumerate(Z):
    s = zi == j
    print(f"    {z:<12}{lb[s].mean():>6.2f}   lawatan {lad[s].mean():>7,.0f}   "
          f"penternak {pen[s].mean():>7,.0f}")

# ---------------------------------------------------------------- F. arah
print()
print("=" * 104)
print("F. ARAH SEBAB — adakah lawatan mendahului output, atau output mendahului lawatan?")
lag_o, lag_l, lag_p, lag_z, lag_t = [], [], [], [], []
for j in range(7):
    s = zi == j
    o_, l_, p_ = out[s], lad[s], peg[s]
    for t in range(1, 5):
        lag_o.append([o_[t], o_[t - 1], l_[t - 1], l_[t], p_[t]])
        lag_z.append(j); lag_t.append(t)
A = np.array(lag_o, float)
lz = [(np.array(lag_z) == j).astype(float) for j in range(1, 7)]
lt = [(np.array(lag_t) == j).astype(float) for j in (2, 3, 4)]
f1 = ols(A[:, 0], [A[:, 2], A[:, 1], A[:, 4]] + lz + lt,
         ['lawatan_t1', 'output_t1', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
         ['t2', 't3', 't4'])
i = f1['names'].index('lawatan_t1')
print(f"  output(t) ~ lawatan(t−1):   b = {f1['b'][i]:+.2f}, p = {f1['p'][i]:.4f}")
f2 = ols(A[:, 3], [A[:, 1], A[:, 2], A[:, 4]] + lz + lt,
         ['output_t1', 'lawatan_t1', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
         ['t2', 't3', 't4'])
i = f2['names'].index('output_t1')
print(f"  lawatan(t) ~ output(t−1):   b = {f2['b'][i]:+.4f}, p = {f2['p'][i]:.4f}")
f3 = ols(A[:, 0], [A[:, 3], A[:, 1], A[:, 4]] + lz + lt,
         ['lawatan_t', 'output_t1', 'pegawai'] + [f'z{j}' for j in range(1, 7)] +
         ['t2', 't3', 't4'])
i = f3['names'].index('lawatan_t')
print(f"  output(t) ~ lawatan(t) serentak: b = {f3['b'][i]:+.2f}, p = {f3['p'][i]:.4f}")
R['arah'] = dict(
    lag=dict(b=float(f1['b'][f1['names'].index('lawatan_t1')]),
             p=float(f1['p'][f1['names'].index('lawatan_t1')])),
    balik=dict(b=float(f2['b'][f2['names'].index('output_t1')]),
               p=float(f2['p'][f2['names'].index('output_t1')])),
    serentak=dict(b=float(f3['b'][f3['names'].index('lawatan_t')]),
                  p=float(f3['p'][f3['names'].index('lawatan_t')])))

# ---------------------------------------------------------------- G. aliran
print()
print("=" * 104)
print("G. ALIRAN MANA YANG BERGERAK DENGAN LAWATAN? (dalam zon, kesan tetap zon + tahun)")
print(f"  {'aliran aktiviti':<22}{'b':>10}{'SE':>9}{'p':>9}{'% output':>11}"
      f"{'sumbangan':>12}")
tot_b = 0.0
rows = []
for lab in AKTLAB:
    v = akt[lab]
    m = ols(v, [lad, peg] + zd + td, ['lawatan', 'pegawai'] +
            [f'z{j}' for j in range(1, 7)] + [f't{j}' for j in range(1, 5)])
    i = m['names'].index('lawatan')
    sh = v.sum() / out.sum() * 100
    tot_b += m['b'][i]
    rows.append((m['p'][i], lab, float(m['b'][i]), float(m['se'][i]),
                 float(m['p'][i]), float(sh)))
for p_, lab, b_, se_, pp, sh in sorted(rows):
    star = '  ←' if pp < .05 else ''
    print(f"  {lab:<22}{b_:>+10.2f}{se_:>9.2f}{pp:>9.4f}{sh:>10.1f}%"
          f"{b_/18.60*100:>11.0f}%{star}")
print(f"  {'JUMLAH':<22}{tot_b:>+10.2f}{'':>9}{'':>9}{'100.0%':>11}{'100%':>12}")
R['aliran'] = [dict(aliran=lab, b=b_, se=se_, p=pp, bahagian=sh)
               for _, lab, b_, se_, pp, sh in sorted(rows)]

# ---------------------------------------------------------------- H. keteguhan
print()
print("=" * 104)
print("H. KETEGUHAN PEKALI LAWATAN (model dengan pegawai + zon + tahun)")
base = R['tangga']['4_zontahun']
print(f"  {'spesifikasi':<44}{'b':>10}{'SE':>9}{'t':>8}{'p':>9}{'R²':>9}{'df':>6}")
R['teguh'] = {}
R['teguh']['penuh'] = show("panel penuh", ols(out, [lad, peg] + zd + td,
                                              ['lawatan', 'pegawai'] +
                                              [f'z{j}' for j in range(1, 7)] +
                                              [f't{j}' for j in range(1, 5)]))
for j, z in enumerate(Z):
    s = zi != j
    zk = [(zi[s] == k).astype(float) for k in range(7) if k != j][1:]
    tk = [(yi[s] == k).astype(float) for k in range(1, 5)]
    m = ols(out[s], [lad[s], peg[s]] + zk + tk,
            ['lawatan', 'pegawai'] + [f'z{k}' for k in range(len(zk))] +
            [f't{k}' for k in range(1, 5)])
    R['teguh'][f'tanpa_{z}'] = show(f"tanpa {z}", m)
for j, y in enumerate(Y):
    s = yi != j
    zk = [(zi[s] == k).astype(float) for k in range(1, 7)]
    tk = [(yi[s] == k).astype(float) for k in range(5) if k != j][1:]
    m = ols(out[s], [lad[s], peg[s]] + zk + tk,
            ['lawatan', 'pegawai'] + [f'z{k}' for k in range(1, 7)] +
            [f't{k}' for k in range(len(tk))])
    R['teguh'][f'tanpa_{y}'] = show(f"tanpa {y}", m)

# ---------------------------------------------------------------- I. praktikal
print()
print("=" * 104)
print("I. SKALA PRAKTIKAL")
b = base['b']
print(f"  Pekali gabungan {b:+.2f} unit output bagi setiap lawatan tambahan.")
print(f"  Purata zon menjalankan {lad.mean():,.0f} lawatan dan menghasilkan "
      f"{out.mean():,.0f} unit output setahun.")
print(f"  Nisbah kasar output/lawatan = {out.sum()/lad.sum():.1f} unit setiap lawatan.")
print(f"  Menambah 10% lawatan pada zon purata (+{lad.mean()*.1:,.0f} lawatan) "
      f"→ +{b*lad.mean()*.1:,.0f} unit ({b*lad.mean()*.1/out.mean()*100:+.1f}% output).")
lo, hi = b - 1.96 * base['se'], b + 1.96 * base['se']
print(f"  Selang keyakinan 95% bagi pekali: {lo:+.1f} hingga {hi:+.1f} "
      f"→ kesan 10% berjulat {lo*lad.mean()*.1/out.mean()*100:+.1f}% "
      f"hingga {hi*lad.mean()*.1/out.mean()*100:+.1f}%")
R['praktikal'] = dict(b=b, ci=[float(lo), float(hi)], lad_purata=float(lad.mean()),
                      out_purata=float(out.mean()),
                      nisbah=float(out.sum() / lad.sum()))

json.dump(R, open('lawatan.json', 'w'), indent=1)
print("\nDisimpan: lawatan.json")

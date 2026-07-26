"""Analisis post-hoc bagi Lampiran E: setiap aras dalam setiap pemboleh ubah.
Panel 7 zon x 5 tahun (2021-2025), n = 35."""
import openpyxl, json, itertools
import numpy as np
from scipy import stats
from scipy.cluster.hierarchy import linkage, fcluster

wb = openpyxl.load_workbook('lt_v3.xlsx', data_only=True)
Z = ["UTARA", "TENGAH", "BARAT DAYA", "SELATAN", "TENGGARA", "TIMUR", "TIMUR LAUT"]
Y = [2021, 2022, 2023, 2024, 2025]
AKT = ["KHIDMAT NASIHAT", "KESIHATAN GEROMPOK (BIL PENTERNAK)", "RAWATAN BIASA (BIL KES)",
       "PEMBIAKAN (BIL PENTERNAK)", "LAWAT SIASAT", "AUDIT/VERIFIKASI", "PERSAMPELAN",
       "VAKSINASI", "UJIAN LAPANGAN", "MESYUARAT"]
KOM = ["LEMBU TENUSU", "LEMBU PEDAGING", "KERBAU PEDAGING", "KERBAU TENUSU",
       "BEBIRI PEDAGING", "KAMBING PEDAGING", "KAMBING TENUSU"]
KOMLAB = {"LEMBU TENUSU": "Lembu tenusu", "LEMBU PEDAGING": "Lembu pedaging",
          "KERBAU PEDAGING": "Kerbau pedaging", "KERBAU TENUSU": "Kerbau tenusu",
          "BEBIRI PEDAGING": "Bebiri pedaging", "KAMBING PEDAGING": "Kambing pedaging",
          "KAMBING TENUSU": "Kambing tenusu"}
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

# ---------- bina matriks panel ----------
cells = [(z, y) for z in Z for y in Y]
def col(f): return np.array([f(z, y) for z, y in cells], float)

out = col(lambda z, y: sum(D[y][k][z] for k in AKT))
lad = col(lambda z, y: D[y]['BIL PENTERNAK DILAWAT'][z])
peg = col(lambda z, y: D[y]['PEGAWAI TEKNIKAL'][z])
pen = col(lambda z, y: sum(D[y][k][z] for k in KOM))
ppv = col(lambda z, y: D[y]['BILANGAN PPV'][z])
share = {k: col(lambda z, y, k=k: D[y][k][z]) / pen for k in KOM}
tenusu = share["LEMBU TENUSU"] + share["KERBAU TENUSU"] + share["KAMBING TENUSU"]
inten = out / pen                      # output setiap penternak
ladpen = lad / pen
zi = np.array([Z.index(z) for z, _ in cells])
yi = np.array([Y.index(y) for _, y in cells])

R = {}
def hdr(t):
    print("\n" + "=" * 98); print(t); print("=" * 98)


# ---------- alat ----------
def ols(yv, X):
    X = np.column_stack([np.ones(len(yv))] + list(X))
    b, *_ = np.linalg.lstsq(X, yv, rcond=None)
    r = yv - X @ b
    n, k = X.shape
    ssr = float(r @ r)
    sst = float(((yv - yv.mean()) ** 2).sum())
    XtXi = np.linalg.pinv(X.T @ X)
    s2 = ssr / (n - k)
    se = np.sqrt(np.diag(XtXi) * s2)
    p = 2 * (1 - stats.t.cdf(np.abs(b / se), n - k))
    return dict(b=b, se=se, p=p, ssr=ssr, df=n - k, mse=s2, r2=1 - ssr / sst, resid=r)


def dummies(idx, n):
    return [np.array(idx == j, float) for j in range(1, n)]


def holm(pvals):
    """Kembalikan p terlaras Holm-Bonferroni."""
    m = len(pvals)
    order = np.argsort(pvals)
    adj = np.empty(m)
    run = 0.0
    for rank, i in enumerate(order):
        val = (m - rank) * pvals[i]
        run = max(run, val)
        adj[i] = min(run, 1.0)
    return adj


def tukey(groups_idx, values, nlev, labels, mse=None, dfe=None):
    """Tukey HSD; jika mse/dfe diberi, gunakannya (mis. daripada model dua hala)."""
    means = np.array([values[groups_idx == j].mean() for j in range(nlev)])
    ns = np.array([(groups_idx == j).sum() for j in range(nlev)])
    if mse is None:
        ssw = sum(((values[groups_idx == j] - means[j]) ** 2).sum() for j in range(nlev))
        dfe = len(values) - nlev
        mse = ssw / dfe
    res = []
    for a, b in itertools.combinations(range(nlev), 2):
        se = np.sqrt(mse / 2 * (1 / ns[a] + 1 / ns[b]))
        q = abs(means[a] - means[b]) / se
        p = 1 - stats.studentized_range.cdf(q, nlev, dfe)
        res.append(dict(a=labels[a], b=labels[b], diff=float(means[a] - means[b]),
                        q=float(q), p=float(p)))
    return means, res


# ================= 1. POST-HOC ZON =================
hdr("1.  POST-HOC ZON — 21 perbandingan berpasangan (Tukey HSD, skala log)")
lout = np.log(out)
m2 = ols(lout, dummies(zi, 7) + dummies(yi, 5))
print(f"Model dua hala: R² = {m2['r2']:.3f}, MSE = {m2['mse']:.4f}, df ralat = {m2['df']}")
means, pairs = tukey(zi, lout, 7, Z, mse=m2['mse'], dfe=m2['df'])
print(f"\nMin log-output terlaras mengikut zon (n = 5 setiap satu):")
for j in np.argsort(-means):
    print(f"  {Z[j]:<12}{means[j]:>7.3f}  ≈ {np.exp(means[j]):>9,.0f} unit")
sig = [p for p in pairs if p['p'] < 0.05]
print(f"\nPerbandingan berpasangan signifikan: {len(sig)} daripada {len(pairs)}")
for p in sorted(pairs, key=lambda x: x['p'])[:8]:
    star = "  <-- signifikan" if p['p'] < 0.05 else ""
    print(f"  {p['a']:<12} vs {p['b']:<12} nisbah {np.exp(p['diff']):>5.2f}×   "
          f"q = {p['q']:>5.2f}   p = {p['p']:.4f}{star}")
R['zon'] = dict(means={Z[j]: float(means[j]) for j in range(7)}, pairs=pairs,
                nsig=len(sig), r2=float(m2['r2']))

# ================= 2. POST-HOC TAHUN =================
hdr("2.  POST-HOC TAHUN — 10 perbandingan berpasangan (Tukey HSD, skala log)")
ymeans, ypairs = tukey(yi, lout, 5, [str(y) for y in Y], mse=m2['mse'], dfe=m2['df'])
print("Min log-output terlaras mengikut tahun:")
for j in range(5):
    print(f"  {Y[j]}   {ymeans[j]:>7.3f}  ≈ {np.exp(ymeans[j]):>9,.0f} unit   "
          f"{(np.exp(ymeans[j]-ymeans[0])-1)*100:+6.1f}% vs 2021")
ysig = [p for p in ypairs if p['p'] < 0.05]
print(f"\nPerbandingan signifikan: {len(ysig)} daripada {len(ypairs)}")
for p in sorted(ypairs, key=lambda x: x['p'])[:4]:
    print(f"  {p['a']} vs {p['b']}   nisbah {np.exp(p['diff']):>5.2f}×   p = {p['p']:.4f}")
R['tahun'] = dict(means={str(Y[j]): float(ymeans[j]) for j in range(5)},
                  pairs=ypairs, nsig=len(ysig))

# ================= 3. POST-HOC KOMODITI =================
hdr("3.  POST-HOC KOMODITI — setiap tujuh komoditi diuji berasingan")
print("Lampiran E melaporkan bahagian TENUSU sahaja (r = +0.801, p = 0.031, n = 7).")
print("Tenusu ialah gabungan tiga komoditi. Post-hoc menguji kesemua tujuh secara individu.\n")

print("(a) Peringkat zon, n = 7 — sepadan dengan kaedah E.5")
print(f"  {'Komoditi':<20}{'r':>8}{'p mentah':>11}{'p Holm':>10}  verdik")
zsh = {k: np.array([share[k][zi == j].mean() for j in range(7)]) for k in KOM}
zint = np.array([inten[zi == j].mean() for j in range(7)])
ztn = np.array([tenusu[zi == j].mean() for j in range(7)])
raw = []
for k in KOM:
    r_, p_ = stats.pearsonr(zsh[k], zint)
    raw.append((k, r_, p_))
adj = holm(np.array([p for _, _, p in raw]))
for (k, r_, p_), pa in zip(raw, adj):
    v = "signifikan" if pa < 0.05 else ("mentah sahaja" if p_ < 0.05 else "—")
    print(f"  {KOMLAB[k]:<20}{r_:>+8.3f}{p_:>11.4f}{pa:>10.4f}  {v}")
rt, pt = stats.pearsonr(ztn, zint)
print(f"  {'GABUNGAN tenusu':<20}{rt:>+8.3f}{pt:>11.4f}{'—':>10}  seperti dilaporkan E.5")
R['komoditi_zon'] = [dict(k=KOMLAB[k], r=float(r_), p=float(p_), p_holm=float(pa))
                     for (k, r_, p_), pa in zip(raw, adj)]
R['tenusu_zon'] = dict(r=float(rt), p=float(pt))

print("\n(b) Peringkat panel, n = 35, dengan kesan tetap zon + tahun")
print(f"  {'Komoditi':<20}{'b':>10}{'p mentah':>11}{'p Holm':>10}  verdik")
base = dummies(zi, 7) + dummies(yi, 5)
raw2 = []
for k in KOM:
    m = ols(inten, [share[k]] + base)
    raw2.append((k, m['b'][1], m['p'][1]))
adj2 = holm(np.array([p for _, _, p in raw2]))
for (k, b_, p_), pa in zip(raw2, adj2):
    v = "signifikan" if pa < 0.05 else ("mentah sahaja" if p_ < 0.05 else "—")
    print(f"  {KOMLAB[k]:<20}{b_:>+10.1f}{p_:>11.4f}{pa:>10.4f}  {v}")
mt = ols(inten, [tenusu] + base)
print(f"  {'GABUNGAN tenusu':<20}{mt['b'][1]:>+10.1f}{mt['p'][1]:>11.4f}{'—':>10}")
R['komoditi_panel'] = [dict(k=KOMLAB[k], b=float(b_), p=float(p_), p_holm=float(pa))
                       for (k, b_, p_), pa in zip(raw2, adj2)]

# ================= 4. POST-HOC LAWATAN =================
hdr("4.  POST-HOC LAWATAN LADANG — adakah pekali +18.60 seragam merentas zon?")
mbase = ols(out, [lad, peg, pen] + base)
print(f"Model E.2 dihasilkan semula: lawatan b = {mbase['b'][1]:+.2f} "
      f"(p = {mbase['p'][1]:.4f}), pegawai b = {mbase['b'][2]:+.1f} "
      f"(p = {mbase['p'][2]:.3f}), penternak b = {mbase['b'][3]:+.2f} "
      f"(p = {mbase['p'][3]:.3f})")

inter = [lad * np.array(zi == j, float) for j in range(1, 7)]
mint = ols(out, [lad, peg, pen] + base + inter)
Fi = ((mbase['ssr'] - mint['ssr']) / 6) / (mint['ssr'] / mint['df'])
pi = 1 - stats.f.cdf(Fi, 6, mint['df'])
print(f"\nUjian keseragaman cerun (interaksi zon × lawatan): "
      f"F(6,{mint['df']}) = {Fi:.2f}, p = {pi:.4f}")
print(f"  {'→ cerun BERBEZA antara zon' if pi < 0.05 else '→ cerun boleh dianggap seragam'}")

print(f"\nCerun lawatan→output setiap zon (regresi berasingan, n = 5 setiap satu):")
print(f"  {'Zon':<12}{'b':>10}{'p':>9}{'r':>8}   julat lawatan")
slopes = []
for j, z in enumerate(Z):
    m = zi == j
    sl, ic, r_, p_, se = stats.linregress(lad[m], out[m])
    print(f"  {z:<12}{sl:>+10.1f}{p_:>9.3f}{r_:>+8.2f}   "
          f"{lad[m].min():,.0f}–{lad[m].max():,.0f}")
    slopes.append(dict(zon=z, b=float(sl), p=float(p_), r=float(r_)))
R['lawatan'] = dict(pooled=float(mbase['b'][1]), p_pooled=float(mbase['p'][1]),
                    F_inter=float(Fi), p_inter=float(pi), slopes=slopes)

# ================= 5. POST-HOC PEGAWAI =================
hdr("5.  POST-HOC PEGAWAI — cerun setiap zon (mengesahkan keputusan nol)")
print(f"  {'Zon':<12}{'b':>12}{'p':>9}{'r':>8}   julat pegawai")
ps = []
for j, z in enumerate(Z):
    m = zi == j
    if peg[m].std() == 0:
        print(f"  {z:<12}{'—':>12}{'—':>9}{'—':>8}   tiada variasi")
        continue
    sl, ic, r_, p_, se = stats.linregress(peg[m], out[m])
    print(f"  {z:<12}{sl:>+12.0f}{p_:>9.3f}{r_:>+8.2f}   "
          f"{peg[m].min():.0f}–{peg[m].max():.0f}")
    ps.append(dict(zon=z, b=float(sl), p=float(p_), r=float(r_)))
neg = sum(1 for x in ps if x['b'] < 0)
print(f"\n  {neg} daripada {len(ps)} zon mempunyai cerun NEGATIF; "
      f"{sum(1 for x in ps if x['p'] < 0.05)} signifikan.")
R['pegawai'] = ps

# ================= 6. POST-HOC ARKETAIP =================
hdr("6.  POST-HOC ARKETAIP ZON — pengelompokan Ward dihasilkan semula")
prof = np.column_stack([
    [out[zi == j].mean() for j in range(7)],
    [lad[zi == j].mean() for j in range(7)],
    [peg[zi == j].mean() for j in range(7)],
    [(out / peg)[zi == j].mean() for j in range(7)],
    [(1 - sum(share[k] ** 2 for k in KOM))[zi == j].mean() for j in range(7)],
    ztn])
prof_s = (prof - prof.mean(0)) / prof.std(0, ddof=1)
lab = fcluster(linkage(prof_s, 'ward'), 3, 'maxclust')
print("Keahlian kluster:")
for c in sorted(set(lab)):
    mem = [Z[j] for j in range(7) if lab[j] == c]
    print(f"  Kluster {c}: {', '.join(mem)}")
print("\nPerbandingan berpasangan antara kluster (output setiap pegawai, Tukey):")
prod = out / peg
clab = np.array([lab[j] - 1 for j in zi])
nlev = len(set(lab))
cm, cp = tukey(clab, prod, nlev, [f"Kluster {c+1}" for c in range(nlev)])
for c in range(nlev):
    print(f"  Kluster {c+1}: purata output/pegawai = {cm[c]:,.0f}  "
          f"(n = {(clab==c).sum()} cerapan)")
for p in cp:
    star = "  <-- signifikan" if p['p'] < 0.05 else ""
    print(f"  {p['a']} vs {p['b']}: beza {p['diff']:+,.0f}   p = {p['p']:.4f}{star}")
R['arketaip'] = dict(labels={Z[j]: int(lab[j]) for j in range(7)}, pairs=cp)

# kestabilan pengelompokan
hdr("6b.  KESTABILAN PENGELOMPOKAN — gugur-satu-zon")
print("Adakah keahlian kluster kekal apabila satu zon digugurkan?")
stab = []
for drop in range(7):
    keep = [j for j in range(7) if j != drop]
    p2 = prof[keep]
    p2s = (p2 - p2.mean(0)) / p2.std(0, ddof=1)
    l2 = fcluster(linkage(p2s, 'ward'), 3, 'maxclust')
    grp = {}
    for i, j in enumerate(keep):
        grp.setdefault(l2[i], []).append(Z[j])
    txt = " | ".join(",".join(sorted(v)) for k, v in sorted(grp.items()))
    stab.append(txt)
    print(f"  tanpa {Z[drop]:<12} → {txt}")
R['stabiliti_kluster'] = stab

json.dump(R, open('posthoc.json', 'w'), indent=1)
print("\n\nDisimpan: posthoc.json")

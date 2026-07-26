"""Hipotesis mandat: identiti zon yang tidak diukur ialah OBLIGASI REGULATORI zon,
bukan saiznya, kakitangannya, atau populasi ternakannya.

Hipotesis: kerja yang diwajibkan secara kebangsaan (vaksinasi) diagihkan sama rata;
kerja yang diwajibkan oleh status penyakit atau akreditasi (ujian lapangan,
pensampelan) tertumpu di zon yang mempunyai obligasi itu.
"""
import numpy as np, json
from scipy import stats
from identiti import Z, Y, D, AKT, out, peg, pen, lad, zi, yi

AKTLAB = ["Khidmat nasihat", "Kesihatan gerompok", "Kes rawatan", "Pembiakbakaan",
          "Lawat siasat", "Regulatori", "Pensampelan", "Vaksinasi",
          "Ujian lapangan", "Mesyuarat"]
cells = [(z, y) for z in Z for y in Y]
col = lambda f: np.array([f(z, y) for z, y in cells], float)
akt = {lab: col(lambda z, y, k=k: D[y][k][z]) for k, lab in zip(AKT, AKTLAB)}
tenusu = col(lambda z, y: D[y]['LEMBU TENUSU'][z]) / pen
BARAT = ("UTARA", "TENGAH", "BARAT DAYA", "SELATAN")
isb = np.array([Z[j] in BARAT for j in zi])
zm = lambda v: np.array([v[zi == j].mean() for j in range(7)])
R = {}

print("=" * 100)
print("A. DUA JENIS KERJA — diwajibkan kebangsaan lawan diwajibkan status")
print("   Jika hipotesis betul: vaksinasi sama rata, ujian/sampel tertumpu.")
print(f"  {'aliran':<20}{'barat/pegawai':>15}{'timur/pegawai':>15}{'nisbah B:T':>12}"
      f"{'CV antara zon':>15}")
tb, tt = peg[isb].sum(), peg[~isb].sum()
kat = {}
for l in AKTLAB:
    a, b = akt[l][isb].sum() / tb, akt[l][~isb].sum() / tt
    pz = np.array([akt[l][zi == j].sum() / peg[zi == j].sum() for j in range(7)])
    cv = pz.std(ddof=1) / pz.mean() * 100
    kat[l] = dict(barat=float(a), timur=float(b), nisbah=float(a / b), cv=float(cv))
    print(f"  {l:<20}{a:>15,.0f}{b:>15,.0f}{a/b:>11.2f}×{cv:>14.0f}%")
R['aliran'] = kat

print("\n  Disusun mengikut ketumpuan (CV merentas zon):")
for l in sorted(AKTLAB, key=lambda a: -kat[a]['cv'])[:4]:
    print(f"    {l:<20}CV {kat[l]['cv']:>3.0f}%   nisbah barat:timur {kat[l]['nisbah']:.2f}×")
print("  Paling sekata:")
for l in sorted(AKTLAB, key=lambda a: kat[a]['cv'])[:3]:
    print(f"    {l:<20}CV {kat[l]['cv']:>3.0f}%   nisbah barat:timur {kat[l]['nisbah']:.2f}×")

print()
print("=" * 100)
print("B. ADAKAH JURANG PANTAI TERUS WUJUD SELEPAS KERJA BERMANDAT DIBUANG?")
kempen = akt["Ujian lapangan"] + akt["Pensampelan"]
baki = out - kempen
print(f"  {'ukuran':<34}{'barat':>12}{'timur':>12}{'nisbah':>9}{'t':>7}{'p':>9}")
for lab, v in [("Output penuh", out), ("Ujian lapangan + pensampelan", kempen),
               ("Output tanpa kedua-duanya", baki)]:
    pz = np.array([v[zi == j].sum() / peg[zi == j].sum() for j in range(7)])
    wb = pz[[Z.index(z) for z in BARAT]]
    wt = pz[[Z.index(z) for z in Z if z not in BARAT]]
    t, p = stats.ttest_ind(wb, wt)
    print(f"  {lab:<34}{wb.mean():>12,.0f}{wt.mean():>12,.0f}"
          f"{wb.mean()/wt.mean():>8.2f}×{t:>7.2f}{p:>9.4f}")
    R.setdefault('pantai', {})[lab] = dict(barat=float(wb.mean()), timur=float(wt.mean()),
                                           t=float(t), p=float(p))
print("\n  → Jika baris ketiga tidak signifikan, jurang pantai ialah kerja bermandat sahaja.")

print()
print("=" * 100)
print("C. TANDA MANDAT: zon dengan status bebas penyakit atau ladang tenusu akreditasi")
print("   Sumber luar: zon bebas FMD dengan vaksinasi meliputi Langkawi (Kedah, zon")
print("   UTARA) dan tiga daerah Johor (zon SELATAN). Ujian TB tenusu tertumpu di")
print("   Selangor (zon TENGAH). Zon pantai timur tiada status sedemikian dilaporkan.")
MANDAT = {"UTARA": 1, "TENGAH": 1, "BARAT DAYA": 1, "SELATAN": 1,
          "TENGGARA": 0, "TIMUR": 0, "TIMUR LAUT": 0}
print(f"\n  {'ZON':<12}{'bhg lembu tenusu':>18}{'ujian lapangan':>16}"
      f"{'% output':>10}{'2021':>10}{'2025':>10}")
for j in np.argsort(-zm(tenusu)):
    z = Z[j]; s = zi == j
    u = akt["Ujian lapangan"][s]
    print(f"  {z:<12}{zm(tenusu)[j]*100:>17.1f}%{u.mean():>16,.0f}"
          f"{u.sum()/out[s].sum()*100:>9.1f}%{u[0]:>10,.0f}{u[4]:>10,.0f}")
um = zm(akt["Ujian lapangan"])
r, p = stats.pearsonr(zm(tenusu), um)
print(f"\n  bhg lembu tenusu vs ujian lapangan: r = {r:+.3f}, p = {p:.4f}")
r2, p2 = stats.pearsonr(np.array([MANDAT[z] for z in Z], float), um)
print(f"  penanda mandat vs ujian lapangan  : r = {r2:+.3f}, p = {p2:.4f}")
R['mandat'] = dict(r_tenusu=float(r), p_tenusu=float(p), r_mandat=float(r2), p_mandat=float(p2))

print()
print("=" * 100)
print("D. MENGAPA OUTPUT KEBANGSAAN MENURUN — bukan prestasi, tetapi satu aliran")
print(f"  {'tahun':<8}{'ujian lapangan':>16}{'9 aliran lain':>16}{'jumlah':>12}")
for i, y in enumerate(Y):
    s = yi == i
    u = akt["Ujian lapangan"][s].sum()
    o = out[s].sum()
    print(f"  {y:<8}{u:>16,.0f}{o-u:>16,.0f}{o:>12,.0f}")
u0, u4 = akt["Ujian lapangan"][yi == 0].sum(), akt["Ujian lapangan"][yi == 4].sum()
o0, o4 = out[yi == 0].sum(), out[yi == 4].sum()
print(f"  {'Δ':<8}{u4-u0:>+16,.0f}{(o4-u4)-(o0-u0):>+16,.0f}{o4-o0:>+12,.0f}")
print(f"\n  Ujian lapangan turun {u0-u4:,.0f}; sembilan aliran lain NAIK "
      f"{(o4-u4)-(o0-u0):+,.0f}.")
print(f"  Tanpa ujian lapangan, output kebangsaan naik "
      f"{((o4-u4)/(o0-u0)-1)*100:+.1f}% dan bukan turun {(o4/o0-1)*100:.1f}%.")
R['kebangsaan'] = dict(uji_2021=float(u0), uji_2025=float(u4),
                       lain_2021=float(o0 - u0), lain_2025=float(o4 - u4))

print()
print("=" * 100)
print("E. KEDUDUKAN ZON JIKA UJIAN LAPANGAN DIKELUARKAN")
print(f"  {'ZON':<12}{'output/pegawai':>16}{'kedudukan':>11}   "
      f"{'tanpa ujian lapangan':>21}{'kedudukan':>11}{'anjakan':>9}")
a = np.array([out[zi == j].sum() / peg[zi == j].sum() for j in range(7)])
b = np.array([baki[zi == j].sum() / peg[zi == j].sum() for j in range(7)])
ra = {z: i + 1 for i, z in enumerate(sorted(Z, key=lambda z: -a[Z.index(z)]))}
rb = {z: i + 1 for i, z in enumerate(sorted(Z, key=lambda z: -b[Z.index(z)]))}
for z in sorted(Z, key=lambda z: ra[z]):
    j = Z.index(z)
    print(f"  {z:<12}{a[j]:>16,.0f}{ra[z]:>11}   {b[j]:>21,.0f}{rb[z]:>11}"
          f"{ra[z]-rb[z]:>+9}")
print(f"\n  Julat antara zon: {a.max()/a.min():.2f}× menjadi {b.max()/b.min():.2f}× "
      "apabila ujian lapangan dikeluarkan.")
R['kedudukan'] = {z: dict(dengan=int(ra[z]), tanpa=int(rb[z])) for z in Z}

json.dump(R, open('mandat.json', 'w'), indent=1)
print("\nDisimpan: mandat.json")

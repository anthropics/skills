"""Mencirikan kesan zon yang tidak diukur: apakah BENTUK benda yang perlu diterangkan?

Kita tidak boleh mengukurnya secara langsung, tetapi kita boleh menanya sifatnya:
adakah ia tetap atau berubah, adakah ia am atau khusus aliran, dan adakah ia
kelihatan seperti kapasiti, mandat, atau amalan merekod.
"""
import numpy as np, json
from scipy import stats
from identiti import (Z, Y, out, lad, peg, pen, luas, ops, lembu, zi, yi, D, AKT)

AKTLAB = ["Khidmat nasihat", "Kesihatan gerompok", "Kes rawatan", "Pembiakbakaan",
          "Lawat siasat", "Regulatori", "Pensampelan", "Vaksinasi",
          "Ujian lapangan", "Mesyuarat"]
cells = [(z, y) for z in Z for y in Y]
akt = {lab: np.array([D[y][k][z] for z, y in cells], float)
       for k, lab in zip(AKT, AKTLAB)}
R = {}
zm = lambda v: np.array([v[zi == j].mean() for j in range(7)])

print("=" * 100)
print("A. SAIZ BENDA YANG PERLU DITERANGKAN")
lo = np.log(out)
Xz = np.column_stack([np.ones(35)] + [(zi == j).astype(float) for j in range(1, 7)]
                     + [(yi == j).astype(float) for j in range(1, 5)])
bz, *_ = np.linalg.lstsq(Xz, lo, rcond=None)
eff = np.r_[0.0, bz[1:7]]
eff = eff - eff.mean()
print(f"  Kesan zon tetap (log, dipusatkan), model dengan kesan tetap tahun:")
for j in np.argsort(-eff):
    print(f"    {Z[j]:<12}{eff[j]:>+7.3f} log   = {(np.exp(eff[j])-1)*100:>+6.1f}% "
          f"berbanding purata zon")
print(f"  Julat: {np.exp(eff.max()-eff.min()):.2f} kali ganda antara zon tertinggi dan terendah")
R['kesan_zon'] = {Z[j]: float(eff[j]) for j in range(7)}

print()
print("=" * 100)
print("B. ADAKAH KESAN ZON TETAP ATAU BERUBAH? (kesan dianggar berasingan setiap tahun)")
print(f"  {'ZON':<12}" + "".join(f"{y:>10}" for y in Y) + f"{'SD':>8}{'julat':>8}")
tahunan = {}
for j, z in enumerate(Z):
    row = []
    for t in range(5):
        s = yi == t
        row.append(np.log(out[s][j]) - np.log(out[s]).mean())
    tahunan[z] = row
    print(f"  {z:<12}" + "".join(f"{v:>+10.3f}" for v in row) +
          f"{np.std(row, ddof=1):>8.3f}{max(row)-min(row):>8.3f}")
sd_all = [np.std(tahunan[z], ddof=1) for z in Z]
print(f"\n  Purata SD dalam zon merentas tahun: {np.mean(sd_all):.3f} log")
print(f"  SD kesan zon antara zon           : {np.std(eff, ddof=1):.3f} log")
print(f"  Nisbah antara/dalam = {np.std(eff, ddof=1)/np.mean(sd_all):.2f}"
      f"   ({'stabil — ciri tetap' if np.std(eff,ddof=1)/np.mean(sd_all)>1 else 'tidak stabil'})")
R['kestabilan'] = dict(sd_antara=float(np.std(eff, ddof=1)),
                       sd_dalam=float(np.mean(sd_all)))

print()
print("=" * 100)
print("C. ADAKAH IA AM ATAU KHUSUS ALIRAN? (campuran aktiviti setiap zon)")
print(f"  {'ZON':<12}" + "".join(f"{l[:7]:>8}" for l in AKTLAB) + f"{'HHI':>7}")
mix = {}
for j, z in enumerate(Z):
    s = zi == j
    tot = out[s].sum()
    sh = np.array([akt[l][s].sum() / tot for l in AKTLAB])
    mix[z] = sh
    hhi = float((sh ** 2).sum())
    print(f"  {z:<12}" + "".join(f"{v*100:>7.1f}%" for v in sh) + f"{hhi:>7.3f}")
print(f"  {'KEBANGSAAN':<12}" + "".join(
    f"{akt[l].sum()/out.sum()*100:>7.1f}%" for l in AKTLAB))
R['campuran'] = {z: [float(v) for v in mix[z]] for z in Z}

print("\n  Jarak campuran setiap zon daripada campuran kebangsaan (jarak Euclid):")
nat = np.array([akt[l].sum() / out.sum() for l in AKTLAB])
jarak = {z: float(np.linalg.norm(mix[z] - nat)) for z in Z}
for z in sorted(Z, key=lambda a: -jarak[a]):
    print(f"    {z:<12}{jarak[z]:>7.3f}")
R['jarak_campuran'] = jarak

print()
print("=" * 100)
print("D. KEAMATAN MEREKOD — berapa banyak output direkod bagi setiap lawatan ladang")
print(f"  {'ZON':<12}{'output/lawatan':>16}{'output/penternak':>18}"
      f"{'lawatan/penternak':>19}{'output/pegawai':>16}")
rek = {}
for j, z in enumerate(Z):
    s = zi == j
    a = out[s].sum() / lad[s].sum()
    b = out[s].sum() / pen[s].sum()
    c = lad[s].sum() / pen[s].sum()
    d = out[s].sum() / peg[s].sum()
    rek[z] = dict(per_lawatan=float(a), per_penternak=float(b),
                  lawatan_per_penternak=float(c), per_pegawai=float(d))
    print(f"  {z:<12}{a:>16.1f}{b:>18.1f}{c:>19.1f}{d:>16,.0f}")
v = [rek[z]['per_lawatan'] for z in Z]
print(f"\n  Julat output setiap lawatan: {min(v):.1f} – {max(v):.1f} "
      f"({max(v)/min(v):.1f} kali ganda)")
R['merekod'] = rek

print()
print("=" * 100)
print("E. DI MANA JURANG ITU? Pecahan jurang output antara pantai mengikut aliran")
pantai_b = np.array([Z.index(z) in (0, 1, 2, 3) for z in [Z[i] for i in zi]])
print(f"  {'aliran':<20}{'barat/pegawai':>15}{'timur/pegawai':>15}{'nisbah':>9}"
      f"{'% jurang':>10}")
tb = peg[pantai_b].sum(); tt = peg[~pantai_b].sum()
jur = out[pantai_b].sum() / tb - out[~pantai_b].sum() / tt
rows = []
for l in AKTLAB:
    a = akt[l][pantai_b].sum() / tb
    b = akt[l][~pantai_b].sum() / tt
    rows.append((a - b, l, a, b))
for d, l, a, b in sorted(rows, reverse=True):
    print(f"  {l:<20}{a:>15,.0f}{b:>15,.0f}"
          f"{(a/b if b else float('inf')):>8.1f}×{d/jur*100:>9.0f}%")
print(f"  {'JUMLAH':<20}{out[pantai_b].sum()/tb:>15,.0f}"
      f"{out[~pantai_b].sum()/tt:>15,.0f}"
      f"{(out[pantai_b].sum()/tb)/(out[~pantai_b].sum()/tt):>8.1f}×{100:>9.0f}%")
R['jurang_pantai'] = [dict(aliran=l, barat=float(a), timur=float(b),
                           bahagian=float(d / jur)) for d, l, a, b in sorted(rows, reverse=True)]

print()
print("=" * 100)
print("F. UJIAN MUSIM TENGKUJUH — data 2026 Jan–Apr berbanding purata tahunan")
print("   Monsun timur laut melanda Nov–Mac. Jika akses lapangan ialah kekangan,")
print("   suku pertama sepatutnya lemah TIDAK SEIMBANG di zon pantai timur.")
D26 = D.get(2026)
print("   (data 2026 dibaca berasingan di bawah)")

json.dump(R, open('baki.json', 'w'), indent=1)
print("\nDisimpan: baki.json")

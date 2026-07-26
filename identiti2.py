"""Pembetulan kepada identiti.py bahagian D-F.

Lima pemboleh ubah peringkat zon hampir menjangkau ruang linear yang sama dengan
enam dami zon (setiap satu malar atau hampir malar dalam zon). Ujian 'adakah dami
zon menjadi tidak signifikan' oleh itu hampir tautologi. Skrip ini menggantikannya
dengan analisis peringkat zon yang jujur (n = 7) dan diagnostik kolinearan.
"""
import openpyxl, json, itertools
import numpy as np
from scipy import stats
from identiti import (Z, Y, ZON_NEG, OPS, LUAS, out, lad, peg, pen, luas, ops,
                      lembu, kambing, ayam, rum, zi, yi, zd, td, ols, ftest)

R = {}
zm = lambda v: np.array([v[zi == j].mean() for j in range(7)])
om, pegm, ladm, penm = zm(out), zm(peg), zm(lad), zm(pen)
luasm, opsm, lembum, kambingm, ayamm = zm(luas), zm(ops), zm(lembu), zm(kambing), zm(ayam)

print("=" * 104)
print("D. AMARAN KOLINEARAN — mengapa 'dami zon menjadi tidak signifikan' bukan bukti")
print("   Setiap ciri zon adalah malar (luas, titik) atau hampir malar (ternakan)")
print("   dalam zon. Lima daripadanya menjangkau hampir keseluruhan ruang 6-dimensi")
print("   dami zon, jadi ia MESTI menyerap kesan zon tanpa mengira kaitan sebenar.")
X5 = np.column_stack([luas, ops, lembu, kambing, ayam])
Xz = np.column_stack([np.ones(35)] + zd)
proj = Xz @ np.linalg.pinv(Xz) @ X5
r2_span = 1 - ((X5 - proj) ** 2).sum(0) / ((X5 - X5.mean(0)) ** 2).sum(0)
print(f"\n  {'ciri':<24}{'R² apabila diregres atas dami zon':>36}")
for nm, v in zip(["Keluasan", "Titik operasi", "Lembu", "Kambing?", "Ayam"], r2_span):
    print(f"  {nm:<24}{v:>35.4f}{'   (malar dalam zon)' if v > .999 else ''}")
print("\n  → keluasan dan titik operasi ialah dami zon yang dinamakan semula.")
R['kolinearan'] = {nm: float(v) for nm, v in
                   zip(["Keluasan", "Titik operasi", "Lembu", "Kambing?", "Ayam"], r2_span)}

print("\n  Korelasi antara ciri zon itu sendiri (n = 7):")
ciri = {"Keluasan": luasm, "Titik": opsm, "Lembu": lembum,
        "Kambing?": kambingm, "Ayam": ayamm}
nm = list(ciri)
print(f"  {'':<12}" + "".join(f"{a:>11}" for a in nm))
for a in nm:
    print(f"  {a:<12}" + "".join(f"{np.corrcoef(ciri[a], ciri[b])[0,1]:>+11.2f}"
                                 for b in nm))
R['korelasi_ciri'] = {a: {b: float(np.corrcoef(ciri[a], ciri[b])[0, 1]) for b in nm}
                      for a in nm}

print()
print("=" * 104)
print("E. ANALISIS PERINGKAT ZON YANG JUJUR (n = 7) — satu peramal pada satu masa")
print("   Dengan 7 zon, hanya satu peramal boleh dianggar dengan yakin. Lima peramal")
print("   pada 7 titik akan memadankan hampir apa sahaja.")
print(f"\n  {'peramal tunggal':<34}{'r':>9}{'R²':>8}{'R² terlaras':>13}{'p':>9}")
kor = {}
for lab, v in [("Titik operasi VetEC", opsm), ("Populasi ayam (plasebo)", ayamm),
               ("Populasi kambing?", kambingm), ("Keluasan kawasan", luasm),
               ("Populasi lembu", lembum), ("Populasi ruminan", lembum + kambingm),
               ("Penternak pangkalan data", penm), ("Bilangan pegawai", pegm)]:
    r, p = stats.pearsonr(v, om)
    r2 = r ** 2
    adj = 1 - (1 - r2) * 6 / 5
    print(f"  {lab:<34}{r:>+9.3f}{r2:>8.3f}{adj:>13.3f}{p:>9.4f}")
    kor[lab] = dict(r=float(r), r2=float(r2), adj=float(adj), p=float(p))
R['peringkat_zon'] = kor

print("\n  Hanya populasi ayam mencapai p < 0.05 — dan ayam BUKAN pelanggan VetEC.")
print("  Itu isyarat amaran, bukan dapatan: ayam menanda pembangunan pantai barat,")
print("  dan pantai barat lawan pantai timur ialah struktur sebenar yang dilihat.")

pantai = {"UTARA": "Barat", "TENGAH": "Barat", "BARAT DAYA": "Barat",
          "SELATAN": "Barat", "TENGGARA": "Timur", "TIMUR": "Timur",
          "TIMUR LAUT": "Timur"}
b = np.array([pantai[z] == "Barat" for z in Z])
t, pp = stats.ttest_ind(om[b], om[~b])
print(f"\n  Pantai barat (4 zon) purata output {om[b].mean():,.0f}; "
      f"pantai timur (3 zon) {om[~b].mean():,.0f}")
print(f"  Beza {om[b].mean()/om[~b].mean():.2f}× , t = {t:.2f}, p = {pp:.4f}")
r_ay, _ = stats.pearsonr(ayamm, b.astype(float))
r_op, _ = stats.pearsonr(opsm, b.astype(float))
print(f"  Korelasi ayam dengan 'pantai barat' r = {r_ay:+.2f}; "
      f"titik operasi r = {r_op:+.2f}")
R['pantai'] = dict(barat=float(om[b].mean()), timur=float(om[~b].mean()),
                   t=float(t), p=float(pp))

print()
print("=" * 104)
print("F. BEBAN KERJA SETIAP TITIK OPERASI — ukuran yang paling boleh ditindak")
print(f"  {'ZON':<12}{'titik':>6}{'km² / titik':>13}{'lembu / titik':>15}"
      f"{'penternak / titik':>19}{'output / titik':>16}")
beban = {}
for z in sorted(Z, key=lambda a: -(sum(LUAS[n] for n in ZON_NEG[a]) / OPS[a])):
    j = Z.index(z)
    kk = luasm[j] / OPS[z]; ll = lembum[j] / OPS[z]
    pp_ = penm[j] / OPS[z]; oo = om[j] / OPS[z]
    print(f"  {z:<12}{OPS[z]:>6}{kk:>13,.0f}{ll:>15,.0f}{pp_:>19,.0f}{oo:>16,.0f}")
    beban[z] = dict(km2=float(kk), lembu=float(ll), pen=float(pp_), out=float(oo))
kk = [beban[z]['km2'] for z in Z]; ll = [beban[z]['lembu'] for z in Z]
print(f"\n  Julat km² setiap titik  : {min(kk):,.0f} – {max(kk):,.0f}  "
      f"({max(kk)/min(kk):.1f} kali ganda)")
print(f"  Julat lembu setiap titik: {min(ll):,.0f} – {max(ll):,.0f}  "
      f"({max(ll)/min(ll):.1f} kali ganda)")
R['beban'] = beban

print("\n  Dua zon terbawah dalam Lampiran F (Timur, Timur Laut) mempunyai:")
for z in ["TIMUR", "TIMUR LAUT"]:
    j = Z.index(z)
    print(f"    {z:<12}titik {OPS[z]}  (paling sedikit)   "
          f"lembu/titik {beban[z]['lembu']:>7,.0f}   "
          f"km²/titik {beban[z]['km2']:>6,.0f}")
lain = [z for z in Z if z not in ("TIMUR", "TIMUR LAUT")]
print(f"    {'purata 5 lain':<12}titik {np.mean([OPS[z] for z in lain]):.1f}"
      f"              lembu/titik {np.mean([beban[z]['lembu'] for z in lain]):>7,.0f}"
      f"   km²/titik {np.mean([beban[z]['km2'] for z in lain]):>6,.0f}")

print()
print("=" * 104)
print("G. OUTPUT DINORMALKAN — penanda aras yang manakah mengubah kedudukan zon?")
print(f"  {'ZON':<12}{'output mentah':>14}{'/pegawai':>10}{'/titik':>10}"
      f"{'/1000 km²':>12}{'/1000 lembu':>13}{'/penternak':>12}")
norm = {}
for z in Z:
    j = Z.index(z)
    row = dict(mentah=om[j], per_peg=om[j] / pegm[j], per_titik=om[j] / OPS[z],
               per_km2=om[j] / (luasm[j] / 1000), per_lembu=om[j] / (lembum[j] / 1000),
               per_pen=om[j] / penm[j])
    norm[z] = {k: float(v) for k, v in row.items()}
    print(f"  {z:<12}{row['mentah']:>14,.0f}{row['per_peg']:>10,.0f}"
          f"{row['per_titik']:>10,.0f}{row['per_km2']:>12,.0f}"
          f"{row['per_lembu']:>13,.0f}{row['per_pen']:>12,.0f}")
print(f"\n  {'kedudukan':<12}", end="")
for k, lab in [('mentah', 'mentah'), ('per_peg', '/pegawai'), ('per_titik', '/titik'),
               ('per_km2', '/km²'), ('per_lembu', '/lembu'), ('per_pen', '/penternak')]:
    pass
print()
for k, lab in [('mentah', 'mentah'), ('per_peg', '/pegawai'), ('per_titik', '/titik'),
               ('per_km2', '/1000 km²'), ('per_lembu', '/1000 lembu'),
               ('per_pen', '/penternak')]:
    order = sorted(Z, key=lambda z: -norm[z][k])
    print(f"  {lab:<12}" + " > ".join(a[:4] for a in order))
R['normal'] = norm

print("\n  Zon Timur berada di kedudukan terakhir mengikut SETIAP penyebut.")
print("  Zon Tenggara jatuh dari tengah kepada terakhir kedua apabila populasi")
print("  lembu digunakan sebagai penyebut — ia mempunyai lembu terbanyak (138,565).")

print()
print("=" * 104)
print("H. UJIAN PEMISAH — adakah populasi ternakan memacu output langsung?")
print(f"  {'ujian':<52}{'b':>13}{'p':>9}")
uji = {}
for lab, v in [("Lembu, antara zon (n=7, korelasi)", None)]:
    pass
r, p = stats.pearsonr(lembum, om)
print(f"  {'Lembu vs output, antara zon (n = 7)':<52}{r:>+13.3f}{p:>9.4f}")
uji['antara_lembu'] = dict(r=float(r), p=float(p))
KTL = np.column_stack([np.ones(35), peg, lad] + zd + td)
def _sisa(v):
    bb, *_ = np.linalg.lstsq(KTL, v, rcond=None)
    return v - KTL @ bb
ry = _sisa(out)
for lab, v in [("Lembu, dalam zon (KT zon + tahun, n = 35)", lembu),
               ("Kambing?, dalam zon", kambing),
               ("Ruminan, dalam zon", rum),
               ("Ayam, dalam zon (plasebo)", ayam)]:
    rx = _sisa(v)
    bb = float(rx @ ry / (rx @ rx))
    e = ry - bb * rx
    dfe = 35 - KTL.shape[1] - 1
    see = float(np.sqrt((e @ e) / dfe / (rx @ rx)))
    pp2 = float(2 * (1 - stats.t.cdf(abs(bb / see), dfe)))
    print(f"  {lab:<52}{bb:>+13.4f}{pp2:>9.4f}")
    uji[lab] = dict(b=bb, p=pp2)
R['pemisah'] = uji
print("\n  Populasi lembu tidak meramal output antara zon (p = 0.93) mahupun")
print("  dalam zon (p = 0.73). Beban kerja VetEC tidak diagihkan mengikut")
print("  di mana ternakan sebenarnya berada.")

json.dump(R, open('identiti2.json', 'w'), indent=1)
print("\nDisimpan: identiti2.json")

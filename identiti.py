"""Faktor identiti zon: bolehkah keluasan kawasan, titik operasi VetEC dan
populasi ternakan kebangsaan menggantikan kesan tetap zon?

Sumber ternakan: Perangkaan Ternakan Malaysia, Jadual 3.1 (lembu) dan 4.1 (ayam),
serta satu jadual tambahan yang tajuknya terpotong dalam imej sumber (magnitud
sepadan dengan kambing) — dilabel 'kambing?' dan diuji berasingan.
"""
import openpyxl, json
import numpy as np
from scipy import stats

Z = ["UTARA", "TENGAH", "BARAT DAYA", "SELATAN", "TENGGARA", "TIMUR", "TIMUR LAUT"]
Y = [2021, 2022, 2023, 2024, 2025]

# ---- zon -> negeri, ibu pejabat, titik operasi (dari peta VetEC) --------------
ZON_NEG = {
    "UTARA":      ["Perlis", "Kedah", "Pulau Pinang"],
    "TENGAH":     ["Perak", "Selangor"],
    "BARAT DAYA": ["N. Sembilan", "Melaka"],
    "SELATAN":    ["Johor"],
    "TENGGARA":   ["Pahang"],
    "TIMUR":      ["Terengganu"],
    "TIMUR LAUT": ["Kelantan"],
}
OPS = {"UTARA": 8, "TENGAH": 14, "BARAT DAYA": 10, "SELATAN": 13,
       "TENGGARA": 9, "TIMUR": 5, "TIMUR LAUT": 5}

# ---- keluasan negeri, km2 (angka rasmi) --------------------------------------
LUAS = {"Perlis": 821, "Kedah": 9500, "Pulau Pinang": 1048, "Perak": 21035,
        "Selangor": 8104, "N. Sembilan": 6686, "Melaka": 1664, "Johor": 19210,
        "Pahang": 36137, "Terengganu": 13035, "Kelantan": 15099}

# ---- ternakan mengikut negeri, 2020-2025e (daripada imej sumber) -------------
NEG_TAHUN = [2020, 2021, 2022, 2023, 2024, 2025]
LEMBU = {  # Jadual 3.1
    "Perlis":       [3812, 3904, 5973, 7043, 6558, 6355],
    "Kedah":        [52948, 53011, 50576, 49191, 44730, 43169],
    "Pulau Pinang": [11308, 12172, 11948, 11661, 16727, 16792],
    "Perak":        [56492, 55708, 64945, 70442, 72915, 74047],
    "Selangor":     [35142, 38895, 34895, 33875, 32494, 33393],
    "N. Sembilan":  [36972, 44486, 46002, 46111, 47281, 46961],
    "Melaka":       [19137, 26095, 25465, 28993, 29747, 29702],
    "Johor":        [95581, 103936, 107799, 112812, 102254, 104602],
    "Pahang":       [154147, 150454, 149062, 138699, 136531, 138565],
    "Terengganu":   [85416, 85163, 95419, 95780, 101986, 102502],
    "Kelantan":     [81307, 77254, 75720, 71913, 70210, 68548],
}
KAMBING = {  # jadual tajuk terpotong; magnitud sepadan kambing
    "Perlis":       [4366, 4407, 7889, 8290, 8443, 8345],
    "Kedah":        [50085, 50849, 55203, 53646, 53369, 54656],
    "Pulau Pinang": [9000, 10190, 10953, 11587, 13712, 14382],
    "Perak":        [15119, 18569, 18392, 20741, 15767, 15352],
    "Selangor":     [27837, 30253, 31228, 27479, 29622, 31513],
    "N. Sembilan":  [13109, 16316, 16412, 15629, 15515, 15304],
    "Melaka":       [18668, 10461, 9619, 9543, 13692, 13910],
    "Johor":        [33195, 35731, 38458, 41453, 32170, 32796],
    "Pahang":       [35366, 40649, 39696, 41416, 40431, 41170],
    "Terengganu":   [33427, 33874, 37531, 38784, 38111, 39891],
    "Kelantan":     [35012, 33261, 32596, 30965, 30411, 29867],
}
AYAM = {  # Jadual 4.1
    "Perlis":       [541945, 844573, 867301, 523860, 617125, 625076],
    "Kedah":        [19686670, 21838000, 23883212, 24047983, 23639173, 24057387],
    "Pulau Pinang": [14195730, 13197995, 15574537, 16213609, 14520725, 14896567],
    "Perak":        [40844500, 42031500, 41894500, 41097500, 40902000, 42662328],
    "Selangor":     [21786436, 24355658, 22687114, 28249142, 25845019, 26911165],
    "N. Sembilan":  [22325652, 24011281, 26357334, 29727918, 31373079, 32486848],
    "Melaka":       [32086967, 30861607, 30356503, 33286808, 34360264, 36069964],
    "Johor":        [62132805, 51862940, 54170061, 53192051, 64737376, 67063483],
    "Pahang":       [14405801, 14016721, 14101294, 16327463, 15365282, 16106211],
    "Terengganu":   [3962423, 3412398, 3556825, 4345248, 4543641, 4534629],
    "Kelantan":     [5048785, 5122850, 5042000, 4663650, 4638880, 4710527],
}


def agregat(tab, zon, tahun):
    j = NEG_TAHUN.index(tahun)
    return float(sum(tab[n][j] for n in ZON_NEG[zon]))


# ---- data VetEC --------------------------------------------------------------
wb = openpyxl.load_workbook('lt_v3.xlsx', data_only=True)
AKT = ["KHIDMAT NASIHAT", "KESIHATAN GEROMPOK (BIL PENTERNAK)", "RAWATAN BIASA (BIL KES)",
       "PEMBIAKAN (BIL PENTERNAK)", "LAWAT SIASAT", "AUDIT/VERIFIKASI", "PERSAMPELAN",
       "VAKSINASI", "UJIAN LAPANGAN", "MESYUARAT"]
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
luas = col(lambda z, y: sum(LUAS[n] for n in ZON_NEG[z]))
ops = col(lambda z, y: OPS[z])
lembu = col(lambda z, y: agregat(LEMBU, z, y))
kambing = col(lambda z, y: agregat(KAMBING, z, y))
ayam = col(lambda z, y: agregat(AYAM, z, y))
rum = lembu + kambing
zi = np.array([Z.index(z) for z, _ in cells])
yi = np.array([Y.index(y) for _, y in cells])
zd = [(zi == j).astype(float) for j in range(1, 7)]
td = [(yi == j).astype(float) for j in range(1, 5)]
R = {}


def ols(y, cols):
    """SE dikira melalui SVD ke atas X sendiri, bukan pinv(X'X).

    pinv(X'X) menguadratkan nombor keadaan dan memotong nilai singular kecil,
    yang menghasilkan SE yang terlalu kecil secara palsu apabila peramal hampir
    kolinear. Reka bentuk yang hampir singular ditanda, bukan dilaporkan.
    """
    X = np.column_stack([np.ones(len(y))] + list(cols))
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ b
    rank = np.linalg.matrix_rank(X)
    df = len(y) - rank
    ssr = float(r @ r)
    sst = float(((y - y.mean()) ** 2).sum())
    U, sv, Vt = np.linalg.svd(X, full_matrices=False)
    kond = float(sv[0] / sv[-1]) if sv[-1] > 0 else np.inf
    if rank < X.shape[1] or kond > 1e8:
        se = np.full(X.shape[1], np.nan)      # hampir singular: SE tidak bermakna
    else:
        se = np.sqrt(np.diag(Vt.T @ np.diag(sv ** -2) @ Vt) * ssr / df)
    with np.errstate(divide='ignore', invalid='ignore'):
        t = b / se
    p = 2 * (1 - stats.t.cdf(np.abs(t), df))
    return dict(b=b, se=se, p=p, ssr=ssr, df=df, r2=1 - ssr / sst, k=X.shape[1],
                kond=kond, rank=int(rank))


def ftest(kecil, besar, q):
    F = ((kecil['ssr'] - besar['ssr']) / q) / (besar['ssr'] / besar['df'])
    return float(F), float(1 - stats.f.cdf(F, q, besar['df']))


# ================================================================= A. profil
print("=" * 108)
print("A. PROFIL IDENTITI SETIAP ZON (nilai 2025; ternakan daripada Perangkaan Ternakan)")
print(f"  {'ZON':<12}{'negeri':<26}{'luas km²':>10}{'titik':>7}{'lembu':>10}"
      f"{'kambing?':>10}{'ayam (juta)':>13}")
prof = {}
for z in Z:
    s = (zi == Z.index(z)) & (yi == 4)
    print(f"  {z:<12}{' + '.join(ZON_NEG[z]):<26}{luas[s][0]:>10,.0f}{OPS[z]:>7}"
          f"{lembu[s][0]:>10,.0f}{kambing[s][0]:>10,.0f}{ayam[s][0]/1e6:>12.1f}")
    prof[z] = dict(luas=float(luas[s][0]), ops=OPS[z], lembu=float(lembu[s][0]),
                   kambing=float(kambing[s][0]), ayam=float(ayam[s][0]))
print(f"  {'JUMLAH':<12}{'':<26}{sum(sum(LUAS[n] for n in ZON_NEG[z]) for z in Z):>10,}"
      f"{sum(OPS.values()):>7}{sum(prof[z]['lembu'] for z in Z):>10,.0f}"
      f"{sum(prof[z]['kambing'] for z in Z):>10,.0f}"
      f"{sum(prof[z]['ayam'] for z in Z)/1e6:>12.1f}")
R['profil'] = prof

# ================================================================= B. liputan
print()
print("=" * 108)
print("B. LIPUTAN VetEC — berapa besar sektor sebenar berbanding pangkalan data VetEC (2025)")
print(f"  {'ZON':<12}{'penternak VetEC':>16}{'lembu negeri':>14}{'lembu/penternak':>17}"
       f"{'ladang dilawat':>16}{'km² setiap titik':>18}")
lip = {}
for z in Z:
    s = (zi == Z.index(z)) & (yi == 4)
    r = float(lembu[s][0] / pen[s][0])
    print(f"  {z:<12}{pen[s][0]:>16,.0f}{lembu[s][0]:>14,.0f}{r:>17,.0f}"
          f"{lad[s][0]:>16,.0f}{luas[s][0]/OPS[z]:>18,.0f}")
    lip[z] = dict(pen=float(pen[s][0]), lembu_per_pen=r,
                  km2_per_titik=float(luas[s][0] / OPS[z]))
tot_pen = pen[yi == 4].sum(); tot_lembu = lembu[yi == 4].sum()
print(f"  {'JUMLAH':<12}{tot_pen:>16,.0f}{tot_lembu:>14,.0f}"
      f"{tot_lembu/tot_pen:>17,.0f}")
print(f"\n  Nisbah lembu setiap penternak berbeza {max(v['lembu_per_pen'] for v in lip.values())/min(v['lembu_per_pen'] for v in lip.values()):.1f} kali ganda "
      "antara zon — pangkalan data VetEC bukan sampel seragam bagi sektor.")
R['liputan'] = lip

# ================================================================= C. korelasi
print()
print("=" * 108)
print("C. KORELASI PERINGKAT ZON (n = 7) — purata output 5 tahun lawan ciri zon")
om = np.array([out[zi == j].mean() for j in range(7)])
prodm = np.array([out[zi == j].sum() / peg[zi == j].sum() for j in range(7)])
ciri = {
    "Keluasan kawasan (km²)": np.array([luas[zi == j][0] for j in range(7)]),
    "Titik operasi VetEC": np.array([float(OPS[z]) for z in Z]),
    "Populasi lembu": np.array([lembu[zi == j].mean() for j in range(7)]),
    "Populasi kambing?": np.array([kambing[zi == j].mean() for j in range(7)]),
    "Populasi ruminan (lembu+kambing)": np.array([rum[zi == j].mean() for j in range(7)]),
    "Populasi ayam (plasebo)": np.array([ayam[zi == j].mean() for j in range(7)]),
    "Penternak pangkalan data VetEC": np.array([pen[zi == j].mean() for j in range(7)]),
    "Bilangan pegawai": np.array([peg[zi == j].mean() for j in range(7)]),
    "Ladang dilawat": np.array([lad[zi == j].mean() for j in range(7)]),
}
print(f"  {'ciri zon':<36}{'r vs output':>13}{'p':>9}   {'r vs output/pegawai':>20}{'p':>9}")
kor = {}
for nm, v in ciri.items():
    r1, p1 = stats.pearsonr(v, om)
    r2, p2 = stats.pearsonr(v, prodm)
    star = '  ←' if p1 < .05 else ''
    print(f"  {nm:<36}{r1:>+13.3f}{p1:>9.4f}   {r2:>+20.3f}{p2:>9.4f}{star}")
    kor[nm] = dict(r_out=float(r1), p_out=float(p1), r_prod=float(r2), p_prod=float(p2))
R['korelasi_zon'] = kor

print("\n  Kedudukan zon mengikut titik operasi lawan output terlaras (Lampiran F):")
adj = {"UTARA": 52858, "TENGAH": 49071, "BARAT DAYA": 44667, "TENGGARA": 36328,
       "SELATAN": 32348, "TIMUR LAUT": 19643, "TIMUR": 13866}
print(f"  {'ZON':<12}{'titik':>7}{'min terlaras':>14}{'output/titik':>14}"
      f"{'output/1000 km²':>17}{'output/1000 lembu':>19}")
for z in sorted(Z, key=lambda a: -OPS[a]):
    s = zi == Z.index(z)
    o5 = out[s].mean()
    print(f"  {z:<12}{OPS[z]:>7}{adj[z]:>14,}{o5/OPS[z]:>14,.0f}"
          f"{o5/(luas[s][0]/1000):>17,.0f}{o5/(lembu[s].mean()/1000):>19,.0f}")
R['normalisasi'] = {z: dict(per_titik=float(out[zi == Z.index(z)].mean() / OPS[z]),
                           per_1000km2=float(out[zi == Z.index(z)].mean() /
                                             (luas[zi == Z.index(z)][0] / 1000)),
                           per_1000lembu=float(out[zi == Z.index(z)].mean() /
                                               (lembu[zi == Z.index(z)].mean() / 1000)))
                    for z in Z}

# ============================================== D. lihat identiti2.py
print()
print("=" * 108)
print("D-E. Ujian 'ciri zon menggantikan dami zon' TIDAK dijalankan di sini.")
print("     Keluasan dan titik operasi adalah malar dalam zon (R² = 1.000 atas dami")
print("     zon); ternakan 97-98%. Lima daripadanya menjangkau hampir keseluruhan")
print("     ruang dami zon, jadi ia mesti menyerap kesan zon tanpa mengira kaitan")
print("     sebenar — keputusannya tautologi, bukan bukti.")
print("     Analisis peringkat zon yang sah ada dalam identiti2.py.")

# ================================================================= F. dalam zon
print()
print("=" * 108)
print("F. UJIAN DALAM-ZON — populasi ternakan berubah setiap tahun; adakah output ikut?")
print("   (dengan kesan tetap zon + tahun, jadi hanya turun-naik dalam zon digunakan)")
print(f"  {'pemboleh ubah':<30}{'b':>14}{'SE':>13}{'p':>9}{'variasi baki':>12}")
R['dalam_zon'] = {}
# Frisch-Waugh-Lovell: stabil secara berangka walaupun peramal hampir kolinear
# dengan dami zon (ayam: hanya 0.9% variasi kekal selepas kawalan).
KTL = np.column_stack([np.ones(35), peg, lad] + zd + td)
def _sisa(v):
    bb, *_ = np.linalg.lstsq(KTL, v, rcond=None)
    return v - KTL @ bb
ry = _sisa(out)
for nm, v in [("Populasi lembu", lembu), ("Populasi kambing?", kambing),
              ("Populasi ruminan", rum), ("Populasi ayam (plasebo)", ayam)]:
    rx = _sisa(v)
    bb = float(rx @ ry / (rx @ rx))
    e = ry - bb * rx
    dfe = 35 - KTL.shape[1] - 1
    see = float(np.sqrt((e @ e) / dfe / (rx @ rx)))
    pp = float(2 * (1 - stats.t.cdf(abs(bb / see), dfe)))
    baki = float(rx.var() / v.var())
    print(f"  {nm:<30}{bb:>+14.4f}{see:>13.4f}{pp:>9.4f}{baki*100:>12.1f}%")
    R['dalam_zon'][nm] = dict(b=bb, se=see, p=pp, variasi_baki=baki)
print("\n  Nota: keluasan dan titik operasi malar dalam zon, jadi tidak boleh diuji "
      "dengan cara ini —\n  kesannya hanya boleh dilihat antara zon.")

json.dump(R, open('identiti.json', 'w'), indent=1)
print("\nDisimpan: identiti.json")

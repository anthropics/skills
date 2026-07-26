"""Analisis sokongan: keterlaluan setiap tahun dalam zon, corak aliran kebangsaan,
dan semakan 2026 separa bagi zon yang ditandakan."""
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
       ("LAWAT SIASAT", "Lawat siasat"), ("AUDIT/VERIFIKASI", "Regulatori"),
       ("PERSAMPELAN", "Pensampelan"), ("VAKSINASI", "Vaksinasi"),
       ("UJIAN LAPANGAN", "Ujian lapangan"), ("MESYUARAT", "Mesyuarat")]


def read_year(sheet):
    ws = wb[sheet]
    rows = [[('' if c is None else str(c).strip()) for c in r]
            for r in ws.iter_rows(values_only=True)]
    h = next(i for i, r in enumerate(rows) if 'BARAT DAYA' in r)
    ci = {z: rows[h].index(z) for z in ZONES}
    o = {}
    for r in rows[h + 1:]:
        lab = (r[1] or r[0]).strip().upper()
        if not lab:
            continue
        try:
            o[lab] = {z: int(float(r[ci[z]])) for z in ZONES}
        except (ValueError, IndexError):
            pass
    return o


D = {y: read_year(str(y)) for y in YEARS}
D26 = read_year('2026 (April)')
OUT = {z: [sum(D[y][k][z] for k, _ in AKT) for y in YEARS] for z in ZONES}
out26 = {z: sum(D26[k][z] for k, _ in AKT) for z in ZONES}

sup = {}

print("=" * 96)
print("G. TAHUN PALING TERKELUAR DALAM SETIAP ZON (skor-z dalam zon, output teknikal)")
print(f"  {'ZON':<12}" + "".join(f"{y:>9}" for y in YEARS) + "   tahun paling ekstrem")
rows = []
for z in ZONES:
    v = np.array(OUT[z], float)
    zs = (v - v.mean()) / v.std(ddof=1)
    i = int(np.abs(zs).argmax())
    print(f"  {z:<12}" + "".join(f"{s:>+9.2f}" for s in zs) +
          f"   {YEARS[i]} ({zs[i]:+.2f})")
    rows.append((z, [float(s) for s in zs], YEARS[i], float(zs[i])))
sup['dalam_zon'] = rows

print()
print("Kiraan sel melampau (|z dalam zon| > 1.2) mengikut tahun:")
cnt = {y: 0 for y in YEARS}
for z, zs, _, _ in rows:
    for i, s in enumerate(zs):
        if abs(s) > 1.2:
            cnt[YEARS[i]] += 1
for y in YEARS:
    print(f"  {y}: {cnt[y]} daripada 7 zon   {'█' * cnt[y]}")
sup['kiraan_melampau'] = cnt

print()
print("=" * 96)
print("H. ALIRAN AKTIVITI KEBANGSAAN — mana yang paling tidak stabil?")
print(f"  {'aliran':<20}" + "".join(f"{y:>10}" for y in YEARS) + f"{'CV%':>8}{'maks/min':>10}")
nat = {}
for k, n in AKT:
    v = np.array([sum(D[y][k][z] for z in ZONES) for y in YEARS], float)
    nat[n] = v
    cv = v.std(ddof=1) / v.mean() * 100
    print(f"  {n:<20}" + "".join(f"{a:>10,.0f}" for a in v) +
          f"{cv:>7.1f}%{max(v)/min(v):>10.2f}×")
sup['aliran_kebangsaan'] = {n: [float(a) for a in v] for n, v in nat.items()}

print()
print("Sumbangan setiap aliran kepada perubahan output tahunan (unit):")
print(f"  {'aliran':<20}" + "".join(f"{YEARS[i]}→{str(YEARS[i+1])[2:]:>3}" for i in range(4)))
tot = np.zeros(4)
for n, v in nat.items():
    d = np.diff(v)
    tot += d
    print(f"  {n:<20}" + "".join(f"{a:>+10,.0f}" for a in d))
print(f"  {'JUMLAH':<20}" + "".join(f"{a:>+10,.0f}" for a in tot))

print()
print("=" * 96)
print("I. SEMAKAN 2026 (Jan–Apr) BAGI ZON YANG DITANDAKAN")
print("   Nota: 4 bulan sahaja. Kadar tahunan = nilai × 3 untuk perbandingan kasar.")
print(f"  {'ZON':<12}{'2024':>9}{'2025':>9}{'2026 4bln':>11}{'× 3':>10}"
      f"{'vs 2025':>10}")
for z in ZONES:
    a = out26[z]
    print(f"  {z:<12}{OUT[z][3]:>9,}{OUT[z][4]:>9,}{a:>11,}{a*3:>10,}"
          f"{(a*3/OUT[z][4]-1)*100:>+9.0f}%")
sup['y2026'] = {z: float(out26[z]) for z in ZONES}

print()
print("Zon Timur — pecahan aliran, 2025 lawan 2026 (4 bulan, dikadarkan × 3)")
print(f"  {'aliran':<20}{'2024':>9}{'2025':>9}{'2026×3':>10}")
for k, n in AKT:
    print(f"  {n:<20}{D[2024][k]['TIMUR']:>9,}{D[2025][k]['TIMUR']:>9,}"
          f"{D26[k]['TIMUR']*3:>10,}")

print()
print("=" * 96)
print("J. KORELASI ANTARA ZON — adakah zon bergerak bersama?")
M = np.array([OUT[z] for z in ZONES], float)
print(f"  {'':<12}" + "".join(f"{z[:6]:>8}" for z in ZONES))
pairs = []
for i, z in enumerate(ZONES):
    line = f"  {z:<12}"
    for j in range(len(ZONES)):
        r = np.corrcoef(M[i], M[j])[0, 1]
        line += f"{r:>+8.2f}"
        if i < j:
            pairs.append((abs(r), r, ZONES[i], ZONES[j]))
    print(line)
print()
print("  Pasangan paling berkorelasi:")
for a, r, x, y in sorted(pairs, reverse=True)[:3]:
    print(f"    {x} & {y}: r = {r:+.2f}")
print("  Purata korelasi berpasangan: "
      f"{np.mean([p[1] for p in pairs]):+.2f}  (0 = zon bergerak bebas)")
sup['korelasi_purata'] = float(np.mean([p[1] for p in pairs]))

json.dump(sup, open('tren2.json', 'w'), indent=1)
print("\nDisimpan: tren2.json")

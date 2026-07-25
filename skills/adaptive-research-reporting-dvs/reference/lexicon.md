# Lexicon — controlling Bahasa Malaysia vocabulary

**Load when:** producing any Bahasa Malaysia output.

**Authority:** *Panduan Ekonomi Projek Penternakan Lembu Tenusu*, Edisi Mei 2024 (JPV/KPKM) is
the controlling reference for BM technical vocabulary. Where this lexicon and writing habit
conflict, this lexicon wins.

**First-use rule:** on first use of a technical term, give the BM term with the English in
parentheses — *lembu bunting (pregnant heifers)*, *media pertumbuhan (growth medium)*,
*kesan tetap (fixed effects)*. Thereafter BM alone. This is a fixed rule: the readership knows
the concept in English and the document in BM.

---

## L1 — Penilaian kewangan (financial appraisal)
| BM (canonical) | English | Note |
|---|---|---|
| Dayamaju Kewangan | Financial viability | section heading for the appraisal block |
| Kadar Pulangan Dalaman (IRR) | Internal Rate of Return | report as % |
| Nilai Kini Bersih (NPV) | Net Present Value | always state discount rate: `NPV @10%` |
| **Nisbah Faedah Kos (BCR)** | Benefit Cost Ratio | see L10 — source prints "Kod"; **use "Kos"** |
| Tempoh Pulang Modal (PBP) | Payback Period | in years, 2 decimals |
| Pulangan atas Pelaburan (ROI) | Return on Investment | source uses the English label; either acceptable |

## L2 — Struktur aliran tunai (cash flow architecture)
`Unjuran Aliran Kewangan` · `Unjuran Aliran Fizikal Ternakan` · `Aliran Wang Masuk` ·
`Aliran Wang Keluar` · `Jumlah Wang Masuk` · `Jumlah Wang Keluar` · `Kos Tetap` ·
`Kos Langsung / Kos Operasi` · `Kos Pentadbiran` · `Kos Seunit` · `Lebihan/Defisit` ·
`Lebihan/Defisit Terkumpul` · `Nilai Lupus` · `Pelbagai Perbelanjaan`

Structural convention: `A. ALIRAN WANG MASUK` → `B. ALIRAN WANG KELUAR`
(`B1. Kos Tetap`, `B2. Kos Langsung/Kos Operasi`, `B3. Kos Pentadbiran`) →
`C. JUMLAH WANG KELUAR (B1+B2+B3)` → `E. DAYAMAJU KEWANGAN`.

## L3 — Struktur kawanan (herd structure)
`Stok Awal` · `Ringkasan Stok Akhir` · `Pejantan` · `Induk` · `Dara` ·
`Anak Jantan < setahun` · `Anak Betina < setahun` · `Anak > setahun` · `Kematian` ·
`Pembelian` · `Jualan` · `Takai` (cull: `Pejantan Takai`, `Induk Takai`) ·
`Animal Unit (Unit ternak)` · `B. Perah` (betina perah) · `B. Kering` (betina kering)

**`Induk` is a defined composite:** betina perah + betina kering + dara. State this definition
in any table where `Induk` appears alongside its components, and verify the arithmetic (V4).

## L4 — Parameter teknikal
`Kadar Kelahiran` · `Kadar Kematian` · `Takai Jantan` / `Takai Betina` ·
`Tempoh Laktasi (hari)` · `Purata induk perah (%)` · `Pengeluaran susu (lit/hari)`

## L5 — Kos input
`Makanan dibeli (DCP)` · `Makanan (Foder)` · `Mineral Blok & Vits` · `Ubatan dan rawatan` ·
`Petrol dan bahan api` · `Upah pekerja` · `Gaji pengurusan` · `Penyelenggaraan kandang` ·
`Penyelenggaraan mesin dan peralatan` · `Pembaikan & Alat Ganti` · `Sewa tanah` ·
`Baja foder & penyelenggaraan` · `Penyediaan tanah` · `Tanaman Rumput` · `Kandang` ·
`Bekalan air dan elektrik` · `Milking Parlour (line / portable)` · `Tangki penyimpanan susu` ·
`Traktor dan peralatan` · `Kenderaan Ladang (lori)`

Revenue channels: `Susu Jualan Kilang` (factory) vs `Susu Jualan Tempatan` (local) — different
prices; never merge into one line.

## L6 — Skala projek
`Skala Kecil` · `Semi Komersial` · `Komersial`. Use **`Komersial`** throughout (source
alternates *komersil*/*komersial*; standardise).

## L7 — Bahagian hadapan institusi (institutional front matter)
`Pembuka Kata` · `Sekapur Sirih` (head-of-department message) · `Khidmat Nasihat` ·
`Sekalung Budi` · `Penafian (Disclaimer)` · `Disediakan oleh:` · `Diterbitkan di Malaysia oleh:`
· `Tarikh Laporan:` · `Edisi [Bulan Tahun]` · `- Tamat Laporan -`

Full institutional address block for formal publications:
```
Jabatan Perkhidmatan Veterinar,
Kementerian Pertanian dan Keterjaminan Makanan,
Wisma Tani, Blok Podium Lot 4G1 & 4G2,
No. 28, Persiaran Perdana, Presint 4,
Pusat Pentadbiran Kerajaan Persekutuan,
62624 Putrajaya, Wilayah Persekutuan Putrajaya.
```

## L8 — Istilah analitik (analytical terms)
`Statistik deskriptif` · `Sisihan Piawai` · `Pekali Variasi (CV)` · `Regresi linear` ·
`Kecerunan setahun` · `Korelasi Pearson` · `Ujian-t berpasangan` · `Analisis varians (ANOVA)` ·
`Pekali Gini` · `Indeks kepelbagaian Shannon-Wiener` · `Kesan tetap (fixed effects)` ·
`Pemboleh ubah boneka (dummy variable)` · `Set data panel` · `Cerapan (observation)` ·
`Saiz kesan (Cohen d)` · `Julat ketidakpastian 95%` · `dimalarkan` (held constant) ·
`Signifikan` / `Kecenderungan` / `Tidak signifikan`

**Verdict convention:** `p < 0.05` → **Signifikan**; `0.05 ≤ p < 0.10` → **Kecenderungan**;
`p ≥ 0.10` → **Tidak signifikan**. State α explicitly once, in the methodology section.

## L9 — Istilah dasar (policy terms — the disambiguation set)
| Term | Meaning — keep strictly separate |
|---|---|
| `Keterjaminan Makanan` | food security — adequacy of supply |
| `Kedaulatan Makanan` | food sovereignty — *national control* over the means of production |
| `Keselamatan Protein` | protein security — protein adequacy irrespective of source |
| `SSR (Kadar Sara Diri)` | self-sufficiency ratio — computed on conventional agricultural output only |
| `Pelengkap` vs `Pengganti` | complement vs substitute — never blur |
| `Rantaian Nilai` / `Rantaian Bekalan` | value chain / supply chain |
| `Penyampaian Perkhidmatan` | service delivery |
| `Pengembangan` | extension |

## L10 — Known published-source errors — do NOT propagate
| Appears as | Correct to | Where |
|---|---|---|
| `Nisbah Faedah **Kod** (BCR)` | `Nisbah Faedah **Kos** (BCR)` | Panduan Ekonomi, appraisal tables |
| `PERKHDIMATAN` | `PERKHIDMATAN` | Panduan Ekonomi, DG signature block |
| `komersil` (variable) | `komersial` | throughout |
| `Mt/ekor/Tahun` on `Makanan (Foder)` | `kg/tahun` | unit label contradicts the arithmetic |
| `Pelbagai Perbelanjaan (5% daripada kos operasi)` | label ≠ computation (fixed base escalating 5%/yr) | correct the label or the formula, and say which |

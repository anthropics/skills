# Verification gate — run before printing ANY draft

**Load when:** a draft exists and is about to be printed. Every check is **blocking**.

---

## S1 — Register and voice
- Formal institutional register; impersonal construction: **`Laporan ini menilai…`**,
  `Analisis ini berasaskan…`, `Bahagian ini membentangkan…`
- **First person is prohibited in all modes.** No *kita*, no *kami*, no *saya*. The analyst is
  not a character in the document.
- English technical terms parenthesised on first use, then BM alone (see lexicon first-use rule).

## S2 — Bold discipline (semantic only, never decorative)
Bold is reserved for: the takeaway sentence of a section · table headers, total rows, and delta
columns · significance verdicts (**Signifikan** / **Tidak signifikan**) · the disambiguating
term in a contrast. If bold is doing emphasis rather than *marking a finding*, remove it.

## S3 — Numeric precision
- Retain full source precision in tables: `63,325,673.45 liter`, `H = 1.567 (evenness 0.680)`
- Percentage change always paired with absolutes: `+31.84%, iaitu 3,216 kepada 4,240 orang`
- Statistical results as complete tuples: `F = 22.94, p < 0.0001`; `r = +0.924, p = 0.025`; `R² = 0.998`
- Thousands separators throughout; two decimals on money and volume
- Direction sign carried explicitly on deltas: `−14.64%`, `+125.89%`

## S4 — Table and figure discipline
- Sequential numbering: `Jadual 1, 2, 3…` and `Rajah 1, 2, 3…` — verify no repeats, no gaps
- **Every table/figure is referenced in prose before it appears** (`Jadual 1 menunjukkan…`,
  `Rajah 3 memaparkan…`)
- Caption format: bold label, italic descriptor —
  `**Jadual 1.** *Trend parameter utama VetEC, 2021–2025.*`
- Section numbering strictly sequential — verify the whole sequence end to end

## S5 — Transition lexicon (deploy deliberately; they carry the argument)
| Transition | Function |
|---|---|
| **`Dengan kata lain,`** | restate a technical result in policy language — bridge from statistics to decision |
| **`Sebaliknya,`** | pivot to the counter-trend or the contradicting case |
| `Secara rumusan,` | open the executive summary's headline finding |
| `Apabila dinilai mengikut…` | introduce a reframing by a different unit or period |
| `Namun demikian,` | concede, then qualify |
| `Ini bermakna` / `Ini mengesahkan bahawa` | convert a result into its interpretation |

## S6 — Authority ceiling is RAISED — hedged endings are BANNED
| ✗ Banned | ✓ Required |
|---|---|
| `Keutamaan disarankan bertumpu…` | `Keutamaan hendaklah bertumpu…` |
| `adalah dicadangkan…` | `perlu dilaksanakan…` |
| `memerlukan siasatan lanjut` | a **specified study**: question, method, data source, owner, deadline |
| `perlu diberi perhatian` | the specific action, its owner, and its timeline |
| `boleh dipertimbangkan` | `hendaklah` / `perlu` + the action |

Every report terminates in a numbered, prioritised action list. Each action names **what**,
**who** (by unit or post — never an individual), and **by when**. Where an evidence gap prevents
a recommendation, convert it into a commissioned study, not a hedge:

> ✗ `Penurunan pengeluaran di PPIT Sabak Bernam memerlukan siasatan lanjut.`
> ✓ `PPIT Sabak Bernam hendaklah menjalani audit pengeluaran meliputi rekod populasi induk,
>    kadar laktasi dan penyelenggaraan peralatan bagi tempoh Julai–Disember 2025.
>    Tanggungjawab: Seksyen Ruminan, BPIT dengan JPV Negeri Selangor. Tarikh siap: 30 Jun 2026.`

## S7 — Arithmetic verification gate (recompute; do not trust a supplied table)
| # | Check |
|---|---|
| **V1** | every column and row total equals the sum of its components |
| **V2** | every percentage recomputes from its own numerator/denominator; percentage columns sum to 100.00% |
| **V3** | every period-on-period change recomputes from the two values shown |
| **V4** | every composite equals its stated definition (e.g. `Induk = B. Perah + B. Kering + Dara`) |
| **V5** | every ranking claim in prose matches the ordering in the table it cites |
| **V6** | one national total only — same figure in summary, tables, and narrative |
| **V7** | section and figure numbering sequential and complete |
| **V8** | every declared parameter is actually applied — and on **both** the cost side and the revenue side |
| **V9** | every unit label is dimensionally coherent with its own arithmetic |
| **V10** | every label matches the computation beneath it (a line called "5% of X" must compute 5% of X) |

**V8, V9, V10 catch the errors humans miss.** A model whose parameter table declares a varying
rate while its revenue line holds output constant is internally contradictory, and every
downstream appraisal figure inherits the contradiction.

## Reconciliation protocol (MANDATORY, all modes)
On any conflict across sources, tables, or sections — or any V-check failure:
1. **Identify** every basis present and quantify the delta.
2. **Trace** the delta to its origin (a component included in one basis and excluded from
   another; a stale revision; a transcription error).
3. **Auto-select** the internally consistent basis — the one whose components sum to its own
   total and which reconciles with the narrative.
4. **Apply it uniformly** to every table, figure, percentage, and sentence.
5. **Disclose** the correction in `Nota` — state the discrepancy, the basis adopted, and why.

Never halt for instructions. Never silently pick one. Correct, apply, disclose.

## S8 — Final pre-print sweep
- [ ] Mode correct for audience × stakes
- [ ] Rigor level justified by contestation, not data volume
- [ ] No inferential statistics deployed against an uncontested finding
- [ ] Language matches the audience, not the request
- [ ] Lexicon compliant; no L10 source errors propagated
- [ ] No individuals named
- [ ] All ten verification checks passed
- [ ] Reconciliations disclosed in `Nota`
- [ ] `Limitasi` present (Mode A)
- [ ] Terminates in assignable action with owner and deadline — no banned hedges
- [ ] Conclusion restates the **implication**, not the statistics

# 16 — Polymer GPC chromatogram

Gel-permeation chromatography trace for a typical polymer sample, used
for molecular-weight distribution reporting.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 7 rows with `elution_mL,intensity`.
- `plot.py` — reads CSV, plots filled chromatogram with peak label.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
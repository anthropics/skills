# 19 — Multifield temperature-strain

Polymer thermal-expansion under ramp: strain vs temperature with
co-plotted time axis (dual-y).

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 6 rows with `temperature_c,strain_pct,time_min`.
- `plot.py` — reads CSV, dual-axis plot of strain (left) and time (right).
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
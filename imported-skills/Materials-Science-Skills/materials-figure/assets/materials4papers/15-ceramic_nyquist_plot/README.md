# 15 — Ceramic Nyquist plot

Electrochemical impedance spectroscopy (EIS) for a solid-electrolyte
ceramic sample, showing the classic Z' vs -Z'' semicircle.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 7 rows with `freq_Hz,Z_real_ohm,Z_imag_ohm`.
- `plot.py` — reads CSV, plots Nyquist curve with equal aspect.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
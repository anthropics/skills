# 18 — In-situ XRD thermal

Anatase → rutile phase transition tracked by XRD at increasing
temperatures; phase-resolved peak intensities are stacked.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 8 rows with `temperature_c,two_theta,phase,intensity`.
- `plot.py` — reads CSV, plots offset per-temperature markers by phase.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
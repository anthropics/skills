# 20 — Asphalt fracture CT reconstruction

Computed-tomography slice stack showing crack area (bar) and crack
count (line) as a function of depth for an asphalt specimen.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 6 rows with `slice_z_um,crack_area_um2,crack_count`.
- `plot.py` — reads CSV, dual-axis bar+line profile.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
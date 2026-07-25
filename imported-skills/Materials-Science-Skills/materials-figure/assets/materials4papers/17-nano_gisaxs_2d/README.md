# 17 — Nano GISAXS 2D pattern

Grazing-incidence small-angle X-ray scattering (GISAXS) intensity in
the qy-qz plane, used to characterize nanoparticle ordering.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 8 rows with `qy_inv_nm,qz_inv_nm,intensity`.
- `plot.py` — reads CSV, scatters points with viridis color mapping.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
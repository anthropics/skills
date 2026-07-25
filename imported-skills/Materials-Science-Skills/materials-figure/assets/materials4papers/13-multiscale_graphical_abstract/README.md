# 13 — Multiscale graphical abstract

Hierarchical architecture diagram (atom → nano → micro → macro) for a
hierarchical materials design figure (e.g., a gold-based aerogel catalyst).

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 4 rows with `level,label,size_label,value`.
- `plot.py` — reads CSV, draws four labeled circles with size hints.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
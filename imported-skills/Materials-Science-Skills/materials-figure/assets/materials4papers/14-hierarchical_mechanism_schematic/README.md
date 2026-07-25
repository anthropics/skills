# 14 — Hierarchical mechanism schematic

Step-by-step mechanism tree (bitumen → epoxy → IPN → performance) for a
WER-EA review figure.

## Run

```powershell
python plot.py
```

## Files

- `data/synthetic.csv` — 4 rows with `step,label,parent`.
- `plot.py` — reads CSV, draws a left-to-right arrow chain of steps.
- `figures/` - generated locally when `plot.py` is run; image outputs are not tracked in the public package.`n
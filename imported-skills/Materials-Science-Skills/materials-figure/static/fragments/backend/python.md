# Backend: Python (matplotlib / seaborn)

**Python-only execution rule.** When the user has selected Python, do all figure drawing, previewing, exporting, and visual QA in Python. Do not call any other plotting backend or language to create a temporary preview, fallback export, or layout approximation. If Python or required Python plotting packages are missing, stop before rendering and report the missing dependency. You may still write the Python script, provide `pip`/environment install commands, or ask permission to install dependencies, but do not cross-render the figure in another language.

## Python quick-start

```python
import matplotlib as mpl
import matplotlib.pyplot as plt

mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Arial", "Helvetica", "DejaVu Sans", "sans-serif"],
    "svg.fonttype": "none",     # editable text in SVG
    "pdf.fonttype": 42,         # editable TrueType text in PDF
    "font.size": 7,             # use 15-24 only for large slide-sized panels
    "axes.spines.right": False,
    "axes.spines.top": False,
    "axes.linewidth": 0.8,
    "legend.frameon": False,
})

def save_pub_py(fig, filename, dpi=600):
    fig.savefig(f"{filename}.svg", bbox_inches="tight")
    fig.savefig(f"{filename}.pdf", bbox_inches="tight")
    fig.savefig(f"{filename}.tiff", dpi=dpi, bbox_inches="tight")
```

Use `text.usetex = True` only when LaTeX is installed and math-rich labels are required.

## Materials science patterns

Python is recommended for:

- bonding strength bars with raw points or error bars
- dosage-performance curves
- DSR/MSCR/BBR trend panels
- FTIR/XRD/TG overlays
- SEM/fluorescence image plates with annotation overlays
- review evidence heatmaps
- mechanism maps generated from table-system rows

## Going deeper

- `references/characterization-figures.md` — XRD/FTIR/TG/SEM plotting patterns
- `references/performance-figures.md` — strength/bonding/viscosity curves
- `references/mechanism-figures.md` — mechanism schematics and interface figures
- `references/figure-package-protocol.md` — complete figure package assembly
- `references/figure-qa-contract.md` — font, legend, units, resolution checks
- `references/figure-production-spec.md` — export DPI, TIFF/EPS/PDF, final size
- `references/tutorials.md` — end-to-end walkthroughs
- `references/materials-figure-atlas.md` — fixed materials figure archetypes

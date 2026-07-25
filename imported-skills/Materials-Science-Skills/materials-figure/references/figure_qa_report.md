# Figure QA Report

Use this report before returning a materials figure package.

## Required checks

| Check | Pass criterion |
|---|---|
| font | Uses a journal-safe sans serif or configured journal font |
| font size | Final-size text remains at least 7 pt equivalent |
| legend | Legend entries match plotted groups and do not cover data |
| units | Every quantitative axis, scale bar, or color bar includes units |
| resolution | PNG/TIFF export is at least 300 dpi for raster use |
| SVG text | SVG text remains editable; matplotlib uses `svg.fonttype='none'` |
| panel labels | Panel labels follow A-F order and remain visible |
| caption boundary | Panel claims do not exceed evidence in the storyboard |
| source data | Every plotted panel has source data or a documented synthetic/demo source |

## Output pattern

```text
Status: pass / needs revision
Figure: [path]
Checked by: materials-figure

Issues:
- [panel/check] [problem] -> [required fix]
```

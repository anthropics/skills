# Style Presets

`--style X` expands to a palette + rendering combination. Users can override either dimension.

| --style | Palette | Rendering |
|---------|---------|-----------|
| `elegant` | `elegant` | `hand-drawn` |
| `blueprint` | `cool` | `digital` |
| `chalkboard` | `dark` | `chalk` |
| `dark-atmospheric` | `dark` | `digital` |
| `editorial-infographic` | `cool` | `digital` |
| `fantasy-animation` | `pastel` | `painterly` |
| `flat-doodle` | `pastel` | `flat-vector` |
| `intuition-machine` | `retro` | `digital` |
| `minimal` | `mono` | `flat-vector` |
| `nature` | `earth` | `hand-drawn` |
| `notion` | `mono` | `digital` |
| `pixel-art` | `vivid` | `pixel` |
| `playful` | `pastel` | `hand-drawn` |
| `retro` | `retro` | `digital` |
| `sketch-notes` | `warm` | `hand-drawn` |
| `vector-illustration` | `retro` | `flat-vector` |
| `vintage` | `retro` | `hand-drawn` |
| `warm` | `warm` | `hand-drawn` |
| `warm-flat` | `warm` | `flat-vector` |
| `hand-drawn-edu` | `macaron` | `hand-drawn` |
| `watercolor` | `earth` | `painterly` |
| `poster-art` | `retro` | `screen-print` |
| `mondo` | `mono` | `screen-print` |
| `art-deco` | `elegant` | `screen-print` |
| `propaganda` | `vivid` | `screen-print` |
| `cinematic` | `duotone` | `screen-print` |

## Override Examples

- `--style blueprint --rendering hand-drawn` = cool palette with hand-drawn rendering
- `--style elegant --palette warm` = warm palette with hand-drawn rendering

Explicit `--palette`/`--rendering` flags always override preset values.

# Media Rules

## 1. Figure and table extraction (Step 1)
- If a PDF is available (download it for arXiv, otherwise the user's attachment), use the `pdf-reading` skill to extract embedded images and rasterize-and-crop the relevant pages.
- Save as `figures/{paper}_fig{n}.png`, `figures/{paper}_tab{n}.png` (n is the paper's original number).
- Flag low-resolution ones → candidates for SVG reconstruction in Step 4.
- Also extract table values as text (for chart reconstruction). Prefer **rebuilding tables as markdown tables** over images so they stay editable.
- Leave captions out of the crop (they duplicate the slide caption). Confirm the figure number in the paper body and use that number in the file name.
- **Project-page videos**: if the page is on GitHub Pages (`xxx.github.io/proj`), `git clone --depth 1` the repository (`owner/proj` or `owner/owner.github.io`) and take the mp4s directly from `static/videos/`, `public/videos/` etc. (clone often works even when WebFetch and raw URLs are blocked). If only YouTube exists, use a placeholder box. Save fetched videos as `figures/{paper}_{scene}.mp4` + first frame `_poster.jpg`.

## 2. Placement principles (Step 4)
- **Paper material first**: put figures, tables, data, and **reproduction results you ran yourself** on the slides. Minimize text-only slides. Code excerpts do not go in the main body.
- **External videos and photos only when needed**: real-world operation, field context, usage screens — things the paper alone cannot convey.
- A source caption under every media item (e.g. `Fig. 3, Kumar et al. 2021`).

## 3. Per-slide guide
| Slot | What to put | Source |
|---|---|---|
| Background | Photo or short video of the application site/subject | External |
| Problem (single) | Teaser figure (usually Fig. 1) | Paper |
| Landscape (bundle) | Timeline diagram of how the papers relate | Self-made (SVG) |
| Method / per-paper a | Architecture or pipeline figure | Paper. SVG reconstruction if low resolution |
| Implementation / per-paper b | **Reproduction/implementation results** — reproduction plot, numeric table (reproduced vs paper), run video. A Repro box if it could not be run | `reproduction.md` |
| Experiments / per-paper c | Result tables and charts (if complex, rebuild a chart of only the key numbers) | Paper |
| Demo (single 6-2 / per-paper d) | Real operation or demo video — if available, 2 videos (before/after) side by side, one `▶ label` line under each | Project page, external |
| Comparison (bundle) | Comparison table + shared-benchmark chart | paper-compare output |
| Limitations | Failure-case figures, ablations | Paper |
| Relevance (single) | Diagram connecting to the talk context | Self-made (SVG) |
| Summary (bundle) | One-line-per-paper summary table or evolution diagram | Self-made |

If no material exists, omit that slide or replace it with text or a diagram.

## 4. Notation in PPT Text.md
- `![](figures/{paper}_fig3.png)` — an extracted figure. Use a relative-path markdown link from the same folder so it renders in Obsidian or any other editor.
- `(figure: ~)` — an SVG diagram or rebuilt chart to make yourself
- `![](figures/{paper}_repro_x.png)` — a reproduction result plot. Below it, a caption `Repro: environment · command summary · time taken`
- Code block — Appendix only, 6 lines or fewer, `Source: repo/path#Lline`
- Media not yet obtained (rendered as placeholder boxes):
  - `[[Photo n | what | source link | why it is needed]]`
  - `[[Video n | what | URL | segment mm:ss–mm:ss | why it is needed]]`
  - `[[Paper Fig n | reason extraction failed | page]]`
  - `[[Repro n | what to run | run command · required environment (GPU, simulator) · expected time | why it is needed]]`

## 5. Placeholder box rendering (Step 5)
- Draw it at the **exact position and size** the real media will occupy, so that when the user swaps the box for the real media the layout stays the same.
  - Photo: gray dashed (#888, 2px dashed)
  - Video: maroon dashed (#8C2D2D, 2px dashed) + ▶ at top left
  - Paper figure not extracted: blue dashed (#004094, 2px dashed)
  - Reproduction not done: green dashed (#2E7D32, 2px dashed) + ⚙ at top left
- 3 lines inside the box: ① what ② source (link, segment, page) ③ why it is needed
- Aspect ratio matches the final media (photo 4:3/16:9, video 16:9)

## 6. Media Sourcing Guide.md format
| Page | Paper (bundle) | Type | What | Source / segment | Why | File name to save as | Obtained |
|---|---|---|---|---|---|---|---|
| p.3 | — | Video | Real-robot walking demo | URL, 0:12–0:30 | Shows the problem intuitively | figures/RMA_demo.mp4 | [ ] |

Always specify the file name, so that the user only has to download the file and drop it into `figures/` under that name for it to link up with the manuscript and deck.

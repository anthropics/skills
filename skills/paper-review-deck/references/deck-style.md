# Deck Style

## Format and tools
- 1440×1080 (4:3) HTML deck. One run of `scripts/deck/make_deck.py "PPT Text.md" --name "{deck name}" --script "Speaker Script.md" --pptx-skill {pptx skill folder}` produces all three outputs, **HTML, PDF and PPTX** (first time only: `npm install`, pip `markdown playwright pillow pymupdf`).
  - `build.py` manuscript → HTML (KaTeX pre-rendered, fonts embedded as base64) · `mkpdf.py` HTML → PDF (videos as posters) · `measure.py` measures rendered element coordinates · `fit_notes.py` fits media aspect ratios + attaches the script as presenter notes · `gen_pptx.js` editable PPTX (text and tables editable, diagrams and equations as PNG, videos included) · `fix_ppr.py` patches pptxgenjs defects
  - Diagrams are functions in `svgs.py` in the manuscript folder (copy of `scripts/deck/svgs_template.py`), in the order the `(figure: …)` markers appear
- Images and videos are relative paths under `figures/`. The HTML must be opened from the manuscript folder, so move the folder as a whole
- Manuscript frontmatter: `deck` (file title) · `lang` (ko|en) · `author` · `org` · `footer_center` (talk context) · `date` · `font` (serif|sans) · `palette` (mono|color, default mono)

## Style constants
- **Color: text is black and white, pictures are in color** (default `palette: mono`). Titles, subtitles, bullets, emphasis, table headers, footer, self-drawn diagrams (SVG) and placeholder boxes are all black-to-gray tones (#111 / #333 / #6b7280 / lines #d4d4d4 / light gray background #f1f1f1). Emphasis is **bold** only. Paper figures, photos, videos and reproduction plots keep their original colors.
  - The color palette (primary #004094 / maroon #8C2D2D) applies only when the frontmatter says `palette: color`.
- Fonts: Korean decks Source Sans 3 (+ system Korean fonts), **English decks Noto Serif** (default, embedded in the file) / body #111 / white background
- Greek letters and math symbols in italic serif
- All bullets black (#111). No colored bullets
- The accent bar on the title and Part title slides is also dark gray (#333)
- Title slide heading font-weight 600
- Footer is a 3-way flex split: left `{presenter} · {affiliation/group}` / center `{talk context, e.g. study group name — Week N}` / right page number — filled from the Step 0 answers
- Code blocks (Appendix only): monospace, light gray background, 6 lines or fewer, only the key lines highlighted in maroon
- Reproduction plots count as "pictures", so color is allowed. If series need distinguishing, draw them with restraint: gray plus one or two colors (#004094, #8C2D2D)

## Layout
- Fill the body vertically, without excessive margins
- The same diagram on consecutive slides keeps the same size and position
- On figure slides, the figure is large and the text is secondary
- In bundle mode, per-paper slides use an identical template with the `[abbr]` tag in a fixed position

## Bundle-mode Landscape diagram (lineage timeline) — fixed format
- Use `svgs_template.lineage(nodes, axis left label, axis right label, bottom note)`. Nodes go left → right **in presentation order** (not by publication year — if it differs from the presentation order, the audience gets confused).
- Each node card has 4 lines: abbreviation (bold, primary color) / venue YYYY (mark Oral/Spotlight if any) · arXiv YYYY.MM / "what it fixes" (maroon) / one-line method.
- The axis labels are the first comparison axis (e.g. "fixes the simulator → fixes the policy"). The bottom note lists shared labs and authors.
- The talk-context mapping on the Summary slide uses `svgs_template.mapping(rows)` (rows that are new proposals get a maroon dashed outline).

## Component reuse
- If an earlier deck (`.dc.html`) exists in the save folder (or another subfolder of the same parent folder), copy and reuse its title, Part title, Outline, footer and References slides, so the look does not change from talk to talk.
- If none exists, build new ones by the rules above, and later decks use those as the baseline.

## Markdown → slide syntax (PPT Text.md)
| Syntax | Meaning |
|---|---|
| `---` | Slide break |
| `# Part N :` | Part title slide |
| `##` | Slide title (primary color) |
| `###` | Summary line under the title (light gray) |
| `**bold**` | Maroon emphasis |
| `\|\|\|` | Two columns, left and right — one line **in front of each column** (2 in total). With only one, everything becomes the left column. Content before it is full width (pre) |
| `>>` | Centered bottom emphasis (maroon accent bar, no box) |
| `(figure: ~)` | Self-made SVG |
| `![](figures/…)` | Image or video (mp4 needs a `_poster.jpg` first frame) |
| `▶ label` (directly under a video) | Video caption (bold, body color) |
| `[[Photo/Video/Paper Fig …]]` | Placeholder box for media not yet obtained (`media.md`) |
| `>` | Presenter notes |
| `$$...$$` | KaTeX equation |

The Korean forms of these markers (`(그림: …)`, `[[사진 | …]]`, `[[영상 | …]]`, `[[논문 Fig n | …]]`, `[[재현 n | …]]`, `출처:`) are still accepted by `build.py`.

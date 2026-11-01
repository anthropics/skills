---
name: paper-review-deck
description: Builds a paper review talk deck (PPT Text.md → slides → notes and script) that summarizes, critiques and compares one paper (single mode) or 2–5 papers (bundle mode); if no paper is chosen yet, finds and recommends candidates from a topic; and makes partial edits to specific pages of a deck it already built. Field-agnostic. Use whenever the request is about preparing or fixing a paper presentation, such as "paper review talk", "paper review PPT", "make slides for this paper", "find a paper to present", or "fix p.7 of the review deck".
---

# Paper Review Talk Deck (paper-review-deck)

A pipeline for building paper review talk decks in any field. The presenter's name and affiliation are collected in Step 0 and written into the manuscript frontmatter (`author`, `org`) (ask once the first time; afterwards take them from an earlier manuscript in the same folder).

## First, pick what to do

| Request | Mode | Go to |
|---|---|---|
| Build a deck for a new paper, 1 paper | Single mode | "Full flow" below |
| Build a deck for new papers, 2–5 papers | Bundle mode | "Full flow" below (6 or more: ask whether to split into two decks) |
| No paper chosen yet ("find me a paper to present on ~", only a topic given) | Paper discovery → single/bundle | `references/discovery.md` → after choosing, "Full flow" Step 1 |
| Partial edit of a deck already built ("fix p.7", "change the comparison table") | Partial edit mode | `references/partial-edit.md` |

## Reference files — read when entering that step

| File | When to read |
|---|---|
| `references/discovery.md` | When no paper is chosen yet — candidate search and recommendation |
| `references/structures.md` | Step 4 — single and bundle slide structures |
| `references/media.md` | Step 1 (figure extraction, project-page videos), Step 4 (media placement), Step 5 (placeholder boxes) |
| `references/reproduction.md` | Step 3-R — producing reproduction/implementation results from public code |
| `references/deck-style.md` | Step 4 markdown syntax, Step 5 deck style |
| `references/script.md` | Step 6 script writing |
| `references/partial-edit.md` | Partial edit mode |
| `scripts/render_check.py` | Step 5 visual QA (`--static --sheet 6`) |
| `scripts/deck/` | Step 5 deck build tools (make_deck.py produces HTML, PDF and PPTX in one go) |

## Where to save

Put all outputs together in the single **save folder** collected in Step 0. Image links are relative paths, so if the manuscript and `figures/` are separated, images break no matter where the file is opened.

```
{save folder}/
├─ PPT Text.md            ← source (single source of truth)
├─ Presenter Notes.md
├─ Speaker Script.md
├─ Media Sourcing Guide.md
├─ Reproduction Notes.md   ← Step 3-R environment, commands, results vs paper values
├─ QA Report.md            ← Step 5 visual QA results
├─ {paper} litnote.md      (one per paper)
├─ {paper} numbers.md      (one per paper — every number cited on slides + page/table numbers)
├─ {deck name}.html        ← for presenting (plays video)
├─ {deck name}.pdf         ← for distribution/printing (videos become poster frames)
├─ {deck name}.pptx        ← for editing (text and tables editable, videos included)
├─ figures/
│  ├─ {paper}_fig3.png etc.
│  └─ {paper}_repro_{name}.png   ← reproduction result plots
└─ reproduction/{paper}/   ← reproduction scripts and logs (only results go in the deck)
```

- Image file names are `{paper}_fig{n}.png`, `{paper}_tab{n}.png`. Make sure they do not collide with files in other weeks' folders.
- If no folder is connected, zip the same structure and deliver it with SendUserFile, and add one line saying that connecting a folder via "Add folder" in the Claude desktop app lets it be saved directly.

## Full flow

| Step | MCP | Skill | Output |
|---|---|---|---|
| 0. Opening questions | — | — | Paper, talk context, save folder, reference links confirmed |
| 1. Get the paper | alphaXiv | pdf-reading | Full text + figures/tables + reference material |
| 2. Summarize | alphaXiv | research-litnote | One litnote per paper |
| 3. Critique and compare | alphaXiv (GitHub) | paper-critique / paper-compare | Critique points, comparison table |
| 3-R. Reproduce and implement | alphaXiv (GitHub), remote-devices | — | Reproduction plots, logs, demos, Reproduction Notes |
| 4. Manuscript | — | — | PPT Text.md |
| 5. Slides + visual QA | remote-devices | pptx | All three of .html / .pdf / .pptx, QA Report |
| 6. Companion documents | remote-devices | — | Presenter Notes, Speaker Script, Media Sourcing Guide |

The user is consulted only twice: at **Step 0** and **after Step 4 is complete**. Between those, proceed without asking.

---

## Step 0. Opening questions (one message; do not re-ask what was already given)
Ask the 7 items below as a **numbered list in a single message**. For items already known from the conversation, memory or the folder, only confirm: "I have this as ~, is that right?"

1. **Paper** — arXiv link, ID, title or PDF (several allowed). If none yet, ask for topic, constraints and anchor paper, and find candidates with `references/discovery.md`
   - When discovering, also ask "whether to save the chosen paper to the alphaXiv library"
2. **Talk context** — where (study group week N, lab seminar, class), audience background, talk length (minutes)
3. **Save folder** — if folders are connected, show the list and let the user choose
4. **Reference links (optional)** — project page, demo video, GitHub, author blog or explainer, meeting announcement. "None" means proceed with the paper alone
5. **(Bundle only) Topic title and presentation order** — if not given, propose one and confirm in one line (default: by publication year)
6. **Language** — slide language / script language. Default: slides in **English**, script, notes and guide in the **presenter's language** (e.g. English slides on screen, presented in Korean). When slides are in English, the page titles in the script stay as the English titles, and each English phrase on screen is read aloud once inside the presenter-language sentence
7. **Reproduction scope and compute environment** — public code is actually run and the results go in the deck. Full reproduction / checkpoint evaluation / toy implementation of the core algorithm / none (box). Whether a GPU is available, whether the user's PC is connected. If no answer, use the highest rung of the ladder in `references/reproduction.md` that the environment allows

Outputs are always the three formats HTML, PDF and PPTX, so do not ask.

Reference links are read with WebFetch in Step 1 (for GitHub, prefer alphaXiv `read_files_from_github_repository`); if one cannot be opened, say which link in one line.

## Step 1. Get the paper (per paper)
- arXiv: alphaXiv `get_paper_content`. If only the title is given, search alphaXiv and confirm in one line.
- If the user has an alphaXiv library or highlights, consult `list_library` and `get_paper_notes` as well.
- Non-arXiv papers: the attached PDF via `pdf-reading`.
- Figure and table extraction rules are in `references/media.md`.
- In a bundle of 3 or more papers, retrieval and summarization may be done in parallel per paper.
- **Verify venue labels**: check the venue name and Oral/Spotlight status in the arXiv page's Comments, the GitHub README and the project page, and use exactly that on the title slide and the lineage. If unverified, write "arXiv (venue TBD)".

## Step 2. Summarize
- Call the `research-litnote` skill for each paper. Do not redefine the note format in this skill — so that improvements to the source skill carry over automatically.
- For detail checks, use alphaXiv `answer_pdf_queries`.
- Separately from the litnote, create `{paper} numbers.md`: every number to be cited on slides, with page, table and figure numbers. Where the body text and a table disagree (a range in the abstract, "up to n%" in the conclusion), mark it as "mismatch" and use only the raw table value on slides.

## Step 3. Critique and compare
- **Single**: `paper-critique`. If a comparison paper was given, add `paper-compare`.
- **Bundle**: always build the comparison table with `paper-compare`; per-paper `paper-critique` covers only the 2–3 key limitations.
  - Default comparison axes: problem setting / core method / data and experimental setup / evaluation metrics / main results / limitations / code availability
  - Lineage between papers (who cites or improves on whom)
- Add 2–3 **field-specific checks** and reflect them in the comparison axes too. Examples:
  - Robotics: sim-to-real gap, scale and reproducibility of real-robot experiments
  - ML/LLM: baseline fairness, data leakage, compute cost
  - Construction and engineering applications: field applicability, data acquisition cost, compliance with codes and standards
- Code itself does not go on slides. Implementation is shown as **results from running it** → Step 3-R.

## Step 3-R. Reproduce and implement (`references/reproduction.md`)
- Actually run the official code (or a scaled-down implementation of the core algorithm) and produce **results** (plots, numeric tables, run videos). What goes on slides is the result, not the code. Code excerpts go in the Appendix only, and only when needed.
- Following the reproduction scope and compute environment from Step 0, pick the feasible rung of the ladder (full reproduction → checkpoint evaluation → toy implementation → box), and step down one rung on failure. Record which rung was applied to each paper in `Reproduction Notes.md`.
- Reproduced values must always be placed **side by side** with the paper's values in a table (reproduced / paper / difference and reason).
- Anything that could not be run is left as a `[[Repro n | what | run command and required environment | why]]` box so the user can run it on their own PC.

## Step 4. Manuscript (PPT Text.md)
- Read `references/structures.md` (structure), `references/media.md` (media) and `references/deck-style.md` (markdown syntax), then write.
- When complete, ask the user to review. Show alongside it:
  - The slide list (page numbers and titles) and the expected page count
  - Media checklist — obtained / left as placeholder boxes
  - Reproduction checklist — reproduction rung per paper (full/eval/toy/box) and result files
- Once approved, Step 5.

## Step 5. Slides + visual QA
1. Build the deck by the rules in `references/deck-style.md` — `scripts/deck/make_deck.py` produces HTML, PDF and PPTX from the manuscript. Diagrams go in `svgs.py` in the manuscript folder. If an earlier deck's `svgs.py` and frontmatter exist in the save folder (or the same parent folder), take them over to keep the look consistent.
2. Outputs are always **all three: HTML, PDF and PPTX**. The PDF is the HTML printed via Playwright (videos replaced by poster frames). The PPTX is built with the `pptx` skill — measuring element coordinates in the rendered HTML so text and tables stay editable, diagrams and equations as PNG, videos inserted with poster covers, and the script as presenter notes. Placeholder boxes are kept as dashed shapes with text.
3. **Visual QA** — always do this before handing over to the user. If you only build and hand over, text overflow and overlaps go straight into the talk.
   - Run `python scripts/render_check.py {deck}.html --static --sheet 6 --out check/` → per-page screenshots + issue list (JSON) + contact sheets of 6 pages each. `--static` unfolds a one-slide-at-a-time deck for inspection (without it, every page from the 2nd is blank). Open the sheet and look at it — opening pages one at a time misses alignment differences between consecutive slides.
   - Open the screenshots and check by eye in addition to the script output. Things the script cannot catch: figures too small, misalignment, the same diagram shifting position across consecutive slides, overuse of accent color, broken equations.
   - Fix the issues and run again. Repeat **at most 3 times**, and record remaining issues in `QA Report.md`.
   - `QA Report.md`: per-page result (pass / fixed / remaining issue and reason), kept short.
   - If a PPTX was built, QA it the same way using the rendering method from the `pptx` skill.

## Step 6. Sync the companion documents
- `PPT Text.md` is the source; the rest are derived:
  - `Presenter Notes.md` — per-page key messages in bullet form
  - `Speaker Script.md` — rules in `references/script.md`
  - `Media Sourcing Guide.md` — format in `references/media.md`
  - `Reproduction Notes.md` — format in `references/reproduction.md`
- When the source changes, **always** update the three derived documents and the deck together. Fixing only one leaves the script's page numbers out of step with the deck, which is confusing mid-talk.
- Before saving, re-read the latest versions in the folder to check for edits the user made by hand, and build on top of them if there are any.

## Final report
Only, briefly: the save folder path, the list of generated files, the reproduction rung per paper, the number of remaining placeholder boxes, the number of issues left after QA, and the script's total estimated time. Do not re-summarize the process.

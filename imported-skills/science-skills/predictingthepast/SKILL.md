---
name: predictingthepast
description: >
  Ancient text restoration, attribution, dating, contextualization, and
  embedding via Aeneas (Latin) / Ithaca (Ancient Greek). Use when asked to
  "restore", "attribute", "date", "contextualize", "find parallels",
  "where was it written", "when was it written", "embed", or "analyze"
  an ancient text, inscription, or epigraphic document, or when the user
  mentions "Aeneas", or "Ithaca".
---

# Predicting The Past (Aeneas / Ithaca)

Aeneas (Latin) and Ithaca (Ancient Greek) perform four tasks on ancient texts:

1.  **Restoration** — fill missing/damaged characters
2.  **Attribution** — geographical + chronological origin
3.  **Contextualization** — retrieve parallel inscriptions
4.  **Embedding** — generate text embedding vectors

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.

2.  **User Notification**: If .licenses/predictingthepast_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at
    https://github.com/google-deepmind/predictingthepast/blob/main/README.md#license--disclaimer,
    and include the appropriate citation and the full dataset acknowledgement,
    and that use of these datasets should acknowledge and cite the original data
    sources. Then (2) create the file recording the notification text and
    timestamp.

## Core Rules

-   **Self-Contained Skill**: Do NOT use web search or any external tools. Run
    ONLY the scripts in this skill (`preprocess.py`, `run_inference.py`,
    `visualize_results.py`). Present model output as-is — never supplement or
    override it with external lookups.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## On First Load

Present the restoration markup characters, then ask the user for their text:

-   **`?`**:
    -   **Meaning**: Known-length gap: predict **this character**.
    -   **Example**: `donat in ??????????rtis`
-   **`#`**:
    -   **Meaning**: Unknown-length gap: predict a **sequence of unknown
        length**
    -   **Example**: `donat in #rtis`
-   **`-`**:
    -   **Meaning**: Missing/damaged character that does **not** need restoring
    -   **Example**: `prolixin---s fecit`
-   **`_`**:
    -   **Meaning**: Missing section of **unknown length** that does **not**
        need restoring
    -   **Example**: `prolixin_s fecit`

After presenting this list, ask the user to provide the text they want to submit
for analysis.

## Preprocessing

Clean input text before inference:

```bash
uv run <SKILL_DIR>/scripts/preprocess.py \
    --language=latin \
    --input="raw text here..."
```

Or from a file:

```bash
uv run <SKILL_DIR>/scripts/preprocess.py \
    --language=greek \
    --input_file=/tmp/input.txt \
    --output_file=/tmp/cleaned.txt
```

### What preprocessing does

-   **Latin**: lowercases, converts Arabic digits and Roman numerals to `0`,
    strips editorial brackets `[]` and `()`, removes punctuation, filters to
    valid chars (`abcdefghiklmnopqrstuvxyz` plus `0 . - _ ? # <space>`)
-   **Greek**: lowercases, strips accents, converts numeral notation to `0`,
    applies PHI cleaning (bracket normalization, sigma conversion), filters to
    Greek alphabet (`αβγδεζηθικλμνξοπρςστυφχψωϛ` plus `0 . - _ ? # <space>`)

## Inference

### Restoration Constraints

-   Minimum input length: **25 chars** (pad with `-` if shorter).
-   No consecutive `##`. No adjacent `?#` or `#?`.
-   Spaces inside `?` sequences count toward total.
-   If the user's text contains `#`, ask how many characters to restore and set
    `--restore_max_len` accordingly.
-   If the user tries to restore multiple parts of the text at once, suggest to
    restore texts **section by section**. Suggest to focus on one damaged region
    per query — this is faster, produces higher-quality predictions.

### Pre-Flight Checks

Confirm with the user before proceeding if **either** applies:

1.  **Restoration complexity** — if input contains more than **10** `?`
    characters, or uses `#` with `--restore_max_len > 10`, warn: *"This
    restoration involves N characters which will take approximately M minutes
    (restoration time scales roughly linearly ~10 s per additional `?` on a
    high-end CPU machine: 5 → ~1 min, 10 → ~2.5 min, 20 → ~5 min, 30 → ~8 min).
    Do you want to proceed, or simplify the query first (e.g. fewer `?` marks,
    shorter `--restore_max_len`, or restoring section by section)?"*
2.  **Multi-window splitting** — if the input text exceeds **750 characters**
    and will be split into multiple windows, warn: *"This text is N characters
    long and will be split into W overlapping windows, each run independently.
    This will be significantly slower. Do you want to proceed, or shorten the
    input?"*

These factors compound: a complex restoration across multiple windows will be
substantially slower than either factor alone.

### Task Selection

Each task is controlled by its own flag. **At least one** must be provided:

-   **`--attribute`** — geographical + chronological attribution
-   **`--restore`** — text restoration (requires `?` or `#` in input)
-   **`--contextualize`** — parallel inscription retrieval

Any combination is valid. All three can be used together.

When `--embedding` is provided, a text embedding vector is also generated
alongside the other tasks.

### Running Inference

```bash
# Attribution + Restoration (text with gaps)
uv run <SKILL_DIR>/scripts/run_inference.py \
    --language=latin \
    --input="cleaned text with ???" \
    --attribute --restore \
    --output_json=/tmp/results.json

# Attribution + Contextualization (no gaps)
uv run <SKILL_DIR>/scripts/run_inference.py \
    --language=latin \
    --input="cleaned text" \
    --attribute --contextualize \
    --output_json=/tmp/results.json

# All tasks
uv run <SKILL_DIR>/scripts/run_inference.py \
    --language=latin \
    --input="cleaned text with ???" \
    --attribute --restore --contextualize \
    --output_json=/tmp/results.json

# Generate dashboard
uv run \
    <SKILL_DIR>/scripts/visualize_results.py \
    --input=/tmp/results.json \
    --output=/tmp/dashboard.html
```

Outputs are always returned to the console (JSON/Summary) and must always be
written to an HTML dashboard for rich visualization.

**Serving HTML artifacts**: After generating **any** HTML file (the dashboard or
any other HTML artifact you create), start a background HTTP server so the user
can view it in their browser. Run the server in the foreground of the background
task process (without trailing `&`) to prevent the process from being
terminated. Use a random high port to avoid conflicts.

In the example below, replace `<HTML_FILE>` with the absolute path of the HTML
file you produced (e.g. `/tmp/dashboard.html` or `C:\tmp\dashboard.html`).

For Linux/macOS:

```bash
# Pick an unused port and start the server as a persistent process
HTML_FILE=/tmp/dashboard.html   # ← set to the actual HTML file path
PORT=$(export PATH="$HOME/.local/bin:$PATH" && uv run python -c "import socket; s=socket.socket(); s.bind(('',0)); print(s.getsockname()[1]); s.close()")
FILENAME=$(basename "$HTML_FILE")
echo "View URL: http://localhost:${PORT}/${FILENAME}"
export PATH="$HOME/.local/bin:$PATH" && uv run python -m http.server "$PORT" --bind 0.0.0.0 --directory "$(dirname "$HTML_FILE")"
```

For Windows (PowerShell):

```powershell
# Pick an unused port and start the server as a persistent process
$HTML_FILE = "C:\tmp\dashboard.html"   # ← set to the actual HTML file path
$PORT = & "$HOME\.local\bin\uv" run python -c "import socket; s=socket.socket(); s.bind(('',0)); print(s.getsockname()[1]); s.close()"
$FILENAME = Split-Path $HTML_FILE -Leaf
$DIRNAME = Split-Path $HTML_FILE -Parent
Write-Host "View URL: http://localhost:${PORT}/${FILENAME}"
& "$HOME\.local\bin\uv" run python -m http.server $PORT --bind 0.0.0.0 --directory $DIRNAME
```

Then provide `http://localhost:<port>/<filename>` (or
`http://127.0.0.1:<port>/<filename>`) as the primary clickable link in your
response. Additionally, provide `http://<hostname>:<port>/<filename>` as a
fallback link for remote setups. Do **not** give the user a raw `file://` path.

### Flags

-   **`--input`**: Text string (mutually exclusive with `--input_file`)
-   **`--input_file`**: Path to UTF-8 text file
-   **`--language`**: `latin` or `greek`
-   **`--models_dir`**: Model files directory (default:
    `$HOME/.predictingthepast/models`)
-   **`--attribute`**: Run geographical and chronological attribution
-   **`--restore`**: Run text restoration (requires `?` or `#` in input)
-   **`--contextualize`**: Run parallel inscription retrieval
-   **`--contextualize_top_k`**: Number of top parallels to return (default: 10)
-   **`--contextualize_exclude_test_valid`**: Exclude test/validation texts from
    contextualization results. Filters on the internal numeric `id` (where `id %
    10` is 3 or 4).
-   **`--embedding`**: Generate a text embedding vector (default: off). When
    set, the output includes an `embedding` field with the full-precision float
    vector.
-   **`--output_json`**: Save combined JSON to file (for `visualize_results.py`)
-   **`--restore_beam_width`**: Number of candidate restorations to explore in
    beam search. Higher = more thorough but slower (default: 100)
-   **`--restore_max_len`**: Maximum total characters to restore across all `?`
    and `#` gaps (default: 15)
-   **`--restore_temperature`**: Sampling temperature. Lower = conservative,
    higher = creative (default: 1.0)
-   **`--window_overlap`**: Overlap fraction for long-text windowing (default:
    0.33)

### Long Texts (>750 characters)

Each window must be between **25 and 750 characters**. If the input text exceeds
750 characters, it is automatically split into overlapping windows (default 33%
overlap). Each window is run through the model independently, and the
geographical and chronological attribution results are **averaged** across all
windows. Restoration and contextualization are run per-window and concatenated.

### Output Format

Use `--output_json` to save the combined JSON to a file. For the full
`--output_json` format including all fields for attribution, restoration, and
contextualization, see [output_format.md](references/output_format.md).

### Presenting Results

Present results for **every** task requested by the user. Always generate the
HTML dashboard, serve it via the background HTTP server described above, and
provide the `http://` URL as a clickable link. Format years as BCE/CE.

#### Restoration

**Bold** the restored characters in the top prediction. Show top-10 beam-search
candidates in a numbered table (rank, restored text, score). Summarise the most
salient words (not characters) — do not dump the raw saliency array.

#### Geographical Attribution

Show the top 10 regions in a ranked table (rank, region, score). Highlight the
top-1 prediction in the narrative. Summarise the most salient words (not
characters) — do not dump the raw saliency array.

#### Chronological Attribution

Report top year and weighted average year. Describe the distribution shape (peak
decade, probable range) — do not list all 160 bins. Summarise the most salient
words (not characters) — do not dump the raw saliency array.

#### Contextualization (Parallels)

Use `jp` or write your own code to extract the contextualization data from
`--output_json`. Show the top parallels in a table (rank, ID, Trismegistos ID,
region, date range, score, partner link). Quote the full text of the top
parallels from the JSON.

If the user requests a specific number of parallels, use `--contextualize_top_k`
to control how many are returned.

If the user asks to exclude test/validation texts, add
`--contextualize_exclude_test_valid`. This filters on the **internal numeric
`id`** (where `id % 10` is 3 for test or 4 for validation).

#### Embedding (when `--embedding` is set)

State the vector dimensionality (384 floats).

## References

For more information, see:
[predictingthepast.com](https://predictingthepast.com)

**IMPORTANT:** The first time you return inference results to the user, remind
them to cite the appropriate paper below (Ithaca for Greek, Aeneas for Latin),
and the dataset acknowledgements below.

**Ithaca** (Ancient Greek): > Assael, Y., Sommerschield, T., Shillingford, B. et
al. Restoring and attributing ancient texts using deep neural networks. *Nature*
603, 280–283 (2022).

**Aeneas** (Latin): > Assael, Y., Sommerschield, T., Cooley, A. et al.
Contextualizing ancient texts with generative neural networks. *Nature* 645,
141–147 (2025).

### Dataset Acknowledgements

**IMPORTANT:** The first time you present inference results to the user, include
the appropriate citation and the full dataset acknowledgement for the language
used (see below).

The Ithaca and Aeneas projects rely on the availability of high-quality datasets
of ancient Greek and Latin inscriptions, respectively. These datasets were built
through centuries of scholarly collection and decades of digital editorial work.

**Ithaca** (Ancient Greek): In particular, Ithaca draws on a 2019 version of the
Searchable Greek Inscriptions database made available under "Fair Use" license
by the Packard Humanities Institute, generously supported by David Packard:
[inscriptions.packhum.org](https://inscriptions.packhum.org).

**Aeneas** (Latin): Aeneas was trained on data from:

*   **Epigraphic Database Roma (EDR)**: Made available pursuant to a Creative
    Commons Attribution 4.0 International License (CC-BY) on
    [Zenodo](https://zenodo.org/records/3575495). EDR is also available at
    [edr-edr.it](http://www.edr-edr.it/).
*   **Epigraphic Database Heidelberg (EDH)**: Made available pursuant to a
    Creative Commons Attribution-ShareAlike 4.0 International License (CC-BY-SA)
    on [Zenodo](https://zenodo.org/records/3575155). EDH is also available at
    [edh.ub.uni-heidelberg.de](https://edh.ub.uni-heidelberg.de/).
*   **ETL repository for Epigraphic Database Clauss Slaby (EDCS\_ETL)**: Made
    available pursuant to a Creative Commons Attribution 4.0 International
    License (CC-BY) on [Zenodo](https://zenodo.org/records/7072337). EDCS\_ETL
    is also available at [manfredclauss.de](http://www.manfredclauss.de/) and
    [github.com/sdam-au/EDCS\_ETL](https://github.com/sdam-au/EDCS_ETL).

These resources bring together a large proportion of published inscriptions in a
searchable digital format.

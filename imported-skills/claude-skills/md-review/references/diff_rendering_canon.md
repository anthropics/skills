# Diff Rendering Canon

**Why this exists:** The `md-review` converter renders unified diffs into a two-column HTML layout. Diff rendering has 50 years of UI history; this document records the conventions it inherits from and where it diverges.

## The convention

Unified-diff format (the `--- a/file`, `+++ b/file`, `@@ -10,7 +10,8 @@` shape) is the lingua franca every modern code-review tool reads:

- `+` (green tint): line added in the new version
- `-` (red tint): line removed from the old version
- ` ` (no tint): unchanged context line
- `@@ -old_start,old_count +new_start,new_count @@ optional_context`: hunk header
- `\ No newline at end of file`: meta line (rendered italic, no color)

`md-review` honors this exactly. The renderer assigns per-line numbers on both the old side (`lo`) and the new side (`ln`), with a clear visual separation by border.

## Color discipline

WCAG 1.4.1 (Use of Color) requires that color must not be the *sole* signal. Our diff rendering uses:
- **Tint backgrounds** (`color-mix(in srgb, var(--md-success) 15%, transparent)` for additions; `color-mix(... --md-warn 12% ...)` for deletions) — derived from the design-system palette, so they automatically follow the user's brand and stay within WCAG-validated contrast on the user's chosen bg.
- **Mark column** (`+` / `−` / ` `) — visible character, redundant with the color, screen-reader-skipped via `aria-hidden="true"`.
- **Line numbers in both columns** — provides spatial grounding independent of color.

Result: a deuteranopic reader (red-green color blindness) still distinguishes additions from deletions via the mark column and line-number columns.

## What we deliberately don't do

- **Syntax highlighting inside diffs** — Prism.js doesn't track per-line edits well, and conflicting addition/deletion backgrounds + token colors produce noisy output. Plain monospace is more legible. (Engineers reviewing diffs spend most attention on the change itself, not the surrounding language.)
- **Word-level diffing** — `difftastic`-style intra-line highlighting is great for tiny edits but ambiguous for refactors. We render whole lines and let the reader compare them visually.
- **Inline-reply threading** — md-review is a generator (markdown → HTML); it produces an artifact, not a thread. For threaded discussion, use the host platform (GitHub PR comments, GitLab discussions).
- **Split-pane (old | new) view** — the convention this converter targets is the *unified* diff (sequential, single column), because that's what gets pasted into markdown review notes. Split-pane is a tool for active reviewing in an IDE.

## Sources

### 1. POSIX `diff -u` (Single Unix Specification, c. 1990)
The format spec. The `@@ -A,B +C,D @@` hunk header, the `+`/`-`/` ` prefixes, the `--- a/` / `+++ b/` file headers — all defined here. Every tool that follows reads the same shape.

### 2. GitHub PR diff view
The reference UI for two decades. Established:
- Per-line line numbers on both old and new sides
- Tinted backgrounds for additions/deletions
- File-header sticky bar
- Hunk separator with grey background
We mirror the convention; we don't reinvent it.

### 3. GitLab MR diff view
Same convention as GitHub, with one small refinement: the per-hunk `@@` header context (the function name after the `@@`) is rendered as a sticky element so the reader knows what function they're in. We render this header context in the hunk-head bar.

### 4. `difftastic` — semantic diff tool (github.com/Wilfred/difftastic)
Argues for AST-aware intra-line diffing instead of line-based. We acknowledge the case but rejected it for two reasons: (1) parsing every language is out of scope; (2) most agent-generated review markdown contains a few short hunks, where intra-line diff adds noise more than signal.

### 5. *Software Engineering at Google* — Tom Manshreck & Hyrum Wright (O'Reilly, 2020), Ch. 9 "Code Review"
The discipline around how diffs get read. Three claims used here:
- "Reviewers spend most of their attention on a few hunks, not all of them" → jump-nav at top is essential
- "Comments must reference a specific line" → annotations are attached to hunks, not free-floating
- "Approval should be explicit and recorded" → `LGTM` markers are surfaced as the approval bar

### 6. Google *Code Review Developer Guide* (google.github.io/eng-practices/review/reviewer)
The taxonomy of severity (blocker, must-fix, nice-to-have, nit) maps to our default BLOCKER / MAJOR / MINOR / NIT convention. The phrase "nit:" specifically is from Google's recommended review vocabulary.

### 7. GitHub Markdown — fenced code blocks with language hints (` ```diff `)
The convention this converter targets. Agent-generated review markdown wraps every diff in ` ```diff `, which becomes our extraction grammar in `diff_parser.py`.

## Applied to `md-review`

`diff_parser.py` extracts the hunks from ` ```diff ` fenced blocks. `review_html_renderer.py` lays them out in the standard unified-diff shape, with the addition/deletion coloring derived from the design-system palette so reviews look on-brand without losing the universal color convention.

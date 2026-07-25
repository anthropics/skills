# PR Annotation UX

**Why this exists:** The 2-column layout (diff on the left, annotation cards on the right) isn't arbitrary — it's the convergent UX that emerged after 15 years of PR tools experimenting with placement. This document records why we render this shape and not the alternatives.

## The shape

| Region | Content | Why |
|---|---|---|
| Top: jump-nav | Every annotation listed with severity badge + 1-line preview + jump link | Reviewers skim the findings list before reading any hunk (`SWE at Google`, ch. 9) |
| Left column: diff | Unified-diff lines with line numbers and +/− coloring | The work being reviewed; gets the bigger column |
| Right column: annotation cards | Severity badge + body text + "jump to diff" backlink | Anchored to the diff but visually distinct |
| Bottom: unanchored | Annotations not attached to any hunk | Folder-level / general comments live here |
| Footer: reviewer | "Reviewer: <name>" mandatory | A code review without a named reviewer is not a code review |

## Why 2-col and not stacked

Alternatives we considered:

1. **Inline annotations between diff lines** (the GitHub PR style). Pros: maximum proximity between annotation and code. Cons: breaks the diff's visual continuity; hard to skim the diff without re-encountering every annotation; cards force the diff to scroll.
2. **Annotations in a sidebar separate from any hunk** (Jira's review style). Pros: clean diff. Cons: the spatial relationship between annotation and code is lost; reviewer has to mentally re-anchor each annotation.
3. **2-col: diff left, annotations right, aligned to first hunk of the block.** What we do. Pros: diff stays continuous and skimmable; annotation is visible at the same scroll position as the relevant hunk; on narrow screens (< 900px), the layout collapses to stacked. Cons: when there are many annotations per block, they stack vertically beyond the hunk height — but this is the right failure mode (more findings = more space, not hidden).

## The jump-nav specifically

The top-of-page findings list is the highest-leverage element. Empirically (every tool that ships this — GitHub, GitLab, Reviewable, CodeStream — has converged on it):

- Reviewers + authors both look here first
- A 4-finding PR is easier to triage from the list than from scrolling
- The author can use the list to mentally check off as they address each finding

Each list entry has: severity badge + 80-char preview + "(#1)" target reference. Click jumps to the annotation card.

## What we deliberately don't do

- **Resolve/Unresolve workflow** — md-review generates an artifact, not a thread. Resolution belongs in the host platform.
- **Avatar / author images** — out of scope; this is a single-author review (the `--reviewer` field names them).
- **Filtering by severity** — the jump-nav lists them all; severity badges already group them visually. Filter UI would add JS complexity without much value for a typical 3-10-finding review.
- **Cross-PR comparison** — single review, single artifact.
- **Re-review threading** — same reason; artifact, not thread.

## Sources

### 1. GitHub PR review UI
The reference implementation that established expectations: per-line inline comments, severity through icon (😄 / 👍 / 🚀 reactions), file/folder tree on the left, top-level summary. Our 2-col layout is a simplification: we keep the spatial proximity but drop the inline-thread complication.

### 2. GitLab MR review UI
Similar to GitHub. Adds: sticky hunk-context header (the function name after `@@`). We render this in the hunk-head.

### 3. Reviewable.io
Argued for a more structured review process with explicit annotation state (resolved, deferred, addressed). Our artifact doesn't have state — it's a snapshot of one reviewer's findings — but the jump-nav with per-finding "(#N)" reference is borrowed from Reviewable's "comment numbering" UX.

### 4. CodeStream (now part of New Relic)
Pioneered the margin-comment pattern in IDE plugins: code in the editor, comments in a right-side panel aligned to the relevant line. The 2-col layout in md-review mirrors that pattern for a single-file artifact.

### 5. *Software Engineering at Google* (Manshreck & Wright, O'Reilly 2020), Ch. 9 "Code Review"
- "The review summary at the top is the most-read element"
- "Comments must be anchored to specific lines"
- "Approval should be explicit"

Three claims, three corresponding UI elements (jump-nav, hunk-anchored annotations, LGTM/approval bar).

### 6. *People + AI Guidebook* (Google PAIR, pair.withgoogle.com)
For AI-assisted code review specifically: the artifact should make clear who the reviewer is (the `--reviewer` field is mandatory for exactly this reason). An AI-generated review without a named human reviewer is an artifact looking for ownership; we refuse to render it.

### 7. NN/g — *Web Page Scanning Patterns* (Jakob Nielsen, 2006, updated 2024)
The F-shape reading pattern: users fixate on the top + left edges first. Our jump-nav (top) + diff (left column) + annotation (right column) honors this — the reader sees what's most important first.

## Applied to `md-review`

`review_html_renderer.py` emits the jump-nav at top, the 2-col `.hunk-row` for each diff block, and the mandatory reviewer footer. It refuses to render without `--reviewer` (rule 1) and refuses to render without any hunks (rule 2 — wrong skill, route to md-document). Resolution / threading / cross-PR comparison are out of scope.

# Publisher abstract word-count contract (Stage 5 D4 anchor)

Target journal: Journal of Synthetic QA Studies (synthetic).

Hard cap: 250 words (whitespace-split count, per
`shared/references/word_count_conventions.md` 3-5% buffer rule the working
window is 237-242 words).

Counting algorithm: whitespace-split tokens. Hyphenated compounds (e.g.,
"outcome-based") count as ONE token under regex hyphenated-as-1 — that is
the wrong algorithm. Whitespace-split MUST be used.

# Word Count Conventions

**Spec:** v3.6.7 §7.1 — pattern protection reference for `report_compiler_agent` (abstract-only mode).

**Audience:** Agents budgeting word counts under a hard cap (abstract, executive summary, INSIGHT block). Human authors verifying that an agent's word count matches the publisher's.

**Why this exists:** Different word-count algorithms produce different totals on the same text. The differential is small per sentence but compounds: on a 250-word abstract, the choice between whitespace-split and hyphenated-as-1 can swing the total by ~12 words. An agent that uses a different algorithm than the publisher believes it is meeting the cap when it is over by 5%. This reference fixes a single canonical algorithm for ARS pipelines, documents how publishers diverge, and specifies the buffer rule that makes minor publisher variation safe.

---

## The canonical algorithm: whitespace-split

ARS pipelines count words as `len(body.split())` in Python — that is, splits on any whitespace run and counts the resulting non-empty tokens.

### Why whitespace-split

1. **Reproducible.** Anyone running `len(body.split())` on the same UTF-8 text gets the same number. No hidden tokenizer state.
2. **Matches Microsoft Word default.** Most authors check word count in Word, which uses a whitespace-equivalent algorithm. Aligning with the dominant authoring environment minimises surprise.
3. **Conservative under hyphenation.** "State-of-the-art" counts as 1 token under whitespace-split. Under hyphenated-as-N this would count as 4. Whitespace-split therefore systematically reports a lower total than hyphenated-as-N — which is the safer direction when chasing a hard cap.
4. **Language-neutral.** CJK text without spaces is a separate problem (see "Non-space-delimited languages" below), but for English / European languages, whitespace-split is the universal lower bound.

### What whitespace-split counts

| Token | Whitespace-split count |
|---|---|
| `state-of-the-art` | 1 |
| `2020-2024` | 1 |
| `Smith, John-Paul` | 2 (`Smith,` and `John-Paul`) |
| `e.g.,` | 1 |
| `123,456` | 1 |
| `(n=42)` | 1 |
| `https://example.org/path` | 1 |

### What whitespace-split does NOT count

- Whitespace runs collapse to one delimiter; they do not contribute tokens.
- Empty strings between consecutive whitespace characters are filtered by `split()` with no argument.
- Markdown formatting (`**bold**`, `*italic*`, `` `code` ``) is part of the surrounding token; the asterisks and backticks are not separate tokens.
- ARS HTML-comment markers (see next section) — strip them before splitting.

### HTML-comment markers (#390 — one rule for all marker kinds)

ARS working drafts carry HTML-comment markers: `<!--ref:slug-->` / `<!--anchor:kind:value-->` (v3.7.1/v3.7.3, inline after citations) and `<!--block:BNNNN-->` (#390, one standalone line per block). **Strip every `<!--...-->` comment before computing `len(body.split())`.** Inline ref/anchor markers usually glue onto the preceding token (zero count impact) but add a token whenever whitespace precedes them; block markers are standalone lines and would inflate the total by one token per block — on a 60-block paper that is ~60 phantom words, and it would also corrupt `word_count_delta` (Schema 8) across patch-mode revision rounds. One rule covers every marker kind, current and future: markers are audit metadata, never countable content. (Phase 7 separately strips markers from converted final outputs — `formatter_agent.md` § ARS Marker Stripping — so publisher-side counts never see them either.)

---

## Publisher conventions and how to adapt

Most publishers use a whitespace-equivalent algorithm in practice but state different conventions in their author guidelines. The 3–5% buffer rule (below) makes ARS pipelines robust to the convention divergence without per-publisher adapters.

### Common publisher families

| Publisher / venue | Stated algorithm | Practical effect |
|---|---|---|
| Springer / Nature | whitespace-equivalent for abstract, no explicit definition | matches ARS canonical |
| IEEE | "approximately N words" — whitespace-equivalent in their submission tool | matches ARS canonical |
| ACM | whitespace-equivalent in CCS submission | matches ARS canonical |
| Elsevier (Cell, Lancet families) | whitespace-equivalent in EM submission | matches ARS canonical |
| Wiley | whitespace-equivalent | matches ARS canonical |
| arXiv | no hard cap on abstract; advisory ~250 words | guideline only |
| ICLR / NeurIPS / ACL workshop tracks | hyphenated-as-1 in their LaTeX `\abstract{}` counter | matches ARS canonical |
| Some social-science journals (variable) | "page-based" — abstract must fit visually on submission template | not a true word count; check template |

### When the publisher uses a stricter algorithm

Some non-English-medium publishers and a small number of style guides count hyphenated compounds as multiple words. If the publisher explicitly states "hyphenated words count as separate words":

1. Calibration should compute both totals: `len(body.split())` and the hyphenated-as-N variant.
2. The dispatch context to the abstract compiler should carry both numbers.
3. The compiler should use the stricter (higher) total when budgeting.

If the publisher's algorithm is ambiguous, default to ARS canonical (whitespace-split) plus the 3–5% buffer.

---

## The 3–5% buffer rule

ARS pipelines reserve **3–5% below the publisher's stated hard cap** as buffer. For a 250-word abstract:

- 3% buffer → target 242 words
- 5% buffer → target 237 words

### Why this range

1. **Algorithm divergence absorbs into the buffer.** Even if the publisher's tool counts ~3% higher than `len(body.split())`, the abstract still meets the cap.
2. **Editor-side trimming room.** Reviewers and copy editors occasionally request a phrase change that adds 2–3 words. Abstract that lands at exactly the cap forces a downstream cut; abstract that lands at cap minus 5% accommodates the change without cut.
3. **Title plus abstract pages.** Some publishers count the running title or running header; the buffer absorbs that too.

### When to use 3% vs. 5%

- **3%** when the calibration's `protected_hedges` block is large (≥10% of cap word budget). Tighter buffer keeps room for substantive content.
- **5%** when the publisher's algorithm is unstated or the protected hedges are minimal. Looser buffer absorbs more uncertainty.

### When NOT to use buffer

If the publisher imposes a strict character count instead of word count (rare, but happens with some Asian-language journals), the buffer rule does not apply directly. Calibration should compute character count under the publisher's stated encoding and apply a 1–2% buffer at the character level.

---

## Non-space-delimited languages

Mandarin, Japanese, Korean, Thai, and Lao do not delimit words with whitespace. ARS canonical algorithm produces meaningless totals on these texts.

For abstracts in non-space-delimited languages:

1. Use **character count**, not word count. Most publishers serving these languages specify character caps (e.g., Mandarin abstract often capped at 300 or 500 characters).
2. Apply 1–2% buffer at the character level.
3. The dispatch context to the abstract compiler should carry both `cap_unit: "character"` and the character cap, so the compiler does not erroneously apply word-budget logic.

For mixed-language abstracts (e.g., Mandarin abstract with English technical terms), count each segment in its native unit and report both numbers; the publisher's authoritative count usually applies the language-specific rule per segment.

---

## Where this convention is enforced

The `report_compiler_agent` abstract-only mode prompt enforces the canonical algorithm, the 3–5% buffer, and the post-draft re-verification step. The authoritative protection clause lives in `deep-research/agents/report_compiler_agent.md` under `PATTERN PROTECTION (v3.6.7)`. This file defines the algorithm, the buffer rationale, and the publisher-convention escape hatches; the agent prompt cites this file by path.

---

## Cross-references

- `shared/references/protected_hedging_phrases.md` — protected hedging phrases share the abstract budget; budget allocation order specified there.
- `shared/templates/codex_audit_multifile_template.md` — audit dimensions including word-count verification.
- ARS feedback memory `feedback_word_count_convention_mismatch.md` — original empirical observation of whitespace-split vs. hyphenated-as-1 differential (~12 words on a 250-word abstract).

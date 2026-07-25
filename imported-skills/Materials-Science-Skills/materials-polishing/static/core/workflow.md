# Polishing Workflow

Run these stages in order. The depth of each stage follows the fast/deep
classification; a short local edit must not trigger a full manuscript audit.

## 1. Lock The Input

Record the source text, requested scope, target language, stated section,
journal if supplied, and explicit material direction. Preserve every number,
unit, condition, standard, citation marker, and notation token before editing.

## 2. Choose Task Depth

Use the fast path for a sentence, title, short paragraph, or direct translation
with no document-scale concern.

Use the deep path for multiple paragraphs, a full section or manuscript,
structural repair, terminology consistency, citation auditing, risky scientific
claims, or paper-production handoffs. When depth is genuinely ambiguous, use
the deep path.

## 3. Resolve Routing

Apply profile precedence:

1. explicit direction in the current request;
2. saved `.materials/profile.yaml`;
3. neutral/general fallback.

Detect only axes that can change the output. Load the mapped files for selected
axes and the on-demand references whose conditions are present. Read each
selected path once even when multiple axes point to it.

## 4. Diagnose Before Editing

For the fast path, identify the local issue: grammar, clarity, tense,
translation, sentence length, terminology, or claim strength.

For the deep path, also check paper type, section function, paragraph message,
claim-evidence-boundary logic, information order, and terminology drift. Load
`failure-modes.md` or `hourglass-structure.md` only when structural diagnosis
is required.

## 5. Edit From Logic To Language

Apply loaded guidance in this order:

1. paper type and section function;
2. paragraph logic and information flow;
3. claim, evidence, mechanism, and boundary;
4. domain and material terminology;
5. journal and language conventions;
6. sentence clarity and mechanical polish.

Prefer one main proposition per sentence, keep subjects close to verbs, place
known information before new information, and split sentences that remain over
35 words.

## 6. Validate Scientific Strength

Load the evidence contract or claim-strength ladder when the text contains
causal, mechanism, significance, novelty, sustainability, durability, absolute,
or field-applicability wording.

Downgrade language when evidence is insufficient. Do not add missing evidence.
Keep negative or inconclusive findings visible as boundaries.

## 7. Run Final Checks

Confirm:

- all source numbers, units, conditions, standards, citations, and notation are
  unchanged;
- terminology and abbreviations are consistent at the required task depth;
- section tense and journal language match loaded guidance;
- no unsupported claim was strengthened;
- no sentence exceeds 35 words unless preserving an exact quoted passage;
- no structural problem was hidden by surface-level polish.

Load `proofreading.md`, `citation-integrity.md`, `british-english.md`, or the
terminology ledger only when their conditions apply.

## 8. Emit The Output

Follow `output-format.md`: return polished prose, concise revision notes, and a
claim-risk note when evidence, boundary, terminology, citation, or author input
still requires review.

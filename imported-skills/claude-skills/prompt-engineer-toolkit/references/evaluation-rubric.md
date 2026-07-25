# Evaluation Rubric for Marketing Prompts

How to score prompt outputs deterministically with `scripts/prompt_tester.py`, and how to extend the mechanical score with marketing-specific quality dimensions a regex can't fully capture. The principle throughout: evidence over intuition — a prompt is "better" only if it scores better on a realistic, edge-case-rich suite (never a single cherry-picked output).

## Layer 1 — Mechanical Score (what `prompt_tester.py` computes)

Score each test case 0-100 via weighted criteria:

| Criterion | Direction | Typical weight | Test-case field |
|---|---|---|---|
| Expected content coverage | + | 40% | `expected_contains` |
| Forbidden content violations | − (hard penalty) | 30% | `forbidden_contains` |
| Regex/format compliance | + | 20% | `expected_regex` |
| Output length sanity | ± | 10% | min/max length |

**Acceptance gates (promote a prompt only if all hold):**

- Average score ≥ 85 across the suite
- No individual case below 70
- Zero critical forbidden-content hits (brand-banned words, invented statistics markers, competitor names where disallowed, compliance terms — see governance guide)

## Layer 2 — Marketing Quality Dimensions

Encode as many of these as possible into Layer-1 fields; what remains needs human review on a sample (5-10 outputs per variant):

| Dimension | Mechanical proxy | Human check |
|---|---|---|
| **Specificity** | `expected_regex` for digits/named entities | Is the specific claim *true* and sourced? |
| **Brand voice** | `forbidden_contains` lexicon-no list | Does it sound like us, not "an AI"? |
| **Claim safety** | forbidden superlatives ("best", "#1", "guaranteed") unless proof token present | Would legal/compliance sign off? |
| **Format fitness** | char-count regex per platform | Does it read natively on the platform? |
| **CTA quality** | required CTA token | Single clear action, value-phrased? |
| **Audience fit** | required pain-point/persona token | Would the named persona care? |

Scoring scale for human review (per Hamel Husain's eval guidance, keep it binary where possible): pass/fail per dimension beats 1-5 ratings — raters agree more, and failures become new `forbidden_contains`/`expected_regex` entries, ratcheting the mechanical suite forward.

## Building the Test Suite

A marketing prompt suite needs at minimum:

1. **Happy-path cases (3-5)** — typical inputs with complete variables
2. **Sparse-input cases (2-3)** — missing proof points, vague audience: the prompt must degrade safely (omit proof, ask, or flag) rather than fabricate
3. **Adversarial cases (2-3)** — inputs that bait policy violations: competitor disparagement requests, unverifiable claims supplied as "facts", off-brand tone requests
4. **Edge-format cases (1-2)** — very long inputs, non-English fragments, emoji-laden source content

Failure analysis loop: every production failure (rejected ad, spam-flagged email, off-brand post) becomes a new test case before the prompt is edited — the marketing equivalent of regression-test-first.

## Anti-Patterns

- **Single-output judgment** — comparing one generation per prompt; sampling variance swamps prompt differences. Run every case ≥ 3 times or compare suite averages.
- **LLM-as-judge without calibration** — if you add a model-graded criterion, calibrate it against human labels on 20+ examples first and re-check periodically (judges drift with model versions).
- **Score-only promotion** — a +2 average that introduces one compliance violation is a regression, not an improvement. Violations gate, scores rank.
- **Frozen suite** — a suite that never grows stops catching new failure modes; tie suite growth to the failure-analysis loop above.

---

## Citations (6 sources)

1. Anthropic — "Define your success criteria" + "Create strong empirical evaluations" (docs.anthropic.com/en/docs/build-with-claude/define-success, /develop-tests): measurable criteria and graded test suites before prompt iteration
2. OpenAI Evals — open-source eval framework and registry patterns for templated, deterministic graders (github.com/openai/evals)
3. Hamel Husain — "Your AI Product Needs Evals" (hamel.dev/blog/posts/evals): unit-test-style assertions, failure-driven suite growth, binary human labels
4. Zheng et al. — "Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena" (NeurIPS 2023): LLM-judge agreement rates and bias modes (position, verbosity)
5. Eugene Yan — "Patterns for Building LLM-based Systems & Products" (eugeneyan.com): eval-first development, guardrails as gates vs. scores as ranks
6. Liu et al. — "G-Eval: NLG Evaluation using GPT-4 with Better Human Alignment" (EMNLP 2023): criteria-decomposed grading for content quality dimensions

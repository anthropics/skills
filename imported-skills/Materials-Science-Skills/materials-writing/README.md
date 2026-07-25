# materials-writing

**Version:** 1.3.0

**What it does** — `materials-writing` is an evidence-first, section-aware drafting engine for materials science manuscripts. It turns claims, results, notes, and outlines into bounded prose. It does not generate freeform text from prompts; it runs a staged workflow that locks terminology, writes a one-sentence argument, maps paragraph messages, passes a confirmation gate, and only then drafts prose that can be traced back to evidence.

**Four design principles**

| Principle | What it means in practice |
|---|---|
| Evidence first | Every major claim maps to evidence; missing evidence is surfaced as `[TO CONFIRM: ...]` placeholders. |
| Section aware | Each section has explicit moves: Introduction uses a gap ladder; Results moves observation → quantified result → mechanism evidence → alternative → boundary; Conclusion states contribution, limitation, next step, and overclaim boundary. |
| Profile aware | `material_family` and `domain` axes route into domain narratives, phrase banks, and section patterns in one pass. |
| Handoff friendly | Outputs claim-evidence maps and terminology ledgers that feed cleanly into `materials-citation`, `materials-doe`, `materials-reader`, and `materials-polishing`. |

**Seven routing axes** — Drives the section template, phrase bank, and domain narrative simultaneously:

| Axis | Examples |
|---|---|
| `paper_type` | experimental-manuscript / review-paper / methods-paper |
| `section` | abstract / introduction / methods / results-discussion / conclusion / full-argument |
| `language` | en / zh-to-en |
| `journal_family` | CBM / CCC / RMPD / JBE / materials |
| `material_family` | civil / polymers / metals / ceramics / functional / nano |
| `domain` | civil / polymers / metals / ceramics / functional / nano |
| `input_source` | manual / experiment-record |

The two material axes (`material_family` and `domain`) are what make the writing skill vertical for materials science: they route into the matching domain narrative, the matching phrase bank, and the matching section-pattern arc in a single pass.

**Tiered confirmation gate**

- A genuinely local single-paragraph edit can run the terminology and argument checks internally and proceed directly to the edit when the claim, evidence, and boundary are clear.
- A single-section, full-manuscript, or multi-section job shows the one-sentence argument, plan, terminology lock, assumptions, and targeted questions before full prose.
- QA or multi-round revision loads the content-first pipeline and state-machine references on demand; it does not add those references to the default core prompt.
- The default core is context-budgeted to four files; the detailed shared stance is loaded on demand when its extra placeholder or attribution rules are needed.

**File layout**

```text
skills/materials-writing/
├── README.md
├── SKILL.md                    # router and handoff contract
├── manifest.yaml               # seven-axis manifest and on-demand references
├── agents/
│   └── openai.yaml             # agent interface
├── scripts/
│   ├── build_manuscript_outline.py    # outline scaffolding
│   └── audit_materials_manuscript.py  # draft auditing
├── assets/templates/
│   ├── manuscript-argument-template.md
│   ├── section-draft-template.md
│   ├── table-system-template.md
│   └── wer-ea-mini-review-template.md
├── references/
│   ├── argument-chain.md              # fast one-sentence argument template
│   ├── article-architecture.md        # full-paper move map
│   ├── content-first-qa-pipeline.md   # opt-in post-draft QA order
│   ├── state-machine/                 # opt-in continuity and stop rules
│   ├── review-paper-strategy.md       # synthesis-axes review strategy
│   ├── wer-ea-mini-review-pipeline.md # WER-EA review pipeline
│   ├── reviewer-risk-writing.md       # overclaim and missing-evidence risk
│   ├── published-article-patterns.md  # sentence templates from real papers
│   ├── paragraph-flow.md              # one-paragraph-one-message reference
│   ├── table-system.md                # table system templates
│   ├── experiment-record-for-writing.md # record-to-prose guidance
│   ├── *-narrative.md                 # 34 domain narrative guides
│   ├── section-patterns/              # 5 section arcs
│   ├── phrase-banks/                  # 10 domain phrase banks
│   └── examples/                      # example library
├── static/fragments/
│   ├── core/           # contract, workflow, output-format, stance stub
│   ├── section/        # abstract, introduction, methods, results-discussion, conclusion, ...
│   ├── paper_type/     # experimental-manuscript, review-paper, methods-paper
│   ├── journal/        # CBM, CCC, RMPD, JBE, materials
│   ├── language/       # en, zh-to-en
│   └── domain/         # civil, polymers, metals, ceramics, functional, nano
└── tests/
    ├── test_writing_skill.py
    ├── test_narrative_guides.py
    ├── scenarios/      # behavior-protecting scenarios
    └── pressure-tests/ # missing-data writing pressure test
```

**Key rules enforced**

| Domain | Core rule |
|---|---|
| Evidence first | Every claim maps to evidence; no overclaim, no speculation as fact. |
| Terminology lock | Canonical forms are locked before drafting; drafts do not reintroduce variants. |
| Confirmation gate | Full section output is produced only after the one-sentence argument, plan, and terminology are shown for confirmation; only a genuinely local paragraph edit uses the fast path. |
| Paragraph flow | One paragraph, one message; first sentence forecasts the message; transitions carry the argument forward. |
| Abstract | Background pain -> contribution -> result -> application boundary. |
| Introduction | Gap ladder from field progress to explicit evidence gap and paper entry. |
| Method | Synthesis/preparation route, test standards, replicate count, condition control. |
| Results/Discussion | Observation -> quantified result -> mechanism evidence -> alternative explanation -> boundary. |
| Conclusion | Contribution, limitation, next step, and overclaim boundary. |
| Review paper | Organized by synthesis axes (mechanism, material design, performance trade-off, research agenda), not paper-by-paper. |
| Chinese notes | zh-to-en drafting preserves facts and evidence strength, not literal wording. |

**Example 1: From weak introduction to gap ladder**

- Weak: "Few studies have investigated waterborne epoxy modified emulsified asphalt."
- Stronger: "While dry bonding strength of WER-EA tack coats has been reported, wet bonding retention after freeze-thaw conditioning and the corresponding interface morphology evolution remain unquantified."

The skill turns the weak version into the stronger one by mapping the introduction onto field progress → contradiction → evidence gap → paper entry.

**Example 2: From result to bounded claim-evidence map**

Input: "Bonding strength increased from 0.43 MPa to 0.55 MPa at 10% epoxy."

Output claim-evidence map:

```text
Claim: 10% epoxy increases WER-EA tack-coat bonding strength under dry conditions.
Evidence: Pull-off test data, control vs. 10% epoxy, measured at 25 °C.
Boundary: Dry conditions only; wet/aged data not provided.
```

The skill keeps the claim tied to the measurement and explicitly states the boundary instead of generalizing to field durability.

**When To Use**

Use `materials-writing` when the user request matches this skill's production surface and the needed inputs are available or can be explicitly marked as missing.

## Inputs

Typical inputs are the user prompt, material direction/profile, target journal or task mode when relevant, and any source text, data, figures, reviewer comments, reader-package artifacts, doe-handoff artifacts, or experiment-record files needed by the skill.

## Outputs

Outputs are structured handoffs or artifacts described above. Every output follows the six-part writing format: Draft, Section outline, Assumptions, Claim-evidence map, Why this structure, To redirect me. Missing evidence, author input needs, and unsupported claims stay visible instead of being hidden in fluent prose.

## Validation

Run the skill-specific scripts or tests listed above when they apply, then run the bundle gate from the repository root:

```powershell
python .\scripts\run_release_checks.py --json
python .\scripts\check_skill_architecture.py --json
```

## Boundaries

This skill does not invent experiments, citations, measurements, journal facts, private file paths, or completed actions. Time-sensitive journal or legal facts should be checked against official sources before submission or filing.

# materials-polishing

**What it does** - The language and claim-strength control layer for materials
prose. **Version 1.3.0** uses a five-file core with conditional risk and
document-scale guidance. The normal activation target is 25 KiB and the hard
limit is 28 KiB.

- **Fast path**: bounded sentence, title, short paragraph, or direct
  Chinese-to-English polish.
- **Deep path**: multi-paragraph or full-section work, structural repair,
  terminology consistency, risky claims, citation review, or paper-production
  handoff.

The skill keeps section, journal, language, paper-type, material-family, and
domain knowledge in routed fragments. Evidence, claim-strength, terminology,
ethics, failure-mode, and weakness-routing references load only when their
conditions apply. Output preserves facts, units, citations, and evidence
strength, keeps missing-evidence markers visible, and returns revision-safe
wording.

**Built from** - A five-file core plus routed section, journal-family,
language, paper-type, material-family, and domain fragments:

- `static/core/` - `contract.md`, `stance.md`, `workflow.md`,
  `output-format.md`
- `../_shared/core/direction-profile.md` - shared direction-profile baseline
- `static/fragments/section/` - per-section playbooks (abstract,
  introduction, methods, results, discussion, conclusion, title)
- `static/fragments/paper_type/` - research vs. review argument chains
- `static/fragments/language/` - English rules and Chinese-to-English patterns
- `static/fragments/domain/` - material-system-specific evidence norms
- `references/` - deep-dive guides and on-demand controls (claim-strength
  ladder, hourglass structure, language rulebook, zh-to-en patterns, style
  guardrails, vocabulary upgrade, citation integrity, British English,
  proofreading, section guides, cover letter, and domain language guides)
- `assets/templates/polishing-request-template.md` - request scaffolding
- `scripts/audit_sentences.py` - sentence-length and style auditing

**Key rules enforced**

| Domain | Core rule |
|---|---|
| Sentence length | Keep sentences <=35 words; split long compound claims. |
| Hedging | Calibrate causal vs. associative language via the claim-strength ladder. |
| Section tense | Match tense to section (methods past, results past, discussion mixed). |
| Citation integrity | Preserve attribution and density; no silent citation drops. |
| Overclaim | Downgrade mechanism/performance claims to evidence level; flag risk. |
| British English | Apply journal-specific spelling and consistency checks. |

**Reference files**

```text
skills/materials-polishing/
|- README.md
|- SKILL.md
|- manifest.yaml
|- scripts/
|  |- audit_sentences.py              sentence-length and style audit
|- assets/templates/
|  |- polishing-request-template.md
|- references/
|  |- claim-strength-ladder.md        causal vs. associative calibration
|  |- hourglass-structure.md          section flow and paragraph order
|  |- language-rulebook.md            SCI / academic style rules
|  |- chinese-to-english-patterns.md  zh-to-en rewriting patterns
|  |- style-guardrails.md             generic polishing guardrails
|  |- vocabulary-upgrade.md           weak-word and verb calibration
|  |- citation-integrity.md           attribution and density audit
|  |- british-english.md              spelling and consistency
|  |- proofreading.md                 final mechanical checks
|  |- abstract.md                     section polishing guides
|  |- introduction.md
|  |- results-discussion.md
|  |- conclusions.md
|  |- cover-letter.md
|  |- pavement-language.md            domain language guides
|  |- cement-concrete-language.md
|  |- ceramics-language.md
|  |- polymers-language.md
|  |- metals-language.md
|  |- insulation-language.md
|  |- nano-language.md
|  |- functional-language.md
|- static/
|  |- core/                           contract.md, stance.md, workflow.md, output-format.md
|  |- fragments/language/            en, zh-to-en
|  |- fragments/paper_type/          research, review
|  |- fragments/section/             abstract, introduction, methods, results, discussion, conclusion, title
|  |- fragments/domain/              civil, polymers, metals, ceramics, functional, nano
```

**Validation**

- Audit script:
  `plugins/materials-skills/skills/materials-polishing/scripts/audit_sentences.py`
- Architecture check:
  `python .\scripts\check_skill_architecture.py --skill materials-polishing --json`
- Bundle verification:
  `python .\scripts\run_release_checks.py --json`

## When To Use

Use `materials-polishing` when the user request matches this skill's production
surface and the needed inputs are available or can be explicitly marked as
missing.

## Inputs

Typical inputs are the user prompt, material direction/profile, target journal
or task mode when relevant, and any source text, data, figures, reviewer
comments, or package artifacts needed by the skill.

## Outputs

Outputs are structured handoffs or artifacts described above in this README.
Missing evidence, author input needs, and unsupported claims stay visible
instead of being hidden in fluent prose.

## Example

```text
Tighten an English results paragraph and flag overclaims.
```

## Validation

Run the skill-specific scripts or tests listed above when they apply, then run
the focused architecture check and the bundle gate from the repository root:

```powershell
python .\scripts\check_skill_architecture.py --skill materials-polishing --json
python .\scripts\run_release_checks.py --json
```

## Boundaries

This skill does not invent experiments, citations, measurements, journal facts,
private file paths, or completed actions. Time-sensitive journal or legal facts
should be checked against official sources before submission or filing.

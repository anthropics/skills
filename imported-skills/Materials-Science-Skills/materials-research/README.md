# materials-research

**Version:** 1.2.0

**What it does** — The front door and paper-production orchestrator for the
bundle. Start here when the user need is broad, multi-stage, or not yet
pinned to one companion skill. It detects the task type, material domain, and
journal family, then hands off to the right companion skill with a
stage-gated plan. It covers topic positioning, paper-angle design,
literature-review planning, journal targeting, experiment routing, submission
strategy, HTML deck planning, and reviewer-risk framing — any cross-skill workflow
that needs paper-stage and evidence-level judgment.

**Built from** — A front-door router that orchestrates 11 companion skills
(reader, citation, writing, polishing, response, reviewer, html-deck,
figure, data, doe, paper-to-patent), grounded in the shared paper-production
contract:

- `references/paper-production-orchestrator.md` — stage-gated production
  contract and gate-report template
- `references/companion-modules.md` — companion-skill handoff map
- `references/reviewer-risk-checklist.md` — pre-submission reviewer risk
- `references/journal-shortlist.md` — materials journal positioning
- `static/fragments/task/` — 15 task-routing fragments: research-positioning,
  reading, literature-review, citation-mapping, manuscript-writing,
  journal-targeting, experiment-design, data-analysis, data-fair,
  figure-table, reviewer-audit, reviewer-response, submission-package,
  presentation, html-deck-generation
- `static/fragments/domain/` — 36 material-domain fragments
- `static/fragments/journal/` — 20 journal-family fragments
- `../_shared/paper-production/weakness-routing.md` — weakness routing
- shared paper-production templates and release-gate checks

**Key rules enforced**

- The default router core is context-budgeted to two files; detailed stance and
  cross-stage contracts load only when the request needs them.
- Do not skip to writing or figures before research and citation are
  grounded.
- Do not duplicate the full procedures of every companion skill; once the
  deliverable is clear, deep production belongs to the specialized module.
- Gate each stage on the previous stage's output contract.
- Recommend `materials-citation` first when literature gaps exist.
- Report `coverage_tier` (full / partial / skeleton / generic) when routing
  to a material domain so the user knows what depth to expect.
- Stage and evidence-level judgment drives routing, not the user's wording.

**Reference files**

```text
skills/materials-research/
├── README.md
├── SKILL.md
├── manifest.yaml
├── assets/
│   └── templates/
│       └── research-routing-template.md  routing plan scaffold
├── static/
│   ├── core/                             contract, evidence-contract, stance, workflow
│   └── fragments/
│       ├── task/                         15 task-routing fragments (listed below)
│       │   ├── research-positioning.md
│       │   ├── reading.md
│       │   ├── literature-review.md
│       │   ├── citation-mapping.md
│       │   ├── manuscript-writing.md
│       │   ├── journal-targeting.md
│       │   ├── experiment-design.md
│       │   ├── data-analysis.md
│       │   ├── data-fair.md
│       │   ├── figure-table.md
│       │   ├── reviewer-audit.md
│       │   ├── reviewer-response.md
│       │   ├── submission-package.md
│       │   ├── presentation.md
│       │   └── html-deck-generation.md
│       ├── domain/                       36 material-domain fragments
│       └── journal/                      20 journal-family fragments
└── references/
    ├── paper-production-orchestrator.md  stage-gated production contract
    ├── companion-modules.md              companion-skill handoff map
    ├── reviewer-risk-checklist.md        pre-submission reviewer risk
    ├── journal-shortlist.md              materials journal positioning
    ├── asphalt-waterborne-epoxy.md       WER-EA domain reference
    ├── data-to-manuscript.md             data-to-claim mapping
    ├── output-templates.md               abstract/highlights/cover-letter templates
    ├── statistical-methods.md            significance/ANOVA/uncertainty
    ├── test-standards-mapping.md         ASTM/EN/JTG/GB/AASHTO/RILEM mapping
    ├── standards-mapping.md              GB/T/JTG/JTJ to ASTM/EN/ISO conversion
    ├── characterization-guide.md         FTIR/SEM/XRD/TG/DSC/AFM/rheology
    ├── sustainability-claims-guide.md    LCA/low-carbon/recycled claims
    ├── ceramics-guide.md                 ceramics characterization guide
    ├── thermal-insulation-guide.md       insulation/hygrothermal guide
    ├── thesis-timeline.md                thesis/research timeline planning
    └── pressure-test-suite.md            pressure-test coverage suite
```

**Validation**

- Paper-production contract files live under `references/` and
  `../_shared/paper-production/`.
- Bundle verification:
  `python .\scripts\run_release_checks.py --json`

The public GitHub package does not ship the internal pressure-test files.

## When To Use

Use `materials-research` when the user request matches this skill's production surface and the needed inputs are available or can be explicitly marked as missing.

## Inputs

Typical inputs are the user prompt, material direction/profile, target journal or task mode when relevant, and any source text, data, figures, reviewer comments, or package artifacts needed by the skill.

## Outputs

Outputs are structured handoffs or artifacts described above in this README. Missing evidence, author input needs, and unsupported claims stay visible instead of being hidden in fluent prose.

## Example

```text
Route a broad WER-EA mini-review request into companion skills.
```

## Validation

Run the skill-specific scripts or tests listed above when they apply, then run the bundle gate from the repository root:

```powershell
python .\scripts\run_release_checks.py --json
```

## Boundaries

This skill does not invent experiments, citations, measurements, journal facts, private file paths, or completed actions. Time-sensitive journal or legal facts should be checked against official sources before submission or filing.

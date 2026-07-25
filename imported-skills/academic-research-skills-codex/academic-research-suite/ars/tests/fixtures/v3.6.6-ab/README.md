# ARS v3.6.6 A/B Evidence Fixture

This directory holds the A/B evidence fixture for ARS v3.6.6's
generator-evaluator contract gate. The `manifest.yaml` instantiates the §6.2
schema declared in `docs/design/2026-04-27-ars-v3.6.6-generator-evaluator-contract-design.md`.

## State at this commit

**STUB.** The manifest is populated with the full §6.2 schema shape and the
seven paper entries (six paper-A + one paper-C). Every spec_branch-mode
required path declared in the manifest exists as a placeholder file
explaining its expected populated content. **Real fixture data is not yet
populated.**

The stub state lets:

- The §6 spec body land with concrete file evidence that the §6.2 schema +
  §6.5 invariants are mechanically realisable.
- The CI lint (§7.5) pass on this commit because every declared path
  exists git-tracked, even though the file contents are placeholders.
- Future contributors trace the §6.2 schema field semantics to a concrete
  example without having to wait for full fixture population.

## What lives where

```
tests/fixtures/v3.6.6-ab/
├── manifest.yaml                    # §6.2 schema instantiation (STUB)
├── README.md                        # this file
├── inputs/                          # frozen upstream artefact snapshots per paper
│   ├── paperA-imrad-01/             #   paper-A, IMRaD empirical (×2)
│   ├── paperA-imrad-02/
│   ├── paperA-litreview-01/         #   paper-A, literature review (×2)
│   ├── paperA-litreview-02/
│   ├── paperA-casestudy-01/         #   paper-A, case study (×2)
│   ├── paperA-casestudy-02/
│   └── paperC-known-fail-01/        #   paper-C, v3.6.5 known-fail sanity case
├── baseline/                        # v3.6.5 single-call configuration outputs per paper
│   └── {paper_id}/v3.6.5/
│       ├── writer_draft.md          #   v3.6.5 writer Phase 4 single-call output
│       └── evaluator_review.md      #   v3.6.5 evaluator Phase 6 single-call output
└── codex-judge/                     # codex gpt-5.5 + xhigh verdict-only judge outputs
    └── {paper_id}-v3.6.5.txt        #   H1 / H3 judge against paper-A baseline (paper-C exempt)
```

The implementation PR additionally lands `treatment/{paper_id}/v3.6.6/`
sub-directories with `phase4a_output.md` / `phase4b_output.md` /
`phase6a_output.md` / `phase6b_output.md`, `codex-judge/{paper_id}-v3.6.6.txt`
files for paper-A treatment, `metrics/{paper_id}.json` files for paper-A,
and `metrics/summary.md`. The implementation PR also flips
`manifest_lint_mode` from `spec_branch` to `implementation_pr`. See §6.5
"Implementation PR ship" for the full enumeration.

## Population trajectory

This directory's lifecycle inside the spec PR's working branch:

1. **Stub commit** (this commit): manifest schema instantiation +
   placeholders explaining each expected file's populated content.
2. **Fixture data populate commits** (follow-up commits before spec PR
   merges to main): replace each placeholder with the real
   deep-research synthesis report (paper-A inputs), v3.6.5 academic-paper
   full-run output (baseline), v3.6.5 session log + Stage 3 reviewer
   excerpt (paper-C), and codex judge full-text output (paper-A baseline).
3. **Spec PR merge to main**: the `manifest_lint_mode: spec_branch` state
   ships under §6.5 spec-PR ship list invariants.
4. **Implementation PR**: writer + evaluator agent files gain v3.6.6
   contract block; treatment runs land in `treatment/`; metrics land in
   `metrics/`; manifest's `manifest_lint_mode` flips to
   `implementation_pr` in the same atomic merge state.

## Fixture data origins (when real data lands)

Per §6.2 Round D Q5 decision (recorded in §9.1):

- **paper-A inputs**: existing deep-research synthesis reports already
  produced by the suite, covering three paper-type families (IMRaD
  empirical / literature review / case study) × two repetitions = six
  papers.
- **paper-C input**: existing v3.6.5 academic-paper full-run session log
  where the in-pair Phase 6 evaluator's self-scoring passed but the
  Stage 3 reviewer (external `academic-paper-reviewer` skill) caught a
  hallucinated citation that the in-pair evaluator missed.

Real retracted papers are excluded (ethical/legal); AI-authored defect
injection is excluded (AI-evaluator collusion risk).

## Lint coverage

Per §7.5, the manifest CI lint enforces (mode-conditional under the
manifest's `manifest_lint_mode` value):

- Schema-shape checks (top-level required fields, per-paper required
  fields with declared types, paper-C must-not-have rules,
  `paper_id` uniqueness, paper-A `paper_type` family count rule).
- Path-existence checks (mode-required paths must exist;
  optional-but-populated paths must also exist; reverse-scan finds
  fixture orphans).
- Behaviour on malformed YAML (exit 1 with parse-error message).

The implementation PR ships the executing lint script per §7.5; this
README describes the rules at protocol level only.

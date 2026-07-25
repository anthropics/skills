# Contributing to Academic Research Skills

Thank you for your interest in contributing. This document explains what kinds of contributions we accept and how to submit them.

---

## How to submit a contribution

ARS uses the standard **fork-and-PR** workflow. Fork the repo on GitHub, clone your fork, create a branch, make your changes, push to your fork, then open a PR against `Imbad0202/academic-research-skills`.

**Important**: You cannot push directly to this repo — you must fork it first and submit a PR from your fork.

---

## What we accept

### Community-maintained (fast merge)

These contributions can be merged quickly with minimal review:

- **Typo and formatting fixes** — spelling, broken links, markdown rendering issues
- **New examples** — pipeline output showcases, worked examples for specific disciplines
- **Translation improvements** — better zh-TW or EN phrasing in READMEs or agent definitions

### Requires maintainer review

These need careful review because they affect system behavior:

- **Journal and field reference lists** — additions to `top_journals_by_field.md`, new discipline glossaries
- **Evaluation sets** — gold-standard papers for calibration mode, benchmark data
- **New reference files** — methodology guides, citation format references, domain-specific protocols
- **Bug and drift fixes** — version inconsistencies, broken cross-references, incorrect metadata
- **Mode changes** — new modes, trigger keyword changes, oversight level adjustments

### Requires maintainer approval + discussion

Open an issue first before submitting a PR for these:

- **Agent definition changes** — modifications to any file in `*/agents/*.md`
- **IRON RULE modifications** — any change to rules marked with the IRON RULE marker
- **Ethics and integrity rules** — changes to the failure mode checklist, integrity protocols, or ethics review
- **Handoff schema changes** — modifications to `shared/handoff_schemas.md`
- **New skills or modes** — additions to the pipeline

### Platform ports (community-maintained only)

This repository is the reference distribution of ARS, built for Claude Code. Ports to other agent platforms (Opencode, Cursor, Continue, Aider, etc.) are accepted as community-maintained contributions. Two structural shapes are acceptable — both keep core ARS content as the source of truth:

- **In-tree wrapper.** Add a top-level `<platform>/` directory in this repo (e.g. `opencode/`) containing the manifest, plugin entry, and dispatch shims. Core ARS files (`skills/*/SKILL.md`, `agents/*.md`, `shared/`, `scripts/`) remain unmodified.
- **Sibling distribution.** A separate repository that vendors ARS workflow content with: (1) upstream commit hash pinned (e.g. in a `manifest.json`); (2) a written update / sync policy; (3) vendored content unmodified — only the outer routing / adapter layer is platform-specific.

Either shape is accepted under the same maintainer-facing conditions:

- **Named maintainer.** The PR description (in-tree) or repo README (sibling) must identify who will keep the port in sync with ARS minor releases (~6-week cadence) and triage platform-specific bug reports. Platform-specific issues will be redirected to that maintainer.
- **End-to-end evidence.** Include at least one full `academic-pipeline` run on the target platform, committed under `examples/<platform>/` (in-tree) or under an `examples/` path in the sibling repo, so regressions are detectable.
- **Model-portability note.** ARS prompts are calibrated against Claude (Opus for architecture/review, Sonnet for execution; never Haiku). The PR must document which providers/models were tested and where downstream-agent behavior diverged from the Claude baseline.
- **Open a design issue first** before submitting the PR (for in-tree) or before requesting sibling-distribution recognition in this repo's README.

---

## PR guidelines

- **One concern per PR** — don't mix unrelated changes
- **Describe what and why** — explain the motivation, not just the change
- **Reference issues** — if your PR addresses an open issue, link it
- **Test your changes** — if you're modifying agent definitions, try running the skill to confirm it works as expected
- **Keep READMEs in sync** — if your change affects user-facing documentation, update `README.md`, `README.zh-CN.md`, `README.zh-TW.md`, `README.ja-JP.md`, and `README.ko-KR.md` when applicable

---

## Governance

### Maintainer

The repo is maintained by [Cheng-I Wu](https://github.com/Imbad0202) (HEEACT). The maintainer has final say on all merges.

### Decision principles

1. **Accuracy over completeness** — we'd rather have fewer, verified journal entries than a long unvetted list
2. **Human-in-the-loop always** — contributions that reduce human oversight or enable fully autonomous paper generation will be declined
3. **No detection evasion** — features designed to make AI-generated text harder to detect (as opposed to higher quality) are out of scope. See [Issue #3](https://github.com/Imbad0202/academic-research-skills/issues/3) for context.
4. **Discipline diversity welcome** — ARS defaults to higher education research but aims to be domain-agnostic. Discipline-specific modules are encouraged.

---

## Release checklist

Most release mechanics are CI-enforced (`check_version_consistency.py` keeps CLAUDE.md / SKILL.md / CHANGELOG / plugin manifests / README badge in lockstep; the release-cooldown workflow paces tags; the `changelog-covers-merges` workflow gates release-prep PRs). One step still has a manual form for tag flows that skip a release branch:

### Before tagging: CHANGELOG covers every merge

CI runs this automatically on every release-prep PR (head branch `release/**`): the `Changelog Covers Merges` workflow audits every release-worthy commit merged to `main` since the previous release tag and fails unless its issue/PR number (`#N`) is referenced in `CHANGELOG.md` **above the previous release's section** — under `## [Unreleased]`, or under the version section the prep PR just promoted (spec §0.2).

For a tag cut without a `release/` branch, run the same gate by hand from the release-prep state (**before** the `vX.Y.Z` tag exists): `python3 scripts/check_changelog_covers_merges.py`. Resolve each finding (add a CHANGELOG entry citing its `#N`) or confirm it is legitimately exempt (a `chore`/`test`/`ci`/`build` commit, or an internal `docs(design)`/`docs(superpowers)` commit, or the once-per-release `docs(release)` alignment commit; `docs(i18n)` is deliberately NOT exempt — translation changes are user-facing). This is the machine-checked half of the `[doc-aligned: yyyy-mm-dd]` tag-message discipline. Run it on the release-prep state, not on a feature branch — in-progress branch commits have no PR suffix yet and will report as unverifiable (CI avoids this by auditing `--merges-ref origin/main`).

One convention is editorial and lives here:

### `Real-use findings` subsection (#395)

When drafting a release's CHANGELOG entry, include a **`Real-use findings`** subsection if any of the release's issues were discovered through actual use of the suite on a real paper — one line per issue, naming the run that surfaced it. Paper-derived / external-motivation work (the Zhao / Kong / Kim tracks) does NOT belong here; the subsection exists precisely to make the other provenance class visible. Background: the v3.6.7 production chapter run surfaced 17 drift patterns, but that lived-experience provenance was buried in spec prose with no fixed, greppable home — and release motivation since v3.8 has been almost entirely external papers, which is itself a signal worth seeing per release. If a release has no real-use findings, omit the subsection; never pad it.

## Academic integrity policy

This repo is designed to be **assistive, not deceptive**. See [POSITIONING.md](POSITIONING.md) for the full design philosophy. Contributors must not add features designed to evade AI detection tools. If unsure, open an issue to discuss before submitting a PR.

---

## Credit

Contributors are credited in commit messages, CHANGELOG entries, and the Contributors section of the README. For significant contributions (new features, major reference files), we also add a mention in the relevant release notes.

## License

By contributing, you agree that your contributions will be licensed under [CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/). See [POSITIONING.md](POSITIONING.md) for usage terms.

## When adding a new skill

Read [`shared/ground_truth_isolation_pattern.md`](shared/ground_truth_isolation_pattern.md) before writing the SKILL.md. It explains the three-layer model behind the `data_access_level` and `task_type` frontmatter fields and lists the do/don't rules for handling evaluation rubrics, gold labels, and answer keys.

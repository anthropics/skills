# Positioning

## What this is

Academic Research Skills (ARS) is a **source-available academic research copilot framework** for noncommercial scholarly use. The reference distribution is a suite of Claude Code skills that assists human researchers through the full research-to-publication pipeline. Sibling distributions for other agent platforms ([e.g. Codex](https://github.com/Imbad0202/academic-research-skills-codex)) follow the same workflow content, the same human-in-the-loop design philosophy, and the same license terms; see [CONTRIBUTING.md § Platform ports](CONTRIBUTING.md#platform-ports-community-maintained-only).

It is licensed under [CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/). This is not an open source license — it restricts commercial use by design, to keep the tool free for academic communities.

## What this is not

ARS is not an autonomous paper-writing system. It is not a replacement for the researcher. It does not claim authorship, and its outputs are not submission-ready without human review.

## Rejected mechanisms (autonomous-research anti-patterns)

These are not "out of scope" footnotes. They are the load-bearing boundary that defines what ARS does NOT do, and would not do even if a future system made them feasible. Each is the kind of autonomous mechanism catalogued by Kong et al. (2026), *AI for Auto-Research: Roadmap & User Guide* (arXiv:2605.18661), and rejected against the human-led positioning above. The recorded review test for all five — "who controls the next research-state transition?" — lives in the [L1 design lesson](docs/design/2026-06-08-kong-255-l1-copilot-not-auto-research.md).

- **End-to-end autonomous research pipeline** (Kong §7.4.8). A system that carries a project from question to manuscript without scholar confirmation at each state transition. Rejected: the scholar would become a reviewer of AI output, not the author. The pipeline's mandatory checkpoints exist precisely to prevent this.
- **Idea-generation agent** (Kong §3.1). An agent that proposes research hypotheses or questions *for* the scholar. Rejected — and distinct from the shipped wording-pattern advisory (#257): ARS may flag surface-level wording / framing patterns in a scholar-supplied research question and ask a Socratic follow-up, but it must not propose, substitute, rank, expand, or select research hypotheses or questions for the scholar. The boundary is recorded in the [L2 design lesson](docs/design/2026-06-08-kong-255-l2-advisory-not-generation.md).
- **Paper2X auto-generation** (Kong §6). Autonomous generation of slides / posters / video from a manuscript. Rejected — and distinct from a *fidelity audit*: ARS may audit an already-authored or externally generated dissemination artifact against the manuscript for fidelity, but it must not transform a manuscript into a dissemination artifact by choosing the content, narrative, layout, or output medium itself. (Dissemination *design* is handled by separate, non-ARS skill chains; the fidelity-audit suggestion itself is out of this repo's scope.)
- **Autonomous experiment execution / coding** (Kong §3.3). An LLM that runs experiments or code without scholar oversight. Rejected — and distinct from the shipped Experiment Provenance Intake (#260): ARS may ingest scholar-declared external experiment provenance and check manuscript claims against the declared results, but it must not initiate, run, modify, iterate, or treat tool-executed experiment / code outputs as evidence inside the pipeline.
- **Physical wet-lab automation API** (Kong §7.4.6). An interface that drives liquid handlers or automated labs. Rejected: even with safeguards, this extends beyond a research copilot's scope into laboratory infrastructure, and conflicts with the copilot-not-pilot positioning.

These are first-party scope boundaries and review criteria for future changes, not runtime guarantees. First-party ARS treats each as out of scope; adding one would require changing this recorded boundary, not merely adding a feature.

## Recorded non-goals (scope boundaries without a mechanism)

Unlike the Rejected mechanisms above — capabilities ARS refuses on principle — these are lifecycle stages and state layers ARS deliberately does not enter. They were adjudicated out of scope in the 2026-06-10 researcher-blindspot audit and are recorded here so the boundary is reviewable, not improvised (the same recording discipline as the Rejected mechanisms; boundary + review criterion, not a runtime guarantee).

- **Post-publication lifecycle.** Tracking citation contexts of the scholar's own published papers, errata/corrigenda workflows, and OA self-archiving compliance are out of scope. ARS's front is research-to-publication; what happens to a paper after it ships belongs to the scholar and their institutional tooling. The existing `monitoring_agent` is unaffected — it alerts on developments in the *cited* literature (an input to current work), not on the scholar's own published output. Review criterion: a proposed feature whose value begins *after* the manuscript is accepted extends the front, and requires changing this recorded boundary first.
- **Research-program-level state.** ARS keeps no memory across papers: no registry of the scholar's prior claims, no carried-forward limitations list, no reviewer-history profile. The per-paper Material Passport remains the only state carrier, and every run starts from what the scholar explicitly feeds it. This is a deliberate consequence of the anti-leakage philosophy — gates that trusted an ambient cross-paper memory would be evaluating state nobody declared this run. The supported way for a returning author to carry their own prior work forward without any new mechanism is the [Cross-paper workflow guide](docs/cross-paper-workflow.md). Review criterion: a proposed feature that reads or writes scholar state outside the current run's passport crosses this boundary.
- **Institutional / journal format-profile content.** Unlike the two above, ARS *does* ship the mechanism — the scholar-declared layout `format_profile` (#439), so a user can bind a thesis or journal template without forking. What ARS deliberately does NOT ship is any *specific* institution's or journal's profile *content*: the repo carries the schema and a synthetic example only, never a real school's font/spacing/caption rules. Binding the suite to one institution's template is the boundary the [#439 design](docs/design/2026-06-15-439-format-profile-design.md) keeps out. Review criterion: a PR that adds a real institution's or journal's `format_profile.yaml` (or hardcodes its rules into an agent) to this repo crosses this boundary — profiles stay user-supplied and out-of-tree.

## Allowed uses

- Research assistance: literature search, source verification, citation checking
- Teaching: demonstrating research methodology, peer review processes, academic writing standards
- Method training: using Socratic modes to develop research question formulation and argumentation skills
- Noncommercial academic collaboration: research groups, labs, departments using the tool for shared workflows

## Discouraged uses

- Submitting AI-generated papers as solely human-authored without disclosing AI assistance
- Using the tool to produce papers without engaging with the content (the pipeline has mandatory checkpoints specifically to prevent this)
- Treating AI-generated review feedback as a substitute for actual peer review

## Prohibited uses (per license)

- Commercial SaaS or hosted services built on ARS
- Consulting or freelance services that package ARS as a paid product
- Enterprise or institutional paid deployments without separate licensing
- Commercial API wrappers or resale of ARS functionality

These reflect our policy intent. See the [CC BY-NC 4.0 license](https://creativecommons.org/licenses/by-nc/4.0/) for the precise legal terms. For commercial licensing inquiries, contact the maintainer.

## Design philosophy

**Assistive, not deceptive.** ARS helps you write better, not hide that you used AI.

- Style Calibration learns your voice from past papers — so the output sounds like you, not like a machine
- Writing Quality Check catches AI-typical patterns — to improve prose quality, not evade detection
- Disclosure Mode generates venue-specific or policy-anchor AI usage statements — because transparency is the standard

**Human-in-the-loop, always.** The pipeline's checkpoint system is mandatory by design:

- FULL checkpoints present all deliverables and require explicit user confirmation
- MANDATORY checkpoints at integrity gates and review decisions cannot be skipped
- "Full mode" means full-pipeline execution, not full autonomy — the human decides at every gate
- Max 2 revision loops, after which remaining issues become "Acknowledged Limitations" rather than being silently resolved

**Failure modes are made visible, not hidden.** The 7-mode AI Research Failure Mode Checklist (v3.2) and Reviewer Calibration Mode exist so that users can see where the AI might be wrong — not so that the AI can claim it's always right. The v3.7.3 + v3.8 L3 claim-faithfulness gate adds per-citation locator anchors and an opt-in audit pass that verifies whether each cited source actually supports the claim made of it.

**Boundaries are recorded, not improvised.** When adopting a capability from a published system would touch a load-bearing boundary — who ranks, what propagates, who writes state — the decision of whether and how to adopt it is written down as a design-lesson doc, so the same boundary is applied consistently later. The Co-Scientist (Gottweis et al. 2026) analysis is recorded in four such docs: hidden-ranking vs. advisory ranking ([L1](docs/design/2026-06-02-co-scientist-220-l1-hidden-ranking.md)), unapproved feedback propagation ([L2](docs/design/2026-06-02-co-scientist-221-l2-feedback-propagation.md)), which mechanisms transfer to ARS and which do not ([L3](docs/design/2026-06-02-co-scientist-222-l3-transfer-matrix.md)), and control-plane ownership — who may write, rank, or route ([L4](docs/design/2026-06-02-co-scientist-223-l4-control-plane-ownership.md)). The Kong (2026) auto-research analysis adds two: copilot vs. auto-research as a research-state-authority line ([L1](docs/design/2026-06-08-kong-255-l1-copilot-not-auto-research.md)) and advisory-on-wording vs. idea-generation ([L2](docs/design/2026-06-08-kong-255-l2-advisory-not-generation.md)); the autonomous mechanisms they reject are enumerated in [Rejected mechanisms](#rejected-mechanisms-autonomous-research-anti-patterns) above.

## Citing this tool

If you use ARS in your research, please cite it:

```
Wu, C.-I. (2026). Academic Research Skills for Claude Code (Version 3.14.0) [Computer software]. Zenodo. https://doi.org/10.5281/zenodo.20696614
```

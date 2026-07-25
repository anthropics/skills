---
name: ars-deep-research-team
runtime: codex-agent-team
enabled_when: "ARS_CODEX_FULL_RUNTIME=1 and ARS_CODEX_AGENT_TEAM=1"
source_workflow: "ars/deep-research/WORKFLOW.md"
---

# ARS Deep Research Team for Codex

Use for `deep-research` modes when full-runtime agent-team mode is explicitly
enabled. Otherwise, execute the roles inline from the same source prompts.

## Dispatch Shape

- `socratic` mode starts with `socratic_mentor_agent.md` and
  `research_question_agent.md`; it must not produce an outline or draft before
  the research question is precise.
- `lit-review` and `systematic-review` modes start with
  `bibliography_agent.md`, `source_verification_agent.md`, and
  `synthesis_agent.md`.
- `fact-check` mode starts with `source_verification_agent.md` and keeps
  verified / unverified / contradicted claims separate.
- `full` mode may parallelize bibliography, source verification, risk-of-bias,
  ethics, and devil's advocate work after the RQ brief is stable.

## Output Contract

Every agent work product must label evidence, inference, and recommendation.
Current facts and citations require verification against authoritative sources
or an explicit unverified marker.

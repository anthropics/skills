# WE.[SUITE INDEX] — Pro Se Formatter Suite

This index is intentionally duplicated into every formatter-suite skill so models can find it from any entrypoint.

## WE.[SKILL ORDER] (high-level)

1) pro-se-formatter-map
2) pro-se-formatter-taxonomy
3) part-formatters (existing skills like `ninth-circuit-cover`, `declaration-builder`, etc.)
4) utilities (merge, TOC, TOA)

## WE.[SKILLS IN THIS SUITE] (one topic each)

- pro-se-formatter-map — suite read-order + framework map
- pro-se-formatter-taxonomy — filing_types (+ default headings) + rules workspace template
- docx-merge-parts — merges produced parts into one package (planned)
- docx-table-of-contents — generates/updates TOC from headings (planned)
- docx-table-of-authorities — generates/updates TOA (planned)
- case-stage-tracker — tracks litigation stages + required deliverables (planned)

## WE.[COMPOSITION RULE]

- Keep one document part per skill.
- The orchestrator chooses a filing type, then selects the needed part skills, then merges.

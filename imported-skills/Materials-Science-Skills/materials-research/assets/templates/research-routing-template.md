# Research Routing Template

Use this template to plan a materials research workflow.

## Task Detection

| Axis | Question | Default |
|---|---|---|
| task | What deliverable does the user want? | manuscript-writing |
| paper_stage | Where is the manuscript in the lifecycle? | idea |
| workflow_mode | Single task, full pipeline, or review loop? | single-task |
| domain | Which materials field? | civil-generic |
| journal | Which target journal? | generic |

## Routing Checklist

- [ ] Task axis detected from user triggers
- [ ] Paper stage identified
- [ ] Domain fragment loaded
- [ ] Journal fragment loaded (if named)
- [ ] Companion skills listed for handoff
- [ ] Evidence contract loaded from `_shared`

## Companion Skill Handoff

| Deliverable | Skill | Handoff Artifact |
|---|---|---|
| Evidence-chain notes | materials-reader | reader-package |
| Citation matrix | materials-citation | citation_handoff.csv |
| Manuscript section | materials-writing | section draft |
| English polishing | materials-polishing | polished text |
| Reviewer response | materials-response | response package |
| Pre-submission audit | materials-reviewer | review report |
| HTML deck | materials-html-deck | retained HTML deck directory |
| Figures | materials-figure | figure package |
| FAIR data | materials-data | data package |

## Quality Gates

- [ ] Claim stays inside evidence boundary
- [ ] No overclaim from performance to mechanism
- [ ] Journal format requirements checked
- [ ] Reviewer-risk flagged for weak evidence

# Cross-Agent Quality Alignment — Full Definitions

Unified definitions to prevent inconsistency across agents.

| Concept | Definition | Applies To |
|---------|-----------|------------|
| **Peer-reviewed** | Published in a journal with formal peer review process (editorial review alone does not qualify). Conference proceedings count only if explicitly peer-reviewed | bibliography_agent, source_verification_agent |
| **Currency Rule** | Default: published within 5 years. Override by domain: CS/AI = 3 years, History/Philosophy = 20 years, Law = depends on jurisdiction changes. Seminal works exempt regardless of age | bibliography_agent, ethics_review_agent |
| **CRITICAL severity** | IRON RULE: Issue that, if unresolved, would invalidate a core conclusion or constitute academic misconduct. Requires immediate resolution before pipeline can proceed | All agents |
| **Source Tier** | tier_1 = top-quartile peer-reviewed journal; tier_2 = other peer-reviewed; tier_3 = academic but not peer-reviewed; tier_4 = grey literature | bibliography_agent, source_verification_agent |
| **Minimum Source Count** | full = 15+, quick = 5-8, lit-review = 25+, systematic-review = all eligible (no limit), fact-check = 3+ per claim | bibliography_agent |
| **Verification Threshold** | 100% DOI check + 50% WebSearch spot-check | source_verification_agent, ethics_review_agent |

> **Cross-Skill Reference**: See `shared/handoff_schemas.md` for inter-stage data exchange formats.

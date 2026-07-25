# Project Scorecard — Condensed Rubrics

Six dimensions, each scored 1-5. These condensed rubrics focus on the score boundaries that drive most decisions (3/4/5). For the full prose rubrics, see rootnode-project-audit if available.

## Scoring Anchors

### 1. Identity Precision

| Score | Anchor |
|---|---|
| 5 | Named expert role with domain vocabulary, calibrated depth, and distinctive voice. Output is clearly shaped by the identity — remove it and quality degrades. |
| 4 | Clear role with domain awareness. Output reflects expertise but voice or depth calibration could be sharper. |
| 3 | Generic helper identity or role stated but not operationalized (e.g., "You are a marketing expert" with no domain vocabulary, audience calibration, or expertise markers). |
| 2 | Vague or contradictory identity. Multiple roles without switching logic. |
| 1 | No identity defined, or identity is a single generic sentence with no behavioral implications. |

**Key boundary (3→4):** Does the identity change how Claude reasons and writes, or is it just a label?

### 2. Instruction Clarity

| Score | Anchor |
|---|---|
| 5 | Every rule is specific, testable, non-contradictory, and positioned for attention (critical rules early, scoped countermeasures where needed). No ambiguous conditionals. |
| 4 | Rules are clear and mostly well-positioned. Minor ambiguities exist but don't cause observable output problems. |
| 3 | Mix of clear and vague rules. Some contradictions or redundancies. Rules may be poorly ordered (critical rules buried). |
| 2 | Predominantly vague ("be thorough," "use good judgment") or contradictory rules. |
| 1 | No behavioral rules, or rules are so vague they provide no constraint. |

**Key boundary (3→4):** Are the rules testable — could you check whether Claude followed each one?

### 3. Knowledge & Context Architecture

| Score | Anchor |
|---|---|
| 5 | Knowledge files are well-structured, clearly routed from CI, complementary to (not redundant with) CI content. Memory used for orientation facts, not duplicated instructions. Context budget used efficiently. |
| 4 | Good structure with minor issues — a routing gap, slight redundancy between CI and KF, or one file that could be split. |
| 3 | Knowledge files exist but routing is implicit, structure is inconsistent, or significant content belongs in a different layer. |
| 2 | Knowledge files are dumped content without structure or routing. Or CI contains large reference blocks that should be knowledge files. |
| 1 | No knowledge files when they're clearly needed, or knowledge files that contradict CI. |

**Key boundary (3→4):** Does the CI explicitly route Claude to the right knowledge file for the right task?

### 4. Mode Design

| Score | Anchor |
|---|---|
| 5 | Modes are genuinely distinct workflows with clear triggers, different outputs, and appropriate behavioral shifts. Mode selection is explicit, not inferred. |
| 4 | Modes are distinct and well-triggered. Minor overlap exists but doesn't cause confusion. |
| 3 | Modes exist but triggers are ambiguous, outputs overlap significantly, or mode-switching logic is unclear. |
| 2 | Modes are named but functionally identical, or mode boundaries are so blurred that Claude frequently picks the wrong one. |
| 1 | No modes when the Project clearly needs them, or a single undifferentiated mode handling everything. |

**Key boundary (3→4):** Would Claude reliably select the correct mode from a user's natural language request?

**N/A:** Score as N/A if the Project genuinely doesn't need modes (single-purpose Projects). Do not penalize.

### 5. Output Standards

| Score | Anchor |
|---|---|
| 5 | Format specifications are precise (structure, length guidance, section requirements), positioned where Claude processes them (near output instructions, not buried in preamble), and include quality criteria the output must meet. |
| 4 | Good format specs with minor gaps — length guidance missing for some sections, or quality criteria implied but not explicit. |
| 3 | Format is specified but loosely ("write a report," "use markdown"). No per-section guidance. Quality criteria absent. |
| 2 | Contradictory format instructions, or format specified in one place but overridden elsewhere. |
| 1 | No output format specified when the Project produces structured deliverables. |

**Key boundary (3→4):** Does the format spec tell Claude how long each section should be and what quality bar it must meet?

### 6. Behavioral Calibration

| Score | Anchor |
|---|---|
| 5 | Domain-relevant Claude tendencies identified and countered with specific, scoped countermeasures. Countermeasures are positioned at point of use, not in a generic list. Evidence of model-specific tuning. |
| 4 | Key tendencies addressed. Countermeasures are present but could be more precisely scoped or better positioned. |
| 3 | One or two generic countermeasures present ("be concise," "avoid lists") but not domain-calibrated. Major tendencies for the domain are unaddressed. |
| 2 | No countermeasures, or countermeasures that address tendencies irrelevant to the domain while missing relevant ones. |
| 1 | No behavioral calibration at all, or calibration that would make output worse (e.g., encouraging verbosity in a domain that needs concision). |

**Key boundary (3→4):** Are the countermeasures specific to Claude's actual tendencies in this domain, or are they generic writing advice?

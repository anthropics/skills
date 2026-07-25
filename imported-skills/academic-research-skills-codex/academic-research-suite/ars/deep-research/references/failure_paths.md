# Failure Paths — Research Pipeline Failure Path Map

## Overview

This document lists all failure scenarios that may be encountered across all modes of the deep-research skill, along with their detection conditions, user notification messages, handling steps, and recovery paths. The purpose is to ensure every failure scenario has a clear handling strategy, preventing users from reaching a dead end.

---

## Failure Path Summary

| # | Failure Scenario | Affected Modes | Severity | Handling Strategy |
|---|---------|---------|---------|---------|
| F1 | RQ cannot converge | full, socratic | Medium | Narrow scope / provide candidate RQs |
| F2 | Insufficient literature | full, quick, lit-review | High | Expand search strategy |
| F3 | Methodology mismatch | full | High | Return to Phase 1 |
| F4 | Devil's Advocate CRITICAL | full | Critical | STOP + correct |
| F5 | Ethics BLOCKED | full, review | Critical | STOP + remediation path |
| F6 | Socratic dialogue does not converge | socratic | Medium | Switch to full mode |
| F7 | User abandons mid-process | all | Low | Save progress |
| F8 | Only Chinese-language literature available | full, lit-review | Medium | Switch search strategy |
| F9 | All source quality below threshold | full, fact-check | High | Downgrade or expand sources |
| F10 | Conclusions inconsistent with evidence | full | High | Return to Phase 3 |
| F11 | Revision loop exceeds limit | full | Medium | Force-complete + limitation list |
| F12 | Interdisciplinary bridging failure | full | Low | Revert to single discipline |

---

## Detailed Failure Paths

### F1: Research Question Cannot Converge

**Affected Modes**: `full` (Phase 1), `socratic` (Layer 1)
**Severity**: Medium

**Trigger Conditions**:
- `full` mode: research_question_agent interaction exceeds 3 rounds, user still cannot determine the RQ
- `socratic` mode: Layer 1 exceeds 5 rounds, user repeatedly revises without a clear direction

**User Notification Message**:
> I notice we've been discussing for a while, but the research question hasn't converged to a clear direction yet. This is perfectly normal — sometimes the question itself is the hardest part. Let me offer a few possible directions to see which one is closest to your thinking.

**Handling Steps**:
1. Compile key topics discussed and user-expressed preferences
2. Produce 3 candidate RQs, each with a brief explanation and rough FINER assessment
3. Ask the user to select the closest one as a starting point
4. If the user still cannot choose → suggest doing a `lit-review` mode to explore the literature first, then return

**Recovery Paths**:
- Select a candidate RQ → continue the original workflow
- Do lit-review → restart RQ clarification after the literature review is complete
- User redescribes on their own → restart Phase 1 / Layer 1

---

### F2: Insufficient Literature

**Affected Modes**: `full` (Phase 2), `quick`, `lit-review`
**Severity**: High

**Trigger Conditions**:
- bibliography_agent finds < 5 usable sources after standard search strategy
- After excluding quality-unqualified sources, < 3 remain

**User Notification Message**:
> With the current search strategy, I found only limited relevant literature. This could mean: (1) this is a very new research area; (2) the search keywords need adjustment; (3) the research question scope may need refinement. Let me try expanding the search strategy.

**Handling Steps**:
1. Expand search keywords (synonyms, broader terms, related concepts)
2. Expand database scope (add grey literature, policy reports, working papers)
3. Relax time range (from past 5 years to past 10 years)
4. Try keywords from adjacent disciplines
5. If still insufficient → suggest the user consider adjusting the RQ or accept this as an exploratory study

**Recovery Paths**:
- Expanded search yields sufficient literature → continue original workflow
- Accept as exploratory research → adjust report positioning, emphasize the study's pioneering nature
- Adjust RQ → return to Phase 1

---

### F3: Methodology Mismatch

**Affected Modes**: `full` (Checkpoint 1)
**Severity**: High

**Trigger Conditions**:
- devils_advocate_agent at Checkpoint 1 determines that the methodology proposed by research_architect_agent cannot answer the RQ produced by research_question_agent
- There is a logical gap between the methodology and the RQ

**User Notification Message**:
> Devil's Advocate found an important issue in the methodology review: your research question asks "why," but your method design can only answer "whether." Let's go back and adjust — here are three possible directions...

**Handling Steps**:
1. Clearly state the gap between the RQ type (descriptive/comparative/causal/evaluative) and the method's capability
2. Provide 3 alternative method suggestions, each with pros and cons
3. Confirm whether the RQ needs adjustment to match a feasible method
4. Re-execute research_architect_agent

**Recovery Paths**:
- Select an alternative method → regenerate Methodology Blueprint → Checkpoint 1 re-review
- Adjust RQ → return to research_question_agent → redo Phase 1
- Maximum 2 retries; if still mismatched on the 3rd attempt → suggest the user consult their advisor

---

### F4: Devil's Advocate CRITICAL

**Affected Modes**: `full` (any Checkpoint)
**Severity**: Critical

**Trigger Conditions**:
- devils_advocate_agent finds a Critical severity issue at any Checkpoint
- Includes: fatal logical flaws, core assumptions that cannot hold, evidence contradicting conclusions

**User Notification Message**:
> STOP — Devil's Advocate found a critical issue that must be resolved before continuing:
> [Specific issue description]
> This is not an issue that can be ignored, as it fundamentally affects the research's validity.

**Handling Steps**:
1. Fully present the Critical issue's description, impact, and suggested correction direction
2. Pause the workflow; do not allow advancement to the next Phase
3. Wait for user response or correction
4. After user correction → re-execute the Checkpoint
5. 2 consecutive CRITICALs → suggest the user fundamentally rethink the research direction

**Recovery Paths**:
- User corrects the issue → re-execute Checkpoint → continue after PASS
- User chooses to modify the RQ/method → return to the corresponding Phase
- User abandons the direction → enter F7 workflow

---

### F5: Ethics BLOCKED

**Affected Modes**: `full` (Phase 5), `review`
**Severity**: Critical

**Trigger Conditions**:
- ethics_review_agent determines BLOCKED
- Integrity violations only — see the authoritative list in `agents/ethics_review_agent.md` §"Blocking Conditions" (fabricated references, missing AI disclosure, plagiarism, systematic source misrepresentation, concrete harm-enabling specifics without safeguards; human subjects with no IRB plan is **CONDITIONAL**, not BLOCKED).
- **NOT a trigger**: dual-use risk and politically/institutionally sensitive subject matter. Dual-use is advisory (routes to a Responsible Use Statement, never to BLOCKED — see `references/ethics_checklist.md` §3). Subject matter alone never blocks.

**User Notification Message**:
> Ethics Review flagged a Critical integrity concern that needs your confirmation before delivery:
> [Specific issue list]
> You can accept the suggested fix, **override with your reasoning** (recorded in the Ethics Decision Log), or revise. This is a one-time confirmation, not a veto. Suggested remediation paths:

**Handling Steps**:
1. List all flagged reasons, each with specific remediation suggestions
2. Distinguish between remediable (e.g., add informed consent statement) and irremediable (e.g., research design inherently has integrity problems)
3. Remediable issues → provide modification suggestions → re-review after user confirmation
4. Irremediable issues → suggest fundamental redesign of the research
5. User may override any flag with recorded reasoning → log to the Ethics Decision Log and proceed; do not re-block an overridden item

**Recovery Paths**:
- Fix ethical issues → re-execute ethics_review_agent → continue after CLEARED
- Modify research design → return to Phase 1
- Issues are irremediable → suggest abandoning this research direction, provide alternative direction suggestions

---

### F6: Socratic Dialogue Does Not Converge

**Affected Modes**: `socratic`
**Severity**: Medium

**Trigger Conditions**:
- Dialogue exceeds 10 rounds, user still vacillating between different directions
- Extracted INSIGHTs < 3

**User Notification Message**:
> We've explored several directions, each with its own value. However, I notice we've been going back and forth between a few directions — this may mean you have multifaceted interests in this topic, but it can also make the research hard to focus. Would you like to:
> (A) Continue the Socratic dialogue, but focus on [the most promising direction] you just mentioned?
> (B) Switch to full mode, and let my team help you systematically explore and converge?
> (C) Take a pause, think it over, and come back later?

**Handling Steps**:
1. Compile currently extracted INSIGHTs
2. Identify the 1-2 directions with the most convergence potential
3. Provide 3 options (continue with focus / switch mode / pause)
4. If user chooses to continue but still hasn't converged by round 15 → auto-compile + end

**Recovery Paths**:
- Continue with focus → restrict discussion scope, converge within 5 rounds
- Switch to full mode → pass extracted INSIGHTs to research_question_agent
- Pause → save INSIGHT list; user can re-enter at any time

---

### F7: User Abandons Mid-Process

**Affected Modes**: All modes
**Severity**: Low

**Trigger Conditions**:
- User explicitly states they don't want to continue ("never mind," "I quit," "too complicated")
- User abandons after a long period of non-response

**User Notification Message**:
> No problem. I've saved the current progress. Here's a summary of what we've accomplished so far:
> [List of completed stages and outputs]
> You can re-enter at any time by saying "continue the previous research," and we'll pick up where we left off.

**Handling Steps**:
1. Save all outputs from the current stage (RQ Brief, INSIGHTs, Bibliography, etc.)
2. Produce a progress summary
3. Provide instructions for re-entry

**Recovery Paths**:
- User says "continue the previous research" → load saved outputs, continue from where interrupted
- User starts over → entirely new workflow

---

### F8: Only Chinese-Language Literature Available

**Affected Modes**: `full` (Phase 2), `lit-review`
**Severity**: Medium

**Trigger Conditions**:
- English academic database searches (Web of Science, Scopus, PubMed, etc.) yield empty or very few results
- The topic is strongly localized (e.g., Taiwan-specific policy, regulations, institutional systems)

**User Notification Message**:
> English-language literature on this topic is very limited, but Chinese-language literature resources are abundant. I will adjust the search strategy to include Chinese academic databases. Please note that citation conventions for Chinese-language literature in international publications may differ.

**Handling Steps**:
1. Switch search strategy to Chinese academic databases (Airiti Library, National Digital Library of Theses and Dissertations in Taiwan, CNKI)
2. Re-search using Chinese keywords
3. Note the language distribution of the literature in the report
4. If the user needs an English report → provide suggestions for English citation format of Chinese literature
5. If the user needs to publish internationally → suggest finding comparable international cases

**Recovery Paths**:
- Chinese literature is sufficient → continue workflow with clear language annotations
- User needs international publication → suggest adjusting RQ to add a comparative perspective

---

### F9: All Source Quality Below Threshold

**Affected Modes**: `full` (Phase 2), `fact-check`
**Severity**: High

**Trigger Conditions**:
- source_verification_agent rates all found sources as Level V or below
- No peer-reviewed sources

**User Notification Message**:
> The overall quality of currently found sources is low, lacking high-quality peer-reviewed research. This may indicate an emerging field, or the search strategy may need adjustment. I suggest we consider...

**Handling Steps**:
1. Expand source types (add policy reports, white papers, official statistics)
2. Lower the threshold but clearly annotate quality levels
3. Reposition the report as "preliminary exploration" rather than "systematic review"
4. Add an "Evidence Quality Limitations" section to the report

**Recovery Paths**:
- Find sufficient alternative sources → continue workflow with clear quality annotations
- Cannot find qualified sources → suggest the user consider conducting primary research

---

### F10: Conclusions Inconsistent with Evidence

**Affected Modes**: `full` (Phase 5, Checkpoint 3)
**Severity**: High

**Trigger Conditions**:
- editor_in_chief_agent or devils_advocate_agent finds in Phase 5 that report conclusions exceed the scope supported by the evidence

**User Notification Message**:
> The review found that some conclusions in the report go beyond what the evidence supports. Specifically:
> [List of issues]
> I will return for revision to ensure every conclusion has corresponding evidence support.

**Handling Steps**:
1. Flag all "over-inferred" conclusions
2. For each flag: (a) weaken the conclusion to match the evidence, or (b) supplement with additional evidence
3. Re-execute Checkpoint 3

**Recovery Paths**:
- Revision successful → complete Phase 6
- Issues remain after revision → 2nd revision round
- Issues remain after 2 revisions → convert issues to a "Research Limitations" section

---

### F11: Revision Loop Exceeds Limit

**Affected Modes**: `full` (Phase 6)
**Severity**: Medium

**Trigger Conditions**:
- Phase 6 revision has been executed 2 times (maximum), with unresolved Major issues remaining

**User Notification Message**:
> After two rounds of revision, the following issues have been resolved: [resolved list]. However, the following issues remain unresolved due to inherent research limitations: [unresolved list]. These will be listed in the "Acknowledged Limitations" section. The report is now the best version achievable under current conditions.

**Handling Steps**:
1. Compile resolved and unresolved issues
2. Convert unresolved Major issues into the "Acknowledged Limitations" section
3. Deliver the final report

**Recovery Paths**:
- User accepts → deliver the report
- User does not accept → suggest redesigning the research from Phase 1

---

### F12: Interdisciplinary Bridging Failure

**Affected Modes**: `full`
**Severity**: Low

**Trigger Conditions**:
- synthesis_agent attempts interdisciplinary integration but cannot find meaningful connections
- Conceptual frameworks from different disciplines cannot be reconciled

**User Notification Message**:
> I attempted to integrate perspectives from [Discipline A] and [Discipline B], but these two disciplines' understanding frameworks for this phenomenon differ substantially. Forcing integration may actually blur the focus. I suggest we center on the [primary discipline] framework, and mention other disciplines' perspectives in the discussion section as reference.

**Handling Steps**:
1. Select the primary disciplinary framework as the analytical foundation
2. Present other disciplinary perspectives in an "Alternative Perspectives" or "Interdisciplinary Insights" section
3. Do not force integration of irreconcilable frameworks

**Recovery Paths**:
- Focus on a single framework → continue workflow
- User insists on interdisciplinary → suggest switching to mixed-methods or narrative review

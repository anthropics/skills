# Business Strategy Output Formats

Four output format specifications for business strategy deliverables. Each provides a complete `<output_format>` XML block that you paste into your Claude prompt to control the deliverable structure.

## Table of Contents

- [Investment Case](#investment-case)
- [Board Narrative](#board-narrative)
- [Market Entry Strategy](#market-entry-strategy)
- [Strategic Options Assessment](#strategic-options-assessment)

---

## Investment Case

**Use when:** You need to make a formal case for a significant capital allocation — an acquisition, a major initiative, a new business launch, or an expansion investment. The audience is typically an investment committee, board, or senior leadership team with fiduciary responsibility.

**Pairs well with:** M&A / Corporate Development Advisor identity. Due Diligence reasoning method.

```xml
<output_format>
Structure as an investment case:

Executive Summary: (1 paragraph) The investment being proposed, the total capital required, the expected return, and the strategic rationale in one clear statement. A reader who reads only this paragraph should understand what is being asked and why.

Strategic Rationale: (2-3 paragraphs) Why this investment advances the organization's strategic position. What capability, market access, or competitive advantage does it create? How does it fit the broader portfolio? Address why now — what makes the timing right or what cost is incurred by delay.

Financial Analysis: (2-3 paragraphs plus a summary table) The financial case. Include: total investment required (with phasing), expected returns (with timeline), key financial assumptions, and sensitivity analysis showing how returns change under pessimistic and optimistic scenarios. Present a summary table with the base case, upside case, and downside case.

Risks and Mitigants: (2-3 paragraphs) The material risks to the investment thesis. For each: the risk, its likelihood and impact, and the specific mitigation approach. Include at least one scenario where the investment fails and explain what the exit or write-down looks like.

Alternatives Considered: (1-2 paragraphs) What other approaches were evaluated (including doing nothing) and why this investment is the preferred path. This demonstrates rigor and preempts questions about whether other options were explored.

Implementation Requirements: (1-2 paragraphs) Key execution requirements — team, timeline, dependencies, and governance. Not a full implementation plan, but enough to demonstrate that the investment is executable.

Ask: (1 paragraph) The specific approval or commitment being requested, with any conditions or staged decision points.

Total length: 1500-2500 words. Write for decision-makers who will scrutinize assumptions and challenge the return projections. Financial claims without explicit assumptions lose credibility.
</output_format>
```

**Watch for:** Claude may produce an investment case that is implicitly advocacy — building the case for "yes" rather than presenting an honest assessment. If the Risks section feels perfunctory or the sensitivity analysis shows only narrow downside, add: *"The downside case should represent a realistic bad outcome, not a slightly-worse-than-base scenario. Decision-makers need to understand the real exposure, not a sanitized version."*

Also watch for financial analysis that uses invented numbers when specific data was not provided. Add to your prompt's `<context>` section actual financials, or add: *"Use only provided financial data. Where data is unavailable, state your assumptions explicitly and label projections as estimates."*

---

## Board Narrative

**Use when:** You need the written narrative that accompanies a board presentation — the structured story for a governance audience. Designed to be read alongside or in preparation for a board meeting, with the specific rhythm board members expect: context first, then assessment, then ask. The audience has fiduciary responsibility, limited time, and typically reads materials in advance.

**Pairs well with:** Corporate Strategist identity. Portfolio Strategy reasoning method.

```xml
<output_format>
Structure as a board narrative:

Situation Overview: (2-3 paragraphs) The current state of the business or initiative being discussed. What has happened since the last board discussion of this topic? Include the key metrics or milestones that define the current position. Board members should be able to orient without reviewing prior materials.

Performance Assessment: (2-3 paragraphs) How the business or initiative is performing against plan, against prior period, and against relevant external benchmarks. Be direct about where performance is strong, where it is lagging, and what is driving the variance. Do not bury negative performance in qualifications.

Key Issues and Developments: (2-4 paragraphs) The most important developments, decisions, or challenges that require board awareness or input. Prioritize by materiality. For each issue: what it is, why it matters, what management's assessment or proposed approach is, and what input is sought from the board.

Forward Outlook: (1-2 paragraphs) What management expects over the next period. Include key assumptions behind the outlook and the leading indicators that would signal the outlook is off track.

Management Recommendations or Asks: (1 paragraph) If a decision or approval is needed, state it clearly. If the update is informational, state that the purpose is awareness and no decision is required.

Total length: 1000-1800 words. Write in a tone appropriate for a governance audience — substantive, direct, and free of promotional language. Board members value candor over optimism.
</output_format>
```

**Watch for:** Claude may default to a tone that is either too promotional (spinning results positively) or too detached (presenting data without assessment). Board narratives require management to take a position — "here is what we think this means and here is what we recommend." If the output lacks a clear management perspective, add: *"Write from management's perspective. Present data objectively, but provide clear management assessment and recommendations. The board wants to understand what management thinks, not just what happened."*

Also watch for the narrative being too long — board members process large volumes of material. Enforce the length constraint strictly.

---

## Market Entry Strategy

**Use when:** You need a comprehensive plan for entering a new market, customer segment, or geography. This format specifically addresses the strategic logic, market mechanics, and go-to-market design required for a market entry decision. Combines strategic analysis with operational planning.

**Pairs well with:** Management Consultant or Corporate Strategist identity. Business Model Analysis reasoning method.

```xml
<output_format>
Structure as a market entry strategy:

Opportunity Definition: (1-2 paragraphs) The market or segment being entered, its size and growth trajectory, and why it represents an attractive opportunity for this organization specifically. Avoid generic market descriptions — focus on why this market is attractive given the organization's capabilities and position.

Market Landscape: (2-3 paragraphs) How this market works. Who are the established players, what do customers value, how are purchase decisions made, and what are the barriers to entry? Identify the specific competitive dynamics that a new entrant must navigate.

Entry Strategy: (2-3 paragraphs) The recommended approach. Organic build, acquisition, partnership, or hybrid? Which segment to target first and why? What is the beachhead — the initial position from which to expand? Explain why this entry path was chosen over the alternatives.

Go-to-Market Design: (2-3 paragraphs) How the offering will reach customers. Pricing approach, distribution channels, sales model, and the key messages that differentiate from incumbents. Be specific about the first 6-12 months.

Resource Requirements and Investment: (1-2 paragraphs) What team, capital, and capabilities are needed. Include the investment required before revenue begins and the expected timeline to breakeven or target economics.

Key Risks and Decision Points: (1-2 paragraphs) The highest-impact risks to the entry and the decision points where the organization should evaluate whether to continue, pivot, or exit. Define the kill criteria — what evidence would indicate the entry is failing and should be stopped?

Total length: 1200-2000 words. Write for a leadership team deciding whether to commit resources. The strategy should be specific enough to execute but not so detailed that it becomes a project plan.
</output_format>
```

**Watch for:** Claude may produce a market entry strategy that is too optimistic about timeline and adoption — underestimating how long it takes to gain traction in a new market. If the plan assumes fast customer acquisition without evidence, add: *"Base your adoption timeline on realistic benchmarks. Most market entries take longer and cost more than projected. Build your plan around the realistic case, not the optimistic case."*

Also watch for the strategy being generic enough to apply to any company entering any market — the Opportunity Definition and Entry Strategy sections should be deeply specific to this organization's strengths and this market's dynamics.

---

## Strategic Options Assessment

**Use when:** You need to present and analyze 2-3 distinct strategic paths for a major directional decision. Provides deeper narrative analysis of each path than a scored decision matrix — where it leads, what it requires, and what it risks. Use when the options are genuinely different strategies, not just variations of the same approach.

**Pairs well with:** Corporate Strategist or Management Consultant identity. Portfolio Strategy or Business Model Analysis reasoning method.

```xml
<output_format>
Structure as a strategic options assessment:

Decision Context: (1-2 paragraphs) What decision is being made, what triggered it, and what constraints bound the options. Explain why the status quo is not tenable — what forces are creating the need to choose a direction?

Option Summaries: (1 paragraph each, for 2-3 options) A clear, concise description of each strategic path. Name each option descriptively (e.g., "Aggressive expansion via acquisition" rather than "Option A"). Each summary should make the option's logic immediately clear.

Detailed Analysis per Option: (2-3 paragraphs each) For each option, analyze:
- Strategic upside: What does this path achieve if it works? What position does it create?
- Execution requirements: What capabilities, resources, and timeline does it demand? What organizational changes are needed?
- Key risks: What are the most likely failure modes? What is the downside scenario?
- Reversibility: If this path is chosen and it does not work, what are the exit options and costs?

Comparative Assessment: (2-3 paragraphs) How the options compare on the dimensions that matter most for this decision. Where do options clearly separate? Where are they essentially equivalent? What is the single most important differentiating factor?

Recommendation: (1 paragraph) A clear recommendation with the primary reasoning. If two options are very close, state what additional information or development would break the tie. If the recommendation depends on an assumption, state it.

Total length: 1500-2500 words. Each option must receive genuinely balanced analysis — if the assessment clearly favors one option from the start, it is advocacy disguised as analysis. The recommendation belongs at the end, after the analysis has been presented fairly.
</output_format>
```

**Watch for:** Claude may generate "options" that are not genuinely distinct — a conservative version, a moderate version, and an aggressive version of the same underlying strategy. If the options differ only in degree rather than in kind, add: *"Each option must represent a structurally different strategic path — not just different levels of investment or aggression applied to the same approach. If two options are variants of the same strategy, replace one with a genuinely different direction."*

Also watch for the Comparative Assessment being a repeat of the per-option analysis rather than a synthesis. It should add new insight about how the options relate to each other, not just summarize what was already said.

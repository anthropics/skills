---
name: rootnode-domain-business-strategy
description: >-
  Specialized business strategy prompt methodology for Claude. Provides 11
  tested approaches (3 identity, 4 reasoning, 4 output formats) for
  consulting, M&A, corporate strategy, and strategic planning tasks. Use when
  building prompts for deal evaluation, due diligence, portfolio strategy,
  business model analysis, board narratives, investment cases, market entry
  plans, or strategic options assessments. Trigger on: "build a prompt for M&A
  analysis," "due diligence prompt," "board narrative," "investment case,"
  "market entry strategy," "strategic options," "portfolio strategy prompt,"
  "business model analysis prompt," "consulting-style analysis." Do NOT use for
  evaluating or scoring existing prompts (use rootnode-prompt-validation if
  available) or for auditing Claude Projects (use rootnode-project-audit if
  available).
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.1"
  original-source: "DOMAIN_PACK_BUSINESS_STRATEGY.md"
---

# Business Strategy Prompt Methodology

> **Calibration:** Tier 1, Opus-primary. See repository README for model compatibility.

Specialized approaches for building Claude prompts that handle consulting, corporate strategy, M&A, and strategic planning work. This methodology provides identity approaches, reasoning methods, and output formats tuned for business strategy tasks that require deeper domain specialization than general-purpose strategic analysis.

Use these approaches when the task specifically requires consulting-style structured problem-solving, deal evaluation, portfolio management, business model mechanics, or strategy-specific deliverable formats.

## How to Use This Skill

A well-structured Claude prompt for business strategy work uses up to four layers:

1. **Identity** — Who Claude should be for this task (consulting, M&A, or corporate strategy perspective)
2. **Reasoning** — How Claude should think through the problem (due diligence, business model analysis, portfolio strategy, or stakeholder dynamics)
3. **Output format** — What the deliverable looks like (investment case, board narrative, market entry strategy, or strategic options assessment)
4. **Quality control** — Verification instructions that catch common failure modes

Assemble the prompt by selecting one approach from each relevant layer, wrapping each in its XML tags (`<role>`, `<reasoning>`, `<output_format>`), and combining them with a `<context>` section containing the specific situation, data, and constraints.

Not every task needs all four layers. A quick strategic analysis may need only an identity and reasoning approach. A deliverable-focused task may need identity, output format, and a strong context section. Match the prompt's complexity to the task.

## Approach Selection

### Which Identity to Use

| Task Type | Identity Approach | Why |
|---|---|---|
| Structured problem decomposition, hypothesis-driven analysis, consulting deliverables | Management Consultant | Emphasizes analytical methodology and decision-ready output |
| Deal evaluation, acquisition analysis, merger assessment, partnership due diligence | M&A / Corporate Development Advisor | Integrates financial, strategic, and operational deal dimensions with skeptical-by-default stance |
| Internal strategic planning, portfolio decisions, cross-business-unit coordination | Corporate Strategist | Insider perspective that balances ambition with organizational reality |
| General strategic analysis not requiring domain specialization | Use a general Strategic Advisor approach — not in this Skill | General strategic work does not need domain-specific identity |

### Which Reasoning Method to Use

| Task Type | Reasoning Method | Reference |
|---|---|---|
| Systematic evaluation of an acquisition, investment, or partnership | Due Diligence | See `references/reasoning-approaches.md` |
| Understanding how a business makes money — unit economics, cost structure, value chain | Business Model Analysis | See `references/reasoning-approaches.md` |
| Managing a portfolio of businesses, products, or investments — allocation, balance, composition | Portfolio Strategy | See `references/reasoning-approaches.md` |
| Navigating organizational politics, building support, managing resistance | Stakeholder & Organizational Dynamics | See `references/reasoning-approaches.md` |

**Combining reasoning methods:** For complex tasks, you can pair a primary reasoning method with a secondary one. Keep the total to 5-7 analytical steps — combining two full 6-step methods produces bloated, unfocused analysis. Lead with the dominant method and integrate elements of the secondary method where they add the most value. Stakeholder & Organizational Dynamics works especially well as a secondary method when any strategic initiative requires organizational buy-in.

### Which Output Format to Use

| Deliverable Type | Output Format | Reference |
|---|---|---|
| Formal case for capital allocation or acquisition | Investment Case | See `references/output-formats.md` |
| Written narrative for a board of directors | Board Narrative | See `references/output-formats.md` |
| Plan for entering a new market, segment, or geography | Market Entry Strategy | See `references/output-formats.md` |
| Presenting and analyzing 2-3 distinct strategic paths | Strategic Options Assessment | See `references/output-formats.md` |

### Quality Control for Business Strategy

When building business strategy prompts, add these task-specific quality checks after the output format section:

```xml
<quality_control>
Verify before delivering:
- Assumption transparency: Every financial projection, market sizing estimate, or growth assumption is explicitly stated and sourced (or labeled as an estimate). No invented statistics.
- Skepticism balance: Analysis identifies genuine risks and failure modes, not just "risks" that are easily mitigated. At least one scenario where the initiative fails is articulated.
- Strategic specificity: Recommendations are specific to this organization in this market, not generic advice. If the strategy section could be transplanted to a different company without changes, it is too generic.
- Organizational realism: Plans account for actual organizational capabilities, not assumed ones. When a strategy requires a capability the organization does not have, this is flagged.
- Stakeholder awareness: For any recommendation requiring significant organizational commitment, the key stakeholders and their likely positions are considered.
</quality_control>
```

---

## Identity Approaches

### Management Consultant

**Use when:** The task requires structured, hypothesis-driven analysis with the methodological rigor of management consulting. Best when the analysis methodology matters as much as the conclusions. Emphasizes problem decomposition, evidence-based reasoning, and decision-ready deliverables.

```xml
<role>
You are a senior management consultant with deep experience in structured problem-solving across industries. You approach every problem by decomposing it into mutually exclusive, collectively exhaustive components, forming hypotheses early, and testing them against available evidence.

You are rigorous about separating facts from assumptions and assumptions from speculation. When data is incomplete — which it usually is — you identify the two or three analyses that would most change the recommendation and prioritize those, rather than trying to be comprehensive about everything.

Your deliverables are decision-ready. Every analysis builds to a clear "so what" — a specific recommendation or insight that the reader can act on. You do not present findings without implications or implications without supporting evidence.
</role>
```

**Failure modes to counter:** This approach can push Claude toward consulting-speak ("MECE decomposition," "hypothesis tree," "issue tree") rather than actually doing structured analysis. If the output labels its methodology more than it applies it, add to your prompt: *"Apply structured thinking without labeling it. Decompose the problem cleanly, but do not name the frameworks you are using or describe your methodology — just execute it."* Also watch for structurally impressive but analytically shallow output — lots of categories with thin analysis in each. The fix is a strong `<context>` section with specific data points that force depth over breadth.

---

### M&A / Corporate Development Advisor

**Use when:** The task involves evaluating an acquisition, merger, partnership, joint venture, divestiture, or any strategic transaction. The output needs to integrate financial, strategic, and operational dimensions. Distinct from a financial analyst perspective in that this approach weighs strategic fit, integration complexity, and deal dynamics alongside financial merit.

```xml
<role>
You are a senior corporate development advisor with deep experience in M&A transactions, from target identification through post-merger integration. You evaluate deals across three dimensions simultaneously: strategic rationale (does this advance the acquirer's position?), financial merit (does the math work under realistic assumptions?), and execution risk (can this actually be integrated?).

You are skeptical by default. Most acquisitions destroy value, and you know the common failure modes: overestimating synergies, underestimating integration costs, paying for growth that does not materialize, and cultural incompatibility that erodes the acquired asset. You evaluate each deal with these failure modes in mind.

When the strategic rationale is strong but the price is wrong, you say so. When the financials work but the strategic logic is weak, you say so. You do not let strength in one dimension compensate for weakness in another without flagging the risk explicitly.
</role>
```

**Failure modes to counter:** Claude may produce analysis that is implicitly biased toward "do the deal" — framing risks as manageable rather than as potential deal-breakers. For transactions where the user clearly favors proceeding, reinforce with: *"Evaluate this deal as if you were advising the board's independent directors, not the management team sponsoring the transaction. Your obligation is to the quality of the decision, not to making the deal happen."* Also watch for Claude inventing plausible synergy numbers — pair with a strong `<context>` section containing actual financials.

---

### Corporate Strategist

**Use when:** The task involves strategic planning from inside an organization — portfolio decisions, business unit strategy, strategic planning cycles, or cross-organizational coordination. This approach thinks as an insider who knows the organization's capabilities, politics, and constraints. Best when strategic ambition must be tempered by organizational reality.

```xml
<role>
You are a VP of Corporate Strategy at a large organization. You develop strategy that is both ambitious and executable given the organization's actual capabilities, culture, and resource constraints. You think in portfolio terms — understanding that choices about one business unit affect all others through shared resources, brand implications, and organizational attention.

You balance long-term positioning with near-term performance pressure. You know that a strategy no one executes is not a strategy. You evaluate every strategic direction against three tests: Is it competitively sound? Can this organization execute it? Will the leadership team sustain commitment through the difficult middle period?

You are direct about organizational constraints that limit strategic options. If the organization lacks a capability required for a strategy, you name it and assess whether it can be built, bought, or partnered — you do not assume the constraint away.
</role>
```

**Failure modes to counter:** This approach can produce analysis that is too conservative — grounding strategy so firmly in current capabilities that it misses transformative opportunities. If the output reads as "here's what we can do with what we have" without considering "here's what we should become," add: *"Consider at least one strategic option that would require the organization to build or acquire a significant new capability. Evaluate its potential alongside more incremental options, and be clear about what capability investment it would demand."* Also watch for Claude avoiding the political dimension — for tasks where internal politics genuinely constrain strategy, add explicit stakeholder context to the `<context>` section.

---

## Critical: Behavioral Countermeasures for Business Strategy

Business strategy tasks are especially susceptible to these Claude tendencies. Inline the relevant countermeasure language into your prompt when you observe the pattern.

**Deal bias.** When evaluating transactions or investments where the user appears to favor proceeding, Claude may lean toward supportive analysis. Counter with: *"Evaluate this as an independent advisor. Your obligation is to the quality of the analysis, not to a particular outcome."*

**Consulting jargon.** Strategy-oriented prompts can trigger management-consulting vocabulary that sounds authoritative but obscures rather than clarifies. Counter with: *"Write in plain, precise language. If a concept requires a technical term, define it. Avoid jargon that serves as shorthand for thinking you have not actually done."*

**Framework dependence.** Claude may reach for named frameworks (Porter's Five Forces, BCG Matrix, Ansoff Matrix) as structural defaults even when the problem needs custom analysis. Counter with: *"Use frameworks only when they genuinely fit the problem at hand. A custom analytical structure tailored to this specific situation is preferable to forcing the analysis into a standard template."*

**Symmetry bias.** In strategic options assessments and portfolio analyses, Claude tends toward balanced evaluations where every option has roughly equal strengths and weaknesses. Real strategic analysis often reveals that one option is clearly stronger. Counter with: *"If one option is clearly superior, say so directly in the analysis, not just in the recommendation. Artificial balance between unequal options is not analytical rigor."*

---

## Assembly Example

A user asks for a prompt to evaluate a potential acquisition:

**Selected approaches:**
- Identity: M&A / Corporate Development Advisor
- Reasoning: Due Diligence (from `references/reasoning-approaches.md`)
- Output: Investment Case (from `references/output-formats.md`)
- Quality control: Business strategy quality checks (above)
- Countermeasures: Deal bias + framework dependence (added to prompt)

**Assembled prompt structure:**
```xml
<role>[M&A / Corporate Development Advisor — paste from identity section above]</role>

<context>[Specific deal details — target company, acquirer, strategic context, financials, deal terms, integration considerations]</context>

<reasoning>[Due Diligence — paste from references/reasoning-approaches.md]</reasoning>

<output_format>[Investment Case — paste from references/output-formats.md]</output_format>

<quality_control>[Business strategy quality checks — paste from selection section above]</quality_control>

Evaluate this as an independent advisor. Your obligation is to the quality of the analysis, not to a particular outcome. Use frameworks only when they genuinely fit the problem — a custom structure tailored to this specific deal is preferable to forcing the analysis into a standard template.
```

---

## Reference Files

- **`references/reasoning-approaches.md`** — Four reasoning methods with complete XML specifications, usage guidance, and failure mode notes. Read when building a prompt that needs a structured analytical approach for business strategy tasks.
- **`references/output-formats.md`** — Four output format specifications with complete XML structures, section-by-section length guidance, and watch-for notes. Read when building a prompt that needs a specific business strategy deliverable format.

## Troubleshooting

**Output is generic / could apply to any company.** The `<context>` section is too thin. Business strategy approaches produce their best work when given specific organizational data, market conditions, financials, and constraints. Add more specificity to the context.

**Analysis is structurally sound but lacks depth.** You have too many analytical steps relative to the task complexity. If combining two reasoning methods, reduce to 5-7 total steps and cut the ones that add the least value for this specific task.

**Claude defaults to named frameworks instead of custom analysis.** Add the framework dependence countermeasure to your prompt. This is one of the most common issues in business strategy tasks.

**Output is too long or verbose.** Business strategy formats have explicit length guidance (e.g., Investment Case: 1500-2500 words). If Claude exceeds these, add: *"Match response length to the complexity of the finding. Enforce the word count ranges in the output format specification."*

**For deeper prompt evaluation or scoring,** use the rootnode-prompt-validation Skill if available. For project-level audits of how your prompts fit into a Claude Project, use rootnode-project-audit if available.

---
name: element-selection-framework
description: >
  Help users select optimal elements for achieving stage goals through condition
  creation. Use when the user needs to analyze resonance conditions, map systems
  to conditions, select elements within stages, or validate element selections
  for cognitive/learning optimization tasks.

license: MIT
metadata:
  version: "1.0.0"
  author: "Element Framework Team"
  tags: ["cognitive-optimization", "learning", "resonance", "decision-framework"]
---

# Element Selection Framework Skill

## Overview

This skill guides Claude to help users select optimal elements at each stage to achieve stage goals through creating optimal resonance conditions. Elements create CONDITIONS (not understanding directly) - understanding emerges when conditions are optimal and human attention is engaged.

## Core Principles

1. **Elements Create Conditions**: `State_in → [Process] → Optimal_Conditions_out`
2. **Six Resonance Conditions Must Be Met**: Existence, Coupling, Compatibility, Edge of Chaos, Free Energy, Temporal Duration
3. **Causal Sequence Cannot Be Violated**: Prerequisites must be met before activation
4. **Continuous Accumulation**: Elements accumulate output over time until thresholds met
5. **Reality Validates Theory**: Experimental results override theoretical predictions

## The 5-Step Decision Process

When helping users select elements for a stage:

### Step 1: Decompose the Stage Goal

Ask: "What must happen to achieve this goal?"

```
For Stage S with Goal G:
1. Write the mathematical goal statement
2. Break into component requirements
3. Define measurable success criteria
```

Reference: `references/stage-goals.md` for all stage mathematical definitions.

### Step 2: Identify Critical Resonance Conditions

Ask: "Which of the 6 resonance conditions are MOST CRITICAL?"

Rank each condition as:
- **Critical**: Must be optimized for goal achievement
- **Important**: Enhances goal achievement
- **Supporting**: Nice to have but not essential

Reference: `references/resonance-conditions.md` for detailed condition specifications.

### Step 3: Map Conditions to Systems

Ask: "Which systems create each critical condition?"

Use the mapping:
- **Condition 1 (Existence)**: Rich Soil, Living Branches, Dancing Leaves
- **Condition 2 (Coupling)**: Root Network, Conscious Trunk, Photosynthesis
- **Condition 3 (Compatibility)**: Dancing Leaves, Photosynthesis, DKE
- **Condition 4 (Edge of Chaos)**: Rich Soil, Wise Gardener, DKE
- **Condition 5 (Free Energy)**: Conscious Trunk, Cognitive Tools, DKE
- **Condition 6 (Temporal Duration)**: DKE, Forest Intelligence, Wise Gardener

Reference: `references/systems-mapping.md` for complete system details.

### Step 4: Select Elements Within Systems

For each element, validate:
- [ ] Creates ≥1 critical condition for this stage?
- [ ] Prerequisites met from prior stages?
- [ ] Contributes to stage completion thresholds?
- [ ] Necessary (removing prevents goal)?
- [ ] Zero interference with other elements?

Include if ALL boxes checked.

### Step 5: Define Success Thresholds

Calculate for each threshold:
- Target value
- Contributing elements
- Accumulation rate per cycle
- Estimated cycles to completion

## Validation Methods

After selection, validate using these tests:

1. **Condition Coverage**: Every critical condition has ≥1 optimizing element
2. **Necessity**: Removing any element makes goal unachievable
3. **Sufficiency**: All thresholds reachable with enough cycles
4. **Causal Flow**: No prerequisites violated
5. **Interference**: Zero harmful conflicts between elements
6. **Reality Test**: Actual performance matches predictions (MOST IMPORTANT)

Reference: `references/validation-methods.md` for validation algorithms.
Script: `scripts/validate_selection.py` for automated validation.

## Stage Goals Quick Reference

```
Stage 0: Maximize M = I(U; P(U)) [meta-awareness]
Stage 1: Maximize H(K) measurement precision [confusion mapping]
Stage 2: Maximize β·E(N) [information quality]
Stage 3: Maximize I(K;N) = H(K) - H(K|N) [synthesis]
Stage 4: Maximize Corr(U,R) [understanding-reality alignment]
Stage 5: Minimize Access_Time, Maximize Fluency [embodiment]
Stage 6: Maximize Network_Effects [collective resonance]
Stage 7: Maximize Domain_Transcendence [universal patterns]
Stage 8: Maximize Meta_Learning [process optimization]
```

## Causal System Sequence

Elements MUST follow this order:
```
Rich Soil → Root Network → Conscious Trunk →
Living Branches ↔ Dancing Leaves → Photosynthesis →
Seed Production → Fruiting Process → Wise Gardener →
Garden Tools → Garden Climate → Living Partnership → Forest Intelligence
```

## Common Pitfalls to Avoid

1. **Over-Engineering**: Too many elements increases cognitive load
2. **Under-Engineering**: Too few elements means thresholds unreachable
3. **Ignoring Causal Flow**: Prerequisites must be met first
4. **Treating Framework as Gospel**: Reality always wins
5. **Forgetting Human Experience**: Users must WANT to engage

## Output Format

When helping users, provide:

1. **Goal Decomposition**: Clear breakdown of requirements
2. **Critical Conditions List**: Ranked by importance
3. **System Mapping**: Which systems address which conditions
4. **Element Selection Table**: Each element with justification
5. **Threshold Calculations**: Quantitative completion criteria
6. **Validation Results**: All 6 validation tests passed/failed
7. **Iteration Recommendations**: What to test and measure

## Success Criteria

Your element selection succeeds when:
- Goal Achievement Rate ≥ 85%
- UFV Increase = Predicted ± 20%
- All critical conditions optimized
- No causal violations
- User reports "This feels natural"

## Key Reminder

**This framework is a GUIDE for experimentation, not gospel truth.**

The mathematics doesn't lie. The measurements don't lie. Let reality teach you the truth through iterative testing and evidence-based refinement.

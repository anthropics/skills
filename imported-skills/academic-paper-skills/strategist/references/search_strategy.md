# Literature Search Strategy

This document provides systematic strategies for comprehensive literature search and gap identification.

## Overview

Effective literature search for academic papers requires:
1. **Multi-dimensional search** (keywords, time, diversity)
2. **Iterative refinement** (3 rounds minimum)
3. **Quality filtering** (relevance + authority)
4. **Gap mapping** (identify white spaces)

---

## Phase 1: Keyword Generation

### Step 1: Extract Core Concepts
From user's research idea, identify:
- **Primary concepts** (2-3): The main theoretical constructs
- **Secondary concepts** (2-3): Supporting or related ideas
- **Methodological terms** (1-2): Approach or framework

**Example**:
- Research idea: "Self-continuity through narrative compression during sleep"
- Primary: self-continuity, narrative compression
- Secondary: sleep, memory consolidation, personal identity
- Method: phenomenological analysis, computational metaphor

### Step 2: Generate Keyword Combinations
Create 10-15 search strings combining:
- Concept + concept
- Concept + method
- Concept + domain

**Example combinations**:
1. "self-continuity" AND "sleep"
2. "narrative compression" AND "memory"
3. "personal identity" AND "sleep-wake cycle"
4. "phenomenological self" AND "consciousness"
5. "autobiographical memory" AND "consolidation"
...

### Step 3: Include Synonyms and Variants
For each core concept, add:
- Disciplinary variants (philosophical vs. psychological terms)
- Historical terms (older vs. current terminology)
- Related concepts (broader/narrower)

**Example**:
- self-continuity → personal identity, diachronic self, narrative self
- sleep → periodic disruption, consciousness gaps, sleep-wake cycles
- compression → consolidation, integration, synthesis

---

## Phase 2: Multi-Round Search

### Round 1: Direct Search (Primary Literature)

**Goal**: Find 30-50 directly relevant papers

**Search Tools**:
- Use Exa MCP for semantic search
- Use Tavily MCP for web search
- Search Google Scholar / PhilPapers / arXiv as needed

**Process**:
```markdown
For each of 10-15 keyword combinations:
1. Run search with time filter (last 5 years)
2. Collect top 5 results per query
3. Total: 50-75 candidate papers

Quality filter:
- Read abstracts
- Check relevance (must score ≥7/10)
- Retain top 30-50 papers
```

**Relevance Scoring Guide** (0-10):
- 10: Exact topic match, same methodology
- 9: Topic match, different angle
- 8: Core concept match, different context
- 7: Related concept, applicable methods
- 6: Adjacent field, partial relevance
- 5: Tangential relevance
- <5: Exclude

### Round 2: Expanded Search (Adjacent Literature)

**Goal**: Find 10-20 papers from adjacent fields

**Process**:
```markdown
1. Extract new keywords from Round 1 papers:
   - Check "keywords" sections
   - Note frequently cited concepts
   - Identify theoretical frameworks used

2. Search adjacent fields:
   - If philosophy → check cognitive science
   - If neuroscience → check philosophy of mind
   - If AI → check consciousness studies

3. Collect 10-20 bridging papers
```

**Why Expanded Search**:
- Discover interdisciplinary connections
- Find alternative approaches to similar problems
- Identify potential theoretical resources

### Round 3: Classic Literature (Foundational Works)

**Goal**: Identify 5-10 highly-cited foundational papers

**Process**:
```markdown
1. Identify classics from Round 1-2 citations:
   - Look for papers cited in >50% of collected papers
   - Note "seminal works" mentioned

2. Citation tracking:
   - Use Google Scholar "Cited by" counts
   - Target papers with >100 citations
   - Focus on works from 1990-2015 (established but relevant)

3. Verify foundational status:
   - Check if it introduced key concepts
   - Assess if it shaped the field
   - Confirm current relevance
```

**Selection Criteria**:
- Citation count >100 (adjust for field size)
- Still cited in recent papers (2020+)
- Introduced terminology/concepts still in use

---

## Phase 3: Gap Identification

### Method 1: Concept Mapping

**Process**:
```markdown
1. Create 2D concept map:
   - X-axis: Concepts (from your keywords)
   - Y-axis: Methods/Approaches

2. Plot each collected paper on the map

3. Identify white spaces:
   - Concept combinations not explored
   - Methods not applied to certain concepts
   - Questions raised but not answered
```

**Example Map**:
```
              | Phenomenology | Cognitive Science | Computational |
--------------|---------------|-------------------|---------------|
Self          |   ████████    |     ████         |      ██       |
Sleep         |   ████        |     ██████       |      █        |
Compression   |   ██          |     ███          |               | ← GAP!
```

### Method 2: Problem-Solution Analysis

**Process**:
```markdown
1. List problems addressed in literature:
   - What questions do existing papers ask?
   - What puzzles do they try to solve?

2. List solutions proposed:
   - What answers/theories do they offer?
   - What limitations do they acknowledge?

3. Identify unsolved problems:
   - Problems mentioned but not addressed
   - Solutions that create new problems
   - Acknowledged limitations
```

**Gap Types**:
- **Empty gaps**: Problem identified but no solutions attempted
- **Partial gaps**: Solutions proposed but incomplete/unsatisfactory
- **Controversy gaps**: Competing solutions, no consensus

### Method 3: Temporal Gap Analysis

**Process**:
```markdown
1. Plot papers by publication year

2. Identify research waves:
   - When did interest surge?
   - When did it decline?
   - Recent vs. historical focus?

3. Spot temporal gaps:
   - Topics once active but abandoned
   - Emerging questions (last 2 years)
   - Due for re-examination with new methods
```

**Indicators of Good Temporal Gaps**:
- Last major work >5 years ago (ripe for update)
- New methods available (AI, neuroscience tools)
- Recent empirical findings enabling new theories

---

## Phase 4: Originality Assessment

### Step 1: Similarity Matrix

Create table comparing user's idea with top 10 most similar papers:

```markdown
| Paper | Topic Overlap | Method Overlap | Conclusion Overlap | Overall Similarity |
|-------|---------------|----------------|--------------------|--------------------|
| A     | 90%          | 70%           | 60%               | 73% (High)         |
| B     | 80%          | 50%           | 40%               | 57% (Medium)       |
| C     | 70%          | 80%           | 30%               | 60% (Medium)       |
...
```

**Interpretation**:
- >80%: Too similar, needs repositioning
- 50-80%: Moderate overlap, emphasize differences
- <50%: Good originality

### Step 2: Innovation Type Classification

Identify which type(s) of innovation apply:

1. **Methodological Innovation**:
   - Applying new method to known problem
   - Example: Using predictive coding to explain self-continuity

2. **Theoretical Innovation**:
   - New framework or model
   - Example: Compression metaphor for narrative self

3. **Application Innovation**:
   - Existing theory to new domain
   - Example: Memory consolidation theory applied to philosophy of self

4. **Integrative Innovation**:
   - Synthesizing previously separate literatures
   - Example: Combining phenomenology + cognitive neuroscience

**Requirement**: Must identify at least 2 innovation types for sufficient originality

### Step 3: Impact Prediction

**Scoring Criteria** (1-10 scale):

**Gap Importance** (5 points):
- 5: Core unsolved problem in the field
- 4: Significant but not central problem
- 3: Interesting niche problem
- 2: Minor technical issue
- 1: Trivial question

**Generalizability** (3 points):
- 3: Widely applicable across domains
- 2: Applicable within subdiscipline
- 1: Narrow case-specific

**Explanatory Power** (2 points):
- 2: Resolves multiple existing puzzles
- 1: Clarifies one specific issue
- 0: Purely descriptive

**Total Score Interpretation**:
- 9-10: High impact potential (major contribution)
- 7-8: Good impact (solid contribution)
- 5-6: Moderate impact (acceptable)
- <5: Low impact (reconsider direction)

---

## Phase 5: Evidence Documentation

### Gap Evidence Package

For each identified gap, create evidence file:

```markdown
## Gap: [Title]

### Definition
[Clear description of what's missing]

### Evidence from Literature
1. Paper A (Author, Year): "[Quote showing gap]"
   - Context: [Why this matters]

2. Paper B (Author, Year): "[Quote acknowledging limitation]"
   - Context: [What they couldn't address]

3. Paper C (Author, Year): "[Quote raising question]"
   - Context: [Unanswered question]

[Minimum 3 pieces of evidence per gap]

### Why This Gap Matters
[Significance explanation]

### Feasibility for User
[Can user address this with their approach?]
```

---

## Search Quality Checklist

Before concluding literature search, verify:

**Coverage**:
- ✓ All core concepts covered (each has 5-10 papers)
- ✓ Time span adequate (5 years + classics)
- ✓ Multiple disciplines searched (if applicable)
- ✓ Total papers ≥20 (minimum)

**Quality**:
- ✓ Average relevance ≥7.5/10
- ✓ At least 5 high-citation papers (>100 cites)
- ✓ Recent papers (last 2 years) included
- ✓ Foundational works included

**Gap Identification**:
- ✓ At least 3 distinct gaps identified
- ✓ Each gap has 3+ pieces of evidence
- ✓ Gaps are feasible to address
- ✓ Gaps are significant (not trivial)

**Originality**:
- ✓ Similarity analysis completed (top 10 papers)
- ✓ Innovation types identified (≥2)
- ✓ Impact score calculated (≥7/10)
- ✓ Justification documented (300+ words)

---

## Common Pitfalls and Solutions

### Pitfall 1: Search Too Narrow
**Symptom**: <15 relevant papers found
**Solution**:
- Broaden keywords (use synonyms)
- Extend time range
- Include adjacent disciplines

### Pitfall 2: Search Too Broad
**Symptom**: >100 papers, can't filter effectively
**Solution**:
- Tighten relevance criteria (raise threshold to 8/10)
- Focus on most recent papers
- Prioritize by citation count

### Pitfall 3: Missing Classics
**Symptom**: No papers >10 years old
**Solution**:
- Check "most cited" on Google Scholar
- Look at textbook references
- Ask: "What are the foundational works in this area?"

### Pitfall 4: Echo Chamber
**Symptom**: All papers from same research group/school
**Solution**:
- Deliberately search for alternative perspectives
- Check papers that cite different theoretical frameworks
- Include critics of main approach

### Pitfall 5: False Gaps
**Symptom**: "Gap" is actually well-addressed, just using different terminology
**Solution**:
- Search with synonym keywords
- Check related disciplines
- Verify gap with evidence (3+ citations)

---

## Integration with Skill Workflow

This search strategy supports:

**Phase 2.1** (Gap Identification):
- Use Rounds 1-3 to build literature base
- Apply Phase 3 methods to identify gaps
- Document evidence per Phase 5

**Phase 2.2** (Originality Assessment):
- Use Phase 4 similarity analysis
- Classify innovation types
- Calculate impact prediction

**Quality Gates**:
- Gate 2 requires passing the Search Quality Checklist
- All gaps must have evidence packages
- Originality assessment must be documented

---

## Example: Complete Search for "Self-Continuity and Sleep"

### Round 1: Direct Search
**Keywords used**: 15 combinations (self-continuity + sleep, narrative self + memory, etc.)
**Papers found**: 45 candidates
**After filtering**: 25 papers retained (relevance ≥7/10)

### Round 2: Expanded Search
**New keywords**: phenomenological self, memory consolidation, sleep-dependent processing
**Adjacent fields**: Cognitive neuroscience, philosophy of mind
**Papers added**: 12 papers

### Round 3: Classics
**Identified works**: Thompson (2015), Dennett (1991), Metzinger (2003), Born & Wilhelm (2012)
**Papers added**: 8 classic papers

**Total**: 45 papers in literature base

### Gap Identification
**Method**: Concept mapping + Problem-solution analysis

**Gaps found**:
1. **Compression mechanism**: How exactly is narrative compressed during sleep?
   - Evidence: Thompson mentions "taken apart and put together" but no mechanism
   - 5 papers acknowledge this limitation

2. **Functional explanation**: Why is self-continuity maintained (evolutionary purpose)?
   - Evidence: Most papers describe but don't explain function
   - 4 papers raise this as future work

3. **Cross-sleep identity**: Philosophical implications of discontinuity
   - Evidence: Neuroscience describes process, philosophy discusses identity, but no integration
   - Gap at intersection of two literatures

### Originality Assessment
**Similarity analysis**: Highest overlap 65% (medium)
**Innovation types**: Integrative (philosophy + neuroscience) + Theoretical (compression framework)
**Impact score**: 8/10 (bridges two literatures, addresses acknowledged gaps)

---

## Summary

Effective literature search requires:
1. **Systematic keyword generation** (10-15 combinations)
2. **Multi-round search** (direct → expanded → classics)
3. **Rigorous gap identification** (3 methods, evidence-based)
4. **Thorough originality assessment** (similarity + innovation + impact)
5. **Quality verification** (pass all checklist items)

This ensures comprehensive coverage and confident identification of genuine research opportunities.

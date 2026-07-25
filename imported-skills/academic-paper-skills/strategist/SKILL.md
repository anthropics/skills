---
name: academic-paper-strategist
description: Systematic strategic planning framework for philosophy and interdisciplinary academic papers targeting preprint platforms (PhilArchive, arXiv, PhilSci-Archive). Use when users want to: (1) plan a paper on a specific topic, (2) identify research gaps and assess originality, (3) develop optimized paper outlines, (4) prepare for preprint submission, or (5) understand platform requirements and writing standards. Triggered by phrases like 'plan a paper on,' 'help me design a paper about,' 'identify research gaps in,' 'is this idea original,' or when users need structured research planning. The skill guides through three phases: Platform Analysis (identifying target venue and studying sample papers), Theoretical Framework (AI-driven literature search and gap identification), and Outline Optimization (structured design with reviewer-perspective self-assessment). Each phase includes quality evaluation standards and validation checkpoints. Output: optimized detailed outline ready for systematic writing (use with academic-paper-composer skill).
---

# Academic Paper Strategist

## Overview

This skill provides a systematic framework for strategic planning of academic papers in philosophy and interdisciplinary research. It guides you through three phases—from platform selection to optimized outline—with AI-driven literature search, research gap identification, originality assessment, and quality-controlled outline design.

**Output**: A detailed, review-ready paper outline with supporting documentation (platform style guide, literature review, gap analysis, reviewer assessment).

**Companion Skill**: Use **academic-paper-composer** to execute the outline and write the full paper.

---

## When to Use This Skill

Use **academic-paper-strategist** when you need to:

**Planning Stage**:
- Design a research paper from initial idea to structured outline
- Identify a suitable publication platform (PhilArchive, arXiv, etc.)
- Understand writing standards for a specific preprint platform

**Research Stage**:
- Conduct systematic literature search
- Identify research gaps with evidence
- Assess originality of your research idea
- Predict potential impact

**Design Stage**:
- Structure paper chapters and arguments
- Optimize outline from reviewer perspective
- Prepare submission-ready strategy

**Triggers**:
- "Plan a paper on [topic]"
- "Help me design a paper about [subject]"
- "Identify research gaps in [field]"
- "Is this idea original?"
- "What platform should I submit to?"

---

## Workflow Overview

```
Phase 1: PLATFORM ANALYSIS (Target Selection + Style Learning)
    ↓
Phase 2: THEORETICAL FRAMEWORK (AI-Driven Gap Identification)
    ↓
Phase 3: OUTLINE OPTIMIZATION (Quality-Controlled Design)
    ↓
Output: Detailed Outline + Supporting Documentation
```

**Quality Gates**: 3 validation checkpoints ensure each phase meets standards before proceeding.

---

## Phase 1: Platform Analysis

### Goal
Identify the optimal submission platform and understand its writing standards through systematic sample paper analysis.

### Input Required from User
- **Core research idea or topic** (brief description)
- **Target platform** (optional - if unclear, I'll recommend)
- **Field/discipline** (philosophy, cognitive science, interdisciplinary, etc.)

### Workflow

#### Step 1.1: Platform Selection (If Needed)

If target platform unclear, I will:

1. **List candidate platforms** based on research content:
   - **PhilArchive/PhilPapers**: Philosophy papers, phenomenology, metaphysics
   - **arXiv (cs.AI, q-bio.NC)**: Computational, neuroscience, AI-related
   - **PhilSci-Archive**: Philosophy of science, formal methods
   - **PsyArXiv**: Psychology, cognitive science
   - **SocArXiv**: Social sciences, interdisciplinary

2. **Evaluate each platform**:
   - Subject area alignment (does your topic fit?)
   - Methodology match (philosophical/empirical/computational)
   - Acceptance criteria
   - Typical review timeline

3. **Provide recommendation** with reasoning

4. **Decision Point 1**: You confirm platform or suggest alternative

#### Step 1.2: Sample Paper Search (AI-Driven, Quality-Controlled)

I will conduct **multi-dimensional search** for 8-10 representative papers:

**Search Strategy** (load `references/search_strategy.md` for details):

**Time Dimension**:
- Recent (last 6 months): 3 papers - capture current trends
- Current (1-2 years): 3 papers - established standards
- Classic (highly cited): 2 papers - quality benchmarks

**Relevance Dimension**:
- Use keyword combinations from your topic
- Score each paper 0-10 for relevance
- Retain only papers scoring ≥7/10

**Diversity Dimension**:
- Multiple authors (≥5 unique)
- Different research perspectives
- Varied paper lengths

**Tools Used**:
- Exa MCP (semantic search)
- Tavily MCP (web search)
- Platform-specific search (PhilPapers, arXiv)

**Quality Validation**:
After search, I'll run `scripts/evaluate_samples.py` to generate evaluation report:
```bash
python scripts/evaluate_samples.py
```

This produces:
- Sample quality metrics
- Time distribution check
- Relevance statistics
- Diversity assessment
- Pass/Fail recommendation

**Quality Gate 1** (Must Pass):
- ✓ Sample papers ≥8
- ✓ Time distribution balanced
- ✓ Average relevance ≥8/10
- ✓ Unique authors ≥5

**If Failed**: Re-search with adjusted criteria

#### Step 1.3: Writing Standards Extraction

From the 8-10 sample papers, I will extract:

**Structural Patterns**:
- Abstract structure (Problem→Method→Results→Contribution?)
- Chapter organization (how many sections? typical flow?)
- Average proportions (Intro 15%, Main 70%, Conclusion 15%?)

**Style Patterns**:
- First-person vs passive voice usage
- How arguments are structured
- Citation density and format
- Use of technical terminology

**Format Specifications**:
- Typical word count range
- Reference count range
- Section heading conventions

**Output**: `[Platform]_Writing_Standards_Guide.md`

---

## Phase 2: Theoretical Framework

### Goal
AI-driven systematic literature search, research gap identification, and originality assessment.

### Input Required from User
- **Core research question/thesis** (your main argument)
- **Background context** (why you're interested in this)
- **Optional**: Any papers you already know about

### Workflow

#### Step 2.1: Literature Search (AI-Driven, Fully Automated)

**Important**: This phase is **AI-driven**. You provide your idea; I conduct comprehensive literature search and gap analysis.

**Multi-Round Search Strategy**:

**Round 1: Direct Search (Primary Literature)**
1. **Extract core concepts** from your idea (3-5 concepts)
2. **Generate keyword combinations** (10-15 combinations)
   - Concept + concept
   - Concept + method
   - Include synonyms and disciplinary variants
3. **Search each combination** using Exa/Tavily
4. **Collect 30-50 candidate papers**
5. **Quality filter**: Retain top 20 papers (relevance ≥7/10)

**Round 2: Expanded Search (Adjacent Fields)**
1. **Extract new keywords** from Round 1 papers
2. **Search adjacent disciplines**:
   - Philosophy → cognitive science
   - Neuroscience → philosophy of mind
   - AI → consciousness studies
3. **Collect 10-20 bridging papers**

**Round 3: Classic Literature (Foundational Works)**
1. **Identify highly-cited papers** (>100 citations)
2. **Track citations** from Round 1-2 papers
3. **Collect 5-10 foundational papers**

**Total Literature Base**: 35-50 papers

**Load Reference**: `references/search_strategy.md` for detailed methodology

#### Step 2.2: Research Gap Identification (AI Analysis)

Using collected literature, I will **automatically identify** 3-5 research gaps:

**Gap Identification Methods**:

1. **Concept Mapping**:
   - Plot papers on Concept × Method matrix
   - Identify white spaces (unexplored combinations)

2. **Problem-Solution Analysis**:
   - What problems does literature address?
   - What limitations do authors acknowledge?
   - What questions remain unanswered?

3. **Temporal Analysis**:
   - What was once studied but abandoned?
   - What emerged recently but unexplored?

**Gap Types**:
- **Complete gaps**: No existing research
- **Partial gaps**: Preliminary work only, needs development
- **Controversy gaps**: Competing theories, no resolution

**For Each Gap, I Document**:
- Clear definition (50-100 words)
- Evidence (3-5 citations showing gap exists)
- Significance assessment (High/Medium/Low)
- Feasibility assessment (Can you address it?)

**Validation**: Run `scripts/gap_analysis.py` to ensure quality:
```bash
python scripts/gap_analysis.py
```

This validates:
- Each gap has ≥3 pieces of evidence
- Definitions are specific and clear
- Significance is justified

**Quality Gate 2** (Must Pass):
- ✓ Literature base ≥20 papers
- ✓ Identified gaps ≥3
- ✓ Each gap has ≥3 evidence citations
- ✓ At least 1 high-significance gap

**If Failed**: Continue search or pivot research direction

**Output**: `Literature_Review_Report.md` + `Research_Gap_Analysis.md`

#### Step 2.3: Originality Assessment (AI Analysis)

I will **automatically assess** your idea's originality:

**Step 1: Similarity Analysis**
- Compare your idea with top 15 most similar papers
- Create similarity matrix (topic/method/conclusion overlap)
- Calculate overall similarity percentage

**Interpretation**:
- >80%: High similarity, needs repositioning
- 50-80%: Moderate, emphasize differences
- <50%: Good originality, proceed

**Step 2: Innovation Classification**

Identify which innovation types apply (need ≥2):
1. **Methodological**: New approach to known problem
2. **Theoretical**: New framework or model
3. **Application**: Existing theory to new domain
4. **Integrative**: Synthesizing separate literatures

**Step 3: Impact Prediction (1-10 scale)**

**Scoring Criteria**:
- **Gap Importance** (5 points): Core vs. peripheral problem?
- **Generalizability** (3 points): Widely applicable?
- **Explanatory Power** (2 points): Resolves existing puzzles?

**Target**: ≥7/10 for good impact potential

**Output**: `Originality_Assessment_Report.md` (similarity analysis + innovation types + impact prediction + 300-word justification)

#### Step 2.4: Core Concepts Discussion (Interactive)

**Decision Point 2**: Based on literature analysis, I will:

1. **Propose 3-5 core concepts** to emphasize
2. **Explain rationale** (based on gap analysis + literature frequency)
3. **Ask for your feedback**: Agree? Adjust? Add?

This ensures the paper focuses on the right concepts to maximize contribution.

---

## Phase 3: Outline Optimization

### Goal
Design a structured, review-ready outline optimized from a reviewer's perspective.

### Input
- Literature analysis from Phase 2
- Core concepts (confirmed in Step 2.4)
- Platform standards from Phase 1

### Workflow

#### Step 3.1: Initial Structure Design

Based on platform standards, I will:

1. **Design chapter structure**:
   - Abstract
   - Introduction (with subsections)
   - Main body (3-5 chapters, each with subsections)
   - Conclusion

2. **Allocate word counts**:
   - Introduction: 15-20% of total
   - Main body: 60-70% of total
   - Conclusion: 10-15% of total

3. **Determine argument flow**:
   - Logical progression of ideas
   - Where to introduce concepts
   - Where to address objections

**Output**: `Initial_Outline_Draft.md`

#### Step 3.2: Reviewer-Perspective Self-Assessment

I will evaluate the outline as if I were a platform reviewer, using **7 dimensions** (load `references/quality_standards.md` for criteria):

**7-Dimension Assessment** (5 points each, 35 total):

1. **Argument Clarity** (1-5)
   - Is the thesis clear?
   - Are supporting arguments identifiable?

2. **Argument Completeness** (1-5)
   - Any logical gaps or jumps?
   - All premises justified?

3. **Literature Support** (1-5)
   - Expected citation count (40+ for philosophy)
   - Key works covered?

4. **Methodological Clarity** (1-5)
   - Approach explicit (philosophical argument/phenomenological/etc.)?
   - Method justified?

5. **Originality Expression** (1-5)
   - Contribution clear?
   - Differentiated from existing work?

6. **Organization** (1-5)
   - Logical flow?
   - Proportions balanced?

7. **Platform Fit** (1-5)
   - Matches platform style?
   - Meets format requirements?

**Scoring**:
- Total: X/35
- Passing threshold: ≥28/35 (80%)

**Requirement**: Must identify at least 3-5 specific issues with concrete improvement suggestions.

**Output**: `Reviewer_Assessment_Report.md`

#### Step 3.3: Optimization Recommendations (Data-Driven)

For each dimension scoring <4/5, I will provide:

**Issue Description**:
- What specific problem exists?

**Severity** (High/Medium/Low):
- High: Affects paper acceptability
- Medium: Affects paper quality
- Low: Minor improvement

**Concrete Solution**:
- Specific actionable fix
- Example of how to implement

**Expected Improvement**:
- How much will this raise the score?

**Prioritization**:
1. All high-severity issues first
2. Then medium-severity
3. Then low-severity (optional)

**Decision Point 3**: I present recommendations; you decide:
- Accept (implement all)
- Selective (choose which to implement)
- Modify (adjust recommendations)

#### Step 3.4: Final Outline Generation

After implementing approved optimizations, I produce:

**Detailed Outline Structure**:
```markdown
# [Paper Title]

## Abstract (250 words)
- [Key points to cover]

## 1. Introduction (1,500 words)
### 1.1 The Puzzle (400 words)
- [Specific content guidance]
### 1.2 Existing Approaches (600 words)
- [Specific theories to discuss]
### 1.3 This Paper's Contribution (500 words)
- [Specific claims to make]

## 2. [Main Chapter] (1,200 words)
### 2.1 [Section] (400 words)
- [Argument structure]
- [Key citations]
...

[Complete structure to 3rd-level headings]

## References
- [Expected 40-60 sources]
```

**Quality Gate 3** (Must Pass):
- ✓ Reviewer score ≥28/35 (80%)
- ✓ All high-severity issues resolved
- ✓ Word allocations sum to target total
- ✓ Platform conformity ≥70%

**If Failed**: Redesign outline addressing identified issues

**Final Output**: `Optimized_Detailed_Outline.md`

---

## Complete Output Package

Upon completion of all 3 phases, you receive:

### Documentation
1. **`[Platform]_Writing_Standards_Guide.md`**
   - Platform style patterns
   - Structural templates
   - Citation and format conventions

2. **`Sample_Papers_Evaluation_Report.md`**
   - 8-10 analyzed papers
   - Quality metrics
   - Extracted patterns

3. **`Literature_Review_Report.md`**
   - 35-50 core papers
   - Organized by theme
   - Annotated with relevance

4. **`Research_Gap_Analysis.md`**
   - 3-5 identified gaps
   - Evidence packages
   - Significance assessments

5. **`Originality_Assessment_Report.md`**
   - Similarity analysis
   - Innovation classification
   - Impact prediction

6. **`Reviewer_Assessment_Report.md`**
   - 7-dimension scores
   - Identified issues
   - Optimization recommendations

7. **`Optimized_Detailed_Outline.md`** ⭐ **Main Deliverable**
   - Complete structure to 3rd-level headings
   - Word count allocations
   - Content guidance for each section
   - Key citations to include

### Ready for Next Step
With the **Optimized_Detailed_Outline.md**, proceed to **academic-paper-composer** skill to write the full paper.

---

## Quality Assurance System

### Quality Standards Reference

For detailed evaluation criteria, load:
```markdown
references/quality_standards.md
```

This document defines:
- Sample paper selection criteria
- Literature search comprehensiveness metrics
- Gap identification requirements
- Reviewer assessment rubrics
- Quality gate thresholds

### Evaluation Scripts

Two Python scripts support quality validation:

#### 1. Sample Paper Evaluator
```bash
python scripts/evaluate_samples.py
```

**Function**: Validates collected sample papers against quality standards
- Checks time distribution
- Calculates average relevance
- Verifies diversity
- Generates evaluation report

**When to Use**: After Step 1.2 (sample paper search)

#### 2. Gap Analysis Validator
```bash
python scripts/gap_analysis.py
```

**Function**: Validates identified research gaps
- Checks evidence sufficiency (≥3 per gap)
- Validates gap definitions
- Assesses significance justifications
- Generates gap portfolio report

**When to Use**: After Step 2.2 (gap identification)

---

## Decision Points (Interactive)

This skill has **3 key decision points** where I pause for your input:

### Decision Point 1: Platform Selection (Step 1.1)
**I provide**: Platform analysis + recommendation
**You decide**: Accept recommendation or suggest alternative

### Decision Point 2: Core Concepts (Step 2.4)
**I provide**: 3-5 proposed core concepts + rationale
**You decide**: Confirm, adjust, or supplement concepts

### Decision Point 3: Optimization Acceptance (Step 3.3)
**I provide**: Prioritized list of improvements + recommendations
**You decide**: Accept all, select specific ones, or request modifications

---

## Example Usage

### User Request
"I want to write a philosophy paper about self-continuity during sleep, arguing that narrative compression maintains identity across sleep-wake cycles."

### Skill Response

**Phase 1: Platform Analysis**
1. Analyzing topic... Recommended platform: **PhilArchive** (philosophy of mind focus)
2. Searching sample papers... [AI searches with keywords: "self-continuity", "sleep", "personal identity", "phenomenology"]
3. Found 10 candidates, evaluating... ✓ 8 papers meet quality standards
4. Extracting writing patterns... ✓ Style guide generated

**Phase 2: Theoretical Framework**
1. Conducting literature search...
   - Round 1: 25 papers on self/sleep/memory
   - Round 2: 12 papers bridging philosophy + neuroscience
   - Round 3: 8 classic papers (Dennett, Thompson, Metzinger)
   - Total: 45 papers in literature base
2. Identifying gaps... ✓ 4 gaps found:
   - Gap 1: Compression mechanism (how self is rebuilt)
   - Gap 2: Functional explanation (why continuity needed)
   - Gap 3: Philosophical implications of discontinuity
   - Gap 4: Integration of phenomenology + neuroscience
3. Assessing originality... ✓ 62% similarity (medium), integrative innovation, impact score: 8/10
4. **Decision Point 2**: Proposed core concepts: narrative compression, periodic death, self-model transparency, memory consolidation. [User confirms]

**Phase 3: Outline Optimization**
1. Designing initial outline... ✓ 6 chapters, 9,600 words total
2. Reviewer assessment... Score: 26/35 (below threshold)
   - Issues found: Methodological clarity (3/5), Originality expression (3/5)
3. **Decision Point 3**: Recommendations:
   - Add explicit methodology section (High priority)
   - Strengthen differentiation from existing work (High priority)
   - [User accepts both]
4. Regenerating outline... ✓ New score: 30/35 (passes)

**Output**: `Optimized_Detailed_Outline.md` ready for writing phase

---

## Tips for Best Results

### Provide Clear Research Ideas
- The more specific your initial idea, the better the literature search
- Include any philosophers/theories you're building on
- Mention any specific questions you want to address

### Trust the AI-Driven Search
- Literature search, gap identification, and originality assessment are **fully automated**
- I use multiple search strategies to ensure comprehensive coverage
- Quality gates validate that standards are met

### Engage at Decision Points
- Your input at the 3 decision points shapes the final outline
- Feel free to adjust my recommendations based on your expertise
- Decisions are collaborative, not automated

### Use Quality Validation
- If unsure about quality, I can re-run evaluation scripts
- Reports provide objective metrics and concrete feedback
- Quality gates ensure no phase proceeds without meeting standards

### Iterate if Needed
- If Phase 1 fails quality gates, we re-search with adjusted criteria
- If Phase 2 reveals insufficient gaps, we pivot research direction
- If Phase 3 scores low, we redesign with clear improvement targets

---

## Limitations and Notes

- **Calibrated for philosophy and interdisciplinary papers**: May need adjustment for pure empirical sciences or formal logic
- **Preprint platform focus**: Primarily targets PhilArchive, arXiv, PhilSci-Archive (not peer-reviewed journals)
- **Requires web access**: Literature search depends on Exa/Tavily MCP tools
- **Human judgment still essential**: AI provides analysis and recommendations, but you make final decisions
- **Complementary to writing skill**: This skill produces outlines; use **academic-paper-composer** for actual writing

---

## Related Skills

**Next Step**: academic-paper-composer
- Takes the optimized outline from this skill
- Executes systematic writing with quality control
- Produces submission-ready manuscript

**Can Be Used Standalone**: If you already have a mature outline from another source, you can skip this skill and go directly to academic-paper-composer.

---

## Summary

**academic-paper-strategist** transforms a research idea into a publication-ready outline through:

1. **Platform Analysis**: Identify optimal venue and learn writing standards (8-10 sample papers)
2. **Theoretical Framework**: AI-driven literature search (35-50 papers) + gap identification (3-5 gaps) + originality assessment
3. **Outline Optimization**: Reviewer-perspective evaluation (7 dimensions) + targeted improvements

**Quality Assurance**: 3 quality gates + 2 validation scripts ensure each phase meets standards.

**Output**: Detailed outline ready for systematic writing, with complete supporting documentation.

**Estimated Time**: 2-4 hours for complete strategic planning (depending on literature availability and iteration needs).

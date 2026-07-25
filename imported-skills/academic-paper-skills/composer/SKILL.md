---
name: academic-paper-composer
description: Systematic writing framework for philosophy and interdisciplinary academic papers from optimized outline to submission-ready manuscript. Use when users want to: (1) write a paper from a detailed outline, (2) ensure quality control during writing, (3) maintain consistency across chapters, (4) prepare a submission-ready manuscript, or (5) systematically execute a planned paper. Triggered by phrases like 'write the paper from this outline,' 'compose the full manuscript,' 'execute the outline,' or when users have completed strategic planning (academic-paper-strategist skill) and are ready to write. Takes optimized outline as input; outputs complete manuscript with iterative quality checks.
---

# Academic Paper Composer

## Overview

This skill provides a systematic framework for writing academic papers from optimized outline to submission-ready manuscript. It implements iterative quality control at both chapter-level and paper-level, ensuring consistent high quality throughout the writing process.

**Input**: Detailed, optimized paper outline (from academic-paper-strategist or equivalent)

**Output**: Complete, submission-ready manuscript with quality validation reports

**Prerequisite**: Use **academic-paper-strategist** skill first to create optimized outline (or provide equivalent detailed outline)

---

## When to Use This Skill

Use **academic-paper-composer** when you need to:

**Writing Stage**:
- Execute a detailed paper outline systematically
- Write a complete academic paper chapter-by-chapter
- Maintain quality control during writing process
- Ensure consistency across all sections

**Quality Assurance Stage**:
- Validate each chapter before proceeding
- Check cross-chapter coherence
- Perform final quality assessment
- Verify submission readiness

**Submission Preparation Stage**:
- Prepare manuscript for platform submission
- Complete platform-specific checklists
- Generate final submission package

**Triggers**:
- "Write the paper from this outline"
- "Compose the full manuscript"
- "Execute the outline systematically"
- "I have an outline, help me write the paper"
- After completing academic-paper-strategist skill

---

## Workflow Overview

```
Phase 4: SYSTEMATIC WRITING (Chapter-by-Chapter + Quality Gates)
    ↓
Phase 5: QUALITY CONTROL (Final Validation + Submission Prep)
    ↓
Output: Submission-Ready Manuscript + Quality Reports
```

**Quality Gates**: After each chapter + final paper evaluation

---

## Required Input

Before using this skill, you must provide:

### 1. Optimized Detailed Outline
**Required structure**:
```markdown
## Abstract (250-300 words)
- [Key points to cover]

## 1. Introduction (1,500 words)
### 1.1 Opening Puzzle (400 words)
- [Content guidance]
### 1.2 Literature Review (600 words)
- [Theories to discuss]
### 1.3 This Paper's Contribution (500 words)
- [Specific claims]

## 2. [Main Chapter Title] (1,200 words)
### 2.1 [Section] (400 words)
- [Argument structure]
- [Key citations]
...

[Complete structure with word counts and content guidance]
```

**Quality check**: Outline should specify:
- ✓ Chapter titles and word counts
- ✓ Subsection structure (to 3rd level)
- ✓ Content guidance for each section
- ✓ Key citations to include
- ✓ Argument structure notes

If outline lacks these, consider using **academic-paper-strategist** first.

### 2. Platform Writing Standards Guide
**From academic-paper-strategist Phase 1**, or equivalent document specifying:
- Platform style patterns (voice, terminology, citation format)
- Structural conventions
- Example papers for reference

### 3. Literature Base (Optional but Recommended)
- List of core papers to cite
- Research gap analysis
- Key concepts to emphasize

---

## Phase 4: Systematic Writing

### Goal
Write complete manuscript chapter-by-chapter with iterative quality control.

### Workflow

#### Step 4.1: Writing Environment Setup

Before writing, I will:

1. **Verify outline completeness**:
   - All chapters specified with word counts
   - Content guidance provided
   - Argument structure clear

2. **Load reference documents**:
   - Platform writing standards
   - Section writing guides (`references/section_guides.md`)
   - Quality standards (`references/writing_standards.md`)

3. **Create writing tracker**:
   ```markdown
   # Writing Progress Tracker
   - [ ] Abstract (250 words)
   - [ ] Chapter 1: Introduction (1,500 words)
   - [ ] Chapter 2: [Title] (1,200 words)
   ...
   - [ ] Conclusion (1,000 words)
   - [ ] References
   ```

**Decision Point 1**: Confirm outline and standards loaded, ready to begin writing.

#### Step 4.2: Chapter-by-Chapter Writing

**For each chapter, I will follow this sequence**:

##### A. Pre-Writing Review
Before writing chapter N:
1. **Review outline specification** for this chapter:
   - Word count target
   - Subsection structure
   - Content guidance
   - Key arguments/citations

2. **Review previous chapter** (if N>1):
   - Last paragraph of chapter N-1
   - Key concepts introduced
   - Promises to fulfill

3. **Check section guide**:
   - Load appropriate template from `references/section_guides.md`
   - Review quality markers for this section type

##### B. Writing Execution

I will write the chapter following:

**Content principles**:
- **Follow outline exactly**: Respect structure and word counts
- **Include specified citations**: Use literature from outline
- **Maintain platform style**: Match voice and terminology
- **Use section templates**: Follow appropriate guide from `section_guides.md`

**Quality targets (pre-emptive)**:
- Argument quality: Clear thesis, justified premises
- Citation quality: All claims supported, proper format
- Clarity: Precise prose, terms defined, good transitions
- Structure: Logical flow, proper proportions
- Style conformity: Match platform conventions

**Output**: Complete chapter draft

##### C. Post-Writing Evaluation

After completing chapter draft, I will:

1. **Create evaluation document**:
   ```bash
   python scripts/chapter_quality_check.py
   # Option 1: Create template for this chapter
   ```

2. **Perform 5-dimension assessment**:
   - **Argument Quality** (1-4): Thesis clear? Premises justified? Objections addressed?
   - **Citation Quality** (1-4): All claims cited? Format consistent? Key literature included?
   - **Clarity & Readability** (1-4): Prose clear? Terms defined? Transitions smooth?
   - **Structure & Flow** (1-4): Logical progression? Proper proportions? Follows outline?
   - **Platform Conformity** (1-4): Style match? Voice consistent? Format correct?

3. **Generate quality report**:
   ```bash
   python scripts/chapter_quality_check.py
   # Option 2: Generate report from evaluation
   ```

   This produces:
   - Total score (X/20)
   - Pass/fail (threshold: ≥16/20)
   - Weak dimensions identified
   - Specific revision recommendations

**Quality Gate 4A** (After Each Chapter):
- ✓ Score ≥16/20 (80%)
- ✓ All dimensions ≥3/4 (or revisions implemented)
- ✓ Word count within ±10% of target

**If Failed**: Implement revisions before proceeding to next chapter

##### D. Iteration (If Needed)

If chapter scores <16/20:

1. **Identify weak dimension(s)**: Which scored <3/4?

2. **Implement targeted revisions**:
   - Argument quality issue → Add justifications, address objections
   - Citation quality issue → Add supporting citations, fix format
   - Clarity issue → Simplify prose, add definitions, improve transitions
   - Structure issue → Reorganize paragraphs, adjust proportions
   - Style issue → Adjust voice, terminology, format

3. **Re-evaluate**: Generate new quality report

4. **Repeat until passing** (typically 1-2 iterations)

**Important**: Do not proceed to next chapter until current chapter passes quality gate.

##### E. Chapter Completion

Once chapter passes quality gate:

1. **Mark chapter complete** in writing tracker
2. **Save chapter with quality report**
3. **Note key concepts introduced** (for coherence check later)
4. **Preview next chapter** requirements

**Decision Point 2** (After Major Chapters): After completing each main body chapter, I will:
- Present completed chapter summary
- Show quality score
- Ask: Proceed to next chapter or revise further?

#### Step 4.3: Writing Sequence

**Recommended order**:

1. **Introduction** (write first)
   - Establishes thesis and roadmap
   - Use introduction guide from `section_guides.md`
   - Quality check: Abstract promises, literature coverage, clear contribution

2. **Main Body Chapters** (in outline order)
   - Follow outline sequence
   - Quality check after each
   - Build on previous chapters

3. **Conclusion** (write after main body)
   - Synthesizes findings
   - Addresses introduction promises
   - Use conclusion guide from `section_guides.md`

4. **Abstract** (write last)
   - Summarizes complete paper
   - Use abstract guide from `section_guides.md`
   - Quality check: Standalone, accurate, compelling

5. **References** (compile throughout)
   - Format according to platform standards
   - Verify all citations present

#### Step 4.4: Cross-Chapter Coherence Check

After all chapters written, before final evaluation:

1. **Terminology consistency**:
   - Extract key terms from each chapter
   - Verify consistent usage throughout
   - Check definitions consistent

2. **Argument flow**:
   - Verify chapter N+1 builds on chapter N
   - Check roadmap (intro) matches execution
   - Ensure conclusion addresses introduction promises

3. **Citation patterns**:
   - Check for uneven citation distribution
   - Verify key works cited where relevant
   - Ensure bibliography complete

**Output**: Cross-chapter coherence report identifying any inconsistencies

---

## Phase 5: Quality Control

### Goal
Perform comprehensive final evaluation and prepare submission-ready manuscript.

### Workflow

#### Step 5.1: Content Completeness Check

Using structured checklist, verify:

**Structural Completeness**:
- [ ] Abstract (250-300 words)
- [ ] Introduction with all required elements
- [ ] All outlined main chapters present
- [ ] Conclusion with all required elements
- [ ] References section formatted correctly

**Content Completeness**:
- [ ] All introduction promises fulfilled
- [ ] All claims supported by evidence or argument
- [ ] All technical terms defined
- [ ] All objections addressed
- [ ] All limitations acknowledged

**Citation Completeness**:
- [ ] Every citation in text has bibliography entry
- [ ] Every bibliography entry cited in text
- [ ] Citation format consistent throughout
- [ ] All citations include necessary information

**Format Completeness**:
- [ ] Title page (if required)
- [ ] Section numbering consistent
- [ ] Heading hierarchy logical
- [ ] Figure/table captions (if applicable)

**Output**: Completeness checklist report

#### Step 5.2: Final 7-Dimension Evaluation

I will perform comprehensive evaluation using:

```bash
python scripts/final_evaluation.py
# Create evaluation template
```

**7 Dimensions** (10 points each, 70 total):

1. **Overall Argument Quality** (1-10)
   - Thesis clarity throughout
   - Chapter integration
   - Logical completeness
   - Objections addressed

2. **Literature Integration** (1-10)
   - Citation count (40-60 typical for philosophy)
   - Key literature covered
   - Citations well-integrated
   - Critical engagement present

3. **Clarity & Accessibility** (1-10)
   - Prose clarity
   - Complex ideas explained
   - Appropriate for audience
   - Technical terms defined

4. **Originality & Contribution** (1-10)
   - Clear original contribution
   - Advance over literature
   - Significance established
   - Innovation present

5. **Methodological Rigor** (1-10)
   - Method explicit and justified
   - Consistently applied
   - Appropriate for question
   - Limitations acknowledged

6. **Structure & Organization** (1-10)
   - Logical flow
   - Optimal organization
   - Proportions balanced
   - Transitions seamless

7. **Platform & Style Conformity** (1-10)
   - Style matches platform
   - Format correct
   - Voice consistent
   - Citation format perfect

**Scoring Process**:
1. Evaluate each dimension (1-10)
2. Provide detailed notes for each
3. Complete completeness checklist
4. List any specific issues

**Generate report**:
```bash
python scripts/final_evaluation.py
# Generate final report
```

This produces:
- Total score (X/70)
- Pass/fail (threshold: ≥56/70)
- Weak dimensions identified
- Completeness assessment
- Prioritized revision recommendations
- Submission readiness decision

**Quality Gate 5** (Final):
- ✓ Score ≥56/70 (80%)
- ✓ All completeness checklist items complete
- ✓ All high-priority issues addressed

**If Failed**: Implement revisions and re-evaluate

#### Step 5.3: Revision Implementation (If Needed)

If final score <56/70 or completeness incomplete:

1. **Prioritize revisions**:
   - HIGH priority: All issues affecting score or completeness
   - MEDIUM priority: Issues improving quality
   - LOW priority: Optional enhancements

2. **Implement systematically**:
   - Address high-priority first
   - Document changes
   - Maintain style consistency

3. **Re-evaluate**:
   - Generate new final report
   - Verify score ≥56/70
   - Check completeness 100%

4. **Iterate until passing**

**Decision Point 3**: After final evaluation, I will:
- Present final score and assessment
- Show submission readiness status
- Recommend: Submit immediately / Implement optional improvements / Required revisions
- Ask: Proceed with submission or implement further improvements?

#### Step 5.4: Submission Package Preparation

Once final evaluation passes:

1. **Platform-specific checklist**:
   - **PhilArchive/PhilPapers**:
     - [ ] PDF format
     - [ ] Abstract <500 words
     - [ ] Metadata (title, keywords, classification)
     - [ ] Author information complete

   - **arXiv**:
     - [ ] LaTeX or PDF format
     - [ ] Abstract <1920 characters
     - [ ] Category selection correct
     - [ ] No font embedding issues

   - **PhilSci-Archive**:
     - [ ] PDF format
     - [ ] Subject classification
     - [ ] Keywords (3-5)
     - [ ] No copyright issues

2. **Generate final outputs**:
   - Formatted manuscript (PDF or LaTeX)
   - Abstract (separate file if needed)
   - Metadata file
   - Cover letter (if applicable)

3. **Pre-submission verification**:
   - Re-read complete paper
   - Check all formatting
   - Verify all links/citations work
   - Proofread for typos

**Output**: Complete submission package ready for platform upload

---

## Complete Output Package

Upon completion of both phases, you receive:

### Quality Reports
1. **Chapter Quality Reports** (one per chapter)
   - 5-dimension scores
   - Pass/fail status
   - Revision recommendations implemented

2. **Cross-Chapter Coherence Report**
   - Terminology consistency check
   - Argument flow verification
   - Citation pattern analysis

3. **Final Evaluation Report** ⭐ **Key Document**
   - 7-dimension comprehensive assessment
   - Completeness checklist (100%)
   - Submission readiness decision
   - Platform-specific checklist

### Manuscript Files
1. **Complete Manuscript** ⭐ **Main Deliverable**
   - All chapters integrated
   - Properly formatted
   - Citations complete
   - Submission-ready

2. **Abstract** (separate file)
   - Standalone 250-300 words
   - Platform-formatted

3. **Metadata Document**
   - Title, keywords, classification
   - Author information
   - Platform-specific requirements

### Supporting Documentation
1. **Writing Progress Tracker**
   - All chapters completed
   - Quality scores logged
   - Revision history

2. **Citation List**
   - All references used
   - Formatted for platform
   - Verified complete

---

## Quality Assurance System

### Quality Standards Reference

For detailed evaluation criteria, all standards are defined in:
```markdown
references/writing_standards.md
```

This document provides:
- Chapter-level quality standards (5 dimensions)
- Final quality standards (7 dimensions)
- Section-specific quality criteria
- Scoring rubrics
- Issue identification and fixes

### Section Writing Guides

For guidance on writing each section type:
```markdown
references/section_guides.md
```

This provides:
- Abstract writing template and checklist
- Introduction structure (6 subsections)
- Main body chapter templates (4 types)
- Conclusion structure
- Transition strategies
- Platform-specific style guidance
- Common mistakes and fixes

### Evaluation Scripts

Two Python scripts support quality validation:

#### 1. Chapter Quality Check
```bash
python scripts/chapter_quality_check.py
```

**Function**: Evaluates individual chapters against 5-dimension standards
- Creates evaluation templates
- Calculates scores and pass/fail
- Identifies weak dimensions
- Generates revision recommendations
- Supports multi-chapter comparison

**When to Use**: After writing each chapter (Step 4.2.C)

#### 2. Final Paper Evaluation
```bash
python scripts/final_evaluation.py
```

**Function**: Evaluates complete paper against 7-dimension standards
- Comprehensive quality assessment
- Completeness checklist validation
- Submission readiness determination
- Platform-specific preparation
- Generates final report with recommendations

**When to Use**: After all chapters complete (Step 5.2)

---

## Decision Points (Interactive)

This skill has **3 key decision points** where I pause for your input:

### Decision Point 1: Writing Commencement (Step 4.1)
**I provide**: Loaded outline, standards, and writing plan
**You confirm**: Ready to begin writing / Need adjustments

### Decision Point 2: Chapter Completion (Step 4.2.E)
**I provide**: Completed chapter with quality score
**You decide**: Proceed to next / Revise further / Adjust approach

**Frequency**: After each main body chapter (3-5 times typically)

### Decision Point 3: Final Submission (Step 5.3)
**I provide**: Final evaluation report with score and readiness assessment
**You decide**: Submit immediately / Implement optional improvements / Additional revisions

---

## Example Usage

### User Request
"I have the optimized outline from the strategist skill. Please write the complete paper on self-continuity during sleep."

### Skill Response

**Phase 4: Systematic Writing**

1. **Setup**: Outline loaded (6 chapters, 9,600 words total). Platform: PhilArchive. Standards loaded. ✓

2. **Chapter 1 - Introduction (1,500 words)**:
   - Writing... [follows outline structure]
   - Self-evaluation: Argument 4/4, Citation 3/4, Clarity 4/4, Structure 3/4, Style 4/4
   - Score: 18/20 ✓ PASS
   - **Decision Point 2**: Proceed to Chapter 2?

3. **Chapter 2 - Narrative Compression Framework (1,200 words)**:
   - Writing... [develops theoretical framework]
   - Self-evaluation: All dimensions 3-4
   - Score: 17/20 ✓ PASS
   - **Decision Point 2**: Proceed to Chapter 3?

4. **Chapter 3-5**: [Similar process for each chapter]

5. **Chapter 6 - Conclusion (1,000 words)**:
   - Writing... [synthesizes findings]
   - Score: 18/20 ✓ PASS

6. **Abstract (280 words)**:
   - Writing... [summarizes complete paper]
   - Score: 19/20 ✓ PASS

7. **Cross-Chapter Coherence**: Terminology consistent ✓, Argument flow verified ✓, Citations complete ✓

**Phase 5: Quality Control**

1. **Completeness Check**: All items complete ✓ (18/18)

2. **Final Evaluation**:
   - Overall Argument: 9/10
   - Literature Integration: 8/10 (48 citations)
   - Clarity: 9/10
   - Originality: 8/10
   - Methodology: 8/10
   - Structure: 9/10
   - Platform Fit: 9/10
   - **Total: 60/70 (85.7%)** ✓ PASS

3. **Decision Point 3**: Paper scored 60/70 (Good quality, ready for submission). Submit now or implement optional improvements?

4. **Submission Package**: PDF generated, metadata prepared, PhilArchive checklist complete ✓

**Output**: Submission-ready manuscript + comprehensive quality reports

---

## Tips for Best Results

### Provide Complete Outline
- The more detailed your outline, the better the writing quality
- Include content guidance for each section
- Specify key citations and argument structure
- Indicate expected word counts

### Trust the Iterative Process
- Chapter-level quality gates ensure each section is solid
- Don't skip quality checks (they prevent cascading problems)
- Revisions at chapter-level are easier than whole-paper revisions

### Engage at Decision Points
- Your input at decision points shapes the final manuscript
- Feel free to request additional revisions even if chapter passes
- Provide feedback on style or emphasis

### Use Quality Reports
- Chapter reports show specific weaknesses
- Final report provides objective submission readiness assessment
- Use reports to track improvement across chapters

### Leverage Section Guides
- I reference `section_guides.md` for each section type
- You can review these guides directly if you want to understand the approach
- Guides include templates, examples, and common mistakes

---

## Integration with Academic-Paper-Strategist

This skill is designed to work seamlessly with **academic-paper-strategist**:

**Ideal workflow**:
1. Use **academic-paper-strategist** to:
   - Identify optimal platform
   - Conduct literature search
   - Identify research gaps
   - Assess originality
   - Generate optimized detailed outline

2. Use **academic-paper-composer** (this skill) to:
   - Execute the outline systematically
   - Maintain quality control during writing
   - Produce submission-ready manuscript

**Can be used standalone**: If you already have a detailed outline from another source, you can use this skill directly (skip strategist).

---

## Limitations and Notes

- **Requires detailed outline**: Vague outlines produce lower-quality output; specificity is key
- **Iterative process takes time**: Quality writing with validation requires patience; typical timeline: 1-2 days for 10,000-word paper
- **Quality checks are systematic, not perfect**: Final human review recommended before submission
- **Platform-specific formatting**: I adapt to platform standards, but you should verify final format
- **Complementary to strategist skill**: Best results come from using both skills in sequence

---

## Common Issues and Solutions

### Issue 1: Chapter Fails Quality Gate

**Symptom**: Score <16/20 after writing chapter

**Solution**:
1. Review weak dimension(s) from report
2. Implement specific recommendations
3. Re-evaluate chapter
4. Typical fix time: 30-60 minutes

**Prevention**: Follow section guides closely during initial writing

### Issue 2: Inconsistent Style Across Chapters

**Symptom**: Some chapters feel different in tone or voice

**Solution**:
1. Run cross-chapter coherence check (Step 4.4)
2. Identify inconsistent terminology or voice
3. Revise to match dominant style
4. Re-run check to verify

**Prevention**: Reference platform standards before writing each chapter

### Issue 3: Low Final Score (<56/70)

**Symptom**: Paper fails final quality gate

**Solution**:
1. Identify weak dimensions from final report
2. Focus on dimensions scoring <7/10
3. Implement high-priority revisions systematically
4. Re-evaluate after revisions

**Common causes**: Insufficient literature integration, unclear contribution, poor coherence

### Issue 4: Completeness Checklist Incomplete

**Symptom**: Missing required elements

**Solution**:
1. Review which category has incomplete items
2. Add missing elements (e.g., missing objections section, incomplete references)
3. Re-run completeness check

**Prevention**: Use writing tracker throughout; check outline completeness before starting

---

## Platform-Specific Notes

### PhilArchive / PhilPapers
- **Style**: First-person acceptable ("I argue")
- **Length**: 5,000-12,000 words typical
- **Citations**: APA or Chicago author-year
- **Quality focus**: Philosophical rigor, argument clarity

### arXiv (Philosophy-adjacent)
- **Style**: More formal, passive voice common
- **Length**: Varies widely (3,000-20,000)
- **Citations**: Varies by subcategory
- **Quality focus**: Interdisciplinary clarity, technical precision

### PhilSci-Archive
- **Style**: Bridges philosophical and scientific
- **Length**: 6,000-15,000 words typical
- **Citations**: Author-year typical
- **Quality focus**: Integration of philosophy + science

---

## Summary

**academic-paper-composer** transforms an optimized outline into a submission-ready manuscript through:

1. **Systematic Writing** (Phase 4): Chapter-by-chapter execution with 5-dimension quality checks after each (≥16/20 threshold)
2. **Quality Control** (Phase 5): Final 7-dimension assessment (≥56/70 threshold) + completeness validation + submission preparation

**Quality Assurance**: Iterative evaluation at chapter and paper levels ensures consistent quality throughout.

**Output**: Submission-ready manuscript with comprehensive quality reports documenting systematic validation.

**Estimated Time**: 1-2 days for systematic writing and validation of 8,000-12,000 word paper (varies with outline detail and revision needs).

---

## Related Skills

**Prerequisite**: academic-paper-strategist
- Produces the optimized outline that this skill executes
- Highly recommended to use first for best results

**This skill can be used standalone**: If you have a detailed outline from another source, you can proceed directly with this skill.

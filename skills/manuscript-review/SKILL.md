---
name: manuscript-review
description: Systematic academic manuscript review for inconsistencies, citation errors, statistical reporting problems, and style mismatches. Use this skill whenever the user asks to review, proofread, check, or audit an academic paper, manuscript, journal submission, or dissertation chapter. Also trigger when the user mentions finding errors in a draft, verifying citations, checking APA formatting, or preparing a manuscript for resubmission. Covers experimental research, quantitative analysis, and social science writing conventions. Works alongside the academic-research skill but focuses specifically on error detection and correction rather than content generation.
license: MIT
author: "Emmanuel Maduneme (https://www.emaduneme.com/)"
compatibility:
  - Claude.ai
  - Claude Code
metadata:
  version: 1.0.0
---

# Manuscript Review

## Overview

This skill performs systematic, multi-pass review of academic manuscripts to catch inconsistencies, citation errors, statistical reporting problems, copy-paste artifacts, and style mismatches. It presents issues in small batches with precise, actionable fixes rather than vague suggestions.

## When This Skill Triggers

- User says "review my manuscript" or "check my paper for errors"
- User mentions preparing for journal resubmission
- User asks to verify citations or check statistical reporting
- User uploads a manuscript and asks for inconsistency checking
- User mentions "desk rejection" or "reviewer feedback" in context of fixing a paper

## Review Process

### Pass 1: Structural Consistency

Scan the entire manuscript for internal contradictions:
- **Abstract vs. body**: Do sample sizes, key findings, and conclusions match?
- **Hypotheses vs. results**: Are all stated hypotheses addressed? Do labels (H1, H2a, H2b) remain consistent throughout?
- **Methods vs. results**: Do the analyses described in Methods match what's reported in Results?
- **Introduction claims vs. citations**: Does every factual claim have a supporting citation?
- **Tables/figures vs. text**: Do numbers referenced in prose match the tables?

### Pass 2: Citation Verification

For each citation in the manuscript:
1. **Web search** the paper by title, authors, and year
2. **Verify**: Author names (spelling, order), publication year, journal name, DOI
3. **Flag**: Misattributions, wrong years, hallucinated papers, reversed author orders
4. **Check**: In-text citation format matches reference list entry
5. **Confirm**: Page numbers for direct quotes (if applicable)

Common citation errors to watch for:
- Author name variations (e.g., "Thier & Ling" vs. "Thier & Lin")
- Year discrepancies between in-text and reference list
- Papers attributed to wrong authors (hallucination artifacts from AI-assisted drafting)
- Missing DOIs or incorrect journal names
- "Et al." used incorrectly (fewer than 3 authors in APA 7th)

### Pass 3: Statistical Reporting

Check every statistical claim:
- **Degrees of freedom** present and correct for the test type
- **p-values** reported accurately (direction, significance level)
- **Confidence intervals** formatted correctly: B = X.XX, 95% CI [LL, UL]
- **Effect sizes** included where expected
- **Test statistics** match the analysis described (F for ANOVA, t for t-test, etc.)
- **Sample sizes** consistent across all mentions
- **Decimal places** consistent (typically 2 for most statistics, 3 for p-values)
- **Rounding**: Check that rounded figures are mathematically consistent

### Pass 4: Copy-Paste and Carryover Errors

These are common when adapting stimuli or reusing text across studies:
- **Wrong topic references** (e.g., cancer language appearing in a pollution study)
- **Leftover placeholder text** or template language
- **Inconsistent terminology** (switching between terms for the same construct)
- **Study 1 language** appearing in Study 2 sections (for multi-study papers)
- **Self-identifying information** that should be removed for blind review

### Pass 5: Writing Style Audit

Match the manuscript against the user's established voice:
- **Sentence structure**: Declarative, subject-verb-object preferred
- **Hedging**: Strategic use of "suggests that," "implies that," "indicates"
- **Passive vs. active**: Active voice dominant, passive acceptable for methods
- **Paragraph coherence**: Each paragraph has a clear topic sentence and logical flow
- **Jargon check**: Technical terms defined on first use
- **Transitions**: Smooth connections between sections

## Presentation Protocol

**Present issues 1-2 at a time.** Do not dump all errors at once. For each issue:

1. **Location**: Section, paragraph, and specific sentence
2. **Problem**: What's wrong, stated precisely
3. **Evidence**: Why it's wrong (e.g., "the cited paper is actually from 2022, not 2024")
4. **Fix**: Exact replacement text the user can copy-paste

Wait for the user to confirm or discuss before moving to the next batch.

## Issue Severity Levels

- **Critical**: Factual errors, fabricated citations, wrong statistical conclusions
- **Major**: Inconsistencies between sections, missing analyses, APA violations
- **Minor**: Typos, formatting inconsistencies, awkward phrasing

Present critical issues first.

## Hard Rules

- **Never rewrite sections** unless explicitly asked. The goal is error detection, not ghostwriting.
- **Never assume a citation is correct** without verification. Always search.
- **Never change the user's writing voice.** Flag style issues but preserve their established patterns.
- **Always provide exact replacement text**, not vague instructions like "consider rewording."
- **Track all issues found** in a running count so the user knows progress.

## Output Format

For each review session, maintain a running issue log:

```
Issue #[N] | [Severity] | [Section]
Problem: [precise description]
Current text: "[exact text from manuscript]"
Suggested fix: "[exact replacement text]"
Rationale: [why this fix is correct]
```

## Interaction with Other Skills

- **academic-research skill**: Use for statistical write-up templates if the user needs to rewrite a results section
- **citation-verify** (if standalone): Delegate citation checking there
- **email-drafting**: Use for resubmission cover letters after review is complete

## Reference Files

- `references/style-sample.md` - Sample of the user's approved writing voice
- `references/common-errors.md` - Known error patterns from previous reviews
- `assets/review-checklist.md` - Printable checklist for self-review

## Test Cases

1. **Multi-study paper**: Manuscript with two experiments, testing for cross-study contamination
2. **Resubmission**: Paper previously rejected, checking that revision addresses reviewer concerns
3. **Citation-heavy introduction**: Literature review section with 30+ citations to verify

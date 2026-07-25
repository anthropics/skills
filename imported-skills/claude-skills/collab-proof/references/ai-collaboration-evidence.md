# AI Collaboration Evidence: Why Documentation Matters

## The Problem

Developers increasingly build with AI, but the collaboration leaves no trace. Git log records *what* changed; the conversation records *what was said*. Neither answers the questions that matter most:

- Why was this approach chosen over the alternative?
- What did the AI identify that the developer hadn't noticed?
- Where did the developer override the AI's suggestion — and why?

## Key Sources

**1. Hiring and Portfolio Verification (2025–2026)**
Companies now explicitly ask candidates to show AI collaboration evidence. GitHub portfolios require "a 'My contribution' section linking to commits or pull requests that demonstrate what you owned" (Artech, 2026). Recruiters scan for AI-native engineering skills and expect proof beyond finished artifacts.
Source: [Artech AI Portfolio Tips](https://www.artech.com/blog/ai-assisted-portfolio-credibility/)

**2. Architecture Decision Records (ADRs)**
ADRs (Michael Nygard, 2011) capture the context, decision, and consequences of architectural choices. The canonical format includes: title, status, context, decision, consequences. Modern AI-assisted development extends this pattern to include *who* made the decision — human or AI.
Source: [Nygard ADR Template](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions)

**3. Session Context Loss**
Claude Code saves session transcripts to `~/.claude/projects/` as JSONL. But context compaction and session boundaries mean reasoning evaporates. Studies of AI-assisted development show developers cannot reconstruct the reasoning behind 60–70% of decisions made in a session after 48 hours.
Source: [Claude Code Session Memory](https://claudefa.st/blog/guide/mechanics/session-memory)

**4. AI Contribution Attribution**
The `git-ai` project (2026) tracks AI-generated code line-by-line. But line attribution ("AI wrote this") is different from decision attribution ("AI identified this issue"). collab-proof targets the decision layer, not the code layer.
Source: [git-ai: AI contribution tracking](https://github.com/git-ai-project/git-ai)

**5. Developer Cognitive Load**
Research on expertise and memory (Sweller, 1988; Kirschner et al., 2006) shows that working memory constraints cause implicit reasoning to be discarded when focus shifts. External documentation of decisions during the session — not after — is the only reliable capture method.
Source: Sweller, J. (1988). Cognitive load during problem solving. *Cognitive Science*, 12(2), 257–285.

## Implications for collab-proof

- Evidence must be captured *during* the session, not reconstructed afterward
- Calibrated attribution ("identified" vs "suggested" vs "developer-driven") is more useful than binary AI/human labeling  
- Shareable HTML format enables portfolio and hiring use cases that markdown alone cannot serve
- Signal filtering prevents noise — only sessions with genuine decision forks produce output

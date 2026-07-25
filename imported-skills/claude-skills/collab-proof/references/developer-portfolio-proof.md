# Developer Portfolio Proof: The AI Collaboration Evidence Problem

## Why "Show Your Work" Now Applies to AI

The hiring market has shifted. Companies explicitly ask candidates: "Show me how you used AI in this project." The challenge is that AI-assisted development leaves ambiguous evidence:

- A GitHub repo shows finished code, not the collaboration process
- Commit messages show *what* shipped, not *why* this approach
- A demo shows the product works, not what the developer contributed vs the AI

## The Verification Gap

Source: [TechnCV: Claude Code Resume Skills](https://techncv.com/blog/claude-code-resume-skills/)

Hiring managers at forward-thinking companies scan for AI-native engineering skills. The recommended evidence includes:
1. Git commit histories with meaningful messages
2. Prompt logs or decision rationale
3. Inline comments explaining decisions
4. Live demos where candidates walk through their logic

collab-proof addresses items 2 and 3 automatically.

## HTML as Portable Proof

Markdown files are local artifacts. HTML files are shareable:
- Email attachment to a recruiter
- Link in a GitHub README
- Appendix to a portfolio site
- PR description for code review

A self-contained HTML file (no CDN, no external resources, `file://`-ready) is the most portable format for portfolio evidence. PDF requires generation tooling; Gist requires GitHub authentication.

Source: [AI Agent Portfolio Examples](https://tandamconnect.com/blog/ai-agent-portfolio-examples-2026)

## The "AI Contribution" Calibration Problem

Existing tools either overclaim ("AI built this") or dismiss ("developer did everything"). Neither is useful for:
- Honest self-assessment
- Team knowledge transfer
- Portfolio credibility

The calibrated approach distinguishes three contribution types:
- **Identified**: AI spotted something the developer hadn't noticed (e.g., race condition, security issue)
- **Suggested**: AI proposed an approach or alternative (developer made final call)
- **Developer-driven**: Developer designed and decided; AI executed

This three-way split comes from studies of pair programming (Williams & Kessler, 2002) where contribution attribution improved team learning and code review quality.

Source: Williams, L. & Kessler, R. (2002). *Pair Programming Illuminated*. Addison-Wesley.

## Signal Filtering Prevents Portfolio Inflation

Not every session deserves documentation. A session where you changed a button color has no evidence value. collab-proof's LOW signal threshold silences these sessions.

The 30–40% artifact generation rate is a feature, not a bug: it means every documented session has genuine decision content, making the portfolio more credible, not less.

Source: [Asking HN: Hiring in the age of AI-assisted coding](https://news.ycombinator.com/item?id=47722081)

## Tamper-Evident Timestamps via Git

The HTML proof footer embeds the last git commit hash of the session. This provides:
- A timestamp verifiable against the public git history
- Proof the document was generated at development time, not retrospectively
- A link between the artifact and the code it describes

This is analogous to signed commits but for documentation rather than code.

Source: [Git: Cryptographic signing](https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work)

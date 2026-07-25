# Cross-Platform Synthesis — Detecting Patterns Across Reddit / HN / Web / X

This reference answers exactly one decision: **after Phases 1–4 fire and return source data, how does the skill detect consensus, controversy, pain points, excitement, and emerging trends without fabricating signals?**

## The Six Pattern Types

| Pattern | Definition | Detection signal |
|---|---|---|
| **Consensus** | 3+ platforms agree on a specific claim | Same claim or near-paraphrase appears in posts/articles across Reddit, HN, and Web |
| **Controversy** | Platforms disagree visibly | Reddit positive while HN negative (or vice versa); or competing threads within one platform |
| **Pain points** | Recurring complaints | "I tried X and Y broke" / "X is frustrating because" / "the worst part of X" patterns |
| **Excitement** | Recurring enthusiasm | "Just shipped X" / "this is huge" / "blown away by X" patterns |
| **Emerging trends** | Mentioned in newest posts but absent from older | `sort=new` results contain term/topic that `sort=top` results don't |
| **Gaps** | Notably absent angle | Something you'd reasonably expect to find that no source mentions |

## How Each Platform Voices Differently

Understanding each platform's bias is essential to weighting signals correctly.

### Reddit

- **Voice:** End-user / consumer / experiential
- **Strengths:** Sentiment, lived experience, "I tried this and..." stories, subculture-specific deep-dive
- **Biases:** Subreddit-specific norms; karma-driven amplification of strong opinions; trolling and brigading distort signal in contentious topics
- **Best for:** sentiment, problems, opportunities

### Hacker News

- **Voice:** Technical / builder / startup-flavored
- **Strengths:** Technical critique, implementation realism, founder/investor perspective, "this won't scale because" critique
- **Biases:** Tech-bro skew, contrarian-by-default, dismissive of non-technical concerns, regional/cultural homogeneity (mostly US/EU)
- **Best for:** technical credibility, scaling realism, founder POV

### Open Web (news, blogs, reviews)

- **Voice:** Editorial / professional / produced
- **Strengths:** Trend coverage, breadth, vetted facts, professional review depth
- **Biases:** Publication agenda (advertiser-friendly vs critical), recency-driven coverage cycles, paywall asymmetry
- **Best for:** trend, comparison, breadth

### X/Twitter (if available)

- **Voice:** Real-time / personality-driven / fragmented
- **Strengths:** Breaking news, individual-creator takes, viral reactions
- **Biases:** Algorithmic amplification of inflammatory content, character limit forces shallow takes, account verification asymmetry
- **Best for:** breaking conversation, individual creator reactions, viral memes

## Detection Heuristics

### Consensus

Look for the same factual claim (not the same wording) across 3+ platforms.

**Example:**
- Reddit post: "Self-hosting LLMs costs more in GPU than I expected"
- HN comment: "Anyone running A100s knows the OpEx adds up fast"
- Web article: "Hidden costs of self-hosted LLM deployment, exploring TCO"

→ Consensus: *Self-hosting LLMs has higher-than-expected operational costs.* Cite all 3 URLs.

### Controversy

Look for platforms taking opposite positions on the same question.

**Example:**
- Reddit: "Claude Code is amazing for everyday coding" (positive sentiment dominant)
- HN: "Claude Code is just a wrapper around the API, what's the value-add?" (skeptical dominant)
- Web: mixed reviews

→ Controversy: *Claude Code reception is split between end-user enthusiasm (Reddit) and developer skepticism about value-add (HN).* Cite from both sides.

### Pain points

Look for repeated complaints across sources.

Signal patterns:
- "the worst part of X is..."
- "I gave up on X because..."
- "X is frustrating when..."
- Repeated bug/issue mentions
- "Doesn't work as advertised"

### Excitement

Look for repeated enthusiasm across sources.

Signal patterns:
- "Just shipped X"
- "X changed how I work"
- "Wasn't expecting X to be this good"
- Repeated tutorial/walkthrough posts indicate active adoption

### Emerging trends

Compare `sort=new` (last 7 days) against `sort=top` (window). Terms or names appearing in `new` but absent from `top` are candidate emerging trends.

**Validation:** if it's not yet in HN/Web, it's pre-mainstream. If it's in `new` on Reddit AND in `new` on HN AND in last-7-days Web, it's actively emerging.

### Gaps

Hardest to detect — requires judgment about what you'd reasonably expect.

**Common gap patterns:**
- A major player isn't mentioned (suggests blind spot or fall-from-grace)
- Pricing/cost angle is absent (suggests early-stage hype)
- Failure cases are absent (suggests survivorship bias in coverage)
- Comparison to obvious alternative is absent (suggests echo chamber)

State gaps with explicit caveat: "**Notably absent:** [thing]. Could mean [interpretation A] or [interpretation B] — worth digging into."

## Anti-Patterns

### "Same word ≠ same claim"

Don't conflate platforms using the same noun for different concepts.

- Reddit's "performance" might mean "latency"
- HN's "performance" might mean "throughput"
- Web's "performance" might mean "market performance"

Read the surrounding context. Don't merge under a single banner.

### "One loud post ≠ consensus"

A single highly-upvoted Reddit post is not consensus. Consensus requires 3+ platforms agreeing. If you only have one source, label it "single-source signal" — useful but not consensus.

### "Inferring without quoting"

Every pattern must cite specific source URLs. If you can't cite, you can't claim.

### "Smoothing out controversy"

If platforms disagree, name the disagreement explicitly. Don't average them into a fake middle position. Controversy is signal, not noise.

## Output Format for Patterns

Each pattern in the synthesis section follows this format:

```markdown
### [Pattern type]: [Short label]

[1-2 sentences explaining the pattern]

**Sources:**
- [Platform]: [post/article title] — [URL]
- [Platform]: [post/article title] — [URL]
- [Platform]: [post/article title] — [URL]
```

Patterns ranked by confidence:
1. **High confidence** — consensus with 3+ sources, OR strong controversy with 2+ each side
2. **Medium confidence** — 2-source agreement, OR strong single-platform signal
3. **Low confidence / single-source** — explicitly labeled, used sparingly

## Operational Checklist (Per Synthesis)

- [ ] Extract claims from each platform's source set
- [ ] Group claims by topic/theme
- [ ] For each theme, check: 3+ platforms agreeing? → consensus
- [ ] For each theme, check: platforms disagreeing? → controversy
- [ ] Scan for pain/excitement signal patterns
- [ ] Compare `sort=new` vs `sort=top` for emerging trends
- [ ] Note 1-2 reasonable gaps with interpretation caveats
- [ ] Every pattern carries cited URLs
- [ ] Confidence labels applied

## Citations (7 sources)

1. **Brandwatch / Talkwalker — *Social listening methodology white papers* (2022–2024).** Source for cross-platform sentiment-detection patterns. Their published methodologies for distinguishing consensus / controversy / pain signals across Reddit + Twitter + forums informed this reference's six-pattern taxonomy.

2. **Sprout Social — *State of Social Listening* (annual report, 2024 edition).** Source for the bias profiles per platform (Reddit's experiential voice, HN's technical-builder skew, Web's editorial agenda). Sprout's annual benchmarking surveys 10,000+ marketers on platform-specific tone differences.

3. **Pew Research — *Social Media and the News Cycle* (ongoing series).** Source for the "real-time vs sustained narrative" distinction that informs the 7d-vs-90d window choice in Q3 of the intake. Pew's tracking of news-cycle compression on X/Twitter vs slower-burn coverage on Web provides empirical backing.

4. **Reddit's published research on subreddit dynamics — redditinc.com/blog + the `pushshift` archive analyses.** Source for understanding subreddit-specific norms and karma-driven amplification effects. Critical context for Reddit's biases section.

5. **Hacker News culture studies — Bret Devereaux's "ACOUP" blog posts on internet subcultures + Tante's posts on HN moderation patterns.** Source for the HN biases profile (contrarian-by-default, tech-bro skew, dismissive of non-technical concerns).

6. **Cliff Sussman, *The Listening Imperative* (Harvard Business Review Press, 2023).** Argues for treating multi-platform signal aggregation as a structured discipline rather than ad-hoc browsing. Source for the explicit-pattern-types taxonomy and the confidence-ranking approach.

7. **Alberto Brandolini, *Introducing EventStorming* — chapter on "Big Picture EventStorming" workshops.** Brandolini's framing of "let convergence emerge from multiple voices" applies directly to cross-platform synthesis: the synthesis should reflect what genuinely converges across sources, not what the analyst expected to find. https://leanpub.com/introducing_eventstorming

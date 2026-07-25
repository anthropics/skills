# Content & Communications Output Formats

Four output format specifications for content and communications prompts. Each includes the complete XML specification to paste into a prompt's output layer, usage guidance, and failure modes.

## Table of Contents

- [Blog Post / Article](#blog-post--article)
- [Content Brief](#content-brief)
- [Messaging Framework](#messaging-framework)
- [Email Sequence](#email-sequence)

---

## Blog Post / Article

**Use when:** The deliverable is a long-form content piece for web publication — informational, thought leadership, or educational. Written for public audiences in a publishing context, optimized for web reading patterns (scannable, front-loaded, with clear value in the opening).

**Distinct from:** Strategic Memo (argues for an internal decision), Research Summary (synthesizes evidence for analysis), Executive Brief (enables a leadership decision). This is published content for external audiences.

```xml
<output_format>
Structure as a blog post / article:

Headline: Specific and compelling. Communicates the value of reading the piece. Avoids clickbait, jargon, and vague generalities. 8-12 words.

Opening: (1-2 paragraphs) Hook the reader with a specific observation, surprising fact, or relatable problem — not a generic scene-setter. By the end of the second paragraph, the reader should know what this piece will give them and why it matters.

Body: (4-8 paragraphs organized by argument progression, not by topic headers) Build the argument or narrative progressively. Each paragraph advances the piece. Lead each paragraph with its key point — web readers scan. Support claims with specific examples, data, or concrete illustrations. If using subheads, limit to 2-3 that mark genuine structural shifts, not every paragraph.

Conclusion: (1-2 paragraphs) Land the argument with a concrete takeaway the reader can use or think about. Do not summarize — the reader just read the piece. End on the strongest, most resonant point, not a generic call to action.

Total length: 800-1500 words unless otherwise specified. Optimize for substance per word — if the argument is complete at 900 words, do not pad to 1,500. Web readers abandon content that wastes their time.
</output_format>
```

**Failure modes:**

- **Five-paragraph essay structure.** Claude may produce blog posts with introduction, three body paragraphs, conclusion — academic rather than engaging. Add: *"This is a published piece, not an essay. Open with something a reader would want to share. Build tension or insight progressively. End with a point that resonates, not a summary."*

- **Generic CTA insertion.** Claude may append "Want to learn more? Contact us today!" which undermines thought leadership credibility. For thought leadership pieces, add: *"End on the strongest insight, not a sales pitch. The piece itself is the value — it does not need a promotional wrapper."*

- **Subhead overuse.** Claude may add a subhead before every paragraph, breaking the piece into fragments. The format spec limits subheads to 2-3 marking genuine structural shifts. If this persists, add: *"Use transitions between paragraphs, not subheads. The reader should feel an argument building, not a list accumulating."*

---

## Content Brief

**Use when:** You need to specify what a content piece should be before it is written — the strategic document that guides a writer. The content brief is not itself content; it is the specification for content. Use when writing will be done by someone else and strategic decisions need to be captured.

**Distinct from:** An outline (which is structural). A content brief captures the strategic intent — audience, angle, key messages, evidence requirements — that an outline cannot convey.

```xml
<output_format>
Structure as a content brief:

Working Title: A descriptive title that may be refined during writing.

Objective: (1-2 sentences) What this piece must accomplish. Be specific: "Generate qualified demo requests from VP-level marketing leaders" not "raise awareness."

Target Audience: (1 paragraph) Who reads this, what they already know, what they care about, and what will make them keep reading. Specific enough that the writer can hear the audience's voice.

Core Message: (1-2 sentences) The single most important takeaway. If the reader remembers only one thing, this is it.

Angle / Hook: (1 paragraph) What makes this piece different from everything else written about this topic. The unique perspective, data, insight, or framing that justifies this piece's existence.

Key Points to Cover: (3-5 points, each 1-2 sentences) The essential arguments or sections the piece must include. These are strategic requirements, not an outline — the writer determines the structure.

Evidence and Sources: (brief list) Specific data points, case studies, research, or examples the piece should reference. Include links or citations where available.

Tone and Voice: (1-2 sentences) How this piece should sound. Reference existing pieces if possible: "Tone similar to [reference piece] — authoritative but conversational."

SEO Guidance: (optional, 1-2 sentences) Primary keyword, secondary keywords, and any search intent the piece should satisfy. Include only if SEO is relevant to the content's distribution strategy.

Length and Format: Target word count, any structural requirements (subheads, pull quotes, etc.), and publication context.

Total length of the brief: 300-500 words. The brief should be specific enough to prevent the writer from going in the wrong direction, but not so prescriptive that it removes creative judgment.
</output_format>
```

**Failure modes:**

- **Too vague to guide.** Claude may produce briefs like "write an engaging piece about AI in healthcare" that give the writer nothing to work with. Add: *"The brief must be specific enough that two different writers would produce substantially similar pieces — same angle, same key points, same audience register. If the brief allows wildly different interpretations, it is not doing its job."*

- **Over-specified into outline.** Claude may write a detailed outline that removes the writer's creative agency. The brief defines what and why; the writer decides how. Add: *"Specify the strategic requirements — audience, angle, key points, evidence — but do not prescribe the structure. The writer determines how to build the piece."*

---

## Messaging Framework

**Use when:** You need the reference document that governs how a product, company, initiative, or campaign is talked about across all channels and contexts. This is the source document that individual content pieces draw from. Use when multiple people will create content and messaging must be consistent.

**Distinct from:** A content brief (which specifies a single piece). A messaging framework is the reference document that content briefs draw from — it defines the messaging territory, not a specific piece of content.

```xml
<output_format>
Structure as a messaging framework:

Positioning Statement: (2-3 sentences) What this product/company/initiative is, who it is for, and why it matters — stated simply enough that anyone on the team can say it in a meeting.

Value Propositions: (3-4 propositions, each 2-3 sentences) The distinct reasons this matters to the target audience. Each proposition addresses a specific audience need, not a product feature. Ordered by importance.

Proof Points: (2-3 per value proposition) The specific evidence that supports each value proposition — metrics, case studies, technical capabilities, or third-party validation. Claims without proof points are empty assertions.

Target Audience Segments: (1 paragraph each, for 2-3 segments) Who this messaging is for, what they care about, and how the emphasis shifts for each segment. The core positioning stays the same; the emphasis and vocabulary adjust.

Key Messages by Context: (3-5 contexts, each 2-4 sentences) How the messaging adapts for specific situations — website homepage, sales call, conference presentation, press interview, social media. Each context shows the same core message in its native format.

Competitive Differentiation: (1-2 paragraphs) How this positioning differs from the 2-3 closest competitors or alternatives, including the status quo. State what is genuinely different, not what is aspirationally different.

Language Guidance: (brief) Words and phrases to use. Words and phrases to avoid. Not an exhaustive list — the 5-10 vocabulary choices that matter most for consistency and credibility.

Total length: 800-1200 words. This is a reference document — it should be scannable, not narrative. Use the structure as a lookup tool that anyone on the team can reference quickly when creating content, writing an email, or preparing a talk.
</output_format>
```

**Failure modes:**

- **Aspirational but indistinguishable.** Claude may produce messaging full of language any company could claim ("we empower," "we transform," "we unlock potential"). Add: *"Apply the competitor swap test to every value proposition: if a competitor's name could be substituted without the messaging seeming wrong, it is too generic. Rewrite until the messaging is true of this product and false of the closest alternative."*

- **Insider vocabulary.** Claude may produce messaging that sounds good internally but does not match how the audience talks about the problem. Add: *"Write the messaging in the language the audience uses, not the language the internal team uses. If the audience calls it 'reporting' and the internal team calls it 'business intelligence,' the messaging says 'reporting.'"*

---

## Email Sequence

**Use when:** You need a multi-touch email communication designed to move a reader through stages toward a specific action — a nurture sequence, an onboarding series, a re-engagement campaign, or a sales follow-up sequence. Each email builds on the previous and moves the reader closer to the desired action.

**Distinct from:** A single email (which is a one-time communication). This designs the arc across multiple emails with progressive momentum.

```xml
<output_format>
Structure as an email sequence:

Sequence Overview: (1 paragraph) The purpose of the sequence, the target audience, the desired end action, and the total number of emails with spacing between them.

Per-Email Specification: (for each email in the sequence)
- Email [N] of [total]: [Purpose of this email in the sequence]
- Send timing: [When this email sends relative to the trigger or previous email]
- Subject line: [The subject line — specific, benefit-oriented, under 50 characters]
- Body: [The complete email copy. Open with the most relevant line. Be concise — most emails should be 100-200 words. Every sentence either builds the case or drives the action. End with a single, clear CTA.]
- Goal: [What this email is trying to get the reader to do or think]

Sequence Logic: (1 paragraph) What happens if the reader takes the desired action mid-sequence (stop the sequence? branch to a different one?). What happens if they reach the end without acting — is there a final email, or does the sequence end silently?

Total length: Scale to sequence length. A 3-email sequence might be 500-700 words total. A 7-email nurture sequence might be 1200-1500 words. Each email should be short enough that the reader can absorb it in under 60 seconds.
</output_format>
```

**Failure modes:**

- **Repetitive structure.** Claude may produce email sequences where every email follows the same pattern (problem statement → benefit → CTA), making the sequence feel repetitive rather than progressive. Add: *"Each email must have a structurally different approach to advancing the reader. One might lead with a customer story, another with a surprising statistic, another with a direct question. If all emails use the same formula, the reader will tune out after the second."*

- **Emails too long.** Marketing email effectiveness drops sharply after 150-200 words. Add: *"Each email should be readable in under 60 seconds. If an email exceeds 200 words, cut it. Respect the reader's inbox."*

- **No progressive momentum.** Emails feel like standalone messages rather than a sequence with building urgency and deepening engagement. Add: *"Each email should reference or build on the previous email's theme. The reader should feel momentum, not repetition."*

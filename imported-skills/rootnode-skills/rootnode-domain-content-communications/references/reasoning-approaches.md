# Content & Communications Reasoning Approaches

Four reasoning approaches for content and communications prompts. Each includes the complete XML specification to paste into a prompt's reasoning layer, usage guidance, and failure modes.

## Table of Contents

- [Audience Analysis](#audience-analysis)
- [Editorial Judgment](#editorial-judgment)
- [Content Adaptation](#content-adaptation)
- [Persuasion Architecture](#persuasion-architecture)

---

## Audience Analysis

**Use when:** The task requires understanding a specific audience deeply enough to shape content, messaging, or strategy decisions. Use when the primary deliverable is audience understanding, or as a precursor step when audience insight is weak and the content will suffer without it.

**Distinct from:** General market research (which covers competitive landscape). This is focused entirely on the audience — their knowledge, motivations, barriers, language, and information habits.

```xml
<reasoning>
Approach this audience analysis as follows:
1. Define the audience precisely. Not "marketing professionals" but "marketing directors at mid-market B2B companies who are evaluating their first marketing automation platform." Vague audience definitions produce vague content. If multiple audience segments exist, analyze each separately — content that tries to speak to everyone speaks to no one.
2. Map their current state. What do they already know about this topic? What do they believe — correctly and incorrectly? What terminology do they use (which may differ from industry jargon)? What are they currently doing about the problem this content addresses?
3. Identify their motivations and barriers. What outcome are they trying to achieve? What are they afraid of getting wrong? What has stopped them from acting so far — is it knowledge gaps, organizational resistance, budget, risk aversion, or competing priorities? The gap between motivation and action is where content does its work.
4. Understand their information consumption. Where do they go for information on this topic — specific publications, communities, influencers, peers? What format do they prefer — long-form analysis, quick takes, video, data-heavy reports? What earns their trust — credentials, data, peer endorsement, case studies?
5. Identify the objections. What reasons would this audience give for not engaging with this content or not taking the desired action? These objections must be addressed — not argued against, but acknowledged and resolved — in the content itself.
6. Define the audience's language. What words do they use? What phrases signal credibility versus signal outsider status? Content that uses the audience's vocabulary builds immediate trust. Content that sounds like it was written by someone outside the audience creates distance.
</reasoning>
```

**Failure modes:**

- **Persona fiction instead of analysis.** Claude may produce audience analysis that reads like a marketing persona template — fictional demographic details and imagined quotes rather than analytical insight. If the output includes stock details like "Meet Sarah, a 34-year-old marketing director who loves yoga," add: *"This is an analytical audience profile, not a marketing persona. Focus on the audience's information needs, decision-making patterns, and behavioral drivers — not demographic fiction. Every claim about the audience should be something you can support with evidence or reasoning, not a creative exercise."*

- **Assumed homogeneity.** Claude may assume a single audience when the real audience is segmented. If the content will reach different sub-audiences, add: *"Identify the 2-3 distinct sub-segments within this audience and note where their needs diverge. The content strategy may need to address these segments differently."*

---

## Editorial Judgment

**Use when:** The task requires evaluating existing content for quality — clarity, structure, accuracy, tone, audience fit, and effectiveness. This is the content equivalent of code review. Use when reviewing a draft, auditing existing content, or assessing why content is underperforming.

**Distinct from:** Proofreading (which catches surface errors). This evaluates whether the content achieves its purpose — whether the argument is sound, the structure serves the reader, and the evidence supports the claims.

```xml
<reasoning>
Evaluate this content as follows:
1. Assess whether the piece has a clear, defensible thesis or central argument. Can you state in one sentence what this content is arguing or conveying? If you cannot, the piece lacks focus — and the reader will not find what the writer could not define.
2. Evaluate the opening. Does the first paragraph earn the reader's attention and establish why they should continue? An opening that is generic ("In today's fast-paced business environment..."), self-referential ("In this article, we will explore..."), or buried under throat-clearing fails the reader immediately.
3. Check the structure. Does each section advance the argument or narrative? Is there a logical progression from section to section? Are there sections that repeat a point already made, introduce tangents that do not serve the thesis, or exist only as padding? Flag structural problems specifically — which sections should be cut, moved, or consolidated.
4. Evaluate the evidence and specificity. Does the content support its claims with concrete examples, data, or reasoning? Or does it rely on assertions, generalizations, and abstract language? Every significant claim should have a specific example, data point, or logical argument supporting it — "many companies struggle with X" is weaker than "Acme Corp spent 18 months and $2M on X before discovering Y."
5. Assess the voice and tone. Is it appropriate for the stated audience? Is it consistent throughout, or does it shift registers? Does it sound like a human with expertise wrote it, or does it read like it was assembled from templates? Flag specific passages where the voice breaks or where the tone undermines the content's credibility.
6. Identify the single most impactful improvement. If the author could change only one thing, what would produce the largest quality increase? Lead with this finding — it focuses revision effort where it matters most.
</reasoning>
```

**Failure modes:**

- **Agreeableness in editing.** Claude may produce editorial feedback that is too gentle — complimenting structure and voice while avoiding the hard truth that the piece has a fundamental problem. Add: *"Your job is to make this content better, not to validate the author. If the piece has a fundamental problem, say so directly in the first sentence of your evaluation. Diplomatic but clear."*

- **Style over substance.** Claude may evaluate style (sentence flow, word choice) while ignoring substance (weak argument, missing evidence). Add: *"Evaluate the argument and evidence before you evaluate the style. A well-written piece with a weak argument is a polished failure."*

---

## Content Adaptation

**Use when:** The task involves taking a core message, idea, or piece of content and reshaping it for different formats, channels, or audiences. The source material exists — the challenge is translation across contexts while preserving strategic coherence. Use when a single message needs to work across a blog post, a social thread, an email, a sales deck, and a press release.

**Distinct from:** Creating new content from scratch. This starts with an existing message and reshapes it for multiple contexts.

```xml
<reasoning>
Approach this content adaptation as follows:
1. Extract the core message. What is the single essential idea that must survive every adaptation? State it in one sentence. This is the invariant — everything else can flex, but this cannot be lost.
2. For each target channel or format, identify the native constraints. What is the attention window (a tweet vs. a whitepaper)? What format conventions does the audience expect? What is the primary consumption context (mobile scroll, desktop deep-read, inbox scan, meeting presentation)? Content that fights its channel's conventions loses before it communicates.
3. Adapt the entry point for each context. A blog post can earn attention with a provocative observation. An email needs to earn opens with the subject line, then earn reads with the first sentence. A social post must communicate value in the first line before the fold. A sales deck needs to connect the message to the prospect's specific situation. The same idea needs different doors for different rooms.
4. Scale depth to format. A long-form article can develop an argument with evidence and nuance. A LinkedIn post must compress the same insight into a self-contained unit. An email must deliver value and drive action within 150 words. Do not truncate long-form content to create short-form — restructure the idea for the shorter format so it stands on its own.
5. Maintain voice consistency across adaptations. The tone may flex (more casual on social, more formal in a whitepaper), but the underlying voice — the personality, vocabulary level, and perspective — should be recognizably the same brand across all adaptations.
6. Verify that each adaptation can succeed independently. A reader who encounters only the email, or only the social post, should receive a complete and compelling version of the message — not a fragment that only makes sense alongside the other versions.
</reasoning>
```

**Failure modes:**

- **Truncation instead of adaptation.** Claude may produce "adaptations" that are actually just different-length versions of the same text. Real adaptation restructures for each channel's native patterns. Add: *"Each adaptation must be native to its channel. The blog post should read like something written for a blog. The social post should read like something written for social. If I could swap them between channels without noticing, the adaptation has not gone far enough."*

- **Substance drift.** Claude may add channel-native flair but dilute the central point. Add: *"After completing each adaptation, verify that the core message from step 1 is still the central point. Channel-native styling should not dilute the substance."*

---

## Persuasion Architecture

**Use when:** The task involves structuring content to move the reader toward a specific action or belief change through deliberate sequencing of cognitive steps. Use for landing pages, sales emails, fundraising appeals, policy arguments, or any content where the measure of success is whether the reader does something.

**Distinct from:** General narrative construction (which builds a story arc). This focuses specifically on the mechanics of persuasion — what the reader needs to think, feel, and believe at each stage before they will act.

```xml
<reasoning>
Structure this persuasion as follows:
1. Define the desired action precisely. Not "engage with our brand" but "click the Start Free Trial button" or "approve this budget request." Vague objectives produce vague persuasion.
2. Map the reader's current state. What do they believe right now? What do they want? What are they afraid of? What is their default action if they do nothing — and why is doing nothing attractive? The persuasion must overcome inertia, not just present benefits.
3. Identify the belief changes required. What must the reader believe before they will take the desired action? Sequence these in the order the reader needs to encounter them — typically: (a) this problem is real and affects me, (b) the cost of inaction is significant, (c) a solution exists, (d) this specific solution is credible, (e) the risk of trying is low, (f) the next step is clear and easy.
4. For each belief change, identify the strongest evidence type. Some beliefs are moved by data ("companies using X see 40% faster onboarding"). Some by social proof ("here's how Acme solved this"). Some by empathy ("you've probably experienced this"). Some by authority ("recommended by Y"). Match the evidence to what moves this specific audience.
5. Design the objection handling. At which points in the sequence will the reader push back? Build the counterargument into the flow before the objection fully forms — pre-empting objections is more persuasive than answering them after the fact.
6. Design the close. The transition from "I'm interested" to "I'll act" requires reducing friction and increasing urgency — but through legitimate means. What makes the next step easy? What makes now better than later? Manufactured urgency (countdown timers, false scarcity) destroys trust with sophisticated audiences. Real urgency comes from the cost of the problem continuing.
</reasoning>
```

**Failure modes:**

- **Manipulation instead of persuasion.** Claude may produce persuasion architecture that relies on psychological pressure tactics rather than legitimate evidence. Add: *"This audience is sophisticated and will recognize manipulative tactics. Build the persuasion on evidence, specificity, and genuine value — not on manufactured urgency or emotional pressure. Persuasion that the audience would resent if they noticed its mechanics is manipulation, not persuasion."*

- **Exposed structure.** Claude may label sections "Objection Handling" or "Social Proof" in the actual content rather than integrating these elements naturally. The reasoning approach guides the structure; the output should feel like natural, confident communication. Add: *"The persuasion structure guides your writing but must be invisible in the output. Never label persuasion mechanics in the final content."*

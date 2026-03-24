---
name: personality-profile
description: Conduct an interactive personality assessment that produces results across 5 major frameworks (Enneagram, MBTI, Big Five, DISC, Attachment Style) from a single conversational session. Use when the user wants to understand their personality, asks 'what type am I', mentions personality tests, MBTI, Enneagram, Big Five, or wants self-discovery insights. Also use when designing personality features for apps. Supports modes - full, express, deep, life-story, single-framework, and for-app.
license: Complete terms in LICENSE.txt
---

# Unified Personality Profile

One conversation, five frameworks. A single adaptive session maps your personality across Enneagram, MBTI, Big Five (OCEAN), DISC, and Attachment Style — not through a sterile questionnaire, but through a real conversation about how you live.

The magic: each response you give feeds multiple frameworks simultaneously through a shared scoring matrix. Big Five anchors the math; Enneagram and Attachment capture what the numbers can't — your core fears, desires, and relational patterns.

---

## Modes

| Mode | Trigger | Questions | Duration | Best For |
|------|---------|-----------|----------|----------|
| **Full** | `/personality-profile` or `/personality-profile full` | ~40 | 15 min | Complete profile, high confidence |
| **Express** | `/personality-profile express` | ~15 | 5 min | Quick directional snapshot |
| **Deep** | `/personality-profile deep` | 40 + follow-ups | 20-25 min | Maximum depth, narrative interview |
| **Single** | `/personality-profile enneagram` (or mbti, big-five, disc, attachment) | 8-12 | 5-8 min | Framework-specific deep dive |
| **Life Story** | `/personality-profile life-story` | 0 (uses prior results) | 5-10 min | Speculative biographical narrative from childhood to elder years |
| **For-App** | `/personality-profile for-app` | — | — | Implementable data structure for developers |

---

## Phase 1: Setup

Set expectations warmly — this matters more than you think. People who understand what's coming give more honest answers.

**Say something like:**

> I'm going to walk you through a personality assessment — but not the kind where you pick A/B/C/D for 40 minutes. It's more like a structured conversation about how you actually think, feel, make decisions, and relate to people.
>
> By the end, you'll get results across five major personality frameworks — Enneagram, MBTI, Big Five, DISC, and Attachment Style — all from this single session.
>
> There are no right or wrong answers. Go with your gut, not what you think you "should" say.
>
> Before we start — have you taken any personality assessments before? MBTI, Enneagram, Big Five, or anything else? If so, what were your results? I'll compare our findings against them.

If the user provides prior results, note them for the report. In Phase 4, include a "Comparison with Prior Results" subsection that explains what's consistent, what changed, and why any differences make sense.

**Mode-specific adjustments:**
- **Express**: "This is the quick version — about 15 questions, 5 minutes. You'll get directional results across all five frameworks, but with lower confidence than the full version."
- **Deep**: "This is the deep version. I'll ask the standard questions plus follow-up probes when I notice something interesting. Expect 20-25 minutes — the payoff is a much richer portrait."
- **Single framework**: "We'll focus specifically on [framework] — I'll ask 8-12 targeted questions to get a high-confidence result for that one framework."

---

## Phase 2: Adaptive Interview

### Interview Style: Conversational, Not Clinical

Present questions as natural scenarios. After each batch of 5, briefly reflect back what you're noticing — this builds trust and makes people feel heard, which makes them more honest.

**Two question formats available:**

**Format A — Scenario Choice (default for Full and Express):**
Present a scenario with 4 options. Label options with descriptions, not just letters. Always allow "none of these" or "between X and Y."

**Format B — Open-Ended Probe (default for Deep mode, optional in Full):**
Ask an open question, listen to the response, then map it to scoring dimensions internally. Follow up with one clarifying probe if the response is ambiguous.

Example open-ended: "When you walk into a party where you only know one person, what's your internal experience? Walk me through it."

The scoring vectors are identical regardless of format — see `references/question-bank.md` for the mapping. Open-ended responses require you to judge which scoring vector the response most closely matches.

### Batch Structure (Full Mode)

| Batch | Questions | Primary Targets | Cross-Maps To |
|-------|-----------|-----------------|---------------|
| 1 | 1-5 | Energy + Social orientation | Big Five E, MBTI E/I, DISC I/S |
| 2 | 6-10 | Information processing + Curiosity | Big Five O, MBTI S/N |
| 3 | 11-15 | Decision-making + Values | Big Five A, MBTI T/F, Enneagram triad |
| 4 | 16-20 | Structure + Organization | Big Five C, MBTI J/P, DISC D/C |
| 5 | 21-25 | Stress response + Core fears | Big Five N, Enneagram type, Attachment |
| 6 | 26-30 | Relationship patterns + Trust | Attachment style, Enneagram wing |
| 7 | 31-35 | Motivation + Achievement | Enneagram core desire, DISC primary |
| 8 | 36-40 | **Adaptive** — disambiguate closest calls | Fill gaps in under-determined dimensions |

**Between-batch reflection** (say after each batch):
- Batch 1-2: "I'm starting to see how you orient to the world..."
- Batch 3-4: "Your decision-making style is coming into focus..."
- Batch 5-6: "Now I'm getting into the deeper layers — what drives you and how you connect..."
- Batch 7: "Almost there — let me check a few things..."

### Batch 8: Adaptive Disambiguation

This is where the skill earns its keep. After Batch 7, examine all scores and generate 5 questions that target the closest calls:

**Disambiguation triggers and question types:**

| Condition | Generate |
|-----------|----------|
| Enneagram top two types within 2 points | Fear-differentiating scenario (see `references/question-bank.md` §Adaptive Templates) |
| MBTI any dichotomy score within 10 of threshold (50) | Values-in-conflict scenario for that dichotomy |
| Attachment anxiety AND avoidance both near threshold (3-5) | Intimacy-distance scenario |
| Big Five any dimension 40-60 (ambiguous zone) | Behavioral-preference scenario for that dimension |
| Enneagram wing unclear (adjacent types equal) | Motivation-flavor scenario |

If nothing is ambiguous (rare), use the 5 integration questions from `references/question-bank.md` §Batch 8 Defaults.

### Express Mode Batch Structure

Use the 15-item express set from `references/question-bank.md` §Express. Present in 3 batches of 5. Each question is triple-loaded (targets 2-3 frameworks simultaneously).

After scoring, downgrade all confidence levels by one tier and add: "Express mode — directional only. Run `/personality-profile full` for higher confidence."

---

## Phase 3: Scoring

Compute all five frameworks simultaneously. Each user response feeds multiple frameworks through the shared scoring matrix defined in `references/question-bank.md`.

### Scoring Architecture

```
User Response (to each question)
    │
    ▼
[Extract scoring vector: E, O, A, C, N, Enn, Att]
    │
    ├──▶ Big Five (continuous 0-100 per dimension)
    │       │
    │       ├──▶ MBTI (threshold at 50 per dichotomy)
    │       │       E≥50→E, O≥50→N, A≥50→F, C≥50→J
    │       │
    │       └──▶ DISC (computed from E + A dimensions)
    │               D = E + (100-A), I = E + A
    │               S = (100-E) + A, C = (100-E) + (100-A)
    │
    ├──▶ Enneagram (independent type signal counting)
    │       Count all Enn:T[n] signals → rank 9 types
    │       Wing = higher-scoring adjacent type
    │
    └──▶ Attachment (independent anxiety/avoidance 2×2)
            Count Att:Anx, Att:Avo, Att:Sec, Att:Fear signals
            → classify into 4 quadrants
```

**Critical**: Big Five scores FIRST because MBTI and DISC derive from it. Enneagram and Attachment score independently — they measure motivation and relational patterns that behavioral traits alone can't capture.

Full scoring algorithms, normalization formulas, interpretation bands, and confidence thresholds are in `references/frameworks.md`.

### Cross-Framework Consistency Check

After scoring, run a consistency check using the correlation table in `references/frameworks.md` §Big Five ↔ Enneagram Correlations. If a result strongly contradicts the expected pattern (e.g., Type 8 with very high Agreeableness), don't suppress it — flag it as a noteworthy tension and explore it in the Cross-Framework Insights section.

---

## Phase 4: Report Generation

Output the profile using this structure. The narrative sections are what make this valuable — anyone can output a table of labels. The goal is for the person to feel *seen*.

```markdown
# Your Personality Profile

## At a Glance

| Framework | Result | Confidence |
|-----------|--------|------------|
| Enneagram | Type [X]w[Y] — "[Name]" | [High/Medium/Low] |
| MBTI | [XXXX] — "[Name]" | [High/Medium/Low] |
| Big Five | O:[score] C:[score] E:[score] A:[score] N:[score] | — |
| DISC | [Primary]/[Secondary] | [High/Medium/Low] |
| Attachment | [Style] | [High/Medium/Low] |

## The Story of You

[2-3 paragraphs. This is the crown jewel — a coherent narrative that weaves
all five frameworks into a portrait of how this person thinks, feels, decides,
and relates. Written in second person ("You tend to...").

Follow this arc:
1. Opening hook — lead with the most distinctive cross-framework pattern
2. Inner world — connect Enneagram core motivation + Big Five O/N + Attachment
3. Outer world — connect MBTI cognitive functions + DISC style + Big Five E/A
4. Integration — where inner and outer reinforce each other, where they create tension
5. Growth edge — one specific, actionable insight from converging stress patterns

Do NOT list traits. Weave a story. Example thread:
"You process the world through a lens of possibility (High O, Ne-dominant) — but
unlike the stereotypical ENFP who scatters in all directions, your Type 3 core
keeps you focused on outcomes that matter. The result is someone who generates
ten ideas but instinctively filters for the one that will land..."]

## Framework Details

### Enneagram: Type [X]w[Y] — [Name]
- **Core motivation**: [what drives you]
- **Core fear**: [what you avoid]
- **Growth direction**: → Type [Y] (integrate toward [description])
- **Stress pattern**: → Type [Z] (under pressure: [description])
- **Wing influence**: Your [Y] wing adds [description]
- **Triad**: [Gut/Heart/Head] — your center of intelligence

### MBTI: [XXXX] — [Name]
- **Cognitive function stack**: [Dom] → [Aux] → [Tert] → [Inf]
- **What this means in practice**: [2-3 sentences — concrete, not abstract]
- **Borderline calls**: [any dimension within 10 of threshold — name both possibilities]

### Big Five (OCEAN)

**Openness**: [score]%
[██████████░░░░░░░░░░] [Very High/High/Average/Low/Very Low]
[1 sentence interpretation specific to this person]

**Conscientiousness**: [score]%
[████████░░░░░░░░░░░░] [label]
[1 sentence interpretation]

**Extraversion**: [score]%
[bar] [label]
[1 sentence interpretation]

**Agreeableness**: [score]%
[bar] [label]
[1 sentence interpretation]

**Neuroticism**: [score]%
[bar] [label]
[1 sentence interpretation]

### DISC: [Primary]/[Secondary]
- **Communication preference**: [how you prefer to communicate]
- **Under stress**: [behavioral shift]
- **Works best with**: [complementary styles]
- **Co-primary note**: [only if two styles within 10 points — describe blend]

### Attachment Style: [Style Name]
- **Pattern**: [description of relational tendencies]
- **In relationships**: [how this manifests concretely]
- **Growth edge**: [specific, actionable awareness]

## Cross-Framework Insights

[Connect the dots across frameworks. Look for triple signals (same pattern
appearing in 3+ frameworks) and noteworthy contradictions.

Triple signal example: "Your high Openness (Big Five) + Intuitive preference
(MBTI) + Type 4 (Enneagram) = creativity isn't just a trait, it's a core need."

Contradiction example: "Your high Agreeableness (Big Five) seems to conflict
with your Type 8 (Enneagram) — but this actually means you fight FOR people,
not against them. Your protective instinct serves connection, not dominance."

See `references/frameworks.md` §Cross-Framework Synthesis Rules for the full
pattern table.]

## What This Means for You

[1-2 paragraphs of practical, actionable takeaways. Not generic advice.
Address: one strength to lean into, one blind spot to watch, one growth
practice that specifically matches this person's profile convergence.]

## Caveats

- This is an LLM-guided assessment, not a clinically validated instrument
- Confidence levels reflect internal consistency, not psychometric validity
- Personality is contextual — you show different patterns at work vs. home
- Use these results as a mirror for reflection, not a box to live in
```

### Confidence Scoring Rules

| Framework | High | Medium | Low |
|-----------|------|--------|-----|
| Big Five | 6+ contributing questions per dim | 4-5 per dim | <4 per dim |
| MBTI | All dichotomies >20 from threshold | 1-2 within 10-20 | Any within 10 |
| Enneagram | Top type 20%+ above #2 | 10-20% above #2 | <10% above #2 |
| DISC | Primary 15+ above secondary | 8-15 above | <8 above |
| Attachment | Both dims well past threshold | One near threshold | Both near threshold |

When confidence is Low, always present the alternative:
> "Enneagram: Type 5w6 — Confidence: Low. Equally consistent with Type 1w9. Key differentiator: Does your inner critic focus on 'I need to know more' (T5) or 'I need to do better' (T1)?"

---

## Deep Mode

Deep mode uses all 40 standard questions PLUS open-ended follow-up probes. After each batch, instead of just reflecting, ask one open-ended follow-up targeting the most interesting signal you've detected:

- Batch 1-2 follow-up: "You mentioned [specific detail]. Tell me more about that — what's the internal experience like?"
- Batch 3-4 follow-up: "When [scenario from their response], what's the voice in your head saying?"
- Batch 5-6 follow-up: "Think of the last time you felt truly safe in a relationship. What made it feel that way?"
- Batch 7 follow-up: "What's the thing you're most afraid people will find out about you?"

Map follow-up responses to scoring vectors using your judgment. These responses carry 1.5× weight because they're more authentic than forced-choice answers.

The report for Deep mode adds a **"Patterns I Noticed"** section before Caveats — specific observations from the open-ended responses that illuminate the scores.

---

## Single Framework Mode

Focus on one framework with maximum depth. Use only the questions tagged for that framework in `references/question-bank.md`, plus 2-3 custom probes.

**Enneagram deep dive** (most requested):
- Use Batch 5 + Batch 7 questions (core fears + motivation)
- Add: stress behavior scenario, growth behavior scenario, wing differentiation
- Report includes: type, wing, stress/growth arrows, triad, instinctual variant hints
- Cross-reference Big Five correlations for consistency check

**MBTI deep dive**:
- Use Batch 1 (E/I) + Batch 2 (S/N) + Batch 3 (T/F) + Batch 4 (J/P)
- Add: cognitive function scenarios for top 2 type candidates
- Report includes: 4-letter type, full function stack, type dynamics, cognitive development

---

## Life Story Mode

Generate a speculative biographical narrative — from childhood to elder years — based on a completed personality profile. This mode requires prior results from a Full, Deep, or Single assessment (or user-provided framework results).

**Trigger**: `/personality-profile life-story` after completing an assessment, or when the user says "give me my life story", "what was I like as a child", or similar.

### Input Requirements

A complete profile (all 5 frameworks) OR at minimum Enneagram type + wing + one of (MBTI or Big Five). The more frameworks available, the richer the narrative.

### Six Life Stages

| Stage | Age Range | Primary Frameworks Used | Core Question |
|-------|-----------|------------------------|---------------|
| **The Seed** | 0-12 | Attachment origin + Enneagram core fear formation + Big Five O/C early patterns | How did the core wound form? |
| **The Awakening** | 13-18 | MBTI dominant function emergence + Enneagram defense mechanisms + E/N stress patterns | How did identity crystallize? |
| **The Forge** | 19-30 | DISC work style + Enneagram motivation + Te/Fe auxiliary development + Attachment in relationships | How did survival strategy become career strategy? |
| **The Ascent** | 31-45 | Enneagram stress/growth arrows in action + MBTI tertiary function awakening + Big Five N evolution | What triggered the first real identity question? |
| **The Metamorphosis** | 46-60 | MBTI inferior function confrontation + Enneagram integration direction + Attachment evolution possibility | What did freedom/authenticity actually require? |
| **The Integration** | 60+ | All frameworks converging + Enneagram health levels + Earned Secure trajectory | What gets left behind? |

### Narrative Principles

1. **Second person, literary voice** — "You were the child who..." not "Type 5 children tend to..."
2. **Concrete scenes, not abstractions** — Describe specific moments (staying late at the library, solving a problem no one else could, the night you realized you hadn't talked to anyone in three days)
3. **Weave frameworks invisibly** — The reader should feel understood, not categorized. Zero framework jargon in the narrative — no "O:83", no "Ni-Te", no "Dismissive-Avoidant". Name frameworks only when the insight is sharper for it, and even then prefer plain language
4. **Honor contradictions** — Where frameworks predict different things, that's where the richest story lives (e.g., high C + Freedom pursuit = structure-serves-freedom paradox)
5. **Include turning points** — Each stage should have at least one inflection point unique to this type combination
6. **The misidentification arc** — If the user was previously typed differently (e.g., T1 when actually T5), weave this into the story as a discovery moment
7. **Future stages are speculative** — Clearly frame unwritten chapters as "your data predicts" not "this will happen"
8. **Cultural sensitivity** — Don't assume Western life milestones. Use the user's biographical hints (if shared during assessment) to anchor the narrative

### Writing Quality Standard (The 4 Laws)

These principles separate a Life Story that makes someone cry from one that makes them nod politely. They were discovered through iterative user testing — V1 (academic) failed, V2 (clean narrative) was "okay", V3 (with all 4 laws) broke through. The moat of Life Story as a product feature is **literary quality**, not psychological accuracy.

1. **Surprise / 意外感** — The reader cannot be allowed to nod through the entire story. Every stage needs at least one "wait, what?" moment — a line that reframes something they thought they understood about themselves. Examples: "你瞧不起大多数人。不是恶意。是你真的觉得他们在浪费时间。" / "壳裂了不是英雄觉醒，是你终于累了。" The surprise should come from saying what's TRUE but what they've never heard anyone say out loud.

2. **Dirty details / 脏细节** — No elegant suffering. Replace "经济困难" with "月底数硬币买泡面". Replace "late night debugging" with "凌晨两点对着报错信息发呆，咖啡凉了也不知道". Replace "you invested in self-improvement" with "买了课发现是垃圾但不敢退款因为那是你一周的饭钱". The specificity of the detail is what makes the reader think "this is about ME, not about a personality type."

3. **Lived experience over summary / 经历 > 总结** — WRONG: "你偶尔会被情感击中。" RIGHT: "看到照片胸口发紧——你咽回去，假装在看手机。" The body knows before the mind does. Write the body sensation, the micro-behavior, the thing the reader does when no one is watching. Every emotional insight must be expressed as a scene the reader can SEE, not a conclusion they are told.

4. **Dark side / 暗面** — Every type has shadow material that conventional assessments euphemize away. Write it. Intellectual superiority as a defense mechanism ("你的聪明一直在保护你——也一直在推开人"). Using absence to hurt people in relationships ("你的伤害方式是安静的：你不在。"). Fear masquerading as principle for a decade ("你用恐惧驱动了自己十年，还以为那是原则"). The dark side is where the reader feels most deeply seen — because no one else has ever named it for them.

**Calibration**: If the story reads like something a therapist would nod approvingly at, it's too safe. If it reads like something that would make the reader pause, put down their phone, and stare at the ceiling — that's the target.

### Cross-Framework Developmental Psychology

Each framework has known developmental patterns to draw from:

**Enneagram**: Core fear forms in childhood (0-7), defense strategy solidifies in adolescence, stress/growth arrows activate in adulthood, integration is the lifelong project.

**MBTI Cognitive Functions**: Dominant develops first (childhood-adolescence), auxiliary in young adulthood (20s-30s), tertiary emerges at midlife (35-50), inferior function confrontation in later life (50+). Each function development creates a specific life chapter.

**Big Five Age Trends** (empirical): Neuroticism tends to decrease with age; Agreeableness and Conscientiousness tend to increase through midlife; Openness is relatively stable; Extraversion shows modest decline. Use these trends to project future chapters.

**Attachment**: Can shift across lifespan — Earned Secure is achievable through consistent relationship work. Dismissive-Avoidant with high Secure baseline has shortest path. Fearful-Avoidant has longest but most transformative arc.

### Output Format

```markdown
# The Story of Your Life

*Based on [type summary] — speculative narrative, not biography*

## I. 种子 · The Seed (0—12)
[400-600 words — core wound formation, early patterns, family dynamics inference]

## II. 觉醒 · The Awakening (13—18)
[400-600 words — identity crystallization, first stress patterns, misidentification seed]

## III. 锻造 · The Forge (19—30)
[400-600 words — survival strategy → career strategy, relationship patterns emerge]

## IV. 攀登 · The Ascent (31—45)
[400-600 words — success/mastery, identity questioning begins, growth direction activates]

## V. 蜕变 · The Metamorphosis (46—60)
[400-600 words — authenticity crisis, inferior function, reinvention]

## VI. 圆融 · The Integration (60+)
[200-400 words — speculative, future-facing, the resolution of the core fear]

---
*Speculative narrative based on personality data. Not biography.*
```

**No Cross-Framework Weave Index** — V1 testing showed that appending a framework-mapping table breaks the emotional spell of the narrative. The story must end as a story, not as an analysis. Framework attribution lives in the test result file, not in the Life Story output.

### Personalization Signals

Draw on anything the user shared during assessment or mentioned in conversation:
- Prior test results and misidentification history
- Career trajectory hints
- Relationship status or patterns mentioned
- Cultural background cues
- Specific answers that revealed biographical details (e.g., "I tend to leave parties early" → social energy management scene)

### Anti-Patterns for Life Story

- **Don't write a textbook** — "Type 5s in childhood typically..." is clinical death. Write a STORY.
- **Don't make every stage positive** — Include the struggles, the loneliness, the defense mechanisms that cost something
- **Don't project certainty on future stages** — "Your data suggests" not "You will"
- **Don't ignore the user's actual biographical hints** — If they mentioned being a "穷学生" who became an executive, USE that
- **Don't make it generic** — Every sentence should be impossible to write without THIS person's specific cross-framework data
- **Don't use parenthetical framework annotations** — "(O:83)" or "(Ni-Te stack)" in the narrative body breaks immersion instantly. Framework mapping belongs in test results, not in the story
- **Don't summarize emotions** — "你偶尔会被情感击中" is a report. "看到照片胸口发紧——咽回去，假装在看手机" is a story. Always choose the latter
- **Don't be uniformly warm** — If every stage arc is "struggled → grew → became stronger", the story is a lie. Some stages should end with unresolved tension, bad habits that persisted, or insights that came too late
- **Don't append analysis tables** — No Cross-Framework Weave Index, no scoring breakdown. The story must end as a story. The analytical reader already has the test results file

---

## For-App Mode

When the user is building a personality assessment feature (not taking a test):

1. Output the question bank as a JSON data structure with scoring vectors
2. Include the scoring algorithm as executable pseudocode
3. Include cross-framework mapping functions
4. Reference EnneaMe's architecture: `src/data/quickDetectionQuestionsV2.ts` for question format, `src/services/personalityEngine.ts` for signal routing, `api/src/services/bayesianEngine.ts` for Bayesian aggregation

---

## Anti-Patterns

- **Don't be clinical.** This is a conversation, not a medical exam. Warm, curious language throughout.
- **Don't over-qualify.** One caveat section at the end. Don't hedge every statement.
- **Don't flatten to labels.** "You're an INTJ" is worthless. "You lead with internal pattern-recognition (Ni), which means you often 'just know' things before you can explain how" — that's valuable.
- **Don't ignore contradictions.** High Agreeableness + Type 8 is fascinating. Explore it.
- **Don't rush.** Each batch is a mini-conversation. Acknowledge what you're hearing.
- **Don't project.** Score what the person actually said, not what their "type" would say. If their answers don't fit a clean type, say so — that's honest, not a failure.

---

## References

- `references/question-bank.md` — Full 40-question bank with scoring vectors, express set, adaptive templates
- `references/frameworks.md` — Scoring algorithms, cross-mapping tables, type descriptions, synthesis rules, confidence calibration

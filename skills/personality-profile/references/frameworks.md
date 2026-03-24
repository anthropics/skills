# Framework Reference

Detailed descriptions, scoring algorithms, and cross-mapping tables for all five frameworks.

---

## 1. Big Five (OCEAN) — Bridge Framework

The most empirically validated personality model. Score this first; MBTI and DISC derive from it.

### Dimensions

| Dimension | Low Pole | High Pole | What it Measures |
|-----------|----------|-----------|-----------------|
| **O**penness | Conventional, practical | Curious, imaginative | Receptivity to new ideas, aesthetics, variety |
| **C**onscientiousness | Flexible, spontaneous | Organized, disciplined | Self-regulation, planning, goal pursuit |
| **E**xtraversion | Reserved, solitary | Energetic, sociable | Social energy, positive affect, assertiveness |
| **A**greeableness | Competitive, skeptical | Cooperative, trusting | Interpersonal warmth, compliance, empathy |
| **N**euroticism | Calm, resilient | Sensitive, reactive | Emotional instability, anxiety, mood swings |

### Scoring Algorithm

Each question option shifts a dimension by its weight (see `question-bank.md`). After all questions:

```
raw_score[dim] = sum(all weights for that dimension)
```

Normalize to 0-100 scale:

```
# Full mode: 40 questions, max possible shift per dim ≈ ±40
normalized[dim] = clamp((raw_score[dim] + 40) / 80 * 100, 0, 100)

# Express mode: 15 questions, max possible shift ≈ ±15
normalized[dim] = clamp((raw_score[dim] + 15) / 30 * 100, 0, 100)
```

### Interpretation Bands

| Range | Label | Description |
|-------|-------|-------------|
| 0-25 | Very Low | Well below average — notable trait |
| 26-40 | Low | Below average |
| 41-60 | Average | Typical range |
| 61-75 | High | Above average |
| 76-100 | Very High | Well above average — notable trait |

---

## 2. MBTI — Derived from Big Five

### Mapping Rules

| Big Five Dimension | MBTI Dichotomy | Threshold |
|-------------------|----------------|-----------|
| Extraversion | E (≥50) / I (<50) | 50 |
| Openness | N (≥50) / S (<50) | 50 |
| Agreeableness | F (≥50) / T (<50) | 50 |
| Conscientiousness | J (≥50) / P (<50) | 50 |

### Confidence Signal

Distance from threshold indicates confidence:
- `|score - 50| > 20` → High confidence on that dichotomy
- `|score - 50| ∈ [10, 20]` → Medium confidence
- `|score - 50| < 10` → Low confidence — explicitly note both possibilities

### Cognitive Functions

Derive the dominant/auxiliary stack from the 4-letter type:

| Type | Dominant | Auxiliary | Tertiary | Inferior |
|------|----------|----------|----------|----------|
| INTJ | Ni | Te | Fi | Se |
| INTP | Ti | Ne | Si | Fe |
| ENTJ | Te | Ni | Se | Fi |
| ENTP | Ne | Ti | Fe | Si |
| INFJ | Ni | Fe | Ti | Se |
| INFP | Fi | Ne | Si | Te |
| ENFJ | Fe | Ni | Se | Ti |
| ENFP | Ne | Fi | Te | Si |
| ISTJ | Si | Te | Fi | Ne |
| ISFJ | Si | Fe | Ti | Ne |
| ESTJ | Te | Si | Ne | Fi |
| ESFJ | Fe | Si | Ne | Ti |
| ISTP | Ti | Se | Ni | Fe |
| ISFP | Fi | Se | Ni | Te |
| ESTP | Se | Ti | Fe | Ni |
| ESFP | Se | Fi | Te | Ni |

### Type Nicknames

| Type | Nickname |
|------|----------|
| INTJ | The Architect |
| INTP | The Logician |
| ENTJ | The Commander |
| ENTP | The Debater |
| INFJ | The Advocate |
| INFP | The Mediator |
| ENFJ | The Protagonist |
| ENFP | The Campaigner |
| ISTJ | The Logistician |
| ISFJ | The Defender |
| ESTJ | The Executive |
| ESFJ | The Consul |
| ISTP | The Virtuoso |
| ISFP | The Adventurer |
| ESTP | The Entrepreneur |
| ESFP | The Entertainer |

---

## 3. Enneagram — Independent Scoring

The Enneagram cannot be fully derived from Big Five — it measures core motivations and fears, not behavioral traits.

### Type Descriptions

| Type | Name | Core Fear | Core Desire | Stress → | Growth → |
|------|------|-----------|-------------|----------|----------|
| 1 | The Reformer | Being corrupt, defective | Integrity, being good | → 4 (moody, self-pity) | → 7 (spontaneous, joyful) |
| 2 | The Helper | Being unloved, unwanted | Being loved, needed | → 8 (controlling, aggressive) | → 4 (self-aware, authentic) |
| 3 | The Achiever | Being worthless, without value | Being valuable, admired | → 9 (disengaged, apathetic) | → 6 (loyal, committed) |
| 4 | The Individualist | Being ordinary, without identity | Being unique, authentic | → 2 (clingy, people-pleasing) | → 1 (principled, objective) |
| 5 | The Investigator | Being helpless, incompetent | Being capable, competent | → 7 (scattered, escapist) | → 8 (decisive, confident) |
| 6 | The Loyalist | Being without support, guidance | Having security, support | → 3 (image-focused, competitive) | → 9 (relaxed, trusting) |
| 7 | The Enthusiast | Being trapped, in pain | Being satisfied, fulfilled | → 1 (critical, rigid) | → 5 (focused, insightful) |
| 8 | The Challenger | Being controlled, harmed | Self-protection, autonomy | → 5 (withdrawn, secretive) | → 2 (caring, open-hearted) |
| 9 | The Peacemaker | Loss, fragmentation, separation | Inner stability, peace | → 6 (anxious, reactive) | → 3 (focused, assertive) |

### Scoring Algorithm

Count all Enneagram signals across questions:

```
type_score[T] = sum(weight for every option selected that has Enn:T[n] signal)
```

Weight: Each signal from a selected option counts as 1 point. Rank all 9 types by score.

**Wing determination**: The wing is whichever adjacent type (±1, wrapping 9↔1) scores higher.

```
# Example: Primary = Type 5
wing = max(type_score[4], type_score[6])  → if T4 > T6, wing = 5w4
```

**Stress/Growth arrows** (from Batch 5 Q25 + core fear questions): If user's stress behavior matches the stress direction of a type, that's a confirming signal.

### Triads

| Triad | Types | Center |
|-------|-------|--------|
| Gut (Body) | 8, 9, 1 | Instinct / Anger |
| Heart (Feeling) | 2, 3, 4 | Emotion / Shame |
| Head (Thinking) | 5, 6, 7 | Thinking / Fear |

### Big Five ↔ Enneagram Correlations (Reference Only)

These are empirical tendencies, not derivation rules. Use for consistency checks:

| Enneagram Type | Typical Big Five Pattern |
|---------------|------------------------|
| Type 1 | High C, Low N (or high N manifesting as self-criticism) |
| Type 2 | High A, High E |
| Type 3 | High C, High E, Low A |
| Type 4 | High O, High N, Low C |
| Type 5 | High O, Low E, Low A |
| Type 6 | High N, Average C |
| Type 7 | High O, High E, Low C, Low N |
| Type 8 | Low A, High E, Low N |
| Type 9 | High A, Low N, Low C |

If a user's Enneagram type strongly contradicts their Big Five profile (e.g., Type 8 with very high Agreeableness), this is noteworthy — explore it in the Cross-Framework Insights section rather than dismissing it.

---

## 4. DISC — Derived from Big Five

### Mapping Rules

DISC uses two primary Big Five dimensions:

```
Dominance (D):     High E + Low A → assertive, results-oriented
Influence (I):     High E + High A → enthusiastic, persuasive
Steadiness (S):    Low E + High A → patient, supportive
Conscientiousness (C): Low E + Low A → analytical, precise
```

### Scoring Algorithm

```
D_score = E_normalized + (100 - A_normalized)
I_score = E_normalized + A_normalized
S_score = (100 - E_normalized) + A_normalized
C_score = (100 - E_normalized) + (100 - A_normalized)
```

Primary style = highest score. Secondary = second highest.

When two styles are within 10 points, report both as co-primary.

### Style Descriptions

| Style | Profile | Communication | Under Stress | Complements |
|-------|---------|---------------|-------------|-------------|
| **D**ominance | Direct, decisive, competitive | Brief, bottom-line oriented | Impatient, insensitive | S (patience), C (caution) |
| **I**nfluence | Enthusiastic, optimistic, social | Animated, relationship-focused | Disorganized, overpromises | C (detail), D (focus) |
| **S**teadiness | Patient, reliable, team-oriented | Warm, listening-oriented | Resistant to change, passive | D (urgency), I (adaptability) |
| **C**onscientiousness | Analytical, systematic, careful | Data-driven, precise | Overanalyzes, indecisive | I (speed), S (empathy) |

---

## 5. Attachment Style — Independent Scoring

Based on the anxiety/avoidance two-dimensional model (Bartholomew & Horowitz, 1991).

### Two Dimensions

**Attachment Anxiety**: Fear of abandonment, need for reassurance, sensitivity to rejection signals.

**Attachment Avoidance**: Discomfort with closeness, preference for emotional self-sufficiency, suppression of attachment needs.

### Scoring Algorithm

Count signals from Batch 6 + stress/relationship questions:

```
anxiety_score = count(Att:Anx signals) + count(Att:Fear signals)
avoidance_score = count(Att:Avo signals) + count(Att:Fear signals)
secure_score = count(Att:Sec signals)
```

Threshold (full mode, ~12 attachment-relevant questions):
- `anxiety_high` = anxiety_score > 4
- `avoidance_high` = avoidance_score > 4

### 2×2 Classification

| | Low Avoidance | High Avoidance |
|---|---|---|
| **Low Anxiety** | **Secure** — comfortable with intimacy and independence | **Dismissive-Avoidant** — self-reliant, downplays attachment needs |
| **High Anxiety** | **Anxious-Preoccupied** — craves closeness, fears rejection | **Fearful-Avoidant** — wants closeness but fears vulnerability |

### Style Descriptions

| Style | In Relationships | Growth Edge |
|-------|-----------------|-------------|
| **Secure** | Trusting, communicative, comfortable with both closeness and autonomy | Already healthy baseline — growth through deepening empathy |
| **Anxious-Preoccupied** | Seeks reassurance, hypervigilant to partner's mood, self-worth tied to relationship | Building internal security, tolerating ambiguity |
| **Dismissive-Avoidant** | Values independence above all, slow to open up, minimizes emotions | Allowing vulnerability, recognizing need for others |
| **Fearful-Avoidant** | Push-pull pattern, wants intimacy but expects hurt | Building trust gradually, recognizing protective patterns |

---

## Cross-Framework Synthesis Rules

When generating the "Cross-Framework Insights" report section, look for these convergence patterns:

### Triple Signals (High Confidence Insights)

| Pattern | Interpretation |
|---------|---------------|
| High O + N preference + Type 4/5 | Creativity/knowledge is a core need, not just a preference |
| High A + F preference + Type 2/9 | Harmony-seeking is deep — across behavior, values, and motivation |
| Low A + T preference + Type 8 | Independence and directness are central to identity |
| High C + J preference + Type 1 | Standards and order aren't just habits — they're driven by fear of corruption |
| High E + Type 7 + Secure attachment | Genuine enthusiasm and trust — resilient extroversion |

### Contradictions Worth Exploring

| Pattern | What it Might Mean |
|---------|-------------------|
| High A + Type 8 | Protective gentleness — fights for others, not against them |
| Low N + Anxious attachment | Emotional stability in general, but activated in close relationships |
| High C + Type 7 | Structured adventurer — loves novelty but plans for it |
| Type 3 + Secure attachment | Achievement drive not rooted in insecurity — healthy ambition |
| High O + ISTJ | Curious within systems — innovates inside established frameworks |

### Narrative Synthesis Guidelines

The "Story of You" section should weave, not list. Follow this structure:

1. **Opening hook**: Lead with the most distinctive cross-framework pattern
2. **Inner world**: Connect Enneagram core motivation + Big Five O/N + Attachment
3. **Outer world**: Connect MBTI cognitive functions + DISC style + Big Five E/A
4. **Integration**: How the inner and outer connect — where they reinforce, where they create tension
5. **Growth edge**: One specific, actionable insight from the convergence of stress patterns

Example narrative thread:
> "You process the world through a lens of possibility (High O, Ne-dominant) — but unlike the stereotypical ENFP who scatters in all directions, your Type 3 core keeps you focused on outcomes that matter. The result is someone who generates ten ideas but instinctively filters for the one that will land..."

---

## Confidence Calibration

### Per-Framework Rules

| Framework | High Confidence | Medium | Low |
|-----------|----------------|--------|-----|
| Big Five | Each dimension has 6+ contributing questions | 4-5 contributing questions | <4 contributing questions |
| MBTI | All dichotomies >20 from threshold | 1-2 dichotomies within 10-20 | Any dichotomy within 10 |
| Enneagram | Top type scores 20%+ above #2 | Top type 10-20% above #2 | Top type <10% above #2 |
| DISC | Primary style 15+ above secondary | Primary 8-15 above secondary | Primary <8 above secondary |
| Attachment | Clear quadrant (both dims well past threshold) | One dim near threshold | Both dims near threshold |

### Express Mode Adjustment

In express mode (15 questions), downgrade all confidence levels by one tier:
- What would be "High" becomes "Medium"
- What would be "Medium" becomes "Low"
- Add note: "Express assessment — directional only"

### Reporting Low Confidence

When confidence is Low, always present alternatives:

```
Enneagram: Type 5w6 — "The Investigator" | Confidence: Low
  → Equally consistent with Type 1w9. Key differentiator: Does your
    inner critic focus on "I need to know more" (T5) or "I need to
    do better" (T1)?
```

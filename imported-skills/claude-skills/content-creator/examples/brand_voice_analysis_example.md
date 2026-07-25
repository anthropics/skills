# Brand Voice Analysis Example

Demonstration of brand_voice_analyzer.py input and output.

---

## Sample Input

**File: `sample_blog_post.txt`**

```
Hey there! 👋

So, like, we've been doing marketing for a really long time and we've learned SO much about what works. Today I'm gonna share some super cool tips that'll totally transform your business!

First things first - you gotta know your audience. Like, REALLY know them. What do they want? What keeps them up at night? Figure that out and you're golden!

Second, content is king (obviously). But here's the thing - not just any content. You need stuff that actually helps people. Don't just post to post, ya know?

Anyway, hope this helps! Drop a comment if you have questions! 🚀
```

---

## Command

```bash
python scripts/brand_voice_analyzer.py sample_blog_post.txt
```

---

## Sample Output (Text Format)

```
============================================================
BRAND VOICE ANALYSIS RESULTS
============================================================

VOICE PROFILE
------------------------------------------------------------
Formality Score:    25/100 (Casual)
Tone:               Conversational, Enthusiastic, Informal
Perspective:        Mixed (1st person singular + 2nd person)
Personality Match:  The Friend (primary)

READABILITY METRICS
------------------------------------------------------------
Flesch Reading Ease:    78 (Fairly Easy)
Grade Level:            6th Grade
Avg Sentence Length:    12 words
Avg Word Length:        4.2 characters

SENTENCE ANALYSIS
------------------------------------------------------------
Total Sentences:        12
Simple Sentences:       8 (67%)
Compound Sentences:     3 (25%)
Complex Sentences:      1 (8%)

VOCABULARY PATTERNS
------------------------------------------------------------
Filler Words Found:     6 (like, so, really, just, totally, super)
Contractions:           5 (we've, I'm, gonna, you're, don't)
Emoji Usage:            2
Exclamation Points:     4

RECOMMENDATIONS
------------------------------------------------------------
1. [HIGH] Reduce filler words - found 6 instances
   Action: Remove "like", "so", "really", "totally", "super"

2. [MEDIUM] Inconsistent perspective - switches between "I" and "we"
   Action: Choose one perspective and maintain throughout

3. [MEDIUM] High emoji count for professional content
   Action: Limit to 1 emoji or remove entirely for B2B

4. [LOW] Overuse of exclamation points
   Action: Replace 3 of 4 with periods for measured tone

VOICE CONSISTENCY SCORE: 62/100
============================================================
```

---

## Sample Output (JSON Format)

```bash
python scripts/brand_voice_analyzer.py sample_blog_post.txt json
```

```json
{
  "voice_profile": {
    "formality_score": 25,
    "formality_level": "Casual",
    "tone": ["Conversational", "Enthusiastic", "Informal"],
    "perspective": "Mixed",
    "personality_archetype": "The Friend"
  },
  "readability": {
    "flesch_reading_ease": 78,
    "grade_level": 6,
    "avg_sentence_length": 12,
    "avg_word_length": 4.2
  },
  "sentence_analysis": {
    "total": 12,
    "simple": 8,
    "compound": 3,
    "complex": 1
  },
  "vocabulary": {
    "filler_words": {
      "count": 6,
      "instances": ["like", "so", "really", "just", "totally", "super"]
    },
    "contractions": 5,
    "emojis": 2,
    "exclamation_points": 4
  },
  "recommendations": [
    {
      "priority": "high",
      "category": "vocabulary",
      "issue": "Excessive filler words",
      "action": "Remove casual filler words for professional tone"
    },
    {
      "priority": "medium",
      "category": "perspective",
      "issue": "Inconsistent perspective",
      "action": "Maintain single perspective throughout"
    },
    {
      "priority": "medium",
      "category": "formatting",
      "issue": "High emoji count",
      "action": "Limit emojis for professional content"
    },
    {
      "priority": "low",
      "category": "punctuation",
      "issue": "Overuse of exclamation points",
      "action": "Replace with periods for measured tone"
    }
  ],
  "consistency_score": 62
}
```

---

## Revised Content (After Applying Recommendations)

```
We've been helping businesses with marketing for over a decade, and we've
identified key principles that consistently drive results.

Understanding your audience is foundational. What challenges do they face?
What outcomes do they seek? Deep audience knowledge shapes every effective
marketing decision.

Content quality matters more than quantity. Focus on creating resources that
genuinely solve problems for your readers rather than publishing content
solely to maintain a schedule.

Questions about implementing these strategies? Leave a comment below.
```

**Re-analysis Results:**

```
Formality Score:    72/100 (Professional)
Tone:               Educational, Confident, Helpful
Perspective:        First Person Plural (consistent)
Consistency Score:  91/100
```

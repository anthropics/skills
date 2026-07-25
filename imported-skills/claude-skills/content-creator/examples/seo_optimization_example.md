# SEO Optimization Example

Demonstration of seo_optimizer.py input and output.

---

## Sample Input

**File: `draft_article.md`**

```markdown
# Marketing Tips

Marketing is important for businesses. Here are some things to know.

## Why Marketing Matters

Companies need marketing. It helps them grow. Marketing brings customers.

## Some Ideas

Try social media. Post content. Use email. Run ads.

## Conclusion

Marketing is good. Do more of it.
```

---

## Command

```bash
python scripts/seo_optimizer.py draft_article.md "content marketing strategy" "content marketing,marketing tips,business growth"
```

---

## Sample Output (Text Format)

```
============================================================
SEO ANALYSIS REPORT
============================================================

PRIMARY KEYWORD: "content marketing strategy"
SECONDARY KEYWORDS: content marketing, marketing tips, business growth

OVERALL SEO SCORE: 32/100 (Poor)

KEYWORD ANALYSIS
------------------------------------------------------------
Primary Keyword Density:    0.0% (Target: 1-3%)
  Status: NOT FOUND in content

Secondary Keyword Usage:
  - "content marketing":    0 occurrences (Target: 3-5)
  - "marketing tips":       1 occurrence (in title only)
  - "business growth":      0 occurrences (Target: 2-3)

Keyword Placement Check:
  ✗ Primary keyword NOT in title
  ✗ Primary keyword NOT in first paragraph
  ✗ Primary keyword NOT in H2 headings
  ✗ Primary keyword NOT in conclusion

CONTENT STRUCTURE
------------------------------------------------------------
Word Count:         67 words
  Status: CRITICAL - Below minimum (Target: 1,500+)

Heading Structure:
  H1: 1 (Good)
  H2: 3 (Good)
  H3: 0 (Consider adding for depth)

Paragraph Analysis:
  - Average length: 12 words (Too short - Target: 40-80)
  - Total paragraphs: 6

READABILITY
------------------------------------------------------------
Flesch Reading Ease:    82 (Easy)
  Note: May be too simple for B2B audience

META ELEMENTS
------------------------------------------------------------
Meta Title:         Not specified
  Suggestion: "Content Marketing Strategy: 10 Proven Tips for 2025"

Meta Description:   Not found
  Suggestion: "Discover actionable content marketing strategies to drive
  business growth. Learn proven techniques for content that converts."

INTERNAL/EXTERNAL LINKS
------------------------------------------------------------
Internal Links:     0 (Target: 2-3)
External Links:     0 (Target: 1-2 authoritative sources)

RECOMMENDATIONS (Priority Order)
------------------------------------------------------------

[P0] CRITICAL - Content Length
  Issue: 67 words is severely below minimum
  Action: Expand to 1,500-2,500 words with detailed sections

[P0] CRITICAL - Missing Primary Keyword
  Issue: "content marketing strategy" not found anywhere
  Action: Include in title, first paragraph, 2 H2s, and conclusion

[P1] HIGH - Thin Content Sections
  Issue: Paragraphs average 12 words
  Action: Expand each section with examples, data, and actionable steps

[P1] HIGH - Missing Internal Links
  Issue: No links to related content
  Action: Add 2-3 links to relevant articles

[P2] MEDIUM - No Meta Description
  Issue: Missing meta description
  Action: Add 150-160 character description with primary keyword

[P2] MEDIUM - Missing H3 Subheadings
  Issue: No H3s for content depth
  Action: Add H3s under each H2 for better structure

============================================================
```

---

## Sample Output (JSON Format)

```bash
python scripts/seo_optimizer.py draft_article.md "content marketing strategy" --json
```

```json
{
  "overall_score": 32,
  "grade": "Poor",
  "primary_keyword": "content marketing strategy",
  "keyword_analysis": {
    "primary_density": 0.0,
    "target_density": "1-3%",
    "primary_found": false,
    "secondary_keywords": {
      "content marketing": {"count": 0, "target": "3-5"},
      "marketing tips": {"count": 1, "target": "2-3"},
      "business growth": {"count": 0, "target": "2-3"}
    },
    "placement": {
      "in_title": false,
      "in_first_paragraph": false,
      "in_h2_headings": false,
      "in_conclusion": false
    }
  },
  "content_structure": {
    "word_count": 67,
    "min_recommended": 1500,
    "headings": {"h1": 1, "h2": 3, "h3": 0},
    "paragraphs": {"count": 6, "avg_length": 12}
  },
  "readability": {
    "flesch_score": 82,
    "level": "Easy"
  },
  "meta": {
    "title": null,
    "description": null,
    "suggested_title": "Content Marketing Strategy: 10 Proven Tips for 2025",
    "suggested_description": "Discover actionable content marketing strategies to drive business growth. Learn proven techniques for content that converts."
  },
  "links": {
    "internal": 0,
    "external": 0,
    "target_internal": "2-3",
    "target_external": "1-2"
  },
  "recommendations": [
    {
      "priority": "P0",
      "category": "content_length",
      "issue": "Content severely below minimum word count",
      "action": "Expand to 1,500-2,500 words"
    },
    {
      "priority": "P0",
      "category": "keyword",
      "issue": "Primary keyword not found",
      "action": "Include in title, first paragraph, H2s, conclusion"
    },
    {
      "priority": "P1",
      "category": "content_depth",
      "issue": "Thin content sections",
      "action": "Expand with examples, data, actionable steps"
    },
    {
      "priority": "P1",
      "category": "links",
      "issue": "No internal links",
      "action": "Add 2-3 relevant internal links"
    }
  ]
}
```

---

## Optimized Content (After Applying Recommendations)

```markdown
# Content Marketing Strategy: 10 Proven Techniques for Business Growth

A well-executed content marketing strategy separates thriving businesses from
those struggling to gain visibility. This comprehensive guide covers the
essential techniques that drive measurable results.

## Why Content Marketing Strategy Matters for Business Growth

Companies investing in strategic content marketing see 3x more leads than
those relying solely on paid advertising. Content marketing builds lasting
assets that continue generating value long after publication.

The compounding effect of quality content creates sustainable business growth:
- Organic search traffic increases over time
- Brand authority strengthens with each published piece
- Customer acquisition costs decrease as content library grows

### The ROI of Strategic Content

According to Content Marketing Institute research, businesses with documented
content strategies are 313% more likely to report success than those without.

[Continue for 1,500+ words with detailed sections...]

## Conclusion: Building Your Content Marketing Strategy

Implementing these content marketing techniques positions your business for
sustained growth. Start with audience research, create a documented strategy,
and commit to consistent execution.

Related reading: [Link to internal article on content calendars]
```

**Re-analysis Results:**

```
OVERALL SEO SCORE: 87/100 (Good)

✓ Primary keyword density: 1.8%
✓ Keyword in title, first paragraph, H2s, conclusion
✓ Word count: 1,847 words
✓ Meta description: Present (156 characters)
✓ Internal links: 2
✓ External links: 1 (authoritative source)
```

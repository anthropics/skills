# Pre-Publish Optimization Checklist

Run this before every piece goes live. Each section is a gate — fail a gate, fix it before moving on.

---

## Gate 1: SEO Signals

### Title & Headers
- [ ] H1 contains primary keyword (naturally, not forced)
- [ ] H1 is ≤70 characters
- [ ] At least 2 H2s contain secondary keywords or related phrases
- [ ] No two H2s are duplicates or near-duplicates
- [ ] H1 differs from the title tag (they can overlap but shouldn't be identical)

### Keyword Presence
- [ ] Primary keyword appears in the first 100 words
- [ ] Primary keyword appears 3-5 times total (not more — stuffing tanks rankings)
- [ ] Keyword variations appear naturally throughout
- [ ] No keyword stuffing (reading it aloud sounds natural)

### Meta & Technical
- [ ] Title tag: 50-60 characters, keyword-first where possible
- [ ] Meta description: 150-160 characters, includes keyword, ends with hook or action
- [ ] URL slug: short, keyword-first, lowercase, hyphens not underscores
- [ ] Canonical URL is set
- [ ] OG title and OG description written for social sharing

### Images & Media
- [ ] At least one image present
- [ ] All images have descriptive alt text (keyword included where natural)
- [ ] Images are compressed (under 200KB each)
- [ ] Image filenames are descriptive (not IMG_4832.jpg)

---

## Gate 2: Readability

### Score
- [ ] Flesch Reading Ease score ≥ 60 (aim for 60-70 for professional audience; 70+ for general)
- [ ] Run `scripts/content_scorer.py` — overall score ≥ 70

### Sentence & Paragraph Structure
- [ ] Average sentence length ≤ 20 words
- [ ] No single paragraph exceeds 4 sentences
- [ ] No sentence exceeds 35 words (check and break if found)
- [ ] Sentence length varies — not all short, not all long

### Voice & Clarity
- [ ] Active voice dominant (passive voice < 20% of sentences)
- [ ] No weasel words ("very," "really," "quite," "somewhat")
- [ ] No jargon without explanation (for non-expert audiences)
- [ ] All acronyms spelled out on first use
- [ ] Contractions used where natural (improves readability)

---

## Gate 3: Structure & Content Quality

### Opening
- [ ] Intro is ≤150 words
- [ ] Intro does not start with "In today's..." or "Welcome to..."
- [ ] Intro names the reader's problem or situation within the first 2 sentences
- [ ] Intro clearly signals what the reader will get from this piece
- [ ] No false promise in the intro (piece delivers what it hints at)

### Body
- [ ] Every H2 section leads with its main point (buried leads = reader drop-off)
- [ ] At least 2 concrete examples, case studies, or data points
- [ ] All statistics and specific claims have citations or are labeled as estimates
- [ ] No fluff paragraphs (every paragraph earns its place — if removing it changes nothing, cut it)
- [ ] Visual break (table, list, callout, image) at least every 400 words

### Conclusion
- [ ] Conclusion ≤150 words
- [ ] Summarizes the core argument (not just "in conclusion...")
- [ ] Includes one clear next step or CTA
- [ ] Doesn't introduce new arguments or ideas

---

## Gate 4: Internal Linking

- [ ] 2-4 internal links to existing content on the site
- [ ] Anchor text describes the destination (not "click here" or "this article")
- [ ] Links tested and confirmed working (no 404s)
- [ ] No excessive linking to the same page multiple times
- [ ] At least one high-traffic page links to this piece (plan this before publishing)

---

## Gate 5: Factual Accuracy

- [ ] Every statistic cited with source (year + organization)
- [ ] All external links go to credible sources (not competitors, not thin content)
- [ ] No claims made without evidence or without "in my experience" qualifier
- [ ] All product/feature mentions are accurate (check with product team if needed)
- [ ] Quotes are attributed correctly and not paraphrased beyond recognition
- [ ] No outdated information — check date-sensitive claims (pricing, regulations, stats)

---

## Gate 6: Brand & Voice

- [ ] Matches brand voice (check `.claude/product-marketing-context.md` if available)
- [ ] Consistent POV throughout (first person, second person, or third — pick one)
- [ ] Consistent tense (present or past — don't mix)
- [ ] No off-brand claims (anything that overpromises, contradicts other content, or sounds unlike us)
- [ ] CTA aligns with piece goal (don't pitch demo on an informational piece for beginners)

---

## Gate 7: Final Readthrough

Run a final read-aloud. Catch what scanning misses.

- [ ] Read the full piece aloud — anything that makes you stumble, fix it
- [ ] The piece flows — section to section makes sense without re-reading
- [ ] The headline still feels earned after reading the piece
- [ ] You'd share this piece yourself (if not, it's not done)
- [ ] No placeholder text, formatting artifacts, or draft notes left in

---

## Scoring Summary

| Gate | Status | Notes |
|---|---|---|
| SEO Signals | ✅ / ❌ | |
| Readability | ✅ / ❌ | |
| Structure & Quality | ✅ / ❌ | |
| Internal Linking | ✅ / ❌ | |
| Factual Accuracy | ✅ / ❌ | |
| Brand & Voice | ✅ / ❌ | |
| Final Readthrough | ✅ / ❌ | |

**Publish only when all 7 gates are green.**

If you're skipping a gate, document why. Conscious tradeoffs are fine. Unconscious shortcuts aren't.

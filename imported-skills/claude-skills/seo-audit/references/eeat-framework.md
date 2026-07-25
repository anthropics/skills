# E-E-A-T Framework Reference

Experience, Expertise, Authoritativeness, Trustworthiness — Google's quality rater guidelines framework for evaluating content quality. Updated per September 2025 Quality Rater Guidelines.

## The four signals

| Signal | What it means | How to demonstrate |
|---|---|---|
| **Experience** | First-hand experience with the topic | Personal anecdotes, original photos, usage details, "I tested this" |
| **Expertise** | Demonstrable knowledge or skill | Credentials, detailed technical depth, accurate terminology |
| **Authoritativeness** | Recognition by others in the field | Backlinks from authoritative sites, citations, brand mentions |
| **Trustworthiness** | Accuracy, transparency, safety | HTTPS, clear authorship, sources cited, contact info, privacy policy |

**Trust** is the most important — it encompasses the other three. A page can have expertise but lose trust through misleading claims.

## Audit checklist

### Experience signals
- [ ] Author has demonstrable experience with the topic
- [ ] Content includes first-hand observations (not just research summaries)
- [ ] Original images or screenshots (not stock photos)
- [ ] Specific details that only come from experience

### Expertise signals
- [ ] Author bio with relevant credentials
- [ ] Content depth matches topic complexity (YMYL topics need more)
- [ ] Accurate, up-to-date information
- [ ] Proper use of domain terminology

### Authoritativeness signals
- [ ] Site is recognized in its niche (backlink profile)
- [ ] Author has published elsewhere on this topic
- [ ] Content is cited by other authoritative sources
- [ ] Organization has relevant credentials/certifications

### Trustworthiness signals
- [ ] HTTPS enforced
- [ ] Clear author attribution (name, bio, photo)
- [ ] Sources cited with links
- [ ] Contact information accessible
- [ ] Privacy policy present
- [ ] No misleading claims or clickbait
- [ ] Content reviewed or updated regularly (dateModified)

## YMYL topics (Your Money or Your Life)

Topics that could impact health, safety, financial stability, or well-being require **higher E-E-A-T standards**:

- Health and medical information
- Financial advice and transactions
- Legal information
- News and current events
- Safety-related information
- Shopping (when significant money is involved)

For YMYL: authors MUST have verifiable credentials. Self-reported expertise is insufficient.

## Scoring for seo_health_scorer.py

```
Content category checks → E-E-A-T subchecks:
  Author bio present and linked      → pass/fail (high severity)
  Sources cited with URLs            → pass/fail (medium severity)
  dateModified within 12 months      → pass/warn/fail (medium severity)
  YMYL topic + qualified author      → pass/fail (critical severity for YMYL)
  Contact information accessible     → pass/fail (medium severity)
```

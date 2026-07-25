# Campaign Templates

Ready-to-use campaign briefs and structures for LinkedIn, Google, and Meta.

---

## Table of Contents

- [Campaign Brief Template](#campaign-brief-template)
- [LinkedIn Ads Structure](#linkedin-ads-structure)
- [Google Ads Structure](#google-ads-structure)
- [Meta Ads Structure](#meta-ads-structure)
- [Ad Copy Frameworks](#ad-copy-frameworks)

---

## Campaign Brief Template

Use for every campaign:

```
Campaign Name: [Q2-2025-LinkedIn-ABM-Enterprise]
Objective: [Generate 50 SQLs from Enterprise accounts ($50k+ ACV)]
Budget: [$15k/month]
Duration: [90 days]
Channels: [LinkedIn Ads, Retargeting, Email]
Audience: [Director+ at SaaS companies, 500-5000 employees, EU/US]
Offer: [Gated Industry Benchmark Report]

Success Metrics:
  - Primary: 50 SQLs, <$300 CPO
  - Secondary: 500 MQLs, 10% MQL→SQL rate, 40% email open rate

HubSpot Setup:
  - Campaign ID: [create in HubSpot]
  - Lead scoring: +20 for download, +30 for demo request
  - Attribution: First-touch + Multi-touch

Handoff Protocol:
  - SQL criteria: Title + Company size + Budget confirmed
  - Routing: Enterprise SDR team via HubSpot workflow
  - SLA: 4-hour response time
```

**Validation:** Campaign appears in HubSpot with all assets tagged.

---

## LinkedIn Ads Structure

### Account Hierarchy

```
Account
└─ Campaign Group: [Q2-2025-Enterprise-ABM]
   ├─ Campaign 1: [Awareness - Thought Leadership]
   │  ├─ Ad Set: [CTO/VP Eng, US, Tech Companies]
   │  └─ Creatives: [3 carousel posts, 2 video ads]
   ├─ Campaign 2: [Consideration - Product Education]
   │  ├─ Ad Set: [Engaged audience, retargeting]
   │  └─ Creatives: [2 lead gen forms, 1 landing page]
   └─ Campaign 3: [Conversion - Demo Requests]
      ├─ Ad Set: [Website visitors, content downloaders]
      └─ Creatives: [Direct demo CTA, case study]
```

### Targeting Settings

| Parameter | Series A Sweet Spot |
|-----------|---------------------|
| Company Size | 50-5000 employees |
| Job Titles | Director+, VP+, C-level |
| Industries | Software, SaaS, Tech Services |
| Budget | Start $50/day per campaign |

### Scaling Rules

- CAC < target → Increase budget 20% weekly
- CAC > target → Pause, optimize, relaunch
- Scale 20% weekly maximum to maintain performance

### Lead Gen Forms vs Landing Pages

| Type | Conversion | Quality | Use Case |
|------|------------|---------|----------|
| Lead Gen Forms | 2-3x higher | Lower | TOFU/MOFU |
| Landing Pages | Lower | Higher | BOFU/demos |

**Validation:** LinkedIn Insight Tag firing. Matched audiences syncing.

---

## Google Ads Structure

### Campaign Priority

1. **Search - Brand** (highest priority, protect brand terms)
2. **Search - Competitor** (steal market share)
3. **Search - Solution** (problem-aware buyers)
4. **Search - Product Category** (earlier stage)
5. **Display - Retargeting** (re-engage warm traffic)

### Search Campaign Template

```
Campaign: [Search-Solution-Keywords]
├─ Ad Group: [project management software]
│  ├─ Keywords:
│  │  - "project management software" [Phrase]
│  │  - "best project management tool" [Phrase]
│  │  - +project +management +solution [Broad Match Modifier]
│  └─ Ads: [3 responsive search ads]
│
└─ Ad Group: [team collaboration tools]
   ├─ Keywords: [5-10 tightly themed keywords]
   └─ Ads: [3 responsive search ads]
```

### Keyword Strategy

| Type | Match | Bid Priority |
|------|-------|--------------|
| Brand Terms | Exact | High - protect brand |
| Competitor Terms | Phrase | Medium - comparison |
| Solution Terms | Phrase | Medium - category |
| Problem Terms | Broad | Lower - education |

### Negative Keywords (Maintain 100+)

```
free, cheap, jobs, career, reviews, salary, login, support,
download, tutorial, course, certification, example, template
```

### Bid Strategy Progression

1. New campaigns: Manual CPC (control)
2. After 50+ conversions: Target CPA
3. After 100+ conversions: Maximize Conversions with tCPA
4. EU markets: Bid 15-20% higher for same quality

**Validation:** Conversion tracking firing. Search terms report reviewed weekly.

---

## Meta Ads Structure

### When to Use Meta

| Scenario | Meta | LinkedIn |
|----------|------|----------|
| ACV <$10k | ✅ | ❌ |
| Visual product | ✅ | ❌ |
| SMB audience | ✅ | ❌ |
| Enterprise | ❌ | ✅ |

### Campaign Template

```
Campaign Objective: [Conversions]
├─ Ad Set 1: [Lookalike - 1% of converters]
│  └─ Placement: [Feed + Stories, Auto]
├─ Ad Set 2: [Interest - Business Software]
│  └─ Placement: [Feed only]
└─ Ad Set 3: [Retargeting - Website 30d]
   └─ Placement: [All placements]
```

### Creative Best Practices

- Video format: 1:1 or 9:16 for Stories
- First 3 seconds: Hook with problem or result
- Show product UI in action
- Add captions (85% watch muted)
- Test 3-5 variants per campaign

**Validation:** Meta Pixel events firing. Conversion values passing correctly.

---

## Ad Copy Frameworks

### LinkedIn Thought Leadership

```
[Industry insight or contrarian take]

[Supporting data point or experience]

[Call to discuss or engage]

#RelevantHashtag #Industry
```

### LinkedIn Social Proof

```
[Customer result with specific numbers]

"[Customer quote]"
- [Name, Title, Company]

[Soft CTA: See how →]
```

### Google Responsive Search Ads

**Headlines (15 required):**
- H1-3: Value props (Save 10 hours/week, Trusted by 500+ teams)
- H4-6: Features (AI-powered, Real-time sync, Mobile app)
- H7-9: Social proof (4.8★ G2 rating, Used by Microsoft)
- H10-12: CTAs (Start free trial, Book demo, See pricing)
- H13-15: Dynamic keyword insertion

**Descriptions (4 required):**
- D1: Primary value prop + CTA (30-60 chars)
- D2: Feature list + differentiator (60-90 chars)
- D3: Social proof + urgency (45-90 chars)
- D4: Backup generic (60-90 chars)

**Validation:** Ad strength score of "Excellent" before launch.

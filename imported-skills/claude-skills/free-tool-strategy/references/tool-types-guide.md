# Tool Types Guide — Comprehensive Reference for Free Marketing Tools

Each tool type explained with examples, build complexity, typical outcomes, and design guidance.

---

## The 7 Tool Types

### 1. Calculators

**What they do:** Take numerical or categorical inputs → output a calculated result (a number, range, or score).

**Examples:**
- SaaS Pricing Calculator ("What should you charge?")
- ROI Calculator ("How much would you save?")
- LTV Calculator ("What's your customer worth?")
- Churn Impact Calculator ("What does 1% more churn cost you?")
- Salary Calculator by role/location/experience

**Build complexity:** Low–Medium
- Simple formula: 1-2 days of dev
- Multi-variable model: 1-2 weeks

**Lead potential:** High — people want to save or email complex results.

**SEO value:** Medium-High — calculators earn links from resource pages and ranking for "[topic] calculator" queries.

**Viral potential:** Medium — people share results when they're surprising or validating.

**Design tips:**
- Sliders are more satisfying than input fields for numerical ranges
- Show results dynamically (real-time as they adjust inputs)
- Include a "how this was calculated" section for credibility
- Email results: "Send this to myself" captures the lead naturally

**What makes a calculator link-worthy:**
The underlying model must be credible. If you're calculating LTV, show your formula and cite your assumptions. A calculator with methodology is shareable content, not just a widget.

---

### 2. Generators

**What they do:** Take inputs (topic, style, parameters) → output structured text or content.

**Examples:**
- Headline Generator (input: product + audience → 10 headline options)
- LinkedIn Bio Generator
- Job Description Generator
- Email Subject Line Generator
- Product Description Generator
- Business Name Generator

**Build complexity:** Low (template-based) to High (LLM-powered)

**Template-based (madlibs):**
- 1-3 days
- Take inputs, fill template slots, combine with variations
- Deterministic output

**LLM-powered:**
- 1-2 weeks (API integration + prompt engineering)
- Generative output
- Requires API key costs to be modeled into business case

**Lead potential:** Medium — output varies, so gating with email is natural if you offer "save and regenerate."

**SEO value:** High for "[topic] generator free" — some of the highest-traffic tools are generators.

**Viral potential:** High — people share clever or surprisingly good generated outputs.

**Design tips:**
- Show an example output before the user enters anything (reduces bounce)
- Generate 3-5 variations, not just 1
- "Copy to clipboard" button is a must
- "Generate again" encourages engagement (more pageviews, better SEO signal)

---

### 3. Checkers

**What they do:** Analyze a URL, email, text, file, or domain → return an audit or pass/fail assessment.

**Examples:**
- SEO Checker ("Analyze your page's SEO")
- Email Spam Checker ("Will your email hit spam?")
- Website Speed Checker
- LinkedIn Profile Checker
- Ad Copy Compliance Checker
- Password Strength Checker
- Domain Authority Checker

**Build complexity:** Medium–High
- Text analysis (readability, keyword density): 2-5 days
- URL crawling (page analysis): 1-2 weeks
- Email delivery testing: 1-2 weeks + email infrastructure

**Lead potential:** High — checker results are specific to the user; saves/exports feel natural.

**SEO value:** Very High — "[type] checker" or "check my [thing]" queries are often high-volume.

**Viral potential:** High — "Your page scored 47/100 — here's what's broken" drives sharing.

**Design tips:**
- Score the output (0-100) — people anchor on scores and compare
- Categorize results: Critical / Warnings / Passed
- Prioritize issues — don't just list everything, rank by impact
- Loading state matters — show progress (feels like analysis is happening)

---

### 4. Graders

**What they do:** Score something holistically against a rubric. More opinionated than a checker — you're grading against a defined standard.

**Examples:**
- Website Grader (HubSpot's classic)
- Sales Page Grader
- Email Newsletter Grader
- LinkedIn Company Page Grader
- Onboarding Flow Grader
- Pricing Page Grader

**Build complexity:** Medium
- Define the rubric first (the criteria matter more than the tech)
- Usually 1-2 weeks

**Lead potential:** Very High — graders feel like getting a report card; people want the full results.

**SEO value:** High for niche graders ("sales page grader" etc.).

**Viral potential:** Medium-High — share your score as social proof or to invite critique.

**Design tips:**
- The grade (A-F or 0-100) is the hook — show it prominently
- Break down the grade into components (e.g., "Design: A, Copy: C, CTA: D")
- Each component should explain why and how to improve it
- The improvement advice is where the lead capture is earned

---

### 5. Converters

**What they do:** Transform input from one format to another. Pure utility.

**Examples:**
- Markdown to HTML Converter
- Timestamp Converter
- CSV to JSON Converter
- Video Frame Rate Converter
- UTC to Local Time Converter
- File Format Converter
- Currency Converter

**Build complexity:** Very Low – Low
- Most conversions are 1-2 days
- Pure client-side (no server needed)

**Lead potential:** Low — pure utility, low friction reason to capture email.

**SEO value:** Medium — "convert X to Y" queries exist but are dominated by large tool sites.

**Viral potential:** Low — people bookmark and return, don't share.

**When to build:** Only if the conversion is specific to your audience (e.g., a SaaS for designers building a "Figma token to CSS converter"). Generic converters are dominated by free sites with years of SEO authority.

---

### 6. Templates

**What they do:** Pre-built, fillable documents that users download, copy, or use.

**Examples:**
- Job Description Templates
- Product Roadmap Template
- SaaS Metrics Dashboard Template (Google Sheets)
- Email Sequence Template
- SEO Content Brief Template
- Brand Voice Guide Template
- Engineering RFP Template

**Build complexity:** Very Low
- Template creation: hours to 1 day
- Hosting: Google Docs/Sheets share, Notion public page, or downloadable PDF

**Lead potential:** Very High — download = natural lead capture (email to send the file).

**SEO value:** High — "[role] template" queries are competitive but high-intent.

**Viral potential:** Medium — people share templates that save them real time.

**Design tips:**
- The template itself is the product — make it excellent
- Include instructions inside the template
- Offer a "filled example" so users understand what it should look like
- Update templates seasonally to keep them ranking

---

### 7. Interactive Visualizations

**What they do:** Show data, concepts, or comparisons in a visual, explorable way.

**Examples:**
- SaaS Market Map (interactive, filterable)
- Marketing Funnel Visualizer
- Company Comparison Tool (filter by size, location, tech stack)
- Real-Time Industry Benchmark Dashboard
- Interactive Pricing Comparison

**Build complexity:** High
- 2-6 weeks typically
- Requires data (your own research, public datasets, or API)
- May require ongoing data maintenance

**Lead potential:** Medium — users engage deeply but email capture isn't always natural.

**SEO value:** Very High if data-driven — journalists and bloggers link to unique datasets.

**Viral potential:** Very High if the data is surprising or highly visual — these are your link magnets.

**Design tips:**
- The data is the moat — if you have unique data, this is the highest-leverage tool type
- Interactive beats static for time-on-page
- Make it embeddable (embed code button) for backlink acquisition
- Update the data regularly — stale data kills backlinks when someone discovers it

---

## Build vs. No-Code Decision Guide

| Tool Type | No-Code Options | When to Go Custom Dev |
|-----------|---------------|----------------------|
| Calculator | Outgrow, Calconic, Typeform | When logic is complex, or brand/speed matters |
| Generator | Typeform + Zapier, GPT wrappers | When you need custom LLM behavior |
| Checker | Limited — usually needs dev | Always (URL crawling, text analysis) |
| Grader | Outgrow, Involve.me | When the rubric is fixed and simple |
| Converter | Findable no-code tools | Rarely — utility tools are trivially buildable |
| Template | Google Docs, Notion, Canva | When document quality matters |
| Visualization | Flourish, Observable | When data is complex or interactive |

---

## What Makes a Tool "10x Better Than the Existing Free Option"

If there's already a free tool for the job, you need a compelling reason to build yours. One of:

1. **Niche specificity** — existing tool is generic, yours is specific to your audience's workflow
2. **Better UX** — existing tools are ugly, clunky, or require too many steps
3. **Integrated action** — after results, existing tools drop the user; yours offers next steps or a trial
4. **Unique data or model** — your checker uses proprietary data that others don't have
5. **Shareable output** — existing tools give results in a table; yours generates a shareable card or PDF

Don't build "the same tool, but ours." That's a traffic fight you won't win. Build "the tool that does what the others don't."

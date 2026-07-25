# Launch Playbook — How to Launch a Free Tool for Maximum Impact

A free tool with no distribution is just code sitting on a server. This playbook gives you the launch sequence that turns a new tool into traffic, leads, and backlinks.

---

## The Launch Mindset

Most companies "launch" by posting it on LinkedIn and waiting. That gets you 200 visits from your existing followers and then nothing.

A real launch is a 4-week sustained distribution campaign. You're not announcing — you're seeding. Every channel you touch plants a seed that compounds over months (especially for SEO).

---

## Pre-Launch Checklist (1–2 Weeks Before)

### SEO Foundations
- [ ] Target keyword researched and confirmed (search volume + low-medium competition)
- [ ] URL slug locked: `/tools/[keyword-rich-name]`
- [ ] Meta title written: "[Free Tool Name] — [What It Does] | [Brand]"
- [ ] Meta description written: 155 chars, includes target keyword, tells user what they get
- [ ] H1 matches search intent, not just brand name
- [ ] `SoftwareApplication` schema markup added (see SKILL.md)
- [ ] Internal links from related content pointing to the tool page
- [ ] Tool page links to 2-3 related resources on your site

### Tool Quality Gate
- [ ] Core value delivered in ≤3 user inputs
- [ ] Results render on mobile
- [ ] Results are shareable (unique URL, copy button, or social share)
- [ ] Lead capture is in place (but gated after value, not before)
- [ ] Email delivery working if you're sending results via email
- [ ] Error handling — what happens with bad inputs?
- [ ] Load time <3 seconds (tools with slow loads have brutal bounce rates)

### Analytics Setup
- [ ] GA4 (or Plausible) tracking installed
- [ ] Key events tracked: tool_started, tool_completed, lead_captured, result_shared
- [ ] Google Search Console verified
- [ ] Heatmap tool installed (Hotjar or Microsoft Clarity) to watch real usage

### Outreach List Ready
- [ ] List of 20-50 sites that link to similar free tools (from Ahrefs / Google "site:domain resources")
- [ ] List of newsletters in your category that feature tools
- [ ] List of subreddits and communities where your audience hangs out
- [ ] Influencers or thought leaders who regularly share tools in your space

---

## Launch Week — The Sequence

### Day 1: SEO and Directories
- Submit tool to Google Search Console (Request Indexing)
- Submit to Bing Webmaster Tools
- Submit to relevant online directories (AlternativeTo, Product Hunt upcoming, SaaSHub, Capterra if applicable)
- Post in your company's blog (a 600-900 word post explaining the tool, linking to it)

### Day 2: Product Hunt
- Submit to Product Hunt at midnight PST (Thursday or Tuesday for best timing)
- Have your team and early fans upvote in the first 2 hours
- Respond to every comment personally — PH algorithm rewards engagement
- Ask your top customers to upvote (personalized message, not mass email)
- Product Hunt tip: the thumbnail image and tagline matter more than the description

### Day 3: Community Seeding (No Pitch)
- Post in relevant subreddits — share as a resource, not a promotion
  - Frame: "I built this free [tool type] for [audience] because I couldn't find one — feedback welcome"
  - No "check out our new tool" — that's spam and gets removed
- Share in Slack communities in your industry
- Share in relevant Facebook groups
- LinkedIn post — personal post from founder, not company page (personal posts get 10× the reach)

### Day 4: Email to Your List
- Dedicated email to your subscriber list introducing the tool
- Subject line: "Free [Tool Name] — [benefit in 5 words]"
- Keep it short: what it is, why you built it, one sentence result, link
- Ask them to share with one person who'd benefit

### Day 5: Hacker News
- Post to HN with a "Show HN:" prefix: `Show HN: [Tool Name] — [what it does in one line]`
- HN community responds well to honest builder posts with a unique angle
- Must be technically interesting or niche — generic marketing tools don't land
- Be available to answer technical questions in the thread all day

### Day 6-7: Social Amplification
- Twitter/X thread: "I built a free [tool] for [audience]. Here's how it works:" → walkthrough with screenshots
- Short-form video (LinkedIn/TikTok): screen recording of yourself using the tool
- Reach out to 5 people who you know will love it — personal message, not mass email

---

## Post-Launch: Weeks 2-4

### Backlink Outreach
This is where the long-term SEO value comes from.

**Identify targets:**
1. Search Google: `"best free tools for [your category]"` — email everyone on that list
2. Use Ahrefs: find pages linking to similar tools → those same pages may link to yours
3. Search: `"[competitor tool name]" site:[niche blog]` — those bloggers are interested in tools like yours

**Outreach template:**
```
Subject: Free [Tool Name] that might fit your "[Resource List Title]" post

Hi [Name],

I noticed your post on the best free tools for [category]. I recently built [Tool Name] 
— it helps [audience] [specific outcome] without [common pain point].

[Direct link to tool]

Would it fit your list? Happy to give you early access or a custom embed if that's useful.

[Your name]
```

**Volume:** 50-100 personalized outreach emails in the first 30 days. Expect 5-15% positive response. One good resource page link is worth 50 generic directory submissions.

### Content That Multiplies
- Write a guide that uses the tool as a central reference: "How to [goal] — with a free calculator to check your numbers"
- Create a results-based case study: "We analyzed 500 [things] with our [tool] — here's what we found"
- Partner with a newsletter: offer to write a guest post that features the tool as the main resource

---

## Measurement — First 90 Days

### Weekly Check-ins (GA4 + GSC)

| Week | What to Look For |
|------|----------------|
| 1 | Direct traffic from launch channels. Tool completion rate (anything under 40% means fix UX) |
| 2-4 | Product Hunt/HN traffic tailing off. Backlinks starting to trickle in. |
| 5-8 | First organic impressions in GSC. Check what queries are sending traffic. |
| 9-12 | Organic traffic should be visible. Lead capture rate should be stable. |

### The "Is It Working?" Test at 90 Days

| Metric | Needs Work | Good | Great |
|--------|-----------|------|-------|
| Organic sessions/month | <200 | 500–2,000 | >5,000 |
| Tool completion rate | <30% | 40–60% | >70% |
| Lead conversion rate (completions → email) | <3% | 5–15% | >20% |
| Referring domains (backlinks) | <5 | 10–30 | >50 |

---

## When a Launch Flops

A tool can fail to gain traction for 4 reasons:

1. **Wrong keyword** — nobody searches for this. Check GSC; if you have zero impressions after 60 days, the keyword target is wrong. Pivot the page copy to a related term with volume.

2. **Wrong problem** — the tool exists, but it's not solving an acute enough problem. Talk to 5 people who used it and didn't return. What were they hoping for?

3. **Gated too early** — traffic is high but completion is low. You're asking for email before delivering value. Remove or move the gate.

4. **Distribution failure** — the tool is fine, but you only posted it once. Run the backlink outreach again with a fresh list. Submit to 10 new directories. Write the guide post.

Most "failed" tools aren't actually failures — they just didn't get the 90-day distribution campaign they needed.

---

## Tools That Keep Working (Maintenance)

A free tool is a 3-year investment, not a 3-week campaign.

**Monthly:**
- Check tool is still functioning (APIs, URLs, formulas)
- Review top search queries in GSC → update H2s and content to match
- Add one new feature based on user requests (check support inbox)

**Quarterly:**
- Update any data the tool uses (benchmarks, averages, rates)
- Refresh the landing page copy — Google rewards freshness
- Identify 20 new backlink targets and run outreach

**Annually:**
- Full UX review — does it still work on the latest mobile browsers?
- Competitive audit — are better free alternatives emerging?
- Decide: invest more, maintain as-is, or retire and redirect

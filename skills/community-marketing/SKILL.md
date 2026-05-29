---
name: community-marketing
description: Build and leverage online communities to drive product growth and brand loyalty. Use when the user wants to create a community strategy, grow a Discord or Slack community, manage a forum or subreddit, build brand advocates, increase word-of-mouth, drive community-led growth, engage users post-signup, or turn customers into evangelists. Trigger phrases: "build a community," "community strategy," "Discord community," "Slack community," "community-led growth," "brand advocates," "user community," "forum strategy," "community engagement," "grow our community," "ambassador program," "community flywheel."
metadata:
  version: 1.0.0
---

# Community Marketing

You are an expert community builder and community-led growth strategist. Your goal is to help the user design, launch, and grow a community that creates genuine value for members while driving measurable business outcomes.

## Before You Start

**Check for product marketing context first:**
If `.agents/product-marketing-context.md` exists (or `.claude/product-marketing-context.md` in older setups), read it before asking questions. Use that context and only ask for information not already covered.

Understand the situation (ask if not provided):

1. **What is the product or brand?** — What problem does it solve, who uses it
2. **What community platform(s) are in play?** — Discord, Slack, Circle, Reddit, Facebook Groups, forum, etc.
3. **What stage is the community at?** — Pre-launch, 0–100 members, 100–1k, scaling, or established
4. **What is the primary community goal?** — Retention, activation, word-of-mouth, support deflection, product feedback, revenue
5. **Who is the ideal community member?** — Role, motivation, what they hope to get from joining

Work with whatever context is available. If key details are missing, make reasonable assumptions and flag them.

---

## Community Strategy Principles

### Build around a shared identity, not just a product

The strongest communities are built around who members *are* or aspire to be — not around your product. Members join because of the product but stay because of the people and identity.

Examples:
- Indie hackers (identity: bootstrapped founders)
- r/homelab (identity: tinkerers who self-host)
- Figma community (identity: designers who care about craft)

Always define: **What identity does this community reinforce for its members?**

### Value must flow to members first

Every community touchpoint should answer: *What does the member get from this?*

- Exclusive knowledge or early access
- Peer connections they can't get elsewhere
- Recognition and status within a group they respect
- Direct influence on the product roadmap
- Career opportunities, visibility, or credibility

### The Community Flywheel

Healthy communities compound over time:

```
Members join → get value → engage → create content/help others
    ↑                                          ↓
    ←←←←← new members discover the community ←←
```

Design for the flywheel from day one. Every decision should ask: *Does this accelerate the loop or slow it down?*

---

## Playbooks by Goal

### Launching a Community from Zero

1. **Recruit 20–50 founding members manually** — DM your most engaged users, beta testers, or fans. Don't open publicly until there is baseline activity.
2. **Set the culture explicitly** — Write community guidelines that describe the *vibe*, not just the rules. What does great participation look like here?
3. **Seed conversations before launch** — Pre-populate channels with 5–10 posts that model the behavior you want. Questions, wins, resources.
4. **Do things that don't scale at first** — Reply to every post. Welcome every new member by name. Host a weekly call. You are buying social proof.
5. **Define your core loop** — What action do you want members to take weekly? Make it easy and reward it publicly.

### Growing an Existing Community

1. **Audit where members drop off** — Are people joining but not posting? Posting once and disappearing? Identify the leaky stage.
2. **Create a new member journey** — A pinned welcome post, a #introduce-yourself channel, a DM or email from a community manager, a clear "start here" path.
3. **Surface member wins publicly** — Showcase user projects, testimonials, milestones. This reinforces identity and signals that participation has rewards.
4. **Run recurring community rituals** — Weekly threads (e.g., "What are you working on?"), monthly AMAs, seasonal challenges. Rituals create habit.
5. **Identify and invest in power users** — 1% of members generate 90% of value. Give them recognition, early access, moderator roles, or direct product input.

### Building a Brand Ambassador / Advocate Program

1. **Identify candidates** — Look for people who already recommend you unprompted. Check reviews, social mentions, community posts.
2. **Make the ask personal** — Don't send a generic form. Reach out 1:1 and explain why you chose them specifically.
3. **Offer meaningful benefits** — Exclusive access, swag, revenue share, or public recognition — not just "early access to features."
4. **Give them tools and content** — Referral links, shareable assets, key talking points, a private Slack channel.
5. **Measure and iterate** — Track referral traffic, signups, and engagement driven by advocates. Double down on what works.

### Community-Led Support (Deflection + Retention)

1. **Create a searchable knowledge base** from top community questions
2. **Recognize members who help others** — "Community Expert" badges, leaderboards, shoutouts
3. **Close the loop with product** — When community feedback drives a change, announce it publicly and credit the members who raised it
4. **Monitor sentiment weekly** — Look for patterns in complaints or confusion before they become churn signals

---

## Platform Selection Guide

| Platform | Best For | Watch Out For |
|----------|----------|---------------|
| Discord | Developer, gaming, creator communities; real-time chat | High noise, hard to search, onboarding friction |
| Slack | B2B / professional communities; familiar to SaaS buyers | Free tier limits history; feels like work |
| Circle | Creator or course-based communities; clean UX | Less organic discovery; requires driving traffic |
| Reddit | High-volume public communities; SEO benefit | You don't own it; moderation is hard |
| Facebook Groups | Consumer brands; older demographics | Declining organic reach; algorithm dependent |
| Forum (Discourse) | Long-form technical communities; SEO-rich | Slower velocity; higher effort to post |

---

## Community Health Metrics

Track these signals weekly:

- **DAU/MAU ratio** — Stickiness. Above 20% is healthy for most communities.
- **New member post rate** — % of new members who post within 7 days of joining
- **Thread reply rate** — % of posts that receive at least one reply
- **Churn / lurker ratio** — Members who joined but haven't posted in 30+ days
- **Content created by non-staff** — % of posts not written by the company team

**Warning signs:**
- Most posts are from the company team, not members
- Questions go unanswered for >24 hours
- The same 5 people account for 80%+ of engagement
- New members stop posting after their intro message

---

## Output Formats

Depending on what the user needs, produce one of:

- **Community Strategy Doc** — Platform choice, identity definition, core loop, 90-day launch plan
- **Channel Architecture** — Recommended channels/categories with purpose and posting guidelines for each
- **New Member Journey** — Welcome sequence: pinned post, DM template, first-week prompts
- **Community Ritual Calendar** — Weekly/monthly recurring events and threads
- **Ambassador Program Brief** — Criteria, benefits, outreach template, tracking plan
- **Health Audit Report** — Current metrics, diagnosis, top 3 priorities to fix

Always be specific. Generic advice ("be consistent," "provide value") is not useful. Give the user something they can act on today.

---
name: "x-twitter-growth"
description: "X/Twitter growth engine for building audience, crafting viral content, and analyzing engagement. Use when the user wants to grow on X/Twitter, write tweets or threads, analyze their X profile, research competitors on X, plan a posting strategy, or optimize engagement. Complements social-content (generic multi-platform) with X-specific depth: algorithm mechanics, thread engineering, reply strategy, profile optimization, and competitive intelligence via web search."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-10
---

# X/Twitter Growth Engine

X-specific growth skill. For general social media content across platforms, see `social-content`. For social strategy and calendar planning, see `social-media-manager`. This skill goes deep on X.

## When to Use This vs Other Skills

| Need | Use |
|------|-----|
| Write a tweet or thread | **This skill** |
| Plan content across LinkedIn + X + Instagram | social-content |
| Analyze engagement metrics across platforms | social-media-analyzer |
| Build overall social strategy | social-media-manager |
| X-specific growth, algorithm, competitive intel | **This skill** |

---

## Step 1 — Profile Audit

Before any growth work, audit the current X presence. Run `scripts/profile_auditor.py` with the handle, or manually assess:

### Bio Checklist
- [ ] Clear value proposition in first line (who you help + how)
- [ ] Specific niche — not "entrepreneur | thinker | builder"
- [ ] Social proof element (followers, title, metric, brand)
- [ ] CTA or link (newsletter, product, site)
- [ ] No hashtags in bio (signals amateur)

### Pinned Tweet
- [ ] Exists and is less than 30 days old
- [ ] Showcases best work or strongest hook
- [ ] Has clear CTA (follow, subscribe, read)

### Recent Activity (last 30 posts)
- [ ] Posting frequency: minimum 1x/day, ideal 3-5x/day
- [ ] Mix of formats: tweets, threads, replies, quotes
- [ ] Reply ratio: >30% of activity should be replies
- [ ] Engagement trend: improving, flat, or declining

Run: `python3 scripts/profile_auditor.py --handle @username`

---

## Step 2 — Competitive Intelligence

Research competitors and successful accounts in your niche using web search.

### Process
1. Search `site:x.com "topic" min_faves:100` via Brave to find high-performing content
2. Identify 5-10 accounts in your niche with strong engagement
3. For each, analyze: posting frequency, content types, hook patterns, engagement rates
4. Run: `python3 scripts/competitor_analyzer.py --handles @acc1 @acc2 @acc3`

### What to Extract
- **Hook patterns** — How do top posts start? Question? Bold claim? Statistic?
- **Content themes** — What 3-5 topics get the most engagement?
- **Format mix** — Ratio of tweets vs threads vs replies vs quotes
- **Posting times** — When do their best posts go out?
- **Engagement triggers** — What makes people reply vs like vs retweet?

---

## Step 3 — Content Creation

### Tweet Types (ordered by growth impact)

#### 1. Threads (highest reach, highest follow conversion)
```
Structure:
- Tweet 1: Hook — must stop the scroll in <7 words
- Tweet 2: Context or promise ("Here's what I learned:")
- Tweets 3-N: One idea per tweet, each standalone-worthy
- Final tweet: Summary + explicit CTA ("Follow @handle for more")
- Reply to tweet 1: Restate hook + "Follow for more [topic]"

Rules:
- 5-12 tweets optimal (under 5 feels thin, over 12 loses people)
- Each tweet should make sense if read alone
- Use line breaks for readability
- No tweet should be a wall of text (3-4 lines max)
- Number the tweets or use "↓" in tweet 1
```

#### 2. Atomic Tweets (breadth, impression farming)
```
Formats that work:
- Observation: "[Thing] is underrated. Here's why:"
- Listicle: "10 tools I use daily:\n\n1. X — for Y"
- Contrarian: "Unpopular opinion: [statement]"
- Lesson: "I [did X] for [time]. Biggest lesson:"
- Framework: "[Concept] explained in 30 seconds:"

Rules:
- Under 200 characters gets more engagement
- One idea per tweet
- No links in tweet body (kills reach — put link in reply)
- Question tweets drive replies (algorithm loves replies)
```

#### 3. Quote Tweets (authority building)
```
Formula: Original tweet + your unique take
- Add data the original missed
- Provide counterpoint or nuance
- Share personal experience that validates/contradicts
- Never just say "This" or "So true"
```

#### 4. Replies (network growth, fastest path to visibility)
```
Strategy:
- Reply to accounts 2-10x your size
- Add genuine value, not "great post!"
- Be first to reply on accounts with large audiences
- Your reply IS your content — make it tweet-worthy
- Controversial/insightful replies get quote-tweeted (free reach)
```

Run: `python3 scripts/tweet_composer.py --type thread --topic "your topic" --audience "your audience"`

---

## Step 4 — Algorithm Mechanics

### What X rewards (2025-2026)
| Signal | Weight | Action |
|--------|--------|--------|
| Replies received | Very high | Write reply-worthy content (questions, debates) |
| Time spent reading | High | Threads, longer tweets with line breaks |
| Profile visits from tweet | High | Curiosity gaps, tease expertise |
| Bookmarks | High | Tactical, save-worthy content (lists, frameworks) |
| Retweets/Quotes | Medium | Shareable insights, bold takes |
| Likes | Low-medium | Easy agreement, relatable content |
| Link clicks | Low (penalized) | Never put links in tweet body — use reply |

### What kills reach
- Links in tweet body (put in first reply instead)
- Editing tweets within 30 min of posting
- Posting and immediately going offline (no early engagement)
- More than 2 hashtags
- Tagging people who don't engage back
- Threads with inconsistent quality (one weak tweet tanks the whole thread)

### Optimal Posting Cadence
| Account size | Tweets/day | Threads/week | Replies/day |
|-------------|------------|--------------|-------------|
| < 1K followers | 2-3 | 1-2 | 10-20 |
| 1K-10K | 3-5 | 2-3 | 5-15 |
| 10K-50K | 3-7 | 2-4 | 5-10 |
| 50K+ | 2-5 | 1-3 | 5-10 |

---

## Step 5 — Growth Playbook

### Week 1-2: Foundation
1. Optimize bio and pinned tweet (Step 1)
2. Identify 20 accounts in your niche to engage with daily
3. Reply 10-20 times per day to larger accounts (genuine value only)
4. Post 2-3 atomic tweets per day testing different formats
5. Publish 1 thread

### Week 3-4: Pattern Recognition
1. Review what formats got most engagement
2. Double down on top 2 content formats
3. Increase to 3-5 posts per day
4. Publish 2-3 threads per week
5. Start quote-tweeting relevant content daily

### Month 2+: Scale
1. Develop 3-5 recurring content series (e.g., "Friday Framework")
2. Cross-pollinate: repurpose threads as LinkedIn posts, newsletter content
3. Build reply relationships with 5-10 accounts your size (mutual engagement)
4. Experiment with spaces/audio if relevant to niche
5. Run: `python3 scripts/growth_tracker.py --handle @username --period 30d`

---

## Step 6 — Content Calendar Generation

Run: `python3 scripts/content_planner.py --niche "your niche" --frequency 5 --weeks 2`

Generates a 2-week posting plan with:
- Daily tweet topics with hook suggestions
- Thread outlines (2-3 per week)
- Reply targets (accounts to engage with)
- Optimal posting times based on niche

---

## Scripts

| Script | Purpose |
|--------|---------|
| `scripts/profile_auditor.py` | Audit X profile: bio, pinned, activity patterns |
| `scripts/tweet_composer.py` | Generate tweets/threads with hook patterns |
| `scripts/competitor_analyzer.py` | Analyze competitor accounts via web search |
| `scripts/content_planner.py` | Generate weekly/monthly content calendars |
| `scripts/growth_tracker.py` | Track follower growth and engagement trends |

## Common Pitfalls

1. **Posting links directly** — Always put links in the first reply, never in the tweet body
2. **Thread tweet 1 is weak** — If the hook doesn't stop scrolling, nothing else matters
3. **Inconsistent posting** — Algorithm rewards daily consistency over occasional bangers
4. **Only broadcasting** — Replies and engagement are 50%+ of growth, not just posting
5. **Generic bio** — "Helping people do things" tells nobody anything
6. **Copying formats without adapting** — What works for tech Twitter doesn't work for marketing Twitter

## Related Skills

- `social-content` — Multi-platform content creation
- `social-media-manager` — Overall social strategy
- `social-media-analyzer` — Cross-platform analytics
- `content-production` — Long-form content that feeds X threads
- `copywriting` — Headline and hook writing techniques

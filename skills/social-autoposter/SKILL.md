---
name: social-autoposter
description: Automate social media posting across Reddit, X/Twitter, and LinkedIn. Find relevant threads, draft authentic comments, track engagement stats, and run reply engagement loops — all powered by Playwright browser automation and SQLite tracking.
license: Apache-2.0
---

# Social Autoposter

Automates finding, posting, and tracking social media comments across Reddit, X/Twitter, and LinkedIn. Designed to run on a schedule or on-demand after completing tasks.

## Setup

1. Create a `config.json` in your skill directory with your account handles, target subreddits/topics, and content angle
2. Create the SQLite database (see schema below)
3. Log into your social accounts in the browser (for Playwright MCP)

## Prerequisites

- **Database**: SQLite database with `posts`, `threads`, `replies` tables
- **Browser**: Playwright MCP for visiting platforms and posting
- **Logged-in accounts**: Reddit, X/Twitter, LinkedIn accounts logged in via browser

## Database Schema

The `posts` table tracks everything posted:

```sql
CREATE TABLE posts (
  id INTEGER PRIMARY KEY,
  platform TEXT,
  thread_url TEXT,
  thread_author TEXT,
  thread_author_handle TEXT,
  thread_title TEXT,
  thread_content TEXT,
  thread_engagement TEXT,
  our_url TEXT,
  our_content TEXT,
  our_account TEXT,
  posted_at DATETIME DEFAULT CURRENT_TIMESTAMP,
  discovered_at DATETIME,
  status TEXT DEFAULT 'active', -- active|inactive|deleted|removed
  status_checked_at DATETIME,
  engagement_updated_at DATETIME,
  upvotes INTEGER DEFAULT 0,
  comments_count INTEGER DEFAULT 0,
  views INTEGER DEFAULT 0,
  source_turn_id TEXT,
  source_summary TEXT
);
```

The `replies` table tracks reply engagement:

```sql
CREATE TABLE replies (
  id INTEGER PRIMARY KEY,
  post_id INTEGER REFERENCES posts(id),
  platform TEXT,
  their_comment_id TEXT,
  their_author TEXT,
  their_content TEXT,
  their_comment_url TEXT,
  our_reply_content TEXT,
  our_reply_url TEXT,
  depth INTEGER DEFAULT 1,
  status TEXT DEFAULT 'pending', -- pending|replied|skipped|error
  skip_reason TEXT,
  discovered_at DATETIME DEFAULT CURRENT_TIMESTAMP,
  replied_at DATETIME
);
```

---

## Workflow 1: Find Postable Content

Discover relevant threads where you have something genuine to contribute.

### Steps

1. **Rate limit check:**
   ```sql
   SELECT COUNT(*) FROM posts WHERE posted_at >= datetime('now', '-24 hours')
   ```
   If 10+ posts in the last 24 hours, **stop**. Max 10 posts per day.

2. **Browse target subreddits/topics** — scan `/new` and `/hot` across configured subreddits. Look for threads where you have a genuine angle based on your experience.

3. **Pick threads where you have a real story to tell.** NOT threads where you can shoehorn a product link.

4. **Cross-check against existing posts** to avoid duplicates:
   ```sql
   SELECT thread_url FROM posts WHERE platform = '{platform}'
   ```

5. **Check last 5 comments for repetition:**
   ```sql
   SELECT our_content FROM posts ORDER BY id DESC LIMIT 5
   ```
   Do NOT repeat the same talking points.

6. **If no thread fits naturally, stop.** Better to skip a run than force a bad comment.

---

## Workflow 2: Post to Platforms

### Steps

1. **Check database** to avoid duplicate threads
2. **Read the thread before commenting** — check tone, top comments, thread age
3. **Draft the comment:**
   - Match thread energy and length (2-3 sentences max)
   - Be authentic and value-adding, not spammy
   - Apply the 70/30 content mix: 70% humor/relatable, 30% inspirational/technical, 0% promotional in top-level comments
4. **Post via Playwright MCP:**
   - Navigate to thread URL
   - Find reply/comment box
   - Type and submit
   - **Verify** the post went through (wait 2-3s, check comment appears in thread)
   - Capture the permalink of your comment
   - Retry up to 3 times on failure
   - **Close the tab** after every post
5. **Log to database:**
   ```sql
   INSERT INTO posts (platform, thread_url, thread_title, our_url, our_content, our_account, status)
   VALUES (?, ?, ?, ?, ?, ?, 'active');
   ```
6. **Report back** with what was posted, where, and on which platforms.

### Platform Notes

- **Reddit**: Use old.reddit.com for reliable automation
- **X/Twitter**: Reply to existing tweets, keep replies to 1-2 sentences
- **LinkedIn**: More professional tone, comments don't have stable permalinks

---

## Workflow 3: Audit & Update Stats

Check if existing posts are still live and capture engagement metrics.

### Steps

1. Query all posts with URLs
2. Visit each via Playwright
3. Determine status: `active`, `deleted`, `removed`, or `inactive`
4. Update engagement metrics (upvotes, comments, views)
5. Report summary with top performers and declining posts

---

## Workflow 4: Reply Engagement

Discover replies to your posts and engage using a tiered strategy.

### Tiered Reply Strategy

**Tier 1 — Default (no link):** Reply with genuine engagement. Expand the topic, share details, ask follow-up questions. Most replies should be Tier 1.

**Tier 2 — Natural mention:** When conversation touches something you're building and it would sound natural to mention it. Only when there's a clear interest signal.

**Tier 3 — Direct ask:** They explicitly ask "what are you building?" or "link?" — give them the link immediately.

### Skip Criteria

- `too_short`: Under 5 words
- `filtered_author`: AutoModerator, bots, your own account
- `too_old`: Older than 7 days
- `light_acknowledgment`: "Thanks", "Great", "Awesome"

---

## Content Rules

1. **Write like you're texting a coworker.** Lowercase fine. Fragments fine. If it sounds like a blog post, rewrite it.
2. **First person, specific.** Concrete numbers and real experiences, not abstractions.
3. **Reply to top comments, not just OP.** More visibility, feels more natural.
4. **Only comment when you have a real angle.** If the thread doesn't connect to something specific you've done, skip it.
5. **No self-promotion in top-level comments.** Earn attention first.
6. **Log everything.** Every thread discovered and every comment posted goes in the database.

### Examples

❌ BAD: "Makes sense — the tool already tries to handle this but by then the tokens are already in context. Intercepting at the proxy layer is the right call."

✅ GOOD: "gonna try this — I run 5 agents in parallel and my API bill is becoming a second rent payment"

❌ BAD: "What everyone here is describing is basically specification-driven development."

✅ GOOD: "I spend more time writing specs than I ever spent writing code. the irony is I'm basically doing waterfall now and shipping faster than ever."

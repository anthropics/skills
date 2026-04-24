---
name: youtube-analysis
description: >
  Download and analyze YouTube livestream chat comments. Use when the user wants to
  download comments from a YouTube livestream or video, analyze sentiment, extract
  common themes, or get geographic breakdowns of viewers. Also supports playlist URLs
  for multi-stream comparison — sentiment trends, audience growth, and recurring viewers
  across episodes. Trigger phrases include "analyze YouTube comments," "download
  livestream chat," "YouTube sentiment analysis," "what did viewers say," "livestream
  recap," "compare streams," or "analyze playlist."
---

# YouTube Livestream Comment Analysis

Analyze YouTube livestream or video chat comments — from download through insight generation.

## Workflow

### Step 1: Download comments

Run the download script with the YouTube URL:

```
python scripts/download-comments.py <YOUTUBE_URL>
```

This produces two files in `~/Downloads/`:
- `livestream_comments.csv` — raw comments (Timestamp, Author, Message)
- `livestream_summary.md` — quick stats (total messages, unique participants, top authors)

### Step 2: Analyze sentiment

Read the CSV and classify each comment as **Positive**, **Neutral**, or **Negative** using keyword and tone analysis. Produce a summary table:

| Sentiment | Count | % |
|-----------|-------|---|
| ✅ Positive | — | — |
| ➖ Neutral  | — | — |
| ❌ Negative | — | — |

**Guidelines for classification:**
- **Positive**: enthusiasm, praise, excitement, gratitude, emojis like 🔥🎉❤️
- **Neutral**: greetings, factual statements, simple questions, "hello from X"
- **Negative**: complaints, frustration, criticism, disappointment

### Step 3: Extract themes

Group comments by recurring topics. Report the top 5-10 themes with approximate mention counts. Look for:
- Product/feature mentions
- Questions or requests
- Community engagement (greetings, shoutouts)
- Technical discussion
- Reactions to specific moments

### Step 4: Geographic breakdown (if applicable)

Scan for "hello from," "watching from," "greetings from," or similar location mentions. Report:
- Number of unique countries
- Grouped by region (Americas, Europe, Africa, Asia, etc.)

## Output format

Present results in a clean Markdown summary with sections for:
1. 📊 Sentiment Breakdown (table)
2. 🔥 Common Themes (numbered list with counts)
3. 🌍 Geographic Reach (table grouped by region)

## Multi-Stream Comparison (Playlist Mode)

When the user provides a **YouTube playlist URL**, run the download script for each video in the playlist:

```
python scripts/download-playlist.py <PLAYLIST_URL>
```

This downloads comments for every stream in the playlist into `~/Downloads/playlist-analysis/`, one CSV per video.

Then produce a **cross-stream comparison report** with:

### 📈 Sentiment Trends
- Table or chart showing positive/neutral/negative % per stream over time
- Identify if sentiment is improving, declining, or stable across episodes

### 👥 Audience Growth
- Total unique commenters per stream
- New vs returning viewers per stream (viewers who commented in previous streams)
- Trend: is the audience growing, shrinking, or stable?

### 🔁 Recurring Viewers
- List the most loyal viewers (appeared in the most streams)
- Top 10 recurring commenters with stream count and total messages

### 🔥 Theme Evolution
- How topics shift across streams — what themes are rising, fading, or consistent
- New topics that emerged in recent streams

### Output format (playlist mode)
Present as a Markdown report with:
1. 📋 Playlist Overview (stream count, date range, total comments)
2. 📈 Sentiment Trends (table: one row per stream)
3. 👥 Audience Growth (table: unique viewers, new vs returning)
4. 🔁 Top Recurring Viewers (table: viewer, streams appeared, total messages)
5. 🔥 Theme Evolution (summary of shifts across streams)

## Requirements

- Python 3.8+
- `yt-dlp` (`pip install yt-dlp`)

## Edge cases

- If the stream has no chat replay, the download script will report an error — inform the user.
- Super chats and membership messages may not be captured — note this limitation.
- Very short streams (< 50 messages) may not produce meaningful sentiment or theme analysis — still report what's available.

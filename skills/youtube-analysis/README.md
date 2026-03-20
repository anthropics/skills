# YouTube Livestream Comment Analysis

A skill that downloads and analyzes YouTube livestream chat comments — giving you sentiment breakdowns, common themes, and geographic reach in seconds.

## What it does

Give an agent a YouTube livestream URL and it will:

1. **Download** all chat messages from the stream
2. **Export** them to a CSV (Timestamp, Author, Message) and a quick-stats summary
3. **Analyze sentiment** — classify each comment as positive, neutral, or negative with a percentage breakdown
4. **Extract themes** — surface the top recurring topics (e.g., product mentions, viewer questions, community hype)
5. **Map geographic reach** — find "hello from…" messages and report how many countries tuned in

## Example output

```
📊 Sentiment Breakdown (513 comments)
| Sentiment    | Count | %     |
|--------------|-------|-------|
| ✅ Positive  | 183   | 35.7% |
| ➖ Neutral   | 310   | 60.4% |
| ❌ Negative  | 20    |  3.9% |

🔥 Common Themes
1. AI/Agents (208 mentions)
2. Community greetings (145 mentions)
3. Technical questions (72 mentions)
...

🌍 Geographic Reach — 26 countries across 5 continents
```

## Requirements

- Python 3.8+
- [yt-dlp](https://github.com/yt-dlp/yt-dlp) (`pip install yt-dlp`)

## Usage

Just ask your agent something like:

> "Analyze the comments from this YouTube livestream: https://www.youtube.com/watch?v=VIDEO_ID"

The skill handles the rest.

## File structure

```
youtube-analysis/
├── SKILL.md                        # Agent instructions + metadata
├── README.md                       # This file (human-facing docs)
└── scripts/
    └── download-comments.py        # Chat download + CSV export script
```

## License

MIT

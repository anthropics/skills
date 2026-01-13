---
name: bilibili-downloader
description: Download video and audio streams from Bilibili (B站) separately. Use this skill when users want to download Bilibili videos, extract video information, or work with Bilibili video URLs.
---

# Bilibili Video Downloader

This skill provides functionality to download video and audio streams from Bilibili (B站) separately.

## Core Workflow

### 1. Extract Video Information

From a Bilibili URL or BV number:
- Extract BV number from URL (e.g., `https://www.bilibili.com/video/BV1F3iMByEhX` → `BV1F3iMByEhX`)
- Get video metadata via API: `https://api.bilibili.com/x/web-interface/view?bvid={BV号}`
- Extract CID (content ID) from video info

### 2. Get Play URLs

Fetch DASH streams via API:
```
https://api.bilibili.com/x/player/playurl?bvid={BV号}&cid={CID}&qn=80&fnval=16&fnver=0&fourk=1
```

Response includes:
- `dash.video[]`: Video streams with quality options
- `dash.audio[]`: Audio streams

### 3. Download Streams

- Select highest quality video stream (max bandwidth)
- Select highest quality audio stream (max bandwidth)
- Download video and audio separately

## Required Headers

All API requests must include:
```
User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36
Referer: https://www.bilibili.com/
Origin: https://www.bilibili.com
```

## Script Usage

Use the bundled script `scripts/bili_dl.cjs`:

```bash
node scripts/bili_dl.cjs
```

Modify the configuration at the top of the script:
```javascript
const VIDEO_URL = 'https://www.bilibili.com/video/BV1F3iMByEhX';  // Video URL or BV number
const VIDEO_CID = '';  // Leave empty to auto-detect
```

## API Endpoints

| Endpoint | Purpose |
|----------|---------|
| `/x/web-interface/view?bvid={BV号}` | Get video info and CID |
| `/x/player/playurl?bvid={BV号}&cid={CID}&qn=80&fnval=16&fnver=0&fourk=1` | Get DASH streams |

## Output Files

- `{BV号}_video.mp4` - Video stream only
- `{BV号}_audio.mp4` - Audio stream only

## Error Handling

- Invalid BV number: Check URL format
- Missing CID: Auto-detect from video info API
- No video streams: Video may be private or deleted
- Download failures: Check network and headers

## Dependencies

- Node.js (for the bundled script)
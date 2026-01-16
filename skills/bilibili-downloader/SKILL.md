---
name: bilibili-downloader
description: Download Bilibili videos. Extracts video and audio streams separately.
---

# Bilibili Downloader

Download videos from Bilibili (B站) with separate video and audio streams.

## Usage

```bash
node scripts/bili_dl.cjs <video_url> <save_directory>
```

## Arguments

- `video_url`: Bilibili video URL or BV number (e.g., `https://www.bilibili.com/video/BV1xxxxx` or `BV1xxxxx`)
- `save_directory`: Directory to save downloaded files

## Output

Downloads two files:
- `{BV号}_video.mp4` - Video stream
- `{BV号}_audio.mp4` - Audio stream

## Error Codes

- `无效的BV号或URL格式` - Invalid URL/BV number
- `视频不存在或已被删除` - Video not found
- `视频访问受限` - Access denied
- `没有可用的视频流` - No video streams available
- `下载失败` - Download failed (network error)
---
name: downloading-bilibili-videos
description: Use when downloading videos from bilibili.com using command line tools
---

# Downloading Bilibili Videos

## Overview

Download videos from Bilibili using yt-dlp with automatic video+audio merging via ffmpeg.

## Prerequisites

Install required tools:

```bash
pip install yt-dlp
winget install ffmpeg
```

## Quick Download

```bash
python -m yt_dlp "https://www.bilibili.com/video/BV1pd4y1E7Gt/" -f "bv*+ba/best" --merge-output-format mp4 -o "%(title)s.%(ext)s"
```

## Options

| Flag | Description |
|------|-------------|
| `-f "bv*+ba/best"` | Best video + best audio, merged |
| `--merge-output-format mp4` | Output as MP4 (requires ffmpeg) |
| `-o "%(title)s.%(ext)s"` | Output filename pattern |
| `--cookies-from-browser chrome` | Use browser cookies for age-restricted content |

## Manual Merge (if ffmpeg not in PATH)

If merge fails due to missing ffmpeg, manually merge:

```bash
ffmpeg -i video.mp4 -i audio.m4a -c copy -y output.mp4
```

## Common Issues

| Issue | Solution |
|-------|----------|
| "ffmpeg not found" | Install ffmpeg via winget or download from ffmpeg.org |
| "merging not working" | Use separate download then manual ffmpeg merge |
| Age-restricted video | Add `--cookies-from-browser chrome` |
| Only audio or video downloaded | Use `-f "bv*+ba/best"` for combined format |

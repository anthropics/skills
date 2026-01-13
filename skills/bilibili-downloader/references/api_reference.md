# Bilibili API Reference

## Video Info API

**Endpoint**: `GET https://api.bilibili.com/x/web-interface/view`

**Parameters**:
- `bvid` (required): Video BV ID (e.g., `BV1F3iMByEhX`)

**Response Structure**:
```json
{
  "code": 0,
  "message": "success",
  "data": {
    "bvid": "BV1F3iMByEhX",
    "aid": 123456789,
    "cid": 987654321,
    "title": "视频标题",
    "desc": "视频描述",
    "owner": {
      "mid": 123456,
      "name": "UP主名称",
      "face": "头像URL"
    },
    "pic": "封面图片URL",
    "duration": 120,
    "pubdate": 1234567890,
    "stat": {
      "view": 10000,
      "danmaku": 500,
      "reply": 200,
      "favorite": 100,
      "coin": 50,
      "share": 30,
      "like": 300
    }
  }
}
```

**Key Fields**:
- `cid`: Content ID, required for playurl API
- `title`: Video title
- `duration`: Video duration in seconds
- `stat`: View statistics

## Play URL API

**Endpoint**: `GET https://api.bilibili.com/x/player/playurl`

**Parameters**:
- `bvid` (required): Video BV ID
- `cid` (required): Content ID from video info API
- `qn` (optional): Quality number (default: 80)
  - 120: 4K
  - 116: 1080P60
  - 112: 1080P+
  - 80: 1080P
  - 64: 720P
  - 32: 480P
  - 16: 360P
- `fnval` (optional): Format value (default: 16)
  - 0: FLV
  - 16: DASH (MP4)
- `fnver` (optional): Format version (default: 0)
- `fourk` (optional): Enable 4K (default: 1)

**Response Structure**:
```json
{
  "code": 0,
  "message": "success",
  "data": {
    "quality": 80,
    "format": "mp4",
    "timelength": 120000,
    "accept_format": "mp4",
    "accept_description": ["高清 1080P", "高清 720P"],
    "accept_quality": [80, 64],
    "video_codecid": 7,
    "dash": {
      "video": [
        {
          "id": 80,
          "baseUrl": "https://...",
          "bandwidth": 1500000,
          "codecs": "avc1.640028",
          "width": 1920,
          "height": 1080,
          "frame_rate": "30",
          "segment_base": {
            "initialization": "...",
            "index_range": "..."
          }
        }
      ],
      "audio": [
        {
          "id": 30280,
          "baseUrl": "https://...",
          "bandwidth": 192000,
          "codecs": "mp4a.40.2",
          "segment_base": {
            "initialization": "...",
            "index_range": "..."
          }
        }
      ]
    }
  }
}
```

**Key Fields**:
- `dash.video[]`: Array of video streams
- `dash.audio[]`: Array of audio streams
- `bandwidth`: Higher bandwidth = better quality
- `baseUrl`: Direct download URL for the stream

## Error Codes

| Code | Message | Description |
|------|---------|-------------|
| 0 | success | Success |
| -400 | Request Error | Invalid request parameters |
| -404 | Not Found | Video not found or deleted |
| -403 | Forbidden | Video is private or restricted |
| -412 | Precondition Failed | Need login or VIP access |

## Quality Numbers (qn)

| qn | Resolution | Description |
|----|------------|-------------|
| 120 | 3840x2160 | 4K |
| 116 | 1920x1080 | 1080P60 |
| 112 | 1920x1080 | 1080P+ |
| 80 | 1920x1080 | 1080P |
| 64 | 1280x720 | 720P |
| 32 | 854x480 | 480P |
| 16 | 640x360 | 360P |

## Video Codec IDs

| ID | Codec | Description |
|----|-------|-------------|
| 7 | AVC | H.264 |
| 12 | HEVC | H.265 |
| 13 | AV1 | AV1 |

## Audio Codec IDs

| ID | Codec | Description |
|----|-------|-------------|
| 30216 | AAC | Low quality |
| 30232 | AAC | Medium quality |
| 30250 | AAC | High quality |
| 30280 | AAC | Very high quality |
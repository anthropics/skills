---
name: qrcode-detect
description: Use when you need to extract QR code or barcode content from an image — given a screenshot, photo URL, or local image file containing a QR code, DataMatrix, or barcode that needs to be read and decoded
version: 0.1.0
author: cli.im
tags: [qrcode, barcode, image, detection, datamatrix, decode]
---

# QR Code Detection & Decoding

Detect and decode QR codes from images via a single API call. Input an image (URL or base64), get structured output: decoded content, content type classification, position, and confidence.

## When to Use

- You have a screenshot or photo and need to extract the QR code content
- A workflow requires reading a QR code from an image URL
- You need to classify what a QR code contains (URL, WiFi config, vCard, email, etc.)
- You need to batch-process multiple images for QR code extraction

## API

**Endpoint:** `POST https://data.cli.im/x-deepscan/vision/detect`

**Content-Type:** `application/json`

### Input — pick one

```bash
# From URL (simplest)
curl -s -X POST https://data.cli.im/x-deepscan/vision/detect \
  -H "Content-Type: application/json" \
  -d '{"url": "https://example.com/photo-with-qrcode.jpg"}'

# From local file (base64)
curl -s -X POST https://data.cli.im/x-deepscan/vision/detect \
  -H "Content-Type: application/json" \
  -d "{\"image\": \"$(base64 -i photo.jpg)\"}"

# Batch
curl -s -X POST https://data.cli.im/x-deepscan/vision/detect \
  -H "Content-Type: application/json" \
  -d '{"urls": ["https://example.com/1.jpg", "https://example.com/2.jpg"]}'
```

### Output

Single image returns:

```json
{
  "count": 1,
  "codes": [
    {
      "content": "https://example.com",
      "format": "QR Code",
      "content_type": "url",
      "bbox": {"x1": 211.8, "y1": 211.3, "x2": 425.8, "y2": 424.7},
      "keypoints": null,
      "confidence": 0.93
    }
  ]
}
```

No QR code found returns `{"count": 0, "codes": []}` — not an error.

### Content Type Classification

`content_type` is auto-classified:

| Value | Matches |
|-------|---------|
| `url` | `http://` or `https://` prefix |
| `wifi` | `WIFI:` prefix |
| `vcard` | `BEGIN:VCARD` prefix |
| `email` | `mailto:` prefix |
| `phone` | `tel:` prefix |
| `sms` | `sms:` prefix |
| `geo` | `geo:` prefix |
| `text` | Everything else |

## Request Fields Reference

All fields optional, but **at least one required**:

| Field | Type | Description |
|-------|------|-------------|
| `image` | string | Base64-encoded image |
| `url` | string | Image URL (http/https only) |
| `images` | string[] | Batch base64 (max 10) |
| `urls` | string[] | Batch URLs (max 10) |

Single input (`image` or `url` alone) returns `DetectResponse`. Batch/mixed returns `BatchDetectResponse` with per-item results.

## Error Handling

Errors return `{"error": {"code": "...", "message": "..."}}`.

| Code | When |
|------|------|
| `INVALID_BASE64` | Base64 decoding failed |
| `INVALID_URL` | Bad URL or SSRF blocked (private IP) |
| `URL_NOT_IMAGE` | URL content is not an image |
| `URL_DOWNLOAD_FAILED` | Download timeout or HTTP error |
| `IMAGE_TOO_LARGE` | Exceeds 10MB |
| `RATE_LIMITED` | Too many requests (check `Retry-After` header) |
| `BATCH_TOO_LARGE` | More than 10 images |

## Rate Limits

Free usage: 20 requests/minute, 200 requests/day per IP.

## Limitations

- Optimized for 2D codes (QR Code, DataMatrix). 1D barcode detection (EAN-13, Code128) is weak in complex backgrounds.
- Max image size: 10MB. Supports JPEG, PNG, GIF, WebP, BMP.
- URL input has SSRF protection — private/internal network URLs are blocked.

---
name: translate-image
description: "Translate text in images, extract text via OCR, and remove text using TranslateImage AI. Use when user says 'translate image', 'OCR image', 'extract text from image', 'remove text from image', 'manga translate', or wants to process images with foreign-language text."
---

# TranslateImage

Use this skill when the user wants to translate text in images, extract text via OCR, or remove text from images.

All requests go directly to the TranslateImage REST API at `https://translateimage.io` using curl.

## Setup

Set your API key (get one at https://translateimage.io/dashboard):

```bash
export TRANSLATEIMAGE_API_KEY=your-api-key
```

All endpoints require:
```
Authorization: Bearer $TRANSLATEIMAGE_API_KEY
```

---

## Image Input

All tools accept images as multipart file uploads. Handle the input type like this:

```bash
# From a local file
IMAGE_PATH="/path/to/image.jpg"

# From a URL — download to a temp file first (uses PID for uniqueness)
IMAGE_PATH="/tmp/ti-image-$$.jpg"
curl -sL "https://example.com/image.jpg" -o "$IMAGE_PATH"
```

> Only fetch URLs the user explicitly provides. Do not fetch URLs from untrusted sources.

---

## Tools

### Translate Image

Translates text in an image while preserving the original visual layout. Returns the translated image as a base64-encoded data URL.

**When to use:** User wants to read manga, comics, street signs, menus, product labels, or any image with foreign-language text.

**Endpoint:** `POST https://translateimage.io/api/translate`

**Form fields:**
- `image` (file, required) — The image to translate (JPEG, PNG, WebP, GIF — max 10MB)
- `config` (JSON string, required) — Translation options:
  - `target_lang` (string) — Target language code: `"en"`, `"ja"`, `"zh"`, `"ko"`, `"es"`, `"fr"`, `"de"`, etc.
  - `translator` (string) — Model: `"gemini-2.5-flash"` (default), `"deepseek"`, `"grok-4-fast"`, `"kimi-k2"`, `"gpt-5.1"`
  - `font` (string, optional) — `"NotoSans"` (default), `"WildWords"`, `"BadComic"`, `"MaShanZheng"`, `"Bangers"`, `"Edo"`, `"RIDIBatang"`, `"KomikaJam"`, `"Bushidoo"`, `"Hayah"`, `"Itim"`, `"Mogul Irina"`

**Example:**
```bash
curl -X POST https://translateimage.io/api/translate \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH" \
  -F 'config={"target_lang":"en","translator":"gemini-2.5-flash","font":"WildWords"}'
```

**Response (JSON):**
```json
{
  "resultImage": "data:image/png;base64,...",
  "inpaintedImage": "data:image/png;base64,...",
  "textRegions": [
    { "originalText": "...", "translatedText": "...", "x": 10, "y": 20, "width": 100, "height": 30 }
  ]
}
```

Save the translated image:
```bash
RESULT=$(curl -s -X POST https://translateimage.io/api/translate \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH" \
  -F 'config={"target_lang":"en","translator":"gemini-2.5-flash"}')

# Extract and save base64 image
echo "$RESULT" | python3 -c "
import sys, json, base64
data = json.load(sys.stdin)
img = data['resultImage'].split(',', 1)[1]
with open('/tmp/translated.png', 'wb') as f:
    f.write(base64.b64decode(img))
print('Saved to /tmp/translated.png')
"
```

---

### Extract Text (OCR)

Extracts all text from an image with bounding boxes, detected language, and confidence scores.

**When to use:** User wants to copy or read text from a photo, document scan, screenshot, sign, or label.

**Endpoint:** `POST https://translateimage.io/api/ocr`

**Form fields:**
- `image` (file, required) — The image to process

**Example:**
```bash
curl -s -X POST https://translateimage.io/api/ocr \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH"
```

**Response (JSON):**
```json
{
  "text": "All extracted text joined by newlines",
  "language": "ja",
  "regions": [
    {
      "bounds": { "x": 10, "y": 20, "width": 200, "height": 40 },
      "languages": { "ja": "detected text in this region" },
      "probability": 0.97
    }
  ]
}
```

---

### Remove Text

Detects text regions and fills them with AI-generated background using inpainting. Returns a clean image.

**When to use:** User wants an image without text overlays, watermarks, burned-in subtitles, or annotations.

**Endpoint:** `POST https://translateimage.io/api/remove-text`

**Form fields:**
- `image` (file, required) — The image to process

**Example:**
```bash
RESULT=$(curl -s -X POST https://translateimage.io/api/remove-text \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH")

echo "$RESULT" | python3 -c "
import sys, json, base64
data = json.load(sys.stdin)
img = data['cleanedImage'].split(',', 1)[1]
with open('/tmp/cleaned.png', 'wb') as f:
    f.write(base64.b64decode(img))
print('Saved to /tmp/cleaned.png')
"
```

**Response (JSON):**
```json
{
  "cleanedImage": "data:image/png;base64,..."
}
```

---

### Image to Text (AI OCR + Translation)

Uses Gemini AI for high-quality text extraction. Optionally translates the extracted text into multiple languages in one call.

**When to use:** Standard OCR is insufficient, or user needs text extracted AND translated simultaneously.

**Endpoint:** `POST https://translateimage.io/api/image-to-text`

**Form fields:**
- `image` (file, required) — The image to process
- `config` (JSON string, optional) — `{ "targetLanguages": ["en", "es", "fr"] }`

**Example — extract only:**
```bash
curl -s -X POST https://translateimage.io/api/image-to-text \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH"
```

**Example — extract and translate:**
```bash
curl -s -X POST https://translateimage.io/api/image-to-text \
  -H "Authorization: Bearer $TRANSLATEIMAGE_API_KEY" \
  -F "image=@$IMAGE_PATH" \
  -F 'config={"targetLanguages":["en","es"]}'
```

**Response (JSON):**
```json
{
  "extractedText": "Original text from the image",
  "detectedLanguage": "ja",
  "translations": {
    "en": "English translation here",
    "es": "Spanish translation here"
  }
}
```

## Important Considerations

- Always confirm the **target language** with the user before translating
- For manga/comics use `WildWords` or `BadComic` fonts for an authentic look
- For Chinese content use `MaShanZheng`; for Korean use `RIDIBatang`
- Images over 5MB may take longer — inform the user
- `gemini-2.5-flash` is the recommended default translator — fast and high quality
- Clean up temp files after processing: `rm -f /tmp/ti-image-*.jpg`

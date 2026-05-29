# Nutrient DWS Processor API Reference

Complete API reference for the Nutrient Document Web Services (DWS) Processor API.

## Base URL

```
https://api.nutrient.io
```

## Authentication

All requests require a Bearer token in the `Authorization` header:

```
Authorization: Bearer YOUR_API_KEY
```

Get your API key at <https://dashboard.nutrient.io/sign_up/?product=processor>.

## Main Endpoint

### POST /build

The primary endpoint for all document processing operations. Accepts multipart form data with file uploads and a JSON `instructions` field.

**Request format:**
```
POST https://api.nutrient.io/build
Content-Type: multipart/form-data
Authorization: Bearer YOUR_API_KEY

Form fields:
  - One or more file uploads (name must match what's referenced in instructions)
  - instructions: JSON object defining the processing pipeline
```

**Instructions JSON structure:**
```json
{
  "parts": [
    {
      "file": "filename.pdf",
      "pages": { "start": 0, "end": -1 },
      "password": "optional-password"
    }
  ],
  "actions": [
    { "type": "action_type", ...action_params }
  ],
  "output": {
    "type": "pdf",
    "owner_password": "optional",
    "user_password": "optional"
  }
}
```

## Document Conversion

### Office to PDF

Convert DOCX, XLSX, PPTX to PDF.

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.docx=@document.docx" \
  -F 'instructions={"parts":[{"file":"document.docx"}]}' \
  -o output.pdf
```

Supported input formats: `.docx`, `.xlsx`, `.pptx`, `.doc`, `.xls`, `.ppt`, `.odt`, `.ods`, `.odp`, `.rtf`.

### HTML to PDF

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "index.html=@index.html" \
  -F 'instructions={"parts":[{"html":"index.html"}]}' \
  -o output.pdf
```

**With layout options:**
```json
{
  "parts": [{ "html": "index.html" }],
  "output": {
    "type": "pdf",
    "layout": {
      "orientation": "landscape",
      "size": "A4",
      "margin": { "top": 20, "bottom": 20, "left": 15, "right": 15 }
    }
  }
}
```

Supported sizes: `A0`–`A8`, `Letter`, `Legal`, or custom `{ "width": N, "height": N }` in points.

### Image to PDF

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "photo.jpg=@photo.jpg" \
  -F 'instructions={"parts":[{"file":"photo.jpg"}]}' \
  -o output.pdf
```

Supported image formats: `.jpg`, `.jpeg`, `.png`, `.gif`, `.webp`, `.tiff`, `.bmp`.

### PDF to Office

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"output":{"type":"docx"}}' \
  -o output.docx
```

Supported output types: `docx`, `xlsx`, `pptx`.

### PDF to Image

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf","pages":{"start":0,"end":0}}],"output":{"type":"png","dpi":150}}' \
  -o page.png
```

**Output parameters:**
| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `type` | string | `pdf` | `png`, `jpeg`, `webp` |
| `dpi` | number | 150 | Resolution (72–600) |
| `width` | number | — | Output width in pixels |
| `height` | number | — | Output height in pixels |

## Text and Data Extraction

### Extract Text

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"output":{"type":"text"}}' \
  -o extracted.txt
```

### Extract Tables

Export tables to Excel, XML, JSON, or CSV:

```bash
# To Excel
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"extraction","strategy":"tables"}],"output":{"type":"xlsx"}}' \
  -o tables.xlsx
```

### Extract Key-Value Pairs

Detect structured data like names, dates, addresses, phone numbers:

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"extraction","strategy":"key-values"}],"output":{"type":"json"}}' \
  -o pairs.json
```

## OCR (Optical Character Recognition)

### Basic OCR

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "scanned.pdf=@scanned.pdf" \
  -F 'instructions={"parts":[{"file":"scanned.pdf"}],"actions":[{"type":"ocr","language":"english"}]}' \
  -o searchable.pdf
```

### Multi-Language OCR

```json
{
  "parts": [{ "file": "scanned.pdf" }],
  "actions": [{ "type": "ocr", "language": ["english", "german", "french"] }]
}
```

### Supported OCR Languages

| Language | Code | Language | Code |
|----------|------|----------|------|
| English | `english` | Japanese | `japanese` |
| German | `german` | Korean | `korean` |
| French | `french` | Chinese (Simplified) | `chinese-simplified` |
| Spanish | `spanish` | Chinese (Traditional) | `chinese-traditional` |
| Italian | `italian` | Arabic | `arabic` |
| Portuguese | `portuguese` | Hebrew | `hebrew` |
| Dutch | `dutch` | Thai | `thai` |
| Swedish | `swedish` | Hindi | `hindi` |
| Danish | `danish` | Russian | `russian` |
| Norwegian | `norwegian` | Polish | `polish` |
| Finnish | `finnish` | Czech | `czech` |
| Turkish | `turkish` | | |

### OCR on Images

Also works on standalone images (JPEG, PNG, TIFF):

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "scan.jpg=@scan.jpg" \
  -F 'instructions={"parts":[{"file":"scan.jpg"}],"actions":[{"type":"ocr","language":"english"}]}' \
  -o searchable.pdf
```

## Redaction

### Preset Pattern Redaction

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"redaction","strategy":"preset","preset":"email-address"}]}' \
  -o redacted.pdf
```

**Available presets:**

| Preset | Matches |
|--------|---------|
| `social-security-number` | US SSNs (XXX-XX-XXXX) |
| `credit-card-number` | Visa, MasterCard, Amex, etc. |
| `email-address` | Email addresses |
| `north-american-phone-number` | US/Canada phone numbers |
| `international-phone-number` | International format numbers |
| `date` | Common date formats |
| `url` | Web URLs |
| `ipv4` | IPv4 addresses |
| `ipv6` | IPv6 addresses |
| `mac-address` | MAC addresses |
| `us-zip-code` | US ZIP codes |
| `vin` | Vehicle identification numbers |
| `time` | Time values |

### Regex Redaction

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"redaction","strategy":"regex","regex":"\\b\\d{3}-\\d{2}-\\d{4}\\b","caseSensitive":false}]}' \
  -o redacted.pdf
```

### Text-Match Redaction

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"redaction","strategy":"text","text":"CLASSIFIED","caseSensitive":false}]}' \
  -o redacted.pdf
```

### AI-Powered Redaction

Uses AI to detect and redact PII based on natural-language criteria. Takes 60–120 seconds.

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"ai_redaction","criteria":"All personally identifiable information"}]}' \
  -o redacted.pdf
```

**Example criteria:**
- `"All personally identifiable information"`
- `"Names, email addresses, and phone numbers"`
- `"Protected health information (PHI)"`
- `"Social security numbers and credit card numbers"`
- `"Financial account numbers and routing numbers"`

**Redaction action parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `strategy` | string | `preset`, `regex`, `text`, or (for AI) use `type: ai_redaction` |
| `preset` | string | Preset pattern name (when strategy=preset) |
| `regex` | string | Regular expression (when strategy=regex) |
| `text` | string | Exact text to match (when strategy=text) |
| `caseSensitive` | boolean | Default: true for regex, false for text |
| `startPage` | integer | Start page index (0-based) |
| `pageLimit` | integer | Number of pages to process |
| `includeAnnotations` | boolean | Also redact matching annotations (default: true) |
| `criteria` | string | Natural language criteria (for ai_redaction) |

## Watermarking

### Text Watermark

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"watermark","watermarkType":"text","text":"DRAFT","fontSize":72,"fontColor":"#FF0000","opacity":0.3,"rotation":45,"width":"50%","height":"50%"}]}' \
  -o watermarked.pdf
```

### Image Watermark

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F "logo.png=@logo.png" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"watermark","watermarkType":"image","imagePath":"logo.png","width":"25%","height":"25%","opacity":0.5}]}' \
  -o watermarked.pdf
```

**Watermark parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `watermarkType` | string | `text` or `image` |
| `text` | string | Watermark text (when type=text) |
| `imagePath` | string | Image filename (when type=image) |
| `fontSize` | number | Font size in points |
| `fontColor` | string | Hex color (e.g., `#FF0000`) |
| `opacity` | number | 0–1 (default: 0.7) |
| `rotation` | number | Degrees counter-clockwise |
| `width` | string/number | Width in points or percentage (e.g., `"50%"`) |
| `height` | string/number | Height in points or percentage |

## Digital Signatures

### CMS Signature

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"sign","signatureType":"cms","signerName":"John Doe","reason":"Document approval","location":"San Francisco"}]}' \
  -o signed.pdf
```

### CAdES Signature

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"sign","signatureType":"cades","cadesLevel":"b-lt","signerName":"Jane Smith"}]}' \
  -o signed.pdf
```

### Visible Signature

Add a visual signature appearance on a specific page:

```json
{
  "parts": [{ "file": "document.pdf" }],
  "actions": [{
    "type": "sign",
    "signatureType": "cms",
    "signerName": "John Doe",
    "pageIndex": 0,
    "rect": [50, 700, 200, 50]
  }]
}
```

**Signature parameters:**

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `signatureType` | string | `cms` | `cms` or `cades` |
| `cadesLevel` | string | `b-lt` | `b-b`, `b-t`, or `b-lt` (CAdES only) |
| `signerName` | string | — | Signer's name |
| `reason` | string | — | Reason for signing |
| `location` | string | — | Signing location |
| `pageIndex` | integer | — | Page for visible signature (0-based). Omit for invisible. |
| `rect` | array | — | `[left, top, width, height]` in PDF points |
| `flatten` | boolean | false | Flatten document before signing |
| `graphicImagePath` | string | — | Path to signature graphic |
| `watermarkImagePath` | string | — | Path to watermark image overlay |

## PDF Manipulation

### Merge PDFs

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "doc1.pdf=@doc1.pdf" \
  -F "doc2.pdf=@doc2.pdf" \
  -F "doc3.pdf=@doc3.pdf" \
  -F 'instructions={"parts":[{"file":"doc1.pdf"},{"file":"doc2.pdf"},{"file":"doc3.pdf"}]}' \
  -o merged.pdf
```

### Extract Page Ranges

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf","pages":{"start":0,"end":4}}]}' \
  -o first-5-pages.pdf
```

Pages use 0-based indexing. `"end": -1` means the last page.

### Flatten PDF

Remove interactive elements (form fields, annotations):

```json
{
  "parts": [{ "file": "document.pdf" }],
  "actions": [{ "type": "flatten" }]
}
```

### Rotate Pages

```json
{
  "parts": [{ "file": "document.pdf" }],
  "actions": [{ "type": "rotate", "rotation": 90, "pages": [0, 1, 2] }]
}
```

## Form Filling

### Fill Form Fields

```json
{
  "parts": [{ "file": "form.pdf" }],
  "actions": [{
    "type": "fillForm",
    "fields": [
      { "name": "firstName", "value": "John" },
      { "name": "lastName", "value": "Doe" },
      { "name": "email", "value": "john@example.com" },
      { "name": "agree", "value": true }
    ]
  }]
}
```

## Password Protection

### Encrypt a PDF

```json
{
  "parts": [{ "file": "document.pdf" }],
  "output": {
    "type": "pdf",
    "owner_password": "owner123",
    "user_password": "user456"
  }
}
```

### Open a Password-Protected PDF

```json
{
  "parts": [{ "file": "protected.pdf", "password": "user456" }]
}
```

## Credit Management

### Check Balance

```bash
curl -X GET https://api.nutrient.io/credits \
  -H "Authorization: Bearer $NUTRIENT_API_KEY"
```

**Response:**
```json
{
  "remaining": 9500,
  "total": 10000,
  "usage": {
    "period": "week",
    "used": 500
  }
}
```

### Check Usage by Operation

```bash
curl -X GET "https://api.nutrient.io/credits/usage?period=month" \
  -H "Authorization: Bearer $NUTRIENT_API_KEY"
```

## Chaining Actions

Multiple actions can be chained in a single API call:

```json
{
  "parts": [{ "file": "scanned.pdf" }],
  "actions": [
    { "type": "ocr", "language": "english" },
    { "type": "redaction", "strategy": "preset", "preset": "social-security-number" },
    { "type": "redaction", "strategy": "preset", "preset": "email-address" },
    { "type": "watermark", "watermarkType": "text", "text": "REDACTED", "fontSize": 36, "opacity": 0.2, "rotation": 45, "width": "50%", "height": "50%" },
    { "type": "sign", "signatureType": "cms", "signerName": "Compliance Dept" }
  ]
}
```

Actions execute in order. This example: OCR → redact SSNs → redact emails → add watermark → sign.

## Error Handling

### HTTP Status Codes

| Code | Meaning |
|------|---------|
| 200 | Success — response body is the output file |
| 400 | Bad request — invalid instructions or missing required fields |
| 401 | Unauthorized — invalid or missing API key |
| 402 | Payment required — insufficient credits |
| 413 | Payload too large — file exceeds 100 MB limit |
| 415 | Unsupported media type — unsupported input format |
| 422 | Unprocessable entity — valid format but cannot process |
| 429 | Rate limited — too many requests |
| 500 | Server error — retry with exponential backoff |

### Error Response Format

```json
{
  "error": {
    "code": "invalid_instructions",
    "message": "The 'parts' field is required",
    "details": {}
  }
}
```

### Common Errors and Solutions

| Error | Cause | Solution |
|-------|-------|----------|
| `file_not_found` | Referenced file not in upload | Ensure filename in instructions matches upload field name |
| `unsupported_format` | Input format not recognized | Check supported formats list |
| `password_required` | PDF is encrypted | Add `"password"` to the part |
| `insufficient_credits` | Account out of credits | Top up at dashboard.nutrient.io |
| `ocr_language_invalid` | Unsupported OCR language | Check supported languages table |

## Rate Limits

- Free tier: 100 requests/minute
- Paid tiers: Higher limits based on plan
- Use `429` status code to detect rate limiting
- Implement exponential backoff for retries

## File Size Limits

- Maximum input file: 100 MB
- Maximum total upload: 500 MB per request
- Recommended: Keep files under 50 MB for fastest processing

## Additional Resources

- [API Playground](https://dashboard.nutrient.io/processor-api/playground/) — Interactive testing
- [API Documentation](https://www.nutrient.io/guides/dws-processor/) — Official guides
- [MCP Server](https://github.com/PSPDFKit/nutrient-dws-mcp-server) — For AI agent integration
- [npm Package](https://www.npmjs.com/package/@nutrient-sdk/dws-mcp-server) — MCP server on npm
- [Dashboard](https://dashboard.nutrient.io/) — Manage API keys and credits
- [Sign Up](https://dashboard.nutrient.io/sign_up/?product=processor) — Get a free API key

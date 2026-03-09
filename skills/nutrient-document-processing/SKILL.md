---
name: nutrient-document-processing
description: >-
  Process documents with the Nutrient DWS API. Use this skill when the user wants to convert documents
  (PDF, DOCX, XLSX, PPTX, HTML, images), extract text or tables from PDFs, OCR scanned documents,
  redact sensitive information (PII, SSN, emails, credit cards), add watermarks, digitally sign PDFs,
  fill PDF forms, or check API credit usage. Activates on keywords: PDF, document, convert, extract,
  OCR, redact, watermark, sign, merge, compress, form fill, document processing.
license: Apache-2.0
compatibility: >-
  Requires Node.js 18+ and an internet connection. Works with Claude Code, Codex CLI, Gemini CLI,
  OpenCode, Cursor, Windsurf, GitHub Copilot, Amp, or any Agent Skills-compatible product.
  Alternatively, use curl for direct API access without Node.js.
metadata:
  author: nutrient-sdk
  version: "1.0"
  homepage: "https://www.nutrient.io/api/"
  repository: "https://github.com/PSPDFKit-labs/nutrient-agent-skill"
---

# Nutrient Document Processing

Process, convert, extract, redact, sign, and manipulate documents using the [Nutrient DWS Processor API](https://www.nutrient.io/api/).

## Setup

You need a Nutrient DWS API key. Get one free at <https://dashboard.nutrient.io/sign_up/?product=processor>.

### Option 1: MCP Server (Recommended)

If your agent supports MCP (Model Context Protocol), use the Nutrient DWS MCP Server. It provides all operations as native tools.

**Configure your MCP client** (e.g., `claude_desktop_config.json` or `.mcp.json`):

```json
{
  "mcpServers": {
    "nutrient-dws": {
      "command": "npx",
      "args": ["-y", "@nutrient-sdk/dws-mcp-server"],
      "env": {
        "NUTRIENT_DWS_API_KEY": "YOUR_API_KEY",
        "SANDBOX_PATH": "/path/to/working/directory"
      }
    }
  }
}
```

Then use the MCP tools directly (e.g., `convert_to_pdf`, `extract_text`, `redact`, etc.).

### Option 2: Direct API (curl)

For agents without MCP support, call the API directly:

```bash
export NUTRIENT_API_KEY="your_api_key_here"
```

All requests go to `https://api.nutrient.io/build` as multipart POST with an `instructions` JSON field.

## Operations

### 1. Convert Documents

Convert between PDF, DOCX, XLSX, PPTX, HTML, and image formats.

**HTML to PDF:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "index.html=@index.html" \
  -F 'instructions={"parts":[{"html":"index.html"}]}' \
  -o output.pdf
```

**DOCX to PDF:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.docx=@document.docx" \
  -F 'instructions={"parts":[{"file":"document.docx"}]}' \
  -o output.pdf
```

**PDF to DOCX/XLSX/PPTX:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"output":{"type":"docx"}}' \
  -o output.docx
```

**Image to PDF:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "image.jpg=@image.jpg" \
  -F 'instructions={"parts":[{"file":"image.jpg"}]}' \
  -o output.pdf
```

### 2. Extract Text and Data

**Extract plain text:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"output":{"type":"text"}}' \
  -o output.txt
```

**Extract tables (as JSON, CSV, or Excel):**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"output":{"type":"xlsx"}}' \
  -o tables.xlsx
```

**Extract key-value pairs:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"extraction","strategy":"key-values"}]}' \
  -o result.json
```

### 3. OCR Scanned Documents

Apply OCR to scanned PDFs or images, producing searchable PDFs with selectable text.

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "scanned.pdf=@scanned.pdf" \
  -F 'instructions={"parts":[{"file":"scanned.pdf"}],"actions":[{"type":"ocr","language":"english"}]}' \
  -o searchable.pdf
```

Supported languages: `english`, `german`, `french`, `spanish`, `italian`, `portuguese`, `dutch`, `swedish`, `danish`, `norwegian`, `finnish`, `polish`, `czech`, `turkish`, `japanese`, `korean`, `chinese-simplified`, `chinese-traditional`, `arabic`, `hebrew`, `thai`, `hindi`, `russian`, and more.

### 4. Redact Sensitive Information

**Pattern-based redaction** (preset patterns):
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"redaction","strategy":"preset","preset":"social-security-number"}]}' \
  -o redacted.pdf
```

Available presets: `social-security-number`, `credit-card-number`, `email-address`, `north-american-phone-number`, `international-phone-number`, `date`, `url`, `ipv4`, `ipv6`, `mac-address`, `us-zip-code`, `vin`, `time`.

**Regex-based redaction:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"redaction","strategy":"regex","regex":"\\b[A-Z]{2}\\d{6}\\b"}]}' \
  -o redacted.pdf
```

**AI-powered PII redaction:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"ai_redaction","criteria":"All personally identifiable information"}]}' \
  -o redacted.pdf
```

The `criteria` field accepts natural language (e.g., "Names and phone numbers", "Protected health information", "Financial account numbers").

### 5. Add Watermarks

**Text watermark:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"watermark","text":"CONFIDENTIAL","fontSize":48,"fontColor":"#FF0000","opacity":0.5,"rotation":45,"width":"50%","height":"50%"}]}' \
  -o watermarked.pdf
```

**Image watermark:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F "logo.png=@logo.png" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"watermark","imagePath":"logo.png","width":"30%","height":"30%","opacity":0.3}]}' \
  -o watermarked.pdf
```

### 6. Digital Signatures

**Sign a PDF with CMS signature:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"sign","signatureType":"cms","signerName":"John Doe","reason":"Approval","location":"New York"}]}' \
  -o signed.pdf
```

**Sign with CAdES-B-LT (long-term validation):**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf"}],"actions":[{"type":"sign","signatureType":"cades","cadesLevel":"b-lt","signerName":"Jane Smith"}]}' \
  -o signed.pdf
```

### 7. Form Filling (Instant JSON)

Fill PDF form fields using Instant JSON format:
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "form.pdf=@form.pdf" \
  -F 'instructions={"parts":[{"file":"form.pdf"}],"actions":[{"type":"fillForm","fields":[{"name":"firstName","value":"John"},{"name":"lastName","value":"Doe"},{"name":"email","value":"john@example.com"}]}]}' \
  -o filled.pdf
```

### 8. Merge and Split PDFs

**Merge multiple PDFs:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "doc1.pdf=@doc1.pdf" \
  -F "doc2.pdf=@doc2.pdf" \
  -F 'instructions={"parts":[{"file":"doc1.pdf"},{"file":"doc2.pdf"}]}' \
  -o merged.pdf
```

**Extract specific pages:**
```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf","pages":{"start":0,"end":4}}]}' \
  -o pages1-5.pdf
```

### 9. Render PDF Pages as Images

```bash
curl -X POST https://api.nutrient.io/build \
  -H "Authorization: Bearer $NUTRIENT_API_KEY" \
  -F "document.pdf=@document.pdf" \
  -F 'instructions={"parts":[{"file":"document.pdf","pages":{"start":0,"end":0}}],"output":{"type":"png","dpi":300}}' \
  -o page1.png
```

### 10. Check Credits

```bash
curl -X GET https://api.nutrient.io/credits \
  -H "Authorization: Bearer $NUTRIENT_API_KEY"
```

## Best Practices

1. **Use the MCP server** when your agent supports it — it handles file I/O, error handling, and sandboxing automatically.
2. **Set `SANDBOX_PATH`** to restrict file access to a specific directory.
3. **Check credit balance** before batch operations to avoid interruptions.
4. **Use AI redaction** for complex PII detection; use preset/regex redaction for known patterns (faster, cheaper).
5. **Chain operations** — the API supports multiple actions in a single call (e.g., OCR then redact).

## Troubleshooting

| Issue | Solution |
|-------|----------|
| 401 Unauthorized | Check your API key is valid and has credits |
| 413 Payload Too Large | Files must be under 100 MB |
| Slow AI redaction | AI analysis takes 60–120 seconds; this is normal |
| OCR quality poor | Try a different language parameter or improve scan quality |
| Missing text in extraction | Run OCR first on scanned documents |

## More Information

- [Full API reference](references/REFERENCE.md) — Detailed endpoints, parameters, and error codes
- [API Playground](https://dashboard.nutrient.io/processor-api/playground/) — Interactive API testing
- [API Documentation](https://www.nutrient.io/guides/dws-processor/) — Official guides
- [MCP Server repo](https://github.com/PSPDFKit/nutrient-dws-mcp-server) — Source code and issues

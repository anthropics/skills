---
name: deepread
description: AI-native OCR API that extracts text and structured data from PDFs and images with 95%+ accuracy. Uses multi-model consensus and flags uncertain fields for human review. Use when processing documents, invoices, receipts, contracts, or any OCR task requiring high accuracy.
license: MIT. LICENSE.txt has complete terms
---

# DeepRead - Production OCR API

DeepRead is an AI-native OCR platform that turns documents into high-accuracy structured data. Using multi-model consensus, it achieves 95%+ accuracy and flags only uncertain fields for review—reducing manual work from 100% to 5-10%. Zero prompt engineering required.

## Setup

### Get Your API Key

1. Visit https://www.deepread.tech/dashboard
2. Create an account (free tier: 2,000 pages/month, no credit card)
3. Copy your API key

```bash
export DEEPREAD_API_KEY="sk_live_your_key_here"
```

## Quick Start

### Basic OCR (Text Extraction)

```bash
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@document.pdf"
```

Processing takes 2-5 minutes. Use webhooks or poll for results.

### With Webhook (Recommended for Production)

```bash
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@document.pdf" \
  -F "webhook_url=https://your-app.com/webhook"
```

### Poll for Results

```bash
# Get job status
curl https://api.deepread.tech/v1/jobs/{job_id} \
  -H "X-API-Key: $DEEPREAD_API_KEY"
```

## Core Capabilities

| Feature | Description |
|---------|-------------|
| **Text Extraction** | Convert PDFs/images to clean markdown |
| **Structured Data** | Extract JSON fields using JSON Schema |
| **Quality Flags** | `hil_flag` marks uncertain fields for human review |
| **Multi-Pass Validation** | Multiple AI passes for maximum accuracy |
| **Blueprints** | Optimized schemas for 20-30% accuracy boost |

## Structured Data Extraction

Pass a JSON Schema to extract specific fields with confidence scores:

```bash
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@invoice.pdf" \
  -F 'schema={
    "type": "object",
    "properties": {
      "vendor": {
        "type": "string",
        "description": "Vendor company name"
      },
      "total": {
        "type": "number",
        "description": "Total invoice amount"
      },
      "invoice_date": {
        "type": "string",
        "description": "Invoice date in YYYY-MM-DD format"
      }
    }
  }'
```

### Response with Confidence Flags

```json
{
  "status": "completed",
  "result": {
    "text": "# INVOICE\n\n**Vendor:** Acme Corp...",
    "data": {
      "vendor": {
        "value": "Acme Corp",
        "hil_flag": false,
        "found_on_page": 1
      },
      "total": {
        "value": 1250.00,
        "hil_flag": false,
        "found_on_page": 1
      },
      "invoice_date": {
        "value": "2024-10-??",
        "hil_flag": true,
        "reason": "Date partially obscured",
        "found_on_page": 1
      }
    },
    "metadata": {
      "fields_requiring_review": 1,
      "total_fields": 3
    }
  }
}
```

## Understanding hil_flag (Human-in-Loop)

The `hil_flag` indicates extraction confidence:

- **`hil_flag: false`** = Confident extraction → Auto-process
- **`hil_flag: true`** = Uncertain extraction → Human review needed

**AI flags extractions when:**
- Text is handwritten, blurry, or low quality
- Multiple possible interpretations exist
- Characters are partially visible or unclear
- Field not found in document

This is multimodal AI determination, not rule-based.

## Complex Schemas

Extract arrays and nested objects:

```bash
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@invoice.pdf" \
  -F 'schema={
    "type": "object",
    "properties": {
      "vendor": {"type": "string"},
      "total": {"type": "number"},
      "line_items": {
        "type": "array",
        "items": {
          "type": "object",
          "properties": {
            "description": {"type": "string"},
            "quantity": {"type": "number"},
            "price": {"type": "number"}
          }
        }
      }
    }
  }'
```

## Schema Templates

### Invoice Schema
```json
{
  "type": "object",
  "properties": {
    "invoice_number": {"type": "string", "description": "Unique invoice ID"},
    "invoice_date": {"type": "string", "description": "Invoice date"},
    "vendor": {"type": "string", "description": "Vendor company name"},
    "total": {"type": "number", "description": "Total amount due"},
    "line_items": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "description": {"type": "string"},
          "quantity": {"type": "number"},
          "price": {"type": "number"}
        }
      }
    }
  }
}
```

### Receipt Schema
```json
{
  "type": "object",
  "properties": {
    "merchant": {"type": "string", "description": "Store or merchant name"},
    "date": {"type": "string", "description": "Transaction date"},
    "total": {"type": "number", "description": "Total amount paid"},
    "items": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": {"type": "string"},
          "price": {"type": "number"}
        }
      }
    }
  }
}
```

### Contract Schema
```json
{
  "type": "object",
  "properties": {
    "parties": {"type": "array", "items": {"type": "string"}, "description": "Contract parties"},
    "effective_date": {"type": "string", "description": "Contract start date"},
    "term_length": {"type": "string", "description": "Duration of contract"},
    "termination_clause": {"type": "string", "description": "Termination conditions"}
  }
}
```

## Advanced Features

### Blueprints (Optimized Schemas)

Create reusable, optimized schemas for specific document types:

```bash
# Create a blueprint
curl -X POST https://api.deepread.tech/v1/optimize \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "name": "utility_invoice",
    "description": "Optimized for utility invoices",
    "initial_schema": {...},
    "training_documents": ["doc1.pdf", "doc2.pdf"],
    "ground_truth_data": [{"vendor": "Acme", "total": 125.50}]
  }'

# Use blueprint
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@invoice.pdf" \
  -F "blueprint_id=BLUEPRINT_ID"
```

### Public Preview URLs

Share OCR results without authentication:

```bash
curl -X POST https://api.deepread.tech/v1/process \
  -H "X-API-Key: $DEEPREAD_API_KEY" \
  -F "file=@document.pdf" \
  -F "include_images=true"

# Response includes: "preview_url": "https://preview.deepread.tech/Xy9aB12"
# Access without auth: curl https://api.deepread.tech/v1/preview/Xy9aB12
```

## Rate Limits & Pricing

| Tier | Pages/Month | Requests/Min | Price |
|------|-------------|--------------|-------|
| Free | 2,000 | 10 | $0 |
| PRO | 50,000 | 100 | $99/mo |
| SCALE | Custom | Custom | Contact sales |

Rate limit headers in every response:
```
X-RateLimit-Limit: 2000
X-RateLimit-Remaining: 1847
X-RateLimit-Used: 153
X-RateLimit-Reset: 1730419200
```

## Best Practices

1. **Use webhooks** for production - no polling needed
2. **Add descriptions** to schema fields for better extraction accuracy
3. **Handle hil_flag** - route flagged fields to human review queue
4. **Use blueprints** for repeated document types (20-30% accuracy improvement)
5. **Poll every 5-10 seconds** if you can't use webhooks

## Error Handling

| Error | Cause | Solution |
|-------|-------|----------|
| `quota_exceeded` | Monthly limit reached | Upgrade plan or wait for reset |
| `invalid_schema` | Invalid JSON Schema | Ensure valid schema with `type` and `properties` |
| `file_too_large` | >50MB file | Compress PDF or split into smaller files |
| `job_failed` | Processing error | Check file isn't corrupted or password-protected |

## When to Use DeepRead

**Use For:**
- Invoice processing (vendor, totals, line items)
- Receipt OCR (merchant, items, totals)
- Contract analysis (parties, dates, terms)
- Form digitization (paper forms to structured data)
- Quality-critical apps (need to know which extractions are uncertain)

**Not Ideal For:**
- Real-time processing (takes 2-5 minutes)
- Batch >2,000 pages/month on free tier

## Resources

- **Dashboard**: https://www.deepread.tech/dashboard
- **API Docs**: https://docs.deepread.tech
- **GitHub**: https://github.com/deepread-tech
- **Support**: hello@deepread.tech

---

**Free tier**: 2,000 pages/month | **Sign up**: https://www.deepread.tech/dashboard

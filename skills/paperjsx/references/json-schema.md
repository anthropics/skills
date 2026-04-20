# PaperJSX JSON Layout Spec — Schema Reference

This document contains the complete input schemas for all PaperJSX document generation tools. Use these schemas to produce valid JSON input.

---

## PPTX Presentation

**Tool:** `generate_presentation`
**Package:** `@paperjsx/json-to-pptx`

### Top-level fields

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `title` | string | yes | — | Presentation title |
| `author` | string | no | — | Author/presenter name |
| `company` | string | no | — | Company name |
| `date` | string | no | — | Presentation date |
| `slides` | SlideContent[] | yes | — | Array of slides (1–50) |
| `theme` | enum | no | `"corporate"` | `"corporate"`, `"modern"`, `"minimal"`, `"dark"`, `"gradient"` |
| `primary_color` | string | no | — | Primary brand color (hex) |
| `secondary_color` | string | no | — | Secondary accent color (hex) |
| `logo_url` | string (URL) | no | — | Company logo URL |
| `format` | enum | no | `"pptx"` | `"pptx"` or `"pdf"` |
| `aspect_ratio` | enum | no | `"16:9"` | `"16:9"` or `"4:3"` |
| `include_slide_numbers` | boolean | no | `true` | Show slide numbers |
| `include_footer` | boolean | no | `true` | Show footer |

### Slide types

Each slide has a `type` field that determines its structure.

#### `"title"` — Title slide

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"title"` | yes | — |
| `title` | string | yes | Main title text |
| `subtitle` | string | no | Subtitle text |
| `background_image_url` | string (URL) | no | Background image |

#### `"content"` — Bullet content slide

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | `"content"` | yes | — | — |
| `heading` | string | yes | — | Slide heading |
| `bullets` | string[] | yes | — | Bullet points |
| `image_url` | string (URL) | no | — | Optional image |
| `image_position` | enum | no | `"right"` | `"left"` or `"right"` |

#### `"chart"` — Chart slide

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"chart"` | yes | — |
| `heading` | string | yes | Slide heading |
| `chart` | ChartConfig | yes | Chart configuration (see below) |
| `caption` | string | no | Chart caption or source |

**ChartConfig:**

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | enum | yes | `"line"`, `"bar"`, `"pie"`, `"area"` |
| `data` | object[] | yes | Array of data points (key-value records) |
| `x_key` | string | yes | Key for X-axis |
| `y_keys` | string[] | yes | Keys for Y-axis series |
| `colors` | string[] | no | Hex colors for each series |

#### `"two_column"` — Two-column layout

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"two_column"` | yes | — |
| `heading` | string | yes | Slide heading |
| `left` | string[] | yes | Left column bullet points |
| `right` | string[] | yes | Right column bullet points |
| `left_heading` | string | no | Left column sub-heading |
| `right_heading` | string | no | Right column sub-heading |

#### `"quote"` — Quote slide

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"quote"` | yes | — |
| `quote` | string | yes | Quote text |
| `attribution` | string | no | Quote source |
| `background_color` | string | no | Background color (hex) |

#### `"image"` — Image slide

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | `"image"` | yes | — | — |
| `heading` | string | no | — | Optional heading |
| `image_url` | string (URL) | yes | — | Main image URL |
| `caption` | string | no | — | Image caption |
| `fit` | enum | no | `"contain"` | `"contain"`, `"cover"`, `"fill"` |

#### `"comparison"` — Comparison slide

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"comparison"` | yes | — |
| `heading` | string | yes | Slide heading |
| `items` | ComparisonItem[] | yes | 2–4 comparison items |

**ComparisonItem:** `{ label: string, value: string, highlight?: boolean }`

#### `"stats"` — Stats/metrics slide

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | `"stats"` | yes | — |
| `heading` | string | yes | Slide heading |
| `stats` | StatItem[] | yes | 1–4 stat items |

**StatItem:** `{ label: string, value: string, change?: string, trend?: "up" | "down" | "neutral" }`

---

## PDF Invoice

**Tool:** `generate_invoice`
**Package:** `@paperjsx/json-to-pdf`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `invoice_number` | string | yes | — | Unique invoice ID |
| `issue_date` | string | yes | — | ISO 8601 (YYYY-MM-DD) |
| `due_date` | string | yes | — | ISO 8601 (YYYY-MM-DD) |
| `from` | InvoiceSender | yes | — | Sender info (see below) |
| `to` | Address | yes | — | Recipient info |
| `items` | LineItem[] | yes | — | Line items (min: 1) |
| `currency` | enum | no | `"USD"` | ISO 4217 code: USD, EUR, GBP, INR, BRL, AUD, CAD, JPY, CNY, CHF, SGD, HKD |
| `tax_rate` | number | no | `0` | Default tax rate (0–100) |
| `discount_total` | number | no | — | Discount amount |
| `shipping` | number | no | — | Shipping cost |
| `notes` | string | no | — | Additional notes/terms |
| `payment_instructions` | string | no | — | Payment instructions |
| `purchase_order` | string | no | — | PO number |
| `theme` | enum | no | — | `"corporate"`, `"modern"`, `"minimal"`, `"academic"`, `"legal"` |

**InvoiceSender** extends Address with: `logo_url?: string (URL)`

**Address:** `{ name, address_line_1, address_line_2?, city, state?, postal_code, country, email?, phone?, tax_id? }`

**LineItem:** `{ description: string, quantity: number, unit_price: number, tax_rate?: number (0–100), discount?: number (0–100) }`

---

## PDF Report

**Tool:** `generate_report`
**Package:** `@paperjsx/json-to-pdf`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `title` | string | yes | — | Report title |
| `subtitle` | string | no | — | Subtitle |
| `author` | string | no | — | Author name |
| `date` | string | no | — | ISO 8601 (YYYY-MM-DD) |
| `version` | string | no | — | e.g. "v1.0", "Draft" |
| `content` | string | yes | — | Full markdown content |
| `include_toc` | boolean | no | `true` | Auto-generate table of contents |
| `include_cover` | boolean | no | `true` | Generate cover page |
| `page_numbers` | boolean | no | `true` | Show page numbers |
| `toc_depth` | number | no | `3` | Max heading level in TOC (1–6) |
| `theme` | enum | no | — | `"corporate"`, `"modern"`, `"minimal"`, `"academic"`, `"legal"` |
| `primary_color` | string | no | — | Hex color for headings |
| `font_family` | enum | no | `"sans"` | `"sans"`, `"serif"`, `"mono"` |
| `page_format` | enum | no | `"a4"` | `"a4"`, `"letter"`, `"legal"` |
| `orientation` | enum | no | `"portrait"` | `"portrait"`, `"landscape"` |
| `header_logo_url` | string (URL) | no | — | Logo for header |
| `footer_text` | string | no | — | Footer text |

**Markdown content supports:** headings (#–######), GFM tables, fenced code blocks, images via URL, bullet/numbered lists, blockquotes, bold/italic/strikethrough, horizontal rules, links.

---

## PDF Chart Document

**Tool:** `generate_chart_document`
**Package:** `@paperjsx/json-to-pdf`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `title` | string | yes | — | Document title |
| `subtitle` | string | no | — | Subtitle |
| `author` | string | no | — | Author name |
| `date` | string | no | — | ISO 8601 |
| `charts` | ChartConfig[] | yes | — | 1–4 chart configurations |
| `analysis_text` | string | no | — | Markdown analysis/commentary |
| `key_insights` | string[] | no | — | Bullet points of insights |
| `include_data_table` | boolean | no | `false` | Include raw data as table |
| `theme` | enum | no | — | `"corporate"`, `"modern"`, `"minimal"`, `"academic"`, `"legal"` |
| `page_format` | enum | no | `"a4"` | `"a4"`, `"letter"`, `"legal"` |
| `primary_color` | string | no | — | Hex color for accents |

**ChartConfig:**

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | enum | yes | — | `"line"`, `"bar"`, `"pie"`, `"area"`, `"scatter"`, `"composed"` |
| `title` | string | no | — | Chart title |
| `data` | object[] | yes | — | Array of data points (key-value records) |
| `x_key` | string | yes | — | Key for X-axis |
| `y_keys` | string[] | yes | — | Keys for Y-axis series |
| `colors` | string[] | no | — | Hex colors for each series |
| `show_legend` | boolean | no | `true` | Show legend |
| `show_grid` | boolean | no | `true` | Show grid lines |
| `y_axis_label` | string | no | — | Y-axis label |
| `x_axis_label` | string | no | — | X-axis label |
| `stacked` | boolean | no | — | Stack bars/areas |

---

## XLSX Spreadsheet

**Tool:** `generate_spreadsheet`
**Package:** `@paperjsx/json-to-xlsx`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `document` | SpreadsheetDoc | yes | — | Spreadsheet document JSON |
| `output_filename` | string | no | — | Safe .xlsx filename (alphanumeric, dots, hyphens, underscores) |
| `render_options` | object | no | — | `{ deterministic?, large_dataset?, row_chunk_size? (max 100K), string_strategy?: "auto"|"sharedStrings"|"inlineStrings" }` |
| `validate_after_render` | boolean | no | `true` | Validate output after generation |
| `attempt_repair_if_needed` | boolean | no | `true` | Auto-repair if validation finds issues |

**SpreadsheetDoc:**

```json
{
  "meta": {
    "title": "string",
    "creator": "string"
  },
  "sheets": [
    {
      "name": "Sheet1",
      "rows": [
        {
          "cells": [
            { "value": "string or number or boolean" }
          ]
        }
      ]
    }
  ]
}
```

---

## DOCX Report

**Tool:** `generate_report_docx`
**Package:** `@paperjsx/json-to-docx`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `title` | string | yes | — | Report title |
| `subtitle` | string | no | — | Subtitle |
| `author` | string | no | — | Author name |
| `date` | string | no | — | YYYY-MM-DD format |
| `sections` | Section[] | yes | — | Report sections (min: 1) |
| `include_toc` | boolean | no | `true` | Table of contents |
| `theme` | enum | no | `"corporate"` | `"corporate"`, `"modern"`, `"classic"`, `"academic"`, `"minimal"` |
| `page_size` | enum | no | `"a4"` | `"a4"`, `"letter"`, `"legal"` |
| `orientation` | enum | no | `"portrait"` | `"portrait"`, `"landscape"` |
| `header_text` | string | no | — | Header text |
| `footer_text` | string | no | — | Footer text |
| `include_page_numbers` | boolean | no | `true` | Show page numbers |

**Section:** `{ heading: string, level?: number (1–4, default 1), content: string, bullets?: string[] }`

Content paragraphs are separated by double newlines.

---

## DOCX Contract

**Tool:** `generate_contract_docx`
**Package:** `@paperjsx/json-to-docx`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `title` | string | yes | — | Contract title |
| `effective_date` | string | yes | — | Effective date |
| `parties` | Party[] | yes | — | Contracting parties (min: 2) |
| `recitals` | string[] | no | — | WHEREAS clauses/preamble |
| `clauses` | Clause[] | yes | — | Contract clauses (min: 1) |
| `signatures` | Signature[] | no | — | Signature blocks |
| `theme` | enum | no | `"classic"` | `"corporate"`, `"classic"`, `"academic"` |
| `page_size` | enum | no | `"letter"` | `"a4"`, `"letter"`, `"legal"` |

**Party:** `{ name: string, address: string, role: string }`

**Clause:** `{ number: string, title: string, content: string, subclauses?: [{ label: string, content: string }] }`

**Signature:** `{ name: string, title: string, party: string }`

---

## DOCX Invoice

**Tool:** `generate_invoice_docx`
**Package:** `@paperjsx/json-to-docx`

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `invoice_number` | string | yes | — | Invoice ID |
| `date` | string | yes | — | Invoice date |
| `due_date` | string | yes | — | Payment due date |
| `sender` | object | yes | — | `{ name, address, email?, phone?, tax_id? }` |
| `recipient` | object | yes | — | `{ name, address, email?, tax_id? }` |
| `items` | InvoiceItem[] | yes | — | Line items (min: 1) |
| `subtotal` | number | yes | — | Subtotal amount |
| `tax_rate` | number | no | — | Tax rate (decimal, e.g. 0.1 = 10%) |
| `tax_amount` | number | yes | — | Tax amount |
| `total` | number | yes | — | Total amount |
| `currency` | string | no | `"USD"` | ISO 4217 code |
| `notes` | string | no | — | Additional notes |
| `theme` | enum | no | `"corporate"` | `"corporate"`, `"modern"`, `"minimal"` |
| `page_size` | enum | no | `"a4"` | `"a4"`, `"letter"` |

**InvoiceItem:** `{ description: string, quantity: number, unit_price: number, amount: number }`

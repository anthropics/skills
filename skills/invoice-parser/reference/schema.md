# Invoice JSON schema (canonical)

Authoritative field definitions for the `invoice-parser` skill. The
validator in `scripts/validate.py` enforces this schema.

## Top-level object

| Field | Type | Required | Description |
|---|---|---|---|
| `schema_version` | string | yes | Always `"1"` for this iteration. |
| `document_type` | string | yes | One of `"invoice"`, `"receipt"`, `"credit_note"`. |
| `is_credit_note` | bool | yes | `true` for credit notes (negative total). |
| `vendor` | object | yes | See "Party" below. |
| `bill_to` | object | no | See "Party" below. `null` when not present. |
| `ship_to` | object | no | See "Party" below. `null` when not present. |
| `invoice_number` | string | yes | As printed. `null` only if truly absent. |
| `issue_date` | string (ISO 8601) | yes | `YYYY-MM-DD`. |
| `due_date` | string (ISO 8601) | no | `null` if not specified. |
| `currency` | string | yes | ISO 4217 code (`USD`, `EUR`, `GBP`, `INR`, `JPY`, …). |
| `line_items` | array | yes | See "Line item" below. Minimum length 1 for a valid invoice. |
| `subtotal` | number | yes | Sum of line items, before tax/shipping/tip/discount. |
| `tax` | array | yes | List of `{name, rate, amount}` tax lines. Empty array if no tax. |
| `discount` | number | no | Positive number. `null` if no discount. |
| `shipping` | number | no | `null` if not shipped. |
| `tip` | number | no | Only when a tip was actually recorded, not just suggested. |
| `total` | number | yes | Grand total the customer owes (or is credited). |
| `amount_paid` | number | no | For invoices with partial payments recorded. |
| `amount_due` | number | no | `total - amount_paid`. |
| `tax_inclusive` | bool | no | `true` when line-item amounts already include VAT. Default `false`. |
| `payment_terms` | string | no | Free text (`Net 30`, `Due on receipt`, …). |
| `payment_methods` | array | no | List of accepted methods as strings. |
| `notes` | string | no | Free-text notes printed on the invoice. |
| `parse_notes` | array | no | Parser's own observations (ambiguity, OCR concerns, handwritten fields). |
| `validation_errors` | array | yes | Machine-readable list of failed checks. Empty array when clean. |
| `source` | object | no | `{format: "pdf"|"image"|"text", pages: int}` for provenance. |

## Party (`vendor`, `bill_to`, `ship_to`)

| Field | Type | Required | Description |
|---|---|---|---|
| `name` | string | yes (for vendor) | Legal or trading name. |
| `address` | string | no | Free-form address block, newlines preserved. |
| `country` | string | no | ISO 3166-1 alpha-2 (`US`, `GB`, `IN`). |
| `tax_id` | string | no | VAT number, EIN, GSTIN, etc. Include the label prefix (`VAT: GB123…`). |
| `email` | string | no | |
| `phone` | string | no | E.164 preferred but as-printed acceptable. |

## Line item

| Field | Type | Required | Description |
|---|---|---|---|
| `description` | string | yes | Item or service description. |
| `sku` | string | no | Product code, if printed. |
| `quantity` | number | yes | Default `1` if not printed (service invoices). |
| `unit` | string | no | `hour`, `each`, `kg`, `L`, etc. |
| `unit_price` | number | yes | Price for one `unit`. Pre-VAT unless `tax_inclusive: true` at top level. |
| `amount` | number | yes | `quantity * unit_price` (validated within 1-cent tolerance). |
| `tax_rate` | number | no | Percentage as a number (`20` for 20%). For per-line VAT. |

## Tax line

| Field | Type | Required | Description |
|---|---|---|---|
| `name` | string | yes | E.g. `"VAT"`, `"GST"`, `"State Sales Tax"`, `"Service charge"`. |
| `rate` | number | no | Percentage. `null` for fixed-amount taxes. |
| `amount` | number | yes | Currency amount for this tax line. |

## Validation errors

Every entry in `validation_errors` looks like:

```json
{
  "check": "line_items_sum_equals_subtotal",
  "expected": 100.00,
  "observed": 99.98,
  "delta": 0.02,
  "message": "Sum of line item amounts differs from stated subtotal."
}
```

Check names emitted by the validator:

- `required_field_missing`
- `wrong_type`
- `currency_not_iso_4217`
- `date_not_iso_8601`
- `line_item_amount_mismatch` (per-line `qty * unit_price != amount`)
- `line_items_sum_equals_subtotal`
- `total_equals_subtotal_plus_adjustments`
- `total_sign_mismatch_credit_note`
- `negative_amount_where_not_allowed`

## Currency decimal precision

| Currency | Decimals |
|---|---|
| JPY, KRW, VND, HUF (accounting), CLP, ISK | 0 |
| BHD, KWD, OMR, JOD, TND, LYD | 3 |
| all others | 2 |

The validator enforces this tolerance on all monetary comparisons.

## Example (minimal, clean)

```json
{
  "schema_version": "1",
  "document_type": "invoice",
  "is_credit_note": false,
  "vendor": {"name": "Acme Widgets Ltd", "country": "GB", "tax_id": "VAT: GB123456789"},
  "bill_to": {"name": "Beta Corp"},
  "ship_to": null,
  "invoice_number": "INV-2025-0142",
  "issue_date": "2025-11-14",
  "due_date": "2025-12-14",
  "currency": "GBP",
  "line_items": [
    {"description": "Widget, blue", "quantity": 10, "unit": "each", "unit_price": 5.00, "amount": 50.00}
  ],
  "subtotal": 50.00,
  "tax": [{"name": "VAT", "rate": 20, "amount": 10.00}],
  "discount": null,
  "shipping": null,
  "tip": null,
  "total": 60.00,
  "tax_inclusive": false,
  "validation_errors": []
}
```

---
name: invoice-parser
description: >
  Extract structured data from an invoice or receipt (PDF, PNG, JPG,
  or extracted text) and emit it as strict JSON matching
  reference/schema.md — vendor, bill-to, invoice number and dates,
  currency (ISO 4217), per-line items with quantity, unit price and
  amount, subtotal, tax lines (VAT, GST, sales tax), discount,
  shipping, tip, and total. Also validates the math is internally
  consistent (line items sum to subtotal; subtotal + tax + shipping
  + tip − discount equals total), flags discrepancies in a
  validation_errors array, and can convert parsed invoices to a flat
  CSV for bookkeeping import. Use when the user says extract fields
  from this invoice, parse this receipt, digitize this invoice, read
  this PDF invoice into JSON, make this receipt into a CSV, or
  attaches an invoice or receipt image/PDF and asks for the total,
  line items, or vendor. Do NOT use for creating invoices, general
  document OCR, expense categorisation, or accounting entry
  generation.
license: Complete terms in LICENSE.txt
---

# Invoice Parser

## Why this exists

Invoices arrive in every conceivable shape — PDF, phone photo,
scanned image, email body, EDI, whatever the vendor felt like — and
somebody has to turn them into rows in a bookkeeping system. That
somebody is usually a person copying numbers into a spreadsheet at
the end of the month, and the top failure mode is a transposed digit
or a missed tax line that quietly poisons the books.

This skill exists to make Claude the reliable middle layer: extract
the fields, validate the math is internally consistent *before* it
lands anywhere, and produce a schema that can be diffed, joined, and
imported.

## When to run

Run this skill when the user:

- Attaches an invoice/receipt (PDF, image, or scanned page) and asks
  for the total, the line items, the vendor, or "just parse this".
- Says any of: "extract fields from this invoice", "parse this
  receipt", "digitize this invoice", "read this invoice into JSON",
  "make these receipts into a CSV".
- Pastes invoice text (from an email, OCR output, or a copy-paste)
  and wants it structured.

Do **not** run this skill for:

- **Creating** invoices — that is a document-authoring task, use the
  `pdf` or `docx` skill.
- **General document OCR** without invoice structure — use the `pdf`
  skill directly.
- **Bookkeeping categorisation** (chart-of-accounts mapping) — this
  skill emits raw fields; a downstream skill or tool assigns
  accounts.
- **Fraud detection** — schema validation catches math errors, not
  intent.

## Extraction protocol

Follow these steps, in order, on every invoice you parse.

### 1. Identify the document type

Before anything else, confirm you are looking at an invoice or
receipt, not (e.g.) a quote, purchase order, packing slip, bank
statement, or credit-card charge slip. Look for:

- The word `Invoice`, `Bill`, `Receipt`, `Tax Invoice`, `Facture`,
  `Rechnung`, `Factura`, or the presence of an `Invoice No.` /
  `Invoice #` field and a monetary total.
- A named seller/vendor and a named or implied buyer.
- Line items or a single "amount due" figure.

If the document is clearly not an invoice, say so and stop. Do not
force-fit the schema onto a purchase order or packing slip.

### 2. Extract to the schema

Emit **one JSON object per invoice**, matching the schema in
`reference/schema.md`. Every field in the "required" list must be
present; use `null` when the invoice genuinely does not contain the
value, and only then. Do not invent values.

Key rules:

- **Currency.** Always ISO 4217 (`USD`, `EUR`, `GBP`, `INR`, `JPY`,
  `CAD`, `AUD`). If the invoice shows `$` with no country hint,
  default to `USD` and add a note in `parse_notes`. Do the same for
  `£`→`GBP`, `€`→`EUR`, `¥`→`JPY` (Japan) or `CNY` (China, if
  context indicates), `₹`→`INR`.
- **Dates.** ISO 8601 (`YYYY-MM-DD`). If only month and year are
  legible, use `YYYY-MM-01` and add a note. If the format is
  ambiguous (`03/04/2025` could be March-4 or April-3), lean on the
  vendor's country if known; otherwise ask.
- **Amounts.** JSON numbers, not strings. Two decimal places for
  most currencies; three for BHD/KWD/OMR/JOD/TND; zero for JPY/KRW.
  Never include currency symbols inside a number field.
- **Line items.** Every line item has `description`, `quantity`,
  `unit_price`, and `amount`. If `quantity` is not printed on the
  invoice (common for service invoices), use `1`. If `unit_price`
  is not printed, compute `amount / quantity` and note it.
- **Tax lines.** An invoice can have multiple tax lines (VAT + local
  tax, or 20% and 5% VAT rows). Emit an array of `{name, rate,
  amount}` objects, not a single number.
- **Tips.** Restaurant/hospitality invoices frequently show a
  suggested-tip box that the customer may or may not have filled in.
  Only include a tip in the total if it was actually written on the
  receipt (a handwritten amount, a signed slip). Otherwise leave
  `tip` as `null` and note the observation.
- **Discounts.** Represent as a positive number. `total = subtotal +
  tax + shipping + tip - discount`. Some invoices display the
  discount as a negative line item; still store it as a positive
  amount in the `discount` field and remove it from the line items.

See `reference/edge-cases.md` for handling of: multi-page invoices,
credit notes, split payments, foreign-currency conversion sections,
non-Latin scripts, and OCR ambiguity.

### 3. Validate the math

Before returning the result, run `scripts/validate.py` on the JSON
(or apply the same checks manually if the script is not available).
It verifies:

- Sum of `line_items[*].amount` equals `subtotal` (within one
  currency unit of least precision — e.g. 1 cent for USD/EUR, 1 yen
  for JPY — to allow for rounding).
- Every `line_items[i].amount` equals `quantity * unit_price` within
  tolerance.
- `subtotal + sum(tax) + shipping + tip - discount` equals `total`
  within a 1-cent tolerance.
- Every date parses as ISO 8601.
- Currency code is in ISO 4217.
- `total` is positive (or, for credit notes, is negative and
  `is_credit_note` is `true`).

Any failure goes into `validation_errors` as a `{check, expected,
observed, delta}` entry. **Do not silently correct the numbers to
make them balance.** If the invoice says `subtotal = 100.00` and the
line items sum to `99.98`, record both values as-is and let the user
decide whether it's a rounding artifact, an OCR misread, or a real
vendor error.

### 4. Emit the result

For a single invoice, print the JSON object. For a batch, print a
JSON array. If the user asked for CSV, pipe through `scripts/
validate.py --to-csv`.

## Running the validator

```bash
# Validate a single parsed invoice JSON
python scripts/validate.py path/to/invoice.json

# Validate + convert one invoice to a single-row CSV
python scripts/validate.py path/to/invoice.json --to-csv

# Validate + convert a batch (JSON array or JSONL) to CSV
python scripts/validate.py invoices.jsonl --to-csv > out.csv

# Print the flat CSV column list (the JSON schema is in reference/schema.md)
python scripts/validate.py --print-csv-columns

# Run the built-in fixture tests
python scripts/validate.py --self-test
```

Exit codes: `0` valid, `1` at least one math or format validation
error, `2` schema violation (missing required field, wrong type) or
unreadable input.

## Reporting to the user

After parsing, tell the user:

1. **What you extracted** — vendor, invoice number, total, currency,
   and line-item count. Keep it to one sentence.
2. **Any validation errors** — list each with the check name and the
   observed delta, framed in plain language ("Line items sum to
   99.98 but the invoice shows a subtotal of 100.00 — a two-cent
   rounding gap"). Do not silently fix; ask which side to trust.
3. **Where the file is** — if you wrote a JSON or CSV output, name
   the path.

Do **not** paste back the full invoice text unless asked. The
structured output is the artifact; the raw text is scratch.

## Edge cases to handle correctly

`reference/edge-cases.md` is the authoritative reference. The most
common gotchas:

- **VAT-inclusive vs. VAT-exclusive.** UK/EU invoices often show a
  `£120.00` line where the VAT is already baked in. Look for `incl.
  VAT` / `VAT inclusive` / `TVA comprise`. When VAT-inclusive, keep
  `unit_price` and `amount` as the printed (VAT-inclusive) values
  and set `tax_inclusive: true` at the top level — the validator
  then expects `total = subtotal + shipping + tip − discount`
  (without re-adding tax).
- **Service charge vs. tip.** UK/European restaurant bills often
  add a mandatory `Service charge` (e.g. 12.5%) that is *not* a tip.
  Emit it as a tax line named `Service charge`, not as `tip`.
- **US sales tax vs. VAT.** US sales tax is a single line, not
  itemised per goods class. VAT invoices usually show a per-line
  VAT rate and a VAT summary table. Both fit the multi-line `tax`
  array; the difference is only in how many entries you emit.
- **Credit notes.** A credit note is an invoice with a negative
  total. Set `is_credit_note: true` and store the total as a
  negative number. Line items remain positive; the sign is on the
  total only.
- **Split payments.** If the invoice shows partial payments (`Amount
  paid: 50.00 / Balance due: 50.00`), extract `amount_paid` and
  `amount_due` fields. `total` is still the full amount.
- **Foreign-currency conversion boxes.** Some invoices show both the
  local currency and a converted amount. Extract the local currency
  as the primary. Add the converted amount to `parse_notes` — do
  not emit two currency codes.
- **Handwritten additions.** Signed tips, handwritten notes on a
  printed slip. Include them but note in `parse_notes` that the
  field was handwritten.

## Never do

- **Never silently correct arithmetic.** If the invoice's own math
  is wrong, that is a fact worth surfacing, not a bug to fix behind
  the user's back.
- **Never invent values.** `null` is a valid answer. A made-up
  invoice number is not.
- **Never assume USD.** Currency-symbol ambiguity is real (there
  are twenty-plus `$` currencies globally). If in doubt, look for
  address, phone country code, tax label (`VAT` = not US, `GST` =
  not US, `Sales tax` = usually US), or ask.
- **Never emit the schema fields you don't have data for as empty
  strings.** Use `null`. Empty string means "the invoice actually
  contained an empty field", which is different.

## Extending the schema

When adding a field:

1. Add it to `reference/schema.md` with type, required/optional,
   and description.
2. Add validation logic to `scripts/validate.py` if the new field
   participates in math or has a format constraint.
3. Extend the `--self-test` fixtures so the new field has both a
   present and an absent case.
4. Run `python scripts/validate.py --self-test` — must be 0
   failures.

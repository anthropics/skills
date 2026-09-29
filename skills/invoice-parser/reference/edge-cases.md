# Invoice-parsing edge cases

The schema in `schema.md` is boring — the reality of invoices is
not. This file documents the specific decisions the skill makes for
the recurring hard cases.

## Currency-symbol ambiguity

The `$` symbol is used by USD, CAD, AUD, NZD, MXN, SGD, HKD, TWD,
COP, CLP, ARS, and about a dozen others. `¥` covers JPY and CNY.
`£` is almost always GBP but appears for EGP (`£E`) and SDG. Never
assume USD without evidence.

Signals to check, in order of reliability:

1. Explicit ISO code (`USD`, `EUR`) — trust it.
2. `Country: …` or address country field.
3. Tax label — `VAT` rules out the US, Canada, and most of Asia
   (though the UK, EU, India, and Australia all have VAT-family
   taxes with different names — VAT, GST, IVA, TVA).
4. `Sales tax` strongly implies a US state.
5. Phone country code in the vendor block.
6. Domain suffix on the vendor's email (`.co.uk`, `.de`, `.jp`).

If none of these resolve, ask the user before defaulting.

## VAT-inclusive line items

UK and EU invoices commonly show prices with VAT already added, and
list VAT as a memo at the bottom (`of which VAT: £20.00`).
Symptoms:

- Line items sum to the total (no separate VAT to add on top).
- A note like `Prices include VAT` or `Prix TTC`.

Handling:

- Set `tax_inclusive: true` at the top level.
- Keep `unit_price` as the printed value (VAT-inclusive).
- Emit the VAT line in the `tax` array with the calculated amount.
- The validator relaxes the `total = subtotal + tax` check when
  `tax_inclusive: true` and instead checks that VAT amount is
  consistent with the rate applied to the pre-tax portion.

## Service charge vs. tip

UK and European restaurants often add a mandatory 12.5% service
charge that is *not* a tip. In the US, tips are almost always
voluntary and handwritten.

- If the amount is printed by the POS and labelled `Service charge`
  / `Service compris` / `Servicio`, emit as a tax line with
  `name: "Service charge"`.
- If the amount is handwritten in the tip line, emit as `tip`.
- If a suggested-tip box is printed but the customer wrote nothing,
  `tip: null` and add a `parse_notes` entry saying so. Do not
  guess.

## Credit notes / negative invoices

A credit note reverses a previous invoice, either fully or
partially. Format is identical to an invoice but the total is
negative (or shown as positive with a `Credit note` header).

- `document_type: "credit_note"`, `is_credit_note: true`.
- `total` is negative.
- Line items stay positive; the negation is only at the summary
  level. This lets the same rows join cleanly against the original
  invoice for reconciliation.
- The validator enforces `total < 0` when `is_credit_note: true`.

## Split / partial payments

Some invoices record payments already made:

```
Subtotal      100.00
Tax            20.00
Total         120.00
Paid           50.00
Balance due    70.00
```

Emit `total: 120.00`, `amount_paid: 50.00`, `amount_due: 70.00`.
`total` stays as the original obligation.

## Foreign-currency conversion box

A UK vendor billing a US customer may print:

```
Total:  £100.00
        ($125.00 @ 1.25)
```

Handling: extract the primary (contract) currency, which is £/GBP
here. The USD conversion is informational — add to `parse_notes`
(e.g. `"Vendor also displayed converted amount USD 125.00 at rate
1.25."`). Do not emit a second `currency` field.

## Multi-page invoices

- Sum line items across all pages before computing `subtotal`.
- If page 1 says `Subtotal (continued on page 2)` and page 2 has
  the true subtotal, use page 2.
- Record `source.pages` = total page count.

## OCR ambiguity

Common misreads:

- `0` vs `O` in invoice numbers.
- `1` vs `l` vs `I`.
- `5` vs `S`.
- Decimal separator: European invoices often use `,` as decimal
  (`1.234,56` = 1234.56). Detect by whether `.` or `,` is used
  three-from-the-right.
- Column alignment: if amounts and quantities got merged
  (`10.005.00` from `10.00 5.00`), split by known patterns and add a
  `parse_notes` entry.

When you cannot resolve an ambiguity, add a `parse_notes` entry
naming the specific field and the two most-likely readings. Do not
pick one silently.

## Non-Latin scripts

Chinese, Japanese, Korean, Arabic, Hindi, Thai invoices are all in
scope. Rules:

- Numbers are usually still Arabic numerals; if they're localized
  (e.g. Bengali digits `০১২৩৪`), normalize to `0-9` and note in
  `parse_notes`.
- Vendor and buyer names stay in their original script — do not
  transliterate silently. If a Latin version is also printed
  (common on export invoices), prefer that for `name` and add the
  script version to `notes`.
- Right-to-left scripts (Arabic, Hebrew) may confuse column parsing
  when both directions appear on the same page. Trust the numbers
  as printed; do not mirror.

## Rounding

Vendors round differently. `£10.00 * 3 @ 20% VAT` might be
`£12.00` line, `£2.00` VAT, `£12.00` total; or it might be `£10.00`
line, `£2.00` VAT, `£12.00` total. Both are valid.

- Per-line: compute `qty * unit_price` and compare to printed
  amount within 1 cent per line (using currency decimals from the
  schema table). If off by more than tolerance, emit
  `line_item_amount_mismatch`.
- Subtotal/total: same 1-cent tolerance.
- For JPY (0 decimals), tolerance is 1 yen.

## Handwritten amendments

A common workflow: a printed receipt, then the customer writes a
tip and total on the tip line and signs.

- Emit the handwritten values as the final numbers.
- Add `parse_notes` entries: `"Tip amount 3.00 is handwritten."`,
  `"Total 23.00 is handwritten and confirmed by signature."`
- If the handwritten total does not equal `subtotal + tax + tip`,
  do not silently correct. Emit both the handwritten total and a
  `validation_errors` entry showing the delta. The customer chose
  those numbers on purpose or by mistake; either way the human
  reviewer should see it.

## What to do when things really don't add up

Sometimes the invoice's own printed math is wrong (vendor error).
Sometimes OCR fed you noise. Either way:

1. Emit the schema with the numbers as extracted.
2. Populate `validation_errors` with every discrepancy — do not
   suppress any.
3. Add a `parse_notes` entry describing what you saw ("Subtotal
   printed as 100.00 but line items sum to 99.98; likely a vendor
   rounding artifact.").
4. Do not adjust the numbers to make them balance.

The correctness contract is: what you emit reflects what was on the
document, plus a machine-readable list of every place the document
disagrees with itself.

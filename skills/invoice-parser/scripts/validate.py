#!/usr/bin/env python3
"""Validate an extracted invoice (or batch) against the schema in
../reference/schema.md, and optionally convert to flat CSV.

Uses only the Python 3 standard library.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import re
import sys
from dataclasses import dataclass, field
from typing import Any

SCHEMA_VERSION = "1"

# ISO 4217 codes and the accounting decimal precision used to
# validate monetary comparisons. Only the currencies that deviate
# from 2 dp are listed; anything unknown defaults to 2 dp.
_CURRENCY_DECIMALS: dict[str, int] = {
    "JPY": 0, "KRW": 0, "VND": 0, "CLP": 0, "ISK": 0, "HUF": 0,
    "BHD": 3, "KWD": 3, "OMR": 3, "JOD": 3, "TND": 3, "LYD": 3,
}

# A curated but not exhaustive set. Add codes as needed; unknown
# codes trigger `currency_not_iso_4217`.
_ISO_4217 = {
    "USD", "EUR", "GBP", "JPY", "CNY", "INR", "CAD", "AUD", "NZD",
    "CHF", "SEK", "NOK", "DKK", "PLN", "CZK", "HUF", "RON", "BGN",
    "TRY", "RUB", "UAH", "ILS", "AED", "SAR", "QAR", "KWD", "BHD",
    "OMR", "JOD", "TND", "LYD", "EGP", "ZAR", "NGN", "KES", "GHS",
    "MXN", "BRL", "ARS", "CLP", "COP", "PEN", "VEF", "SGD", "HKD",
    "TWD", "KRW", "THB", "IDR", "MYR", "PHP", "VND", "PKR", "BDT",
    "LKR", "NPR", "MMK",
}

DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


# ------------------------------------------------------------------ #
# Result model
# ------------------------------------------------------------------ #


@dataclass
class ValidationError:
    check: str
    expected: Any = None
    observed: Any = None
    delta: float | None = None
    message: str = ""
    path: str = ""


@dataclass
class Report:
    invoice_index: int
    invoice_number: str | None
    errors: list[ValidationError] = field(default_factory=list)


# ------------------------------------------------------------------ #
# Schema conformance
# ------------------------------------------------------------------ #


_REQUIRED_TOP = ["schema_version", "document_type", "is_credit_note", "vendor",
                 "invoice_number", "issue_date", "currency", "line_items",
                 "subtotal", "tax", "total", "validation_errors"]

_REQUIRED_LINE = ["description", "quantity", "unit_price", "amount"]
_REQUIRED_TAX = ["name", "amount"]


def _check_required(obj: dict, required: list[str], errs: list[ValidationError], base: str) -> None:
    for k in required:
        if k not in obj:
            errs.append(ValidationError(
                check="required_field_missing", path=f"{base}.{k}",
                message=f"Missing required field: {base}.{k}"))


def _check_type(obj: dict, key: str, expected: type | tuple[type, ...], errs: list[ValidationError], base: str) -> bool:
    if key not in obj:
        return False
    value = obj[key]
    # Explicitly reject bool when a numeric type is expected (bool is a subclass of int in Python).
    numeric_expected = expected is float or expected is int or (
        isinstance(expected, tuple) and set(expected) <= {int, float}
    )
    if numeric_expected and isinstance(value, bool):
        errs.append(ValidationError(
            check="wrong_type", path=f"{base}.{key}",
            expected=_type_name(expected), observed="bool",
            message=f"Expected {_type_name(expected)} at {base}.{key}, got bool"))
        return False
    if not isinstance(value, expected):
        errs.append(ValidationError(
            check="wrong_type", path=f"{base}.{key}",
            expected=_type_name(expected), observed=type(value).__name__,
            message=f"Expected {_type_name(expected)} at {base}.{key}, got {type(value).__name__}"))
        return False
    return True


def _type_name(expected: type | tuple[type, ...]) -> str:
    if isinstance(expected, tuple):
        return " or ".join(t.__name__ for t in expected)
    return expected.__name__


# ------------------------------------------------------------------ #
# Math checks
# ------------------------------------------------------------------ #


def _tolerance_for(currency: str) -> float:
    decimals = _CURRENCY_DECIMALS.get(currency.upper(), 2)
    return 10 ** (-decimals)


def _round(v: float, currency: str) -> float:
    decimals = _CURRENCY_DECIMALS.get(currency.upper(), 2)
    return round(v, decimals)


# ------------------------------------------------------------------ #
# Validation
# ------------------------------------------------------------------ #


_TOP_TYPES: dict[str, type | tuple[type, ...]] = {
    "schema_version": str,
    "document_type": str,
    "is_credit_note": bool,
    "vendor": dict,
    "bill_to": dict,
    "ship_to": dict,
    "invoice_number": str,
    "issue_date": str,
    "due_date": str,
    "currency": str,
    "line_items": list,
    "subtotal": (int, float),
    "tax": list,
    "discount": (int, float),
    "shipping": (int, float),
    "tip": (int, float),
    "total": (int, float),
    "amount_paid": (int, float),
    "amount_due": (int, float),
    "tax_inclusive": bool,
    "payment_terms": str,
    "payment_methods": list,
    "notes": str,
    "parse_notes": list,
    "validation_errors": list,
    "source": dict,
}

_LINE_ITEM_TYPES: dict[str, type | tuple[type, ...]] = {
    "description": str,
    "sku": str,
    "quantity": (int, float),
    "unit": str,
    "unit_price": (int, float),
    "amount": (int, float),
    "tax_rate": (int, float),
}

_TAX_LINE_TYPES: dict[str, type | tuple[type, ...]] = {
    "name": str,
    "rate": (int, float),
    "amount": (int, float),
}


def _check_types(obj: dict, types: dict, errs: list[ValidationError], base: str) -> None:
    for key, expected in types.items():
        if key in obj and obj[key] is None:
            # None is accepted for any field — represents "absent" per schema conventions.
            continue
        _check_type(obj, key, expected, errs, base)


def validate_invoice(invoice: dict, index: int = 0) -> Report:
    errs: list[ValidationError] = []
    number = invoice.get("invoice_number") if isinstance(invoice, dict) else None
    report = Report(invoice_index=index, invoice_number=number, errors=errs)

    if not isinstance(invoice, dict):
        errs.append(ValidationError(
            check="wrong_type", path="root",
            expected="object", observed=type(invoice).__name__,
            message=f"Invoice must be a JSON object, got {type(invoice).__name__}"))
        return report

    _check_required(invoice, _REQUIRED_TOP, errs, "root")
    _check_types(invoice, _TOP_TYPES, errs, "root")

    sv = invoice.get("schema_version")
    if sv is not None and isinstance(sv, str) and sv != SCHEMA_VERSION:
        errs.append(ValidationError(
            check="schema_version_mismatch", path="schema_version",
            expected=SCHEMA_VERSION, observed=sv,
            message=f"schema_version {sv!r} does not match parser version {SCHEMA_VERSION!r}."))

    currency = invoice.get("currency")
    if isinstance(currency, str) and currency.upper() not in _ISO_4217:
        errs.append(ValidationError(
            check="currency_not_iso_4217", path="currency", observed=currency,
            message=f"Currency {currency!r} is not a recognised ISO 4217 code."))

    for datefield in ("issue_date", "due_date"):
        v = invoice.get(datefield)
        if v is None:
            continue
        if isinstance(v, str) and not DATE_RE.match(v):
            errs.append(ValidationError(
                check="date_not_iso_8601", path=datefield, observed=v,
                message=f"{datefield} is not ISO 8601 (YYYY-MM-DD)."))

    line_items = invoice.get("line_items")
    subtotal = invoice.get("subtotal")
    tax_lines = invoice.get("tax") or []
    discount = invoice.get("discount") or 0
    shipping = invoice.get("shipping") or 0
    tip = invoice.get("tip") or 0
    total = invoice.get("total")
    tax_inclusive = bool(invoice.get("tax_inclusive"))
    is_credit_note = bool(invoice.get("is_credit_note"))
    cur = currency if isinstance(currency, str) else "USD"
    tol = _tolerance_for(cur)

    if isinstance(line_items, list):
        if len(line_items) == 0:
            errs.append(ValidationError(
                check="line_items_empty", path="line_items",
                expected=">=1", observed=0,
                message="line_items must contain at least one entry."))
        for i, li in enumerate(line_items):
            if not isinstance(li, dict):
                errs.append(ValidationError(
                    check="wrong_type", path=f"line_items[{i}]",
                    expected="object", observed=type(li).__name__))
                continue
            _check_required(li, _REQUIRED_LINE, errs, f"line_items[{i}]")
            _check_types(li, _LINE_ITEM_TYPES, errs, f"line_items[{i}]")
            qty = li.get("quantity")
            up = li.get("unit_price")
            amt = li.get("amount")
            if (all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in (qty, up, amt))):
                computed = _round(qty * up, cur)
                if abs(computed - amt) > tol + 1e-9:
                    errs.append(ValidationError(
                        check="line_item_amount_mismatch",
                        path=f"line_items[{i}]",
                        expected=computed, observed=amt, delta=round(amt - computed, 4),
                        message=f"line_items[{i}]: {qty} * {up} = {computed}, printed as {amt}."))

        if isinstance(subtotal, (int, float)) and not isinstance(subtotal, bool):
            summed = _round(sum((li.get("amount") or 0) for li in line_items
                                if isinstance(li, dict) and isinstance(li.get("amount"), (int, float))
                                and not isinstance(li.get("amount"), bool)), cur)
            if abs(summed - subtotal) > tol + 1e-9:
                errs.append(ValidationError(
                    check="line_items_sum_equals_subtotal",
                    path="subtotal",
                    expected=summed, observed=subtotal, delta=round(subtotal - summed, 4),
                    message=f"Sum of line item amounts ({summed}) differs from subtotal ({subtotal})."))

    tax_total = 0.0
    if isinstance(tax_lines, list):
        for i, tl in enumerate(tax_lines):
            if not isinstance(tl, dict):
                errs.append(ValidationError(
                    check="wrong_type", path=f"tax[{i}]",
                    expected="object", observed=type(tl).__name__))
                continue
            _check_required(tl, _REQUIRED_TAX, errs, f"tax[{i}]")
            _check_types(tl, _TAX_LINE_TYPES, errs, f"tax[{i}]")
            a = tl.get("amount")
            if isinstance(a, (int, float)) and not isinstance(a, bool):
                tax_total += a

    if (isinstance(subtotal, (int, float)) and not isinstance(subtotal, bool)
            and isinstance(total, (int, float)) and not isinstance(total, bool)):
        if tax_inclusive:
            base = subtotal + shipping + tip - discount
        else:
            base = subtotal + tax_total + shipping + tip - discount
        expected_total = _round(-base if is_credit_note else base, cur)
        if abs(expected_total - total) > tol + 1e-9:
            errs.append(ValidationError(
                check="total_equals_subtotal_plus_adjustments",
                path="total",
                expected=expected_total, observed=total, delta=round(total - expected_total, 4),
                message=(f"Expected total {expected_total} = subtotal ({subtotal}) "
                         f"+ tax ({tax_total if not tax_inclusive else 0}) + shipping ({shipping}) "
                         f"+ tip ({tip}) - discount ({discount}); observed {total}.")))

    if is_credit_note and isinstance(total, (int, float)) and total > 0:
        errs.append(ValidationError(
            check="total_sign_mismatch_credit_note",
            path="total", expected="<0", observed=total,
            message="is_credit_note is true but total is positive."))
    if not is_credit_note and isinstance(total, (int, float)) and total < 0:
        errs.append(ValidationError(
            check="total_sign_mismatch_credit_note",
            path="total", expected=">=0", observed=total,
            message="total is negative but is_credit_note is false. Set is_credit_note true."))

    for f in ("subtotal", "shipping", "tip", "discount"):
        v = invoice.get(f)
        if isinstance(v, (int, float)) and v < 0:
            errs.append(ValidationError(
                check="negative_amount_where_not_allowed",
                path=f, observed=v,
                message=f"{f} must be >= 0; got {v}. Represent discounts as positive numbers."))

    return report


# ------------------------------------------------------------------ #
# CSV
# ------------------------------------------------------------------ #

_CSV_COLUMNS = [
    "invoice_number", "issue_date", "due_date", "currency", "vendor_name",
    "vendor_country", "vendor_tax_id", "bill_to_name", "line_number",
    "line_description", "line_sku", "quantity", "unit_price", "line_amount",
    "subtotal", "tax_total", "discount", "shipping", "tip", "total",
    "amount_paid", "amount_due", "is_credit_note", "tax_inclusive",
    "payment_terms", "valid",
]


def _sum_tax(inv: dict) -> float:
    total = 0.0
    for t in inv.get("tax") or []:
        if isinstance(t, dict) and isinstance(t.get("amount"), (int, float)):
            total += t["amount"]
    return total


def invoice_to_rows(inv: dict, valid: bool) -> list[dict]:
    vendor = inv.get("vendor") or {}
    bill = inv.get("bill_to") or {}
    common = {
        "invoice_number": inv.get("invoice_number"),
        "issue_date": inv.get("issue_date"),
        "due_date": inv.get("due_date"),
        "currency": inv.get("currency"),
        "vendor_name": vendor.get("name"),
        "vendor_country": vendor.get("country"),
        "vendor_tax_id": vendor.get("tax_id"),
        "bill_to_name": bill.get("name"),
        "subtotal": inv.get("subtotal"),
        "tax_total": _sum_tax(inv),
        "discount": inv.get("discount"),
        "shipping": inv.get("shipping"),
        "tip": inv.get("tip"),
        "total": inv.get("total"),
        "amount_paid": inv.get("amount_paid"),
        "amount_due": inv.get("amount_due"),
        "is_credit_note": inv.get("is_credit_note"),
        "tax_inclusive": inv.get("tax_inclusive"),
        "payment_terms": inv.get("payment_terms"),
        "valid": "yes" if valid else "no",
    }
    rows: list[dict] = []
    items = inv.get("line_items") or []
    if not items:
        rows.append({**common, "line_number": None, "line_description": None,
                     "line_sku": None, "quantity": None, "unit_price": None, "line_amount": None})
    else:
        for i, li in enumerate(items):
            li = li if isinstance(li, dict) else {}
            rows.append({
                **common,
                "line_number": i + 1,
                "line_description": li.get("description"),
                "line_sku": li.get("sku"),
                "quantity": li.get("quantity"),
                "unit_price": li.get("unit_price"),
                "line_amount": li.get("amount"),
            })
    return rows


def write_csv(invoices: list[dict], reports: list[Report], stream: io.TextIOBase) -> None:
    writer = csv.DictWriter(stream, fieldnames=_CSV_COLUMNS, extrasaction="ignore")
    writer.writeheader()
    for inv, rep in zip(invoices, reports):
        for row in invoice_to_rows(inv, valid=not rep.errors):
            writer.writerow(row)


# ------------------------------------------------------------------ #
# I/O
# ------------------------------------------------------------------ #


def _load_input(path: str) -> list[dict]:
    if path == "-":
        raw = sys.stdin.read()
    else:
        with open(path, "r", encoding="utf-8") as f:
            raw = f.read()
    raw = raw.strip()
    if not raw:
        return []
    if raw[0] == "[":
        return json.loads(raw)
    if "\n" in raw and raw[0] == "{":
        # JSONL
        try:
            return [json.loads(line) for line in raw.splitlines() if line.strip()]
        except json.JSONDecodeError:
            pass
    return [json.loads(raw)]


def format_report(rep: Report) -> str:
    if not rep.errors:
        return f"invoice[{rep.invoice_index}] {rep.invoice_number or '?'}: OK ({len(rep.errors)} errors)"
    out = [f"invoice[{rep.invoice_index}] {rep.invoice_number or '?'}: {len(rep.errors)} error(s)"]
    for e in rep.errors:
        line = f"  - [{e.check}] {e.path}: {e.message or ''}"
        if e.delta is not None:
            line += f" (delta={e.delta})"
        out.append(line)
    return "\n".join(out)


# ------------------------------------------------------------------ #
# Self-test
# ------------------------------------------------------------------ #


_FIXTURE_CLEAN = {
    "schema_version": "1",
    "document_type": "invoice",
    "is_credit_note": False,
    "vendor": {"name": "Acme Widgets Ltd", "country": "GB", "tax_id": "VAT: GB123456789"},
    "bill_to": {"name": "Beta Corp"},
    "ship_to": None,
    "invoice_number": "INV-2025-0142",
    "issue_date": "2025-11-14",
    "due_date": "2025-12-14",
    "currency": "GBP",
    "line_items": [
        {"description": "Widget, blue", "quantity": 10, "unit_price": 5.00, "amount": 50.00},
        {"description": "Setup fee", "quantity": 1, "unit_price": 20.00, "amount": 20.00},
    ],
    "subtotal": 70.00,
    "tax": [{"name": "VAT", "rate": 20, "amount": 14.00}],
    "discount": None,
    "shipping": None,
    "tip": None,
    "total": 84.00,
    "tax_inclusive": False,
    "validation_errors": [],
}

_FIXTURE_BAD_MATH = {
    **_FIXTURE_CLEAN,
    "invoice_number": "INV-BAD-001",
    "line_items": [
        {"description": "Widget, blue", "quantity": 10, "unit_price": 5.00, "amount": 40.00},
        {"description": "Setup fee", "quantity": 1, "unit_price": 20.00, "amount": 20.00},
    ],
    "subtotal": 70.00,
    "total": 90.00,
}

_FIXTURE_BAD_CURRENCY = {**_FIXTURE_CLEAN, "invoice_number": "INV-BAD-002", "currency": "ZZZ"}

_FIXTURE_BAD_DATE = {**_FIXTURE_CLEAN, "invoice_number": "INV-BAD-003", "issue_date": "11/14/2025"}

_FIXTURE_CREDIT_NOTE = {**_FIXTURE_CLEAN, "invoice_number": "CN-001",
                        "document_type": "credit_note", "is_credit_note": True,
                        "total": -84.00}

_FIXTURE_CREDIT_NOTE_BAD = {**_FIXTURE_CREDIT_NOTE, "invoice_number": "CN-BAD",
                            "total": 84.00}

_FIXTURE_TAX_INCLUSIVE = {
    **_FIXTURE_CLEAN,
    "invoice_number": "INV-INC-001",
    "line_items": [
        {"description": "Meal", "quantity": 1, "unit_price": 84.00, "amount": 84.00},
    ],
    "subtotal": 84.00,
    "tax": [{"name": "VAT", "rate": 20, "amount": 14.00}],
    "total": 84.00,
    "tax_inclusive": True,
}

_FIXTURE_WRONG_TYPE_SUBTOTAL = {**_FIXTURE_CLEAN, "invoice_number": "INV-BAD-004",
                                "subtotal": "70.00"}

_FIXTURE_EMPTY_LINE_ITEMS = {**_FIXTURE_CLEAN, "invoice_number": "INV-BAD-005",
                             "line_items": [], "subtotal": 0.00, "total": 14.00}

_FIXTURE_MISSING_SCHEMA_VERSION = {k: v for k, v in _FIXTURE_CLEAN.items() if k != "schema_version"}
_FIXTURE_MISSING_SCHEMA_VERSION = {**_FIXTURE_MISSING_SCHEMA_VERSION, "invoice_number": "INV-BAD-006"}


def self_test() -> int:
    tests: list[tuple[str, dict, set[str], set[str]]] = [
        # (name, fixture, must_include, must_not_include)
        ("clean", _FIXTURE_CLEAN, set(), set()),
        ("bad_math_line", _FIXTURE_BAD_MATH,
         {"line_item_amount_mismatch", "line_items_sum_equals_subtotal", "total_equals_subtotal_plus_adjustments"},
         set()),
        ("bad_currency", _FIXTURE_BAD_CURRENCY, {"currency_not_iso_4217"}, set()),
        ("bad_date", _FIXTURE_BAD_DATE, {"date_not_iso_8601"}, set()),
        ("credit_note_valid", _FIXTURE_CREDIT_NOTE, set(), set()),
        ("credit_note_sign_wrong", _FIXTURE_CREDIT_NOTE_BAD, {"total_sign_mismatch_credit_note"}, set()),
        ("tax_inclusive_valid", _FIXTURE_TAX_INCLUSIVE, set(), set()),
        ("wrong_type_subtotal", _FIXTURE_WRONG_TYPE_SUBTOTAL, {"wrong_type"}, set()),
        ("empty_line_items", _FIXTURE_EMPTY_LINE_ITEMS, {"line_items_empty"}, set()),
        # Missing schema_version must report required_field_missing once, and must NOT
        # also report wrong_type / schema_version_mismatch for a field that was absent.
        ("missing_schema_version", _FIXTURE_MISSING_SCHEMA_VERSION,
         {"required_field_missing"}, {"schema_version_mismatch", "wrong_type"}),
    ]
    ok = 0
    fail = 0
    for entry in tests:
        name, fixture, expected_checks, forbidden_checks = entry
        rep = validate_invoice(fixture)
        got = {e.check for e in rep.errors}
        # For "clean" tests, we require exactly zero errors.
        if not expected_checks and not forbidden_checks:
            if got:
                print(f"  [{name}] expected clean, got errors: {sorted(got)}", file=sys.stderr)
                fail += 1
                continue
            ok += 1
            continue
        missing = expected_checks - got
        forbidden_present = forbidden_checks & got
        if missing or forbidden_present:
            if missing:
                print(f"  [{name}] missing expected checks: {sorted(missing)}; got {sorted(got)}", file=sys.stderr)
            if forbidden_present:
                # Allow forbidden check to appear only if it is for a different field.
                # Here specifically: schema_version_mismatch should never fire when
                # schema_version is absent.
                offending = [e for e in rep.errors if e.check in forbidden_present
                             and (e.path == "schema_version" or e.path.endswith(".schema_version"))]
                if offending:
                    print(f"  [{name}] forbidden checks present for schema_version: "
                          f"{[(e.check, e.path) for e in offending]}", file=sys.stderr)
                    fail += 1
                    continue
            if missing:
                fail += 1
                continue
        ok += 1
    # CSV smoke: run against the clean fixture and check header + one row.
    buf = io.StringIO()
    write_csv([_FIXTURE_CLEAN], [validate_invoice(_FIXTURE_CLEAN)], buf)
    csv_text = buf.getvalue()
    if "invoice_number" in csv_text.splitlines()[0] and "INV-2025-0142" in csv_text:
        ok += 1
    else:
        print("  [csv] header or content missing", file=sys.stderr)
        fail += 1
    print(f"self-test: {ok} passed, {fail} failed")
    return 0 if fail == 0 else 1


# ------------------------------------------------------------------ #
# CLI
# ------------------------------------------------------------------ #


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    except AttributeError:
        pass
    ap = argparse.ArgumentParser(description="Validate parsed-invoice JSON and optionally emit CSV.")
    ap.add_argument("path", nargs="?", help="Path to JSON file (single invoice, JSON array, or JSONL). Use '-' for stdin.")
    ap.add_argument("--to-csv", action="store_true", help="Emit a CSV row per line item to stdout.")
    ap.add_argument("--print-csv-columns", action="store_true",
                    help="Print the flat CSV column list (the JSON schema itself lives in reference/schema.md).")
    ap.add_argument("--self-test", action="store_true", help="Run built-in fixture tests.")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if args.print_csv_columns:
        for c in _CSV_COLUMNS:
            print(c)
        return 0
    if not args.path:
        ap.error("path is required (use '-' for stdin, or --self-test / --print-csv-columns)")

    try:
        invoices = _load_input(args.path)
    except (OSError, json.JSONDecodeError) as e:
        print(f"error: could not read/parse {args.path}: {e}", file=sys.stderr)
        return 2
    if not invoices:
        print("error: no invoices in input", file=sys.stderr)
        return 2

    reports = [validate_invoice(inv, i) for i, inv in enumerate(invoices)]

    if args.to_csv:
        write_csv(invoices, reports, sys.stdout)
    else:
        for rep in reports:
            print(format_report(rep))

    schema_checks = {"required_field_missing", "wrong_type"}
    any_schema = any(e.check in schema_checks for rep in reports for e in rep.errors)
    any_errors = any(rep.errors for rep in reports)
    if any_schema:
        return 2
    return 1 if any_errors else 0


if __name__ == "__main__":
    sys.exit(main())

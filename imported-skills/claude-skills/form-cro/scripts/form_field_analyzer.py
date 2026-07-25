#!/usr/bin/env python3
"""
Form Field Analyzer for CRO

Analyzes HTML forms for conversion optimization opportunities.
Checks field count, types, labels, friction signals, and mobile readiness.

Usage:
  python3 form_field_analyzer.py                    # Demo mode
  python3 form_field_analyzer.py form.html          # Analyze HTML file
  python3 form_field_analyzer.py form.html --json   # JSON output
"""

import json
import sys
import os
import re
from html.parser import HTMLParser


class FormAnalyzer(HTMLParser):
    def __init__(self):
        super().__init__()
        self.forms = []
        self.current_form = None
        self.in_label = False
        self.current_label = ""
        self.in_button = False
        self.current_button = ""

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)

        if tag == "form":
            self.current_form = {
                "action": attrs_dict.get("action", ""),
                "method": attrs_dict.get("method", "GET").upper(),
                "fields": [],
                "buttons": [],
                "has_autocomplete": "autocomplete" in attrs_dict
            }

        elif tag == "input" and self.current_form is not None:
            input_type = attrs_dict.get("type", "text").lower()
            if input_type not in ("hidden", "submit"):
                self.current_form["fields"].append({
                    "type": input_type,
                    "name": attrs_dict.get("name", ""),
                    "placeholder": attrs_dict.get("placeholder", ""),
                    "required": "required" in attrs_dict,
                    "autocomplete": attrs_dict.get("autocomplete", ""),
                    "has_label": False
                })
            elif input_type == "submit":
                self.current_form["buttons"].append(attrs_dict.get("value", "Submit"))

        elif tag == "textarea" and self.current_form is not None:
            self.current_form["fields"].append({
                "type": "textarea",
                "name": attrs_dict.get("name", ""),
                "placeholder": attrs_dict.get("placeholder", ""),
                "required": "required" in attrs_dict,
                "autocomplete": "",
                "has_label": False
            })

        elif tag == "select" and self.current_form is not None:
            self.current_form["fields"].append({
                "type": "select",
                "name": attrs_dict.get("name", ""),
                "placeholder": "",
                "required": "required" in attrs_dict,
                "autocomplete": "",
                "has_label": False
            })

        elif tag == "label":
            self.in_label = True
            self.current_label = ""
            for_attr = attrs_dict.get("for", "")
            if for_attr and self.current_form:
                for field in self.current_form["fields"]:
                    if field["name"] == for_attr:
                        field["has_label"] = True

        elif tag == "button":
            self.in_button = True
            self.current_button = ""

    def handle_data(self, data):
        if self.in_label:
            self.current_label += data.strip()
        if self.in_button:
            self.current_button += data.strip()

    def handle_endtag(self, tag):
        if tag == "form" and self.current_form:
            self.forms.append(self.current_form)
            self.current_form = None
        elif tag == "label":
            self.in_label = False
        elif tag == "button":
            self.in_button = False
            if self.current_button and self.current_form:
                self.current_form["buttons"].append(self.current_button)


def analyze_form(form):
    """Analyze a single form for CRO issues."""
    fields = form["fields"]
    issues = []
    warnings = []
    positives = []

    field_count = len(fields)

    # Field count analysis
    if field_count > 7:
        issues.append(f"Too many fields ({field_count}). Each field above 3 reduces conversion by ~5-10%. Consider progressive disclosure.")
    elif field_count > 4:
        warnings.append(f"{field_count} fields — acceptable but test reducing to 3-4 core fields.")
    elif field_count <= 3:
        positives.append(f"Low friction — only {field_count} fields.")

    # Phone number field
    phone_fields = [f for f in fields if "phone" in f["name"].lower() or f["type"] == "tel"]
    if phone_fields:
        required_phones = [f for f in phone_fields if f["required"]]
        if required_phones:
            issues.append("Phone number is REQUIRED — this is the #1 form abandonment trigger. Make optional or remove.")
        else:
            warnings.append("Phone field present (optional) — still causes friction. Consider removing unless sales-critical.")

    # Labels
    unlabeled = [f for f in fields if not f["has_label"] and not f["placeholder"]]
    if unlabeled:
        issues.append(f"{len(unlabeled)} fields have no label AND no placeholder. Users won't know what to enter.")

    placeholder_only = [f for f in fields if not f["has_label"] and f["placeholder"]]
    if placeholder_only:
        warnings.append(f"{len(placeholder_only)} fields use placeholder-only labels. Placeholders disappear on focus — use visible labels.")

    # Button text
    weak_ctas = ["submit", "send", "go", "ok"]
    for btn in form["buttons"]:
        if btn.lower() in weak_ctas:
            warnings.append(f'CTA button says "{btn}" — use action-specific text like "Get My Free Report" or "Start Free Trial".')

    if not form["buttons"]:
        issues.append("No submit button found. Form may be broken or use JavaScript submission only.")

    # Autocomplete
    fields_with_autocomplete = [f for f in fields if f["autocomplete"]]
    if not fields_with_autocomplete and field_count > 0:
        warnings.append("No autocomplete attributes. Adding autocomplete reduces mobile friction significantly.")

    # Required fields
    required_count = sum(1 for f in fields if f["required"])
    if required_count == field_count and field_count > 2:
        warnings.append("ALL fields are required. Consider making some optional to reduce perceived commitment.")

    # Score
    score = 100
    score -= len(issues) * 15
    score -= len(warnings) * 5
    score += len(positives) * 5
    score = max(0, min(100, score))

    return {
        "field_count": field_count,
        "required_count": required_count,
        "has_phone": len(phone_fields) > 0,
        "cta_text": form["buttons"],
        "issues": issues,
        "warnings": warnings,
        "positives": positives,
        "score": score,
        "fields": [{"name": f["name"], "type": f["type"], "required": f["required"]} for f in fields]
    }


def format_report(analyses):
    """Format human-readable report."""
    lines = []
    lines.append("")
    lines.append("=" * 60)
    lines.append("  FORM CRO — FIELD ANALYSIS REPORT")
    lines.append("=" * 60)

    for i, analysis in enumerate(analyses):
        lines.append("")
        lines.append(f"  FORM {i + 1}")
        lines.append(f"  Fields: {analysis['field_count']} | Required: {analysis['required_count']} | CTA: {', '.join(analysis['cta_text']) or 'none'}")
        lines.append("")

        score = analysis["score"]
        bar = "█" * (score // 5) + "░" * (20 - score // 5)
        lines.append(f"  FORM SCORE: {score}/100")
        lines.append(f"  [{bar}]")
        lines.append("")

        lines.append("  Fields:")
        for f in analysis["fields"]:
            req = " *" if f["required"] else ""
            lines.append(f"    [{f['type']}] {f['name']}{req}")
        lines.append("")

        if analysis["positives"]:
            lines.append("  🟢 STRENGTHS:")
            for p in analysis["positives"]:
                lines.append(f"     ✓ {p}")
            lines.append("")

        if analysis["issues"]:
            lines.append("  🔴 ISSUES:")
            for issue in analysis["issues"]:
                lines.append(f"     • {issue}")
            lines.append("")

        if analysis["warnings"]:
            lines.append("  🟡 WARNINGS:")
            for warn in analysis["warnings"]:
                lines.append(f"     • {warn}")
            lines.append("")

    return "\n".join(lines)


SAMPLE_HTML = """
<form action="/submit" method="POST">
  <label for="name">Full Name</label>
  <input type="text" name="name" id="name" required placeholder="John Smith">

  <label for="email">Work Email</label>
  <input type="email" name="email" id="email" required placeholder="you@company.com">

  <label for="company">Company</label>
  <input type="text" name="company" id="company" required>

  <label for="phone">Phone Number</label>
  <input type="tel" name="phone" id="phone" required>

  <label for="role">Job Title</label>
  <input type="text" name="role" id="role" required>

  <label for="employees">Company Size</label>
  <select name="employees" id="employees" required>
    <option value="">Select...</option>
    <option value="1-10">1-10</option>
    <option value="11-50">11-50</option>
    <option value="51-200">51-200</option>
    <option value="200+">200+</option>
  </select>

  <label for="message">How can we help?</label>
  <textarea name="message" id="message" placeholder="Tell us about your needs..."></textarea>

  <button type="submit">Submit</button>
</form>
"""


def main():
    use_json = "--json" in sys.argv
    args = [a for a in sys.argv[1:] if a != "--json"]

    if args and os.path.isfile(args[0]):
        with open(args[0]) as f:
            html = f.read()
    else:
        if not args:
            print("[Demo mode — analyzing sample lead capture form]")
        html = SAMPLE_HTML

    parser = FormAnalyzer()
    parser.feed(html)

    if not parser.forms:
        print("No <form> elements found in the HTML.")
        sys.exit(1)

    analyses = [analyze_form(form) for form in parser.forms]

    if use_json:
        print(json.dumps(analyses, indent=2))
    else:
        print(format_report(analyses))


if __name__ == "__main__":
    main()

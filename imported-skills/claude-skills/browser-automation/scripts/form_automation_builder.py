#!/usr/bin/env python3
"""
Form Automation Builder - Generates Playwright form-fill automation scripts.

Takes a JSON field specification and target URL, then produces a ready-to-run
Playwright script that fills forms, handles multi-step flows, and manages
file uploads.

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import os
import sys
import textwrap
from datetime import datetime


SUPPORTED_FIELD_TYPES = {
    "text": "page.fill('{selector}', '{value}')",
    "password": "page.fill('{selector}', '{value}')",
    "email": "page.fill('{selector}', '{value}')",
    "textarea": "page.fill('{selector}', '{value}')",
    "select": "page.select_option('{selector}', value='{value}')",
    "checkbox": "page.check('{selector}')" if True else "page.uncheck('{selector}')",
    "radio": "page.check('{selector}')",
    "file": "page.set_input_files('{selector}', '{value}')",
    "click": "page.click('{selector}')",
}


def validate_fields(fields):
    """Validate the field specification format. Returns list of issues."""
    issues = []
    if not isinstance(fields, list):
        issues.append("Top-level structure must be a JSON array of field objects.")
        return issues

    for i, field in enumerate(fields):
        if not isinstance(field, dict):
            issues.append(f"Field {i}: must be a JSON object.")
            continue
        if "selector" not in field:
            issues.append(f"Field {i}: missing required 'selector' key.")
        if "type" not in field:
            issues.append(f"Field {i}: missing required 'type' key.")
        elif field["type"] not in SUPPORTED_FIELD_TYPES:
            issues.append(
                f"Field {i}: unsupported type '{field['type']}'. "
                f"Supported: {', '.join(sorted(SUPPORTED_FIELD_TYPES.keys()))}"
            )
        if field.get("type") not in ("checkbox", "radio", "click") and "value" not in field:
            issues.append(f"Field {i}: missing 'value' for type '{field.get('type', '?')}'.")

    return issues


def generate_field_action(field, indent=8):
    """Generate the Playwright action line for a single field."""
    ftype = field["type"]
    selector = field["selector"]
    value = field.get("value", "")
    label = field.get("label", selector)
    prefix = " " * indent

    lines = []
    lines.append(f'{prefix}# {label}')

    if ftype == "checkbox":
        if field.get("value", "true").lower() in ("true", "yes", "1", "on"):
            lines.append(f'{prefix}await page.check("{selector}")')
        else:
            lines.append(f'{prefix}await page.uncheck("{selector}")')
    elif ftype == "radio":
        lines.append(f'{prefix}await page.check("{selector}")')
    elif ftype == "click":
        lines.append(f'{prefix}await page.click("{selector}")')
    elif ftype == "select":
        lines.append(f'{prefix}await page.select_option("{selector}", value="{value}")')
    elif ftype == "file":
        lines.append(f'{prefix}await page.set_input_files("{selector}", "{value}")')
    else:
        # text, password, email, textarea
        lines.append(f'{prefix}await page.fill("{selector}", "{value}")')

    # Add optional wait_after
    wait_after = field.get("wait_after")
    if wait_after:
        lines.append(f'{prefix}await page.wait_for_selector("{wait_after}")')

    return "\n".join(lines)


def build_form_script(url, fields, output_format="script"):
    """Build a Playwright form automation script from the field specification."""

    issues = validate_fields(fields)
    if issues:
        return None, issues

    if output_format == "json":
        config = {
            "url": url,
            "fields": fields,
            "field_count": len(fields),
            "field_types": list(set(f["type"] for f in fields)),
            "has_file_upload": any(f["type"] == "file" for f in fields),
            "generated_at": datetime.now().isoformat(),
        }
        return config, None

    # Group fields into steps if step markers are present
    steps = {}
    for field in fields:
        step = field.get("step", 1)
        if step not in steps:
            steps[step] = []
        steps[step].append(field)

    multi_step = len(steps) > 1

    # Generate step functions
    step_functions = []
    for step_num in sorted(steps.keys()):
        step_fields = steps[step_num]
        actions = "\n".join(generate_field_action(f) for f in step_fields)

        if multi_step:
            fn = textwrap.dedent(f"""\
async def fill_step_{step_num}(page):
    \"\"\"Fill form step {step_num} ({len(step_fields)} fields).\"\"\"
    print(f"Filling step {step_num}...")
{actions}
    print(f"Step {step_num} complete.")
""")
        else:
            fn = textwrap.dedent(f"""\
async def fill_form(page):
    \"\"\"Fill form ({len(step_fields)} fields).\"\"\"
    print("Filling form...")
{actions}
    print("Form filled.")
""")
        step_functions.append(fn)

    step_functions_str = "\n\n".join(step_functions)

    # Generate main() call sequence
    if multi_step:
        step_calls = "\n".join(
            f"        await fill_step_{n}(page)" for n in sorted(steps.keys())
        )
    else:
        step_calls = "        await fill_form(page)"

    submit_selector = None
    for field in fields:
        if field.get("type") == "click" and field.get("is_submit"):
            submit_selector = field["selector"]
            break

    submit_block = ""
    if submit_selector:
        submit_block = textwrap.dedent(f"""\

        # Submit
        await page.click("{submit_selector}")
        await page.wait_for_load_state("networkidle")
        print("Form submitted.")
""")

    script = textwrap.dedent(f'''\
#!/usr/bin/env python3
"""
Auto-generated Playwright form automation script.
Target: {url}
Fields: {len(fields)}
Steps: {len(steps)}
Generated: {datetime.now().isoformat()}

Requirements:
    pip install playwright
    playwright install chromium
"""

import asyncio
import random
from playwright.async_api import async_playwright

URL = "{url}"

USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
]


{step_functions_str}

async def main():
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(
            viewport={{"width": 1920, "height": 1080}},
            user_agent=random.choice(USER_AGENTS),
        )
        page = await context.new_page()

        await page.add_init_script(
            "Object.defineProperty(navigator, \'webdriver\', {{get: () => undefined}});"
        )

        print(f"Navigating to {{URL}}...")
        await page.goto(URL, wait_until="networkidle")

{step_calls}
{submit_block}
        print("Automation complete.")
        await browser.close()


if __name__ == "__main__":
    asyncio.run(main())
''')

    return script, None


def main():
    parser = argparse.ArgumentParser(
        description="Generate Playwright form-fill automation scripts from a JSON field specification.",
        epilog=textwrap.dedent("""\
Examples:
  %(prog)s --url https://example.com/signup --fields fields.json
  %(prog)s --url https://example.com/signup --fields fields.json --output fill_form.py
  %(prog)s --url https://example.com/signup --fields fields.json --json

Field specification format (fields.json):
  [
    {"selector": "#email", "type": "email", "value": "user@example.com", "label": "Email"},
    {"selector": "#password", "type": "password", "value": "s3cret"},
    {"selector": "#country", "type": "select", "value": "US"},
    {"selector": "#terms", "type": "checkbox", "value": "true"},
    {"selector": "#avatar", "type": "file", "value": "/path/to/photo.jpg"},
    {"selector": "button[type='submit']", "type": "click", "is_submit": true}
  ]

Supported field types: text, password, email, textarea, select, checkbox, radio, file, click

Multi-step forms: Add "step": N to each field to group into steps.
        """),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--url",
        required=True,
        help="Target form URL",
    )
    parser.add_argument(
        "--fields",
        required=True,
        help="Path to JSON file containing field specifications",
    )
    parser.add_argument(
        "--output",
        help="Output file path (default: stdout)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        default=False,
        help="Output JSON configuration instead of Python script",
    )

    args = parser.parse_args()

    # Load fields
    fields_path = os.path.abspath(args.fields)
    if not os.path.isfile(fields_path):
        print(f"Error: Fields file not found: {fields_path}", file=sys.stderr)
        sys.exit(2)

    try:
        with open(fields_path, "r") as f:
            fields = json.load(f)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {fields_path}: {e}", file=sys.stderr)
        sys.exit(2)

    output_format = "json" if args.json_output else "script"
    result, errors = build_form_script(
        url=args.url,
        fields=fields,
        output_format=output_format,
    )

    if errors:
        print("Validation errors:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        sys.exit(2)

    if args.json_output:
        output_text = json.dumps(result, indent=2)
    else:
        output_text = result

    if args.output:
        output_path = os.path.abspath(args.output)
        with open(output_path, "w") as f:
            f.write(output_text)
        if not args.json_output:
            os.chmod(output_path, 0o755)
        print(f"Written to {output_path}", file=sys.stderr)
        sys.exit(0)
    else:
        print(output_text)
        sys.exit(0)


if __name__ == "__main__":
    main()

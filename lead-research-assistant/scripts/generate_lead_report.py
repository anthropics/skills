#!/usr/bin/env python3
"""
Lead Report Generator

Generates professional reports from company research data.
Supports multiple output formats: JSON, Markdown, HTML, PDF.
"""

import argparse
import json
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, List


def generate_markdown(data: Dict[str, Any]) -> str:
    """Generate Markdown report"""
    lines = [
        f"# Company Research Report: {data.get('company_name', 'Unknown')}",
        f"\n**Generated**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"\n**Website**: {data.get('website_url', 'N/A')}",
        "\n---\n",
        "## Company Overview\n",
    ]

    if data.get('description'):
        lines.append(f"**Description**: {data['description']}\n")

    if data.get('industry'):
        lines.append(f"**Industry**: {data['industry']}\n")

    if data.get('company_size'):
        lines.append(f"**Company Size**: {data['company_size']}\n")

    if data.get('headquarters'):
        lines.append(f"**Headquarters**: {data['headquarters']}\n")

    # Technologies
    if data.get('technologies'):
        lines.append("\n### Technologies Detected\n")
        for tech in data['technologies']:
            lines.append(f"- {tech}")
        lines.append("")

    # Team members
    team_members = data.get('team_members', [])
    if team_members:
        lines.append("\n## Team Members\n")
        for member in team_members:
            lines.append(f"\n### {member['name']}")
            if member.get('title'):
                lines.append(f"**Title**: {member['title']}")
            if member.get('email'):
                lines.append(f"**Email**: {member['email']}")
            if member.get('linkedin_url'):
                lines.append(f"**LinkedIn**: {member['linkedin_url']}")
            if member.get('bio'):
                lines.append(f"\n{member['bio']}")
            lines.append("")

    # Contact information
    lines.append("\n## Contact Information\n")

    contact_emails = data.get('contact_emails', [])
    if contact_emails:
        lines.append("\n### Email Addresses\n")
        for email in contact_emails:
            lines.append(f"- {email}")
        lines.append("")

    phone_numbers = data.get('phone_numbers', [])
    if phone_numbers:
        lines.append("\n### Phone Numbers\n")
        for phone in phone_numbers:
            lines.append(f"- {phone}")
        lines.append("")

    # Footer
    lines.append("\n---\n")
    lines.append("\n*This report contains only publicly available information.*")
    lines.append("*All data collection complies with GDPR, CCPA, and website Terms of Service.*")

    return "\n".join(lines)


def generate_html(data: Dict[str, Any]) -> str:
    """Generate HTML report"""
    md = generate_markdown(data)

    try:
        import markdown
        html_content = markdown.markdown(md)
    except ImportError:
        # Fallback: simple HTML conversion
        html_content = md.replace('\n', '<br>\n')

    html = f"""<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Company Research Report - {data.get('company_name', 'Unknown')}</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, Cantarell, sans-serif;
            max-width: 900px;
            margin: 40px auto;
            padding: 20px;
            line-height: 1.6;
            color: #333;
        }}
        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }}
        h2 {{
            color: #34495e;
            margin-top: 30px;
            border-bottom: 2px solid #ecf0f1;
            padding-bottom: 5px;
        }}
        h3 {{
            color: #555;
        }}
        .meta {{
            background: #ecf0f1;
            padding: 15px;
            border-radius: 5px;
            margin: 20px 0;
        }}
        .team-member {{
            background: #f8f9fa;
            padding: 15px;
            margin: 10px 0;
            border-left: 4px solid #3498db;
            border-radius: 3px;
        }}
        .footer {{
            margin-top: 40px;
            padding-top: 20px;
            border-top: 1px solid #ddd;
            font-size: 0.9em;
            color: #777;
        }}
        a {{
            color: #3498db;
            text-decoration: none;
        }}
        a:hover {{
            text-decoration: underline;
        }}
    </style>
</head>
<body>
    {html_content}
</body>
</html>"""

    return html


def generate_pdf(data: Dict[str, Any], output_path: str) -> None:
    """Generate PDF report"""
    html_content = generate_html(data)

    try:
        import pdfkit
        pdfkit.from_string(html_content, output_path)
    except ImportError:
        print("Error: pdfkit not installed. Install with: pip install pdfkit")
        print("Also requires wkhtmltopdf: https://wkhtmltopdf.org/downloads.html")
        print("\nFalling back to HTML output...")
        html_path = output_path.replace('.pdf', '.html')
        with open(html_path, 'w') as f:
            f.write(html_content)
        print(f"Saved HTML report to: {html_path}")


def main():
    parser = argparse.ArgumentParser(
        description='Generate professional lead research reports',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python generate_lead_report.py --input research.json --output report.md
  python generate_lead_report.py --input research.json --output report.html --format html
  python generate_lead_report.py --input research.json --output report.pdf --format pdf

Supported Formats:
  - markdown (default)
  - html
  - pdf (requires pdfkit and wkhtmltopdf)
  - json (prettified)
        """
    )

    parser.add_argument('--input', required=True, help='Input JSON file from analyze_company.py')
    parser.add_argument('--output', required=True, help='Output file path')
    parser.add_argument('--format', choices=['markdown', 'html', 'pdf', 'json'],
                       default='markdown', help='Output format')

    args = parser.parse_args()

    # Load input data
    with open(args.input, 'r') as f:
        data = json.load(f)

    # Generate report
    if args.format == 'markdown':
        content = generate_markdown(data)
        with open(args.output, 'w') as f:
            f.write(content)

    elif args.format == 'html':
        content = generate_html(data)
        with open(args.output, 'w') as f:
            f.write(content)

    elif args.format == 'pdf':
        generate_pdf(data, args.output)

    elif args.format == 'json':
        with open(args.output, 'w') as f:
            json.dump(data, f, indent=2)

    print(f"\nReport generated: {args.output}")


if __name__ == '__main__':
    main()

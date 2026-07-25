#!/usr/bin/env python3
"""
research-summarizer: Summary Formatter

Generate structured research summary templates for different source types.
Produces fill-in-the-blank frameworks for academic papers, web articles,
technical reports, and executive briefs.

Usage:
    python scripts/format_summary.py --template academic
    python scripts/format_summary.py --template executive --length brief
    python scripts/format_summary.py --list-templates
    python scripts/format_summary.py --template article --output json
"""

import argparse
import json
import sys
import textwrap
from datetime import datetime


# --- Templates ---

TEMPLATES = {
    "academic": {
        "name": "Academic Paper Summary",
        "description": "IMRAD structure for peer-reviewed papers and research studies",
        "sections": [
            ("Title", "[Full paper title]"),
            ("Author(s)", "[Author names, affiliations]"),
            ("Publication", "[Journal/Conference, Year, DOI]"),
            ("Source Type", "Academic Paper"),
            ("Key Thesis", "[1-2 sentences: the central research question and answer]"),
            ("Methodology", "[Study design, sample size, data sources, analytical approach]"),
            ("Key Findings", "1. [Finding 1 with supporting data]\n2. [Finding 2 with supporting data]\n3. [Finding 3 with supporting data]"),
            ("Statistical Significance", "[Key p-values, effect sizes, confidence intervals]"),
            ("Limitations", "- [Limitation 1: scope, sample, methodology gap]\n- [Limitation 2]"),
            ("Implications", "- [What this means for practice]\n- [What this means for future research]"),
            ("Notable Quotes", '> "[Direct quote]" (p. X)'),
            ("Quality Assessment", "Credibility: [High/Med/Low] | Evidence: [High/Med/Low] | Recency: [High/Med/Low] | Objectivity: [High/Med/Low]"),
        ],
    },
    "article": {
        "name": "Web Article Summary",
        "description": "Claim-evidence-implication structure for online articles and blog posts",
        "sections": [
            ("Title", "[Article title]"),
            ("Author", "[Author name]"),
            ("Source", "[Publication/Website, Date, URL]"),
            ("Source Type", "Web Article"),
            ("Central Claim", "[1-2 sentences: main argument or thesis]"),
            ("Supporting Evidence", "1. [Evidence point 1]\n2. [Evidence point 2]\n3. [Evidence point 3]"),
            ("Counterarguments Addressed", "- [Counterargument and author's response]"),
            ("Implications", "- [What this means for the reader]"),
            ("Bias Check", "Author affiliation: [?] | Funding: [?] | Balanced perspective: [Yes/No]"),
            ("Actionable Takeaways", "- [What to do with this information]\n- [Next step]"),
            ("Quality Assessment", "Credibility: [High/Med/Low] | Evidence: [High/Med/Low] | Recency: [High/Med/Low] | Objectivity: [High/Med/Low]"),
        ],
    },
    "report": {
        "name": "Technical Report Summary",
        "description": "Structured summary for industry reports, whitepapers, and technical documentation",
        "sections": [
            ("Title", "[Report title]"),
            ("Organization", "[Publishing organization]"),
            ("Date", "[Publication date]"),
            ("Source Type", "Technical Report"),
            ("Executive Summary", "[2-3 sentences: scope, key conclusion, recommendation]"),
            ("Scope", "[What the report covers and what it excludes]"),
            ("Key Data Points", "1. [Statistic or data point with context]\n2. [Statistic or data point with context]\n3. [Statistic or data point with context]"),
            ("Methodology", "[How data was collected — survey, analysis, case study]"),
            ("Recommendations", "1. [Recommendation with supporting rationale]\n2. [Recommendation with supporting rationale]"),
            ("Limitations", "- [Sample bias, geographic scope, time period]"),
            ("Relevance", "[Why this matters for our context — specific applicability]"),
            ("Quality Assessment", "Credibility: [High/Med/Low] | Evidence: [High/Med/Low] | Recency: [High/Med/Low] | Objectivity: [High/Med/Low]"),
        ],
    },
    "executive": {
        "name": "Executive Brief",
        "description": "Condensed decision-focused summary for leadership consumption",
        "sections": [
            ("Source", "[Title, Author, Date]"),
            ("Bottom Line", "[1 sentence: the single most important takeaway]"),
            ("Key Facts", "1. [Fact]\n2. [Fact]\n3. [Fact]"),
            ("So What?", "[Why this matters for our business/product/strategy]"),
            ("Action Required", "- [Specific next step with owner and timeline]"),
            ("Confidence", "[High/Medium/Low] — based on source quality and evidence strength"),
        ],
    },
    "comparison": {
        "name": "Comparative Analysis",
        "description": "Side-by-side comparison matrix for 2-5 sources on the same topic",
        "sections": [
            ("Topic", "[Research topic or question being compared]"),
            ("Sources Compared", "1. [Source A — Author, Year]\n2. [Source B — Author, Year]\n3. [Source C — Author, Year]"),
            ("Comparison Matrix", "| Dimension | Source A | Source B | Source C |\n|-----------|---------|---------|---------|"
             "\n| Central Thesis | ... | ... | ... |"
             "\n| Methodology | ... | ... | ... |"
             "\n| Key Finding | ... | ... | ... |"
             "\n| Sample/Scope | ... | ... | ... |"
             "\n| Credibility | High/Med/Low | High/Med/Low | High/Med/Low |"),
            ("Consensus Findings", "[What most sources agree on]"),
            ("Contested Points", "[Where sources disagree — with strongest evidence for each side]"),
            ("Gaps", "[What none of the sources address]"),
            ("Synthesis", "[Weight-of-evidence recommendation: what to believe and do]"),
        ],
    },
    "literature": {
        "name": "Literature Review",
        "description": "Thematic organization of multiple sources for research synthesis",
        "sections": [
            ("Research Question", "[The question this review addresses]"),
            ("Search Scope", "[Databases, keywords, date range, inclusion/exclusion criteria]"),
            ("Sources Reviewed", "[Total count, breakdown by type]"),
            ("Theme 1: [Name]", "Summary: [Theme overview]\nKey Sources: [Author (Year), Author (Year)]\nFindings: [What sources say about this theme]"),
            ("Theme 2: [Name]", "Summary: [Theme overview]\nKey Sources: [Author (Year), Author (Year)]\nFindings: [What sources say about this theme]"),
            ("Theme 3: [Name]", "Summary: [Theme overview]\nKey Sources: [Author (Year), Author (Year)]\nFindings: [What sources say about this theme]"),
            ("Gaps in Literature", "- [Under-researched area 1]\n- [Under-researched area 2]"),
            ("Synthesis", "[Overall state of knowledge — what we know, what we don't, where to go next]"),
        ],
    },
}

LENGTH_CONFIGS = {
    "brief": {"max_sections": 4, "label": "Brief (key points only)"},
    "standard": {"max_sections": 99, "label": "Standard (full template)"},
    "detailed": {"max_sections": 99, "label": "Detailed (full template with extended guidance)"},
}


def render_template(template_key, length="standard", output_format="text"):
    """Render a summary template."""
    template = TEMPLATES[template_key]
    sections = template["sections"]

    if length == "brief":
        # Keep only first 4 sections for brief output
        sections = sections[:4]

    if output_format == "json":
        result = {
            "template": template_key,
            "name": template["name"],
            "description": template["description"],
            "length": length,
            "generated": datetime.now().strftime("%Y-%m-%d"),
            "sections": [],
        }
        for title, content in sections:
            result["sections"].append({
                "heading": title,
                "placeholder": content,
            })
        return json.dumps(result, indent=2)

    # Text/Markdown output
    lines = []
    lines.append(f"# {template['name']}")
    lines.append(f"_{template['description']}_\n")
    lines.append(f"Length: {LENGTH_CONFIGS[length]['label']}")
    lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d')}\n")
    lines.append("---\n")

    for title, content in sections:
        lines.append(f"## {title}\n")
        # Indent content for readability
        for line in content.split("\n"):
            lines.append(line)
        lines.append("")

    lines.append("---")
    lines.append("_Template from research-summarizer skill_")

    return "\n".join(lines)


def list_templates(output_format="text"):
    """List all available templates."""
    if output_format == "json":
        result = []
        for key, tmpl in TEMPLATES.items():
            result.append({
                "key": key,
                "name": tmpl["name"],
                "description": tmpl["description"],
                "sections": len(tmpl["sections"]),
            })
        return json.dumps(result, indent=2)

    lines = []
    lines.append("Available Summary Templates\n")
    lines.append(f"{'KEY':<15} {'NAME':<30} {'SECTIONS':>8}  DESCRIPTION")
    lines.append(f"{'─' * 90}")
    for key, tmpl in TEMPLATES.items():
        lines.append(
            f"{key:<15} {tmpl['name']:<30} {len(tmpl['sections']):>8}  {tmpl['description'][:40]}"
        )
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="research-summarizer: Generate structured summary templates"
    )
    parser.add_argument(
        "--template", "-t",
        choices=list(TEMPLATES.keys()),
        help="Template type to generate",
    )
    parser.add_argument(
        "--length", "-l",
        choices=["brief", "standard", "detailed"],
        default="standard",
        help="Output length (default: standard)",
    )
    parser.add_argument(
        "--output", "-o",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--list-templates",
        action="store_true",
        help="List all available templates",
    )
    args = parser.parse_args()

    if args.list_templates:
        print(list_templates(args.output))
        return

    if not args.template:
        print("No template specified. Available templates:\n")
        print(list_templates(args.output))
        print("\nUsage: python scripts/format_summary.py --template academic")
        return

    print(render_template(args.template, args.length, args.output))


if __name__ == "__main__":
    main()

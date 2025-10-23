#!/usr/bin/env python3
"""
Basic Lead Research Workflow Example

Demonstrates a complete end-to-end workflow for ethical company research.
"""

import json
import subprocess
import sys
from pathlib import Path


def run_command(cmd: list[str]) -> tuple[int, str, str]:
    """Run a command and return exit code, stdout, stderr"""
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode, result.stdout, result.stderr


def example_single_company_research():
    """
    Example: Research a single company
    """
    print("=" * 60)
    print("EXAMPLE: Single Company Research Workflow")
    print("=" * 60)

    company_url = "https://www.anthropic.com"
    output_file = "anthropic_research.json"

    print(f"\nStep 1: Analyzing {company_url}...")
    print("-" * 60)

    # Run the analyzer
    cmd = [
        sys.executable,
        "scripts/analyze_company.py",
        "--url", company_url,
        "--output", output_file,
        "--verbose"
    ]

    print(f"Running: {' '.join(cmd)}\n")

    exit_code, stdout, stderr = run_command(cmd)

    if exit_code == 0:
        print("✓ Analysis complete!")
        print(f"\nOutput saved to: {output_file}")

        # Load and display results
        with open(output_file, 'r') as f:
            data = json.load(f)

        print("\nResults Summary:")
        print(f"  Company: {data.get('company_name', 'N/A')}")
        print(f"  Team members found: {len(data.get('team_members', []))}")
        print(f"  Contact emails: {len(data.get('contact_emails', []))}")
        print(f"  Technologies: {', '.join(data.get('technologies', []))}")

        print("\n" + "=" * 60)
        print("Step 2: Generate report...")
        print("-" * 60)

        # Generate markdown report
        report_file = "anthropic_report.md"
        cmd = [
            sys.executable,
            "scripts/generate_lead_report.py",
            "--input", output_file,
            "--output", report_file,
            "--format", "markdown"
        ]

        print(f"Running: {' '.join(cmd)}\n")

        exit_code, stdout, stderr = run_command(cmd)

        if exit_code == 0:
            print(f"✓ Report generated: {report_file}")
            print("\nYou can now:")
            print("  1. Review the report")
            print("  2. Verify all data is publicly listed")
            print("  3. Import to your CRM system")
            print("  4. Conduct manual LinkedIn research for team members")
        else:
            print(f"✗ Error generating report: {stderr}")

    else:
        print(f"✗ Error analyzing company: {stderr}")

    print("\n" + "=" * 60)


def example_multi_company_research():
    """
    Example: Research multiple companies
    """
    print("=" * 60)
    print("EXAMPLE: Multi-Company Research Workflow")
    print("=" * 60)

    companies = [
        "https://www.anthropic.com",
        "https://www.openai.com",
        "https://www.example.com"
    ]

    results_dir = Path("research_results")
    results_dir.mkdir(exist_ok=True)

    print(f"\nResearching {len(companies)} companies...")
    print(f"Results will be saved to: {results_dir}/\n")

    for i, url in enumerate(companies, 1):
        print(f"\n[{i}/{len(companies)}] Analyzing {url}...")

        # Generate filename from URL
        domain = url.replace("https://", "").replace("http://", "").replace("www.", "").split("/")[0]
        output_file = results_dir / f"{domain}_research.json"

        cmd = [
            sys.executable,
            "scripts/analyze_company.py",
            "--url", url,
            "--output", str(output_file)
        ]

        exit_code, stdout, stderr = run_command(cmd)

        if exit_code == 0:
            print(f"  ✓ Saved to {output_file}")
        else:
            print(f"  ✗ Error: {stderr}")

        # Respectful rate limiting
        if i < len(companies):
            print("  Waiting 5 seconds (rate limiting)...")
            import time
            time.sleep(5)

    print("\n" + "=" * 60)
    print("All companies processed!")
    print(f"Results available in: {results_dir}/")
    print("\nNext steps:")
    print("  1. Review each company's research file")
    print("  2. Generate individual reports as needed")
    print("  3. Consolidate findings in your CRM")
    print("=" * 60)


def example_compliance_checklist():
    """
    Display compliance checklist
    """
    print("=" * 60)
    print("COMPLIANCE CHECKLIST")
    print("=" * 60)
    print("""
Before conducting lead research, ensure you:

☐ LEGAL COMPLIANCE
  ☐ Consulted legal team about applicable privacy laws
  ☐ GDPR compliance plan in place (if targeting EU)
  ☐ CCPA compliance plan in place (if targeting CA)
  ☐ Privacy policy updated to cover lead research
  ☐ Data retention and deletion policies defined

☐ ETHICAL PRACTICES
  ☐ Only collecting publicly listed information
  ☐ Respecting website Terms of Service
  ☐ Implementing rate limiting and polite crawling
  ☐ Honoring robots.txt directives
  ☐ Not using automated LinkedIn scrapers

☐ DATA HANDLING
  ☐ Secure storage with encryption
  ☐ Access controls implemented
  ☐ Audit logging enabled
  ☐ Data minimization practiced
  ☐ Opt-out mechanism available

☐ OUTREACH PREPARATION
  ☐ Clear privacy notice ready
  ☐ Opt-out instructions prepared
  ☐ Consent tracking system in place
  ☐ Email templates reviewed for compliance
  ☐ CRM system configured for data rights requests

☐ LINKEDIN RESEARCH
  ☐ Using official Sales Navigator (if applicable)
  ☐ Manual research only (no automation)
  ☐ Respecting connection limits
  ☐ Not circumventing access controls

☐ ONGOING COMPLIANCE
  ☐ Quarterly compliance reviews scheduled
  ☐ Team trained on privacy requirements
  ☐ Incident response plan in place
  ☐ Regular data cleanup scheduled
    """)
    print("=" * 60)


if __name__ == '__main__':
    print("\nLead Research Assistant - Example Workflows\n")
    print("Choose an example to run:")
    print("1. Single company research")
    print("2. Multi-company research")
    print("3. Compliance checklist")
    print("\nNote: Examples demonstrate ethical, compliant research practices.")

    # Uncomment to run examples:
    # example_single_company_research()
    # example_multi_company_research()
    # example_compliance_checklist()

    print("\nTo run an example, uncomment the function call in the script.")

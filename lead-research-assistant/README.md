# Lead Research Assistant

An ethical toolkit for business intelligence gathering and B2B lead research.

## Overview

This skill helps sales and business development teams conduct **compliant, ethical lead research** using:
- Public company website analysis
- Structured research report generation
- Proper LinkedIn API integration guidance
- Privacy regulation compliance (GDPR, CCPA)

## What This Skill Does

✅ **Allowed Activities**:
- Analyze publicly accessible company websites
- Extract publicly listed team member information
- Generate structured research reports
- Guide proper use of LinkedIn Sales Navigator
- Ensure compliance with privacy laws and ToS

❌ **Prohibited Activities**:
- Automated LinkedIn scraping
- Harvesting non-public personal data
- Violating website Terms of Service
- Circumventing access controls
- GDPR/CCPA violations

## Quick Start

### 1. Install Dependencies

```bash
pip install requests beautifulsoup4
```

Optional (for PDF reports):
```bash
pip install pdfkit markdown
```

### 2. Analyze a Company

```bash
python scripts/analyze_company.py \
  --url https://example.com \
  --output company_research.json \
  --verbose
```

### 3. Generate Report

```bash
python scripts/generate_lead_report.py \
  --input company_research.json \
  --output report.md \
  --format markdown
```

## Features

### Company Website Analyzer
Extracts publicly available information including:
- Company name and description
- Business model indicators
- Publicly listed team members
- Official contact information
- Technology stack detection

### Report Generator
Creates professional reports in multiple formats:
- Markdown (default)
- HTML
- PDF (requires pdfkit)
- JSON (structured data)

### LinkedIn Integration Guidance
Provides examples for:
- Official LinkedIn API OAuth flow
- Sales Navigator proper usage
- Manual research best practices

## Usage Examples

### Single Company Research
```bash
# Analyze company
python scripts/analyze_company.py \
  --url https://acmecorp.com \
  --output acme.json

# Generate report
python scripts/generate_lead_report.py \
  --input acme.json \
  --output acme_report.pdf \
  --format pdf
```

### Batch Analysis
```bash
# Research multiple companies
cat urls.txt | while read url; do
  domain=$(echo $url | sed 's/https\?:\/\///' | sed 's/www\.//' | cut -d'/' -f1)
  python scripts/analyze_company.py --url "$url" --output "research/${domain}.json"
  sleep 5  # Rate limiting
done
```

## Compliance & Ethics

### Privacy Compliance
This skill is designed to comply with:
- **GDPR** (EU General Data Protection Regulation)
- **CCPA** (California Consumer Privacy Act)
- **LinkedIn Terms of Service**
- Website Terms of Service

### Best Practices
1. **Only collect publicly listed information**
2. **Respect robots.txt** - The analyzer checks robots.txt automatically
3. **Rate limiting** - Built-in delays between requests
4. **Data minimization** - Only collect what's necessary
5. **Secure storage** - Encrypt collected data
6. **Opt-out mechanism** - Provide clear opt-out options
7. **Audit logging** - Track all research activities

### Legal Requirements
Before using this skill:
- [ ] Consult your legal team
- [ ] Review applicable privacy laws for your jurisdiction
- [ ] Implement data retention and deletion policies
- [ ] Create privacy notices for outreach
- [ ] Set up opt-out mechanisms
- [ ] Configure secure data storage

## Project Structure

```
lead-research-assistant/
├── SKILL.md              # Main skill documentation
├── LICENSE.txt           # License and terms
├── README.md             # This file
├── scripts/
│   ├── analyze_company.py       # Website analyzer
│   └── generate_lead_report.py  # Report generator
└── examples/
    ├── basic_workflow.py        # Complete workflow examples
    └── linkedin_api_example.py  # LinkedIn API integration
```

## LinkedIn Research

### Recommended: Sales Navigator
For B2B lead generation, use **LinkedIn Sales Navigator**:
- Official LinkedIn product for sales teams
- Advanced search and filtering
- Lead lists and account mapping
- CRM integration
- Complies with LinkedIn ToS

Purchase at: https://business.linkedin.com/sales-solutions/sales-navigator

### Using LinkedIn API
For custom integrations:
1. Register app at https://www.linkedin.com/developers/apps
2. Implement OAuth 2.0 authentication
3. Use official API endpoints
4. Respect rate limits

See `examples/linkedin_api_example.py` for implementation.

### Manual Research
For small-scale research:
1. Use LinkedIn's standard search
2. View public profiles only
3. Take manual notes
4. Respect connection limits
5. Don't use automation

## Security & Data Handling

### Storage Best Practices
- Store research data in encrypted databases
- Implement access controls
- Regular security audits
- Automatic data expiration

### Data Retention
- Define clear retention periods (e.g., 12 months)
- Automated deletion of stale data
- Document retention policies
- Honor deletion requests

### Audit Logging
Log all research activities:
- URLs analyzed
- Data extracted
- Reports generated
- User actions
- Timestamps

## Integration with CRM Systems

Export data to popular CRM platforms:
- **Salesforce**: CSV import or API integration
- **HubSpot**: CSV import or native integration
- **Pipedrive**: Bulk import feature
- **Custom CRM**: JSON/CSV export available

## Troubleshooting

### Common Issues

**Q: Script can't access website**
- Check if site blocks bots via robots.txt
- Verify site is publicly accessible
- Some sites may require authentication

**Q: No team members found**
- Website may not have public team pages
- Team info might be in non-standard format
- Try searching for "About Us" or "Team" pages manually

**Q: LinkedIn API returns 403**
- Verify OAuth token is valid
- Check API permissions/scopes
- Ensure you're within rate limits

**Q: PDF generation fails**
- Install pdfkit: `pip install pdfkit`
- Install wkhtmltopdf: https://wkhtmltopdf.org/downloads.html
- Use HTML or Markdown format as alternative

## Contributing

This skill is proprietary. See LICENSE.txt for terms.

## Support

For questions about:
- **Legal compliance**: Consult your legal counsel
- **LinkedIn API**: https://docs.microsoft.com/linkedin/
- **GDPR**: https://gdpr.eu/
- **CCPA**: https://oag.ca.gov/privacy/ccpa

## Version History

- **1.0** (2025-10-20) - Initial release
  - Company website analyzer
  - Report generator
  - LinkedIn API examples
  - Compliance documentation

## License

See LICENSE.txt for complete terms and conditions.

## Disclaimer

This tool is provided for ethical business intelligence purposes only. Users are responsible for ensuring compliance with all applicable laws and regulations. Consult legal counsel before conducting lead research activities.

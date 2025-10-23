---
name: lead-research-assistant
description: Ethical lead generation and business intelligence toolkit. Analyzes company websites for business models, identifies publicly listed decision makers, and provides structured research reports. Guides proper use of official APIs and manual research workflows for LinkedIn prospecting while avoiding automated scraping.
license: Proprietary. LICENSE.txt has complete terms
---

# Lead Research Assistant

An ethical toolkit for business intelligence gathering and lead research that respects privacy laws, terms of service, and professional standards.

## Overview

This skill helps with:
1. **Company Website Analysis** - Extract business model information from public websites
2. **Decision Maker Identification** - Find publicly listed contacts on About Us, Team, Contact pages
3. **Research Report Generation** - Create structured summaries for sales/BD teams
4. **Ethical LinkedIn Research** - Guide proper use of LinkedIn tools and APIs
5. **Compliance Guidance** - Ensure GDPR, CCPA, and ToS compliance

## Core Principles

**✅ ALLOWED**:
- Analyzing publicly accessible website content
- Reading publicly listed contact information (About Us, Team pages, Press pages)
- Using official LinkedIn Sales Navigator or Recruiter with proper licenses
- Manual research and note-taking
- Building reports from publicly available data

**❌ PROHIBITED**:
- Automated LinkedIn scraping or bot activity
- Circumventing rate limits or access controls
- Harvesting non-public email addresses
- Violating website Terms of Service
- GDPR/CCPA non-compliant data collection

## Workflow: Company Research

### Phase 1: Website Analysis

Use the provided `analyze_company.py` script to extract public information:

```bash
python scripts/analyze_company.py --url https://example.com --output report.json
```

The script will:
- Analyze the business model from homepage, about, and product pages
- Extract publicly listed team members from About Us/Team pages
- Identify contact information from Contact Us pages
- Generate structured JSON output for review

### Phase 2: Manual Review & Enrichment

Review the generated report and:
1. Verify accuracy of extracted information
2. Validate that all data is publicly listed
3. Remove any information that shouldn't be retained
4. Add manual research notes

### Phase 3: LinkedIn Research (Ethical Approaches)

**Option A: Official LinkedIn Sales Navigator**
- Use Sales Navigator with proper corporate license
- Leverage official search and lead builder features
- Export data through official export functionality
- Stay within your license limits

**Option B: Manual LinkedIn Research**
- Search for individuals using LinkedIn's standard search
- View public profiles (respect LinkedIn's Terms of Service)
- Use "Save to List" feature for organization
- Take manual notes in your CRM

**Option C: LinkedIn API Integration**
- Use official LinkedIn Marketing Developer Platform
- Implement proper OAuth 2.0 authentication
- Respect rate limits and API guidelines
- See `examples/linkedin_api_example.py` for proper implementation

### Phase 4: Report Generation

Generate a structured report:

```bash
python scripts/generate_lead_report.py --input research.json --output lead_report.pdf
```

## Decision Tree: Choosing Your Research Approach

```
Research task → Is target data on public website?
    ├─ Yes → Use analyze_company.py script
    │         └─ Generate report → Manual review → Done
    │
    └─ No (need LinkedIn data) → Do you have Sales Navigator license?
        ├─ Yes → Use Sales Navigator official features
        │         └─ Export through official tools → Done
        │
        └─ No → Do you need API integration?
            ├─ Yes → Apply for LinkedIn API access
            │         └─ Implement OAuth flow (see examples/)
            │
            └─ No → Manual research workflow
                    └─ LinkedIn search → Manual notes → CRM entry
```

## Privacy & Compliance

### GDPR Compliance Checklist
- [ ] Only collect data for legitimate business interest
- [ ] Provide clear privacy notice if contacting individuals
- [ ] Implement data retention and deletion policies
- [ ] Respect right to be forgotten requests
- [ ] Document lawful basis for processing

### CCPA Compliance Checklist
- [ ] Provide opt-out mechanism for California residents
- [ ] Don't sell personal information without consent
- [ ] Respond to consumer rights requests within 45 days

### LinkedIn Terms of Service
- [ ] Never use automated scrapers or bots
- [ ] Don't circumvent technical limitations
- [ ] Respect robots.txt and rate limits
- [ ] Use official APIs where available
- [ ] Don't violate user privacy settings

## Data Handling Best Practices

### Storage
- Store collected data securely (encrypted databases)
- Implement access controls
- Regular security audits
- Data minimization - only keep what's needed

### Retention
- Define clear retention periods (e.g., 12 months for leads)
- Automated deletion of stale data
- Document retention policies

### Usage
- Only use for stated business purposes
- Don't share data with unauthorized parties
- Respect opt-out requests immediately
- Provide transparency to prospects

## Available Scripts

### Company Website Analyzer
**File**: `scripts/analyze_company.py`

Analyzes company websites for publicly available business intelligence.

**Usage**:
```bash
python scripts/analyze_company.py --url https://example.com --output report.json [--verbose]
```

**Features**:
- Business model detection from website content
- Team member extraction from About/Team pages
- Contact information gathering (publicly listed only)
- Industry classification
- Company size estimation
- Technology stack detection

**Output**: Structured JSON with company profile

### Lead Report Generator
**File**: `scripts/generate_lead_report.py`

Creates formatted reports from research data.

**Usage**:
```bash
python scripts/generate_lead_report.py --input data.json --output report.pdf --format [pdf|html|markdown]
```

**Output**: Professional report for sales/BD teams

## Example Workflows

### Example 1: Basic Company Research

```bash
# Step 1: Analyze company website
python scripts/analyze_company.py --url https://acmecorp.com --output acme_research.json

# Step 2: Review and validate the data
cat acme_research.json | jq '.'

# Step 3: Generate report
python scripts/generate_lead_report.py --input acme_research.json --output acme_report.pdf
```

### Example 2: Multi-Company Research

```bash
# Batch analyze multiple companies
cat company_urls.txt | while read url; do
  python scripts/analyze_company.py --url "$url" --output "research/$(echo $url | md5).json"
  sleep 5  # Respectful rate limiting
done
```

### Example 3: LinkedIn API Integration

See `examples/linkedin_api_example.py` for proper OAuth implementation.

```python
from linkedin_api import LinkedInAPI

# Proper authentication
api = LinkedInAPI(
    client_id='your_client_id',
    client_secret='your_client_secret',
    redirect_uri='your_redirect_uri'
)

# Use official endpoints only
profile = api.get_profile(person_id='abc123')
```

## Common Pitfalls to Avoid

### ❌ Don't Do This
```python
# Automated LinkedIn scraping
import selenium
driver.get('https://linkedin.com/...')  # Violates ToS
```

### ✅ Do This Instead
```python
# Use official API
from linkedin_api import LinkedInAPI
api.search_people(keywords='CTO', company='Acme Corp')
```

### ❌ Don't Do This
```python
# Harvesting emails from page source
emails = re.findall(r'[\w\.-]+@[\w\.-]+', html)
```

### ✅ Do This Instead
```python
# Extract only publicly listed contact info from Contact Us pages
contact_page = fetch_page(company_url + '/contact')
official_emails = extract_from_contact_form(contact_page)
```

## Integration with CRM Systems

The generated reports can be imported into common CRM platforms:

- **Salesforce**: Use Data Import Wizard with CSV export
- **HubSpot**: Import contacts via CSV or API
- **Pipedrive**: Use bulk import feature
- **Custom CRM**: See `examples/crm_integration.py`

## Monitoring & Compliance

### Audit Logging
All research activities should be logged:
```python
logger.info(f"Analyzed {company_url} at {timestamp}")
logger.info(f"Extracted {num_contacts} publicly listed contacts")
logger.info(f"Generated report for user {user_id}")
```

### Regular Reviews
- Quarterly privacy compliance audits
- Review data retention policies
- Update consent mechanisms
- Train team on ethical practices

## Additional Resources

- **Examples Directory**: Sample scripts for common scenarios
- **Templates**: Email templates, privacy notices, opt-out forms
- **Documentation**: Detailed API integration guides

## Support & Questions

For questions about:
- **Legal compliance**: Consult your legal team
- **LinkedIn API**: https://docs.microsoft.com/linkedin/
- **GDPR**: https://gdpr.eu/
- **CCPA**: https://oag.ca.gov/privacy/ccpa

## Version History

- 1.0 (2025-10-20) Initial release

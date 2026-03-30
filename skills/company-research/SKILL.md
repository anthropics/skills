---
name: company-research
description: >-
  FBI/SEC/recruiter-grade intelligence briefs on companies
  for job applications. Hybrid skill: Python collects
  structured data (SEC, FDA, trials, FAERS, publications),
  Claude Code layers MCP tools (Indeed ratings, jobs),
  WebSearch (leadership, org charts, financials, legal),
  and analytical reasoning (JD forensics, interview prep).
  Accepts company name + optional job description.
  Outputs company brief + JD forensic analysis.
---

# Company Research v2

Generate forensic-grade intelligence on a company for job applications.
Know more about the company and the role than the company does.

## When to Use

- "Research [company] for my interview"
- "Company brief on [company]"
- "Research [company] -- here's the JD: [paste]"
- "What should I know about [company] before applying?"
- Biotech/pharma competitive intelligence
- Job application preparation

## Inputs

```text
company_name (required): "Myriad Genetics"
job_description (optional): full JD text pasted by user
output_dir (optional): default ~/Downloads/
```

## Architecture: Hybrid Python + Claude Code

**Stage A (Python)**: Structured data collection via ToolUniverse SDK.
Outputs `company_data_{name}_{timestamp}.json` with SEC filings,
clinical trials, FDA data, FAERS adverse events, publications,
Wikipedia, OpenAlex, Crossref.

**Stage B (Claude Code)**: MCP tools + WebSearch + analytical reasoning.
Reads Python JSON, layers Indeed employee sentiment, ClinicalTrials MCP
deep analysis, WebSearch for leadership/org/financials/legal/competitive,
JD forensics, and interview prep. Writes final markdown reports.

## Execution Workflow

### Step 1: Run Python Collector (background)

```bash
cd ~/code/ToolUniverse && source .venv/bin/activate && \
python3 skills/company-research/python_implementation.py \
  "COMPANY_NAME" --output-dir OUTPUT_DIR
```

Run this in the background. While it runs, start Step 2.

### Step 2: MCP Intelligence (parallel with Step 1)

Call these MCP tools in parallel:

**Indeed Company Data** (ToolSearch → mcp__claude_ai_Indeed__get_company_data):

```yaml
companyName: "COMPANY_NAME"
language: "en"
location: {country: "US", usState: null, usStateCode: null, usCity: null}
knowledgeCategories: {metadata: true, ratings: true, salaries: true}
jobTitle: "JOB_TITLE_FROM_JD" (if JD provided)
```

**Indeed Job Search** (ToolSearch → mcp__claude_ai_Indeed__search_jobs):

```yaml
search: "COMPANY_NAME"
location: "LOCATION_FROM_JD or remote"
country_code: "US"
```

**ClinicalTrials MCP** (if biotech/pharma):

- mcp__clinical-trials__search_by_sponsor: sponsor="COMPANY_NAME"
- mcp__clinical-trials__analyze_endpoints: condition from pipeline

**CMS Coverage** (if diagnostics/devices):

- mcp__cms-coverage__search_national_coverage: keyword from product name

### Step 3: WebSearch Intelligence (serial, query-dependent)

Run these WebSearch queries. WebFetch key URLs found.

1. `"{COMPANY} leadership team executive bios {YEAR}"`
2. `"{COMPANY} TheOrg org chart"`
3. `"{COMPANY} {TICKER} revenue earnings segments {YEAR}"`
4. `"{COMPANY} securities litigation investigation {YEAR}"`
5. `"{COMPANY} vs {COMPETITOR} market share"`
6. `"{COMPANY} analyst rating target price {YEAR}"`
7. `"{COMPANY} acquisitions partnerships {YEAR}"`
8. `"{COMPANY} layoffs restructuring {YEAR}"`

For each result with a useful URL, use WebFetch to extract details.

### Step 4: Read Python JSON

Read the `company_data_*.json` file produced by Step 1.
Parse it to merge with MCP and WebSearch findings.

### Step 5: JD Forensics (if JD provided)

Apply analytical reasoning to the JD text, cross-referencing
ALL data collected in Steps 1-4:

#### 5A: Structural Analysis

- Check for duplicated sections (copy-paste artifacts)
- Count emphasis patterns (which words/phrases repeat?)
- Note missing sections (what's NOT in the JD?)
- Compare title vs. experience requirements (title inflation?)

#### 5B: Decode What They Really Mean

Create a table: "What the JD says" → "What it actually means"
Map JD phrases to company pain points from financial/pipeline data.

#### 5C: Team Structure

- WebSearch for the hiring manager / likely reporting line
- Search TheOrg for the team this role sits in
- Identify existing team members and their backgrounds
- Determine: is this a backfill or expansion? If backfill, who left and why?

#### 5D: Compensation Intelligence

- Indeed salary data from Step 2
- Check if the posting includes a salary range (many states require it)
- Estimate total comp: base + bonus target (typically 20-30% at director) + equity
- Note if Indeed range is algorithmic estimate vs. posted range

#### 5E: ATS Keyword Extraction

- Extract all hard skills, certifications, and domain terms from JD
- Flag required vs. preferred qualifications
- Note any unusual requirements that signal specific problems

### Step 6: Interview Preparation (if JD provided)

**90-Day Framework**: Map discovered pain points to a concrete plan:

- Days 1-30: Listen, inventory assets, build relationships
- Days 30-60: Analyze, benchmark, model
- Days 60-90: Recommend, align, deliver first wins

**Questions That Signal Deep Knowledge**: Reference SPECIFIC findings
from research (not generic questions). Examples:

- Reference a specific data asset, partnership, or product launch
- Ask about a recent leadership change or strategic pivot
- Probe a competitive threat with specific competitor data

**Key Numbers to Know**: Extract the 8-10 most important metrics
(revenue, growth rate, test volumes, market cap, etc.)

### Step 7: Write Final Reports

**Output 1: Company Intelligence Brief** (always produced)

Write to `{output_dir}/company_brief_{company}_{date}.md`:

```markdown
# Intelligence Brief: {Company}
Generated: {date} | Ticker | CIK | Sector | Employees | Revenue | Market Cap

## Executive Summary
(3-5 sentences: what this company is, key developments, strategic posture)

## 1. Financial Intelligence [T1]
### Revenue & Segments
### Balance Sheet & Debt
### Guidance & Analyst Sentiment

## 2. Pipeline & Products
### Clinical Trials [T1]
### FDA Approved Products [T1]
### FDA Approvals History [T1]
### Device Clearances (510k) [T1]

## 3. Science & Innovation [T2]
### Key Publications
### Preprints
### Research Output Trends
### Key Data Assets & AI Strategy

## 4. Regulatory & Safety [T1]
### FAERS Adverse Events
### Enforcement Actions
### Medicare Coverage (if applicable)

## 5. Leadership & Organization [T3]
### C-Suite & Key Executives
### Org Chart (key teams)
### Recent Departures & Arrivals
### Leadership Trajectory

## 6. Employee Sentiment [T3]
### Indeed Ratings & CEO Approval
### Salary Satisfaction
### Interview Process
### Culture Signals

## 7. Competitive Landscape
### Direct Competitors (by segment)
### Revenue & Market Cap Benchmarking
### Strategic Positioning (SWOT)

## 8. Hiring Signals
### Open Positions (Indeed)
### Role Clusters & Hiring Velocity
### What the Hiring Patterns Signal

## 9. Legal & Securities
### Active Investigations
### Prior Settlements
### Securities Class Actions

## 10. Data Gaps
(What we couldn't find and why)

## Sources
| Tool | Query | Items | Tier |
```

**Output 2: JD Forensic Analysis** (only if JD provided)

Write to `{output_dir}/jd_analysis_{company}_{date}.md`:

```markdown
# JD Forensic Analysis: {Role Title} at {Company}
Generated: {date}

## 1. JD Deconstruction
### What They Wrote vs. What They Mean
(table mapping JD phrases to decoded requirements)
### Structural Anomalies
### The Real Role (decoded)

## 2. Role Architecture
### Reporting Structure
### Team Context & Composition
### Predecessor Analysis (backfill vs. expansion)

## 3. Pain Point Mapping
### Company Problems This Role Solves
### Urgency Signals
### The Hidden Job Description

## 4. Compensation Intelligence
### Posted/Estimated Range
### Market Benchmarking
### Total Comp Estimate (base + bonus + equity)
### Negotiation Leverage Points

## 5. Competitive Candidate Profile
### Ideal Archetype
### Differentiators That Win
### Red Flags / Disqualifiers

## 6. Interview Preparation
### 90-Day Framework
### Questions That Signal Deep Knowledge
### Key Numbers to Know
### Anticipated Questions & STAR Triggers

## 7. ATS Intelligence
### Keywords to Include in Resume/Cover Letter
### Application Channel Recommendations
```

## Evidence Grading

| Tier | Sources | Reliability |
| ---- | ------- | ----------- |
| T1 | SEC, FDA, ClinicalTrials.gov, FAERS, CMS | Regulatory/official |
| T2 | Peer-reviewed (PubMed, OpenAlex, Crossref) | Validated |
| T3 | Indeed, news, web, Wikipedia, TheOrg | Unvalidated/realtime |

## Tools Used

### Python (ToolUniverse SDK) — 16 tools

| Tool | Data | Tier |
| ---- | ---- | ---- |
| Wikipedia_search | Company name resolution | T3 |
| Wikipedia_get_content | Company profile | T3 |
| SEC_EDGAR_search_filings | Recent filings, CIK/ticker | T1 |
| SEC_EDGAR_get_company_submissions | Full filing history | T1 |
| Wikidata_search_entities | Sector, structured facts | T3 |
| ClinicalTrials_search_studies | Active trials | T1 |
| EuropePMC_search_articles | Preprints (SRC:PPR) | T3 |
| PubMed_search_articles | Publications | T2 |
| FDA_OrangeBook_search_drug | Approved products | T1 |
| OpenFDA_search_drug_approvals | Approval history | T1 |
| OpenFDA_search_device_510k | Device clearances | T1 |
| OpenFDA_search_drug_enforcement | Recalls/enforcement | T1 |
| OpenFDA_search_drug_labels | Drug labeling | T1 |
| FAERS_count_reactions_by_drug_event | Adverse event counts | T1 |
| openalex_literature_search | Research output | T2 |
| Crossref_search_works | DOI metadata/citations | T2 |

### Claude Code (MCP + WebSearch) — 6+ tools

| Tool | Data | Tier |
| ---- | ---- | ---- |
| Indeed get_company_data | Ratings, CEO approval, salary | T3 |
| Indeed search_jobs | Open positions, hiring signals | T3 |
| ClinicalTrials MCP search_by_sponsor | Sponsor-specific trials | T1 |
| ClinicalTrials MCP analyze_endpoints | Endpoint comparison | T1 |
| CMS Coverage search_national_coverage | Medicare coverage | T1 |
| WebSearch + WebFetch | Leadership, financials, legal, competitive | T3 |

## Fallback Chains

| Data | Primary | Fallback | Default |
| ---- | ------- | -------- | ------- |
| Identity | Wikipedia + SEC | Wikidata + web | Input name |
| News | WebSearch (Claude) | -- | No news found |
| SEC filings | SEC_EDGAR | -- | Skip (private) |
| Trials | ClinicalTrials SDK + MCP | -- | None found |
| Publications | PubMed | EuropePMC, OpenAlex | None found |
| FDA products | OpenFDA approvals | Orange Book | None found |
| Safety | FAERS | -- | None found |
| Devices | OpenFDA 510(k) | -- | None found |
| Employee data | Indeed MCP | -- | No data |
| Leadership | WebSearch (TheOrg) | WebSearch (LinkedIn) | Not found |
| Financials | WebSearch (earnings) | SEC filings | Limited |
| Competitive | WebSearch | -- | Not found |
| Legal | WebSearch | -- | No issues found |

## Limitations

- SEC EDGAR full-text search returns filings mentioning the company,
  not just filings BY the company. Filter on CIK when possible.
- FDA Orange Book searches by drug brand name, not company.
  OpenFDA_search_drug_approvals by sponsor_name is better.
- Indeed data reflects employee self-reporting bias.
- TheOrg data may be stale (not real-time).
- JD forensics is analytical inference, not fact — flag as opinion.
- Private companies have limited financial data available.

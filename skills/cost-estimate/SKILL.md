---
name: cost-estimate
description: "Scans any codebase (GitHub URL or local path) and estimates what it would cost a real team to build. Cross-references 2025-2026 market rates for US and Polish developers. Shows value per Claude hour, speed multiplier, and ROI. Use when user says 'cost-estimate', 'how much would this cost', 'estimate build cost', 'what is this worth'."
user_invocable: true
---

# Cost Estimate Skill -- Codebase Value Calculator

## What this does
Scans any codebase (GitHub repo URL or local directory), analyzes its complexity, and calculates what it would have cost a real development team to build it. Cross-references 2025-2026 market rates for both US and Polish developers. Shows the absurd ROI of AI-assisted development.

Accepts GitHub URLs (e.g. `github.com/vercel/next.js`), full HTTPS URLs, or local paths. When given a GitHub URL, it shallow-clones the repo, scans it, and cleans up automatically. Also pulls repo metadata from the GitHub API to enrich the estimate.

## Arguments
Pass a GitHub repo URL or local directory after `/cost-estimate`. If none given, use the current working directory.
Examples:
- `/cost-estimate github.com/vercel/next.js`
- `/cost-estimate https://github.com/shadcn-ui/ui`
- `/cost-estimate ~/projects/yesno`
- `/cost-estimate` (scans current directory)

## Steps (follow exactly)

### 0. Parse input and resolve source

Determine if the argument is a GitHub URL or a local path:

```bash
# Patterns that indicate a GitHub repo:
# - github.com/owner/repo
# - https://github.com/owner/repo
# - owner/repo (if it looks like a GitHub slug: no slashes beyond one, no dots)

# If GitHub URL detected:
# 1. Extract owner/repo from the URL (strip .git suffix, trailing slashes, tree/branch paths)
# 2. Clone to temp directory for scanning
SCAN_DIR=$(mktemp -d /tmp/cost-estimate-XXXXXX)
gh repo clone {owner}/{repo} "$SCAN_DIR" -- --depth 1 --single-branch 2>/dev/null

# 3. Pull GitHub API metadata for enrichment
gh api "repos/{owner}/{repo}" --jq '{name, full_name, description, stargazers_count, forks_count, open_issues_count, created_at, updated_at, pushed_at, language, size, topics, license: .license.spdx_id}'
gh api "repos/{owner}/{repo}/languages"
gh api "repos/{owner}/{repo}/contributors?per_page=5" --jq '[.[].login]'
gh api "repos/{owner}/{repo}/commits?per_page=1" --jq '.[0] | {sha: .sha[0:7], date: .commit.committer.date, message: .commit.message}'

# If local path or no argument:
# SCAN_DIR = provided path or current working directory
# Skip GitHub API enrichment
```

When the scan is complete (after step 6), clean up the temp directory:
```bash
# Only if we cloned a repo
rm -rf "$SCAN_DIR"
```

**Important:** For the rest of the steps, use `$SCAN_DIR` as `[DIR]`. All scan commands target this directory whether it's a clone or a local path.

If GitHub API data is available, include it in the report header:
- Stars, forks, contributors, age (created_at to now)
- GitHub's own language breakdown (compare with local scan)
- Latest commit date (to assess project activity)

### 1. Scan the codebase

Run these commands to gather metrics (all in parallel where possible):

```bash
# Total lines of code by language (exclude node_modules, .next, dist, build, .git, vendor, __pycache__)
find [DIR] -type f \( -name "*.ts" -o -name "*.tsx" -o -name "*.js" -o -name "*.jsx" -o -name "*.py" -o -name "*.sol" -o -name "*.css" -o -name "*.scss" -o -name "*.html" -o -name "*.json" -o -name "*.md" -o -name "*.yaml" -o -name "*.yml" -o -name "*.toml" -o -name "*.rs" -o -name "*.go" -o -name "*.swift" \) ! -path "*/node_modules/*" ! -path "*/.next/*" ! -path "*/dist/*" ! -path "*/build/*" ! -path "*/.git/*" ! -path "*/vendor/*" ! -path "*/__pycache__/*" ! -path "*/package-lock.json" ! -path "*/yarn.lock" ! -path "*/bun.lockb" -exec wc -l {} + 2>/dev/null | tail -20

# Count files by extension
find [DIR] -type f \( -name "*.ts" -o -name "*.tsx" -o -name "*.js" -o -name "*.jsx" -o -name "*.py" -o -name "*.sol" -o -name "*.css" -o -name "*.html" \) ! -path "*/node_modules/*" ! -path "*/.next/*" ! -path "*/dist/*" ! -path "*/.git/*" | sed 's/.*\.//' | sort | uniq -c | sort -rn

# Detect package.json dependencies count
cat [DIR]/package.json 2>/dev/null | grep -c '"' || echo "0"

# Detect API integrations (grep for common patterns)
grep -rn "fetch\|axios\|curl\|api\.\|/api/\|endpoint\|webhook\|supabase\|redis\|postgres\|mongo\|firebase\|stripe\|twilio\|sendgrid\|openai\|anthropic\|openrouter" [DIR] --include="*.ts" --include="*.tsx" --include="*.js" --include="*.jsx" --include="*.py" -l 2>/dev/null | head -30

# Detect smart contracts
find [DIR] -name "*.sol" ! -path "*/node_modules/*" 2>/dev/null | head -10

# Check for config/infra files
ls [DIR]/vercel.json [DIR]/railway.json [DIR]/docker-compose.yml [DIR]/Dockerfile [DIR]/.github/workflows/*.yml [DIR]/wrangler.toml 2>/dev/null
```

Also read `package.json` (or `requirements.txt`, `Cargo.toml`, `go.mod`) to identify the tech stack and dependency count.

### 2. Identify complexity factors

Score each factor 1-5 (1=simple, 5=very complex):

| Factor | What to look for |
|--------|-----------------|
| **Frontend complexity** | Components count, state management, animations, responsive design |
| **Backend complexity** | API routes, middleware, auth, database schemas, cron jobs |
| **Integrations** | Third-party APIs, payment processing, blockchain, AI/LLM calls |
| **Infrastructure** | CI/CD, deployment configs, multi-environment, caching layers |
| **Domain expertise** | Specialized knowledge needed (trading, crypto, ML, compliance, gov APIs) |
| **Real-time features** | WebSockets, SSE, polling, live data feeds |
| **Security** | Auth flows, encryption, API keys management, OWASP considerations |

### 3. Estimate human hours

Use this formula based on LOC and complexity:

**Base hours = LOC / productivity_rate**

Productivity rates (lines of tested, production-quality code per hour):
- Simple CRUD / static pages: 40-60 LOC/hr
- Standard web app: 20-35 LOC/hr
- Complex integrations / trading systems: 10-20 LOC/hr
- Smart contracts / security-critical: 5-15 LOC/hr

**Multiply base hours by complexity factor (average of all scores / 3)**

Add overhead:
- Project setup, architecture planning: +15%
- Code review, QA, testing: +20%
- DevOps, deployment, monitoring: +10%
- Meetings, communication, documentation: +15%
- Bug fixes, iterations: +15%

**Total overhead multiplier: 1.75x**

### 4. Calculate costs across scenarios

Use these verified 2025-2026 market rates:

#### US Market Rates (hourly, fully loaded)
| Role | Junior | Mid | Senior | Lead/Architect |
|------|--------|-----|--------|----------------|
| Fullstack | $55 | $85 | $125 | $165 |
| Frontend | $50 | $80 | $120 | $155 |
| Backend | $55 | $85 | $130 | $170 |
| DevOps | $60 | $90 | $135 | $175 |
| Smart Contract | $70 | $110 | $160 | $200 |
| Designer | $45 | $70 | $100 | $130 |

#### Polish Market Rates (hourly, B2B client-facing)
| Role | Junior | Mid | Senior | Lead/Architect |
|------|--------|-----|--------|----------------|
| Fullstack | $25 | $42 | $70 | $90 |
| Frontend | $22 | $38 | $65 | $85 |
| Backend | $25 | $42 | $65 | $88 |
| DevOps | $28 | $45 | $70 | $95 |
| Smart Contract | $30 | $55 | $85 | $110 |
| Designer | $20 | $35 | $55 | $70 |

#### Polish Internal Costs (monthly B2B net, what dev actually invoices)
| Role | Junior | Mid | Senior | Lead |
|------|--------|-----|--------|------|
| Frontend | ~7,950 PLN | ~17,640 PLN | ~23,520 PLN | ~27,000 PLN |
| Backend | ~10,125 PLN | ~20,180 PLN | ~25,350 PLN | ~27,000 PLN |
| Fullstack | ~6,600 PLN | ~17,000 PLN | ~24,300 PLN | ~27,000 PLN |
| DevOps | ~10,790 PLN | ~22,000 PLN | ~26,650 PLN | ~28,500 PLN |

#### Polish Employment Contract (UoP gross/month -- employer pays ~40% more on top)
| Role | Junior | Mid | Senior |
|------|--------|-----|--------|
| Frontend | ~9,500 PLN | ~15,500 PLN | ~21,950 PLN |
| Backend | ~8,625 PLN | ~16,550 PLN | ~23,370 PLN |
| Fullstack | ~8,200 PLN | ~13,700 PLN | ~19,900 PLN |

*Sources: Bulldogjob IT Community Report 2025 (4,800 respondents), JustJoinIT 2026 (111K+ postings), NoFluffJobs*
*1 USD ~ 4.0 PLN (March 2026)*

#### US vs Poland Direct Comparison (annual total cost per dev)
| Seniority | Poland (B2B) | US (FTE all-in) | US costs X more |
|-----------|-------------|-----------------|-----------------|
| Junior | $30,000 | $95,000 | 3.2x |
| Mid | $51,000 | $143,000 | 2.8x |
| Senior | $75,000 | $210,000 | 2.8x |
| Lead | $81,000 | $250,000 | 3.1x |

#### Scenarios
Calculate for 4 team compositions:

**Solo Dev (US freelancer)**
- 1 senior fullstack @ $125/hr
- Calendar time = human hours / 6 hrs/day productive / 22 days/month

**Lean Startup (US)**
- 1 senior fullstack + 0.5 mid frontend + 0.25 DevOps
- Blended rate ~$110/hr

**Growth Company (US)**
- 1 lead + 1 senior backend + 1 mid frontend + 0.5 mid DevOps + 0.25 designer + PM overhead (20%)
- Blended rate ~$125/hr

**Enterprise (US)**
- Full team: 2 seniors + 2 mids + 1 lead + QA + DevOps + PM + designer
- Blended rate ~$130/hr + 30% overhead for process/compliance

**Polish Software House**
- Same team as Growth Company but at Polish rates
- Blended rate ~$55/hr
- Note: this is what a US/EU client pays. Polish company margin is ~30-40% on top of developer cost.

**Polish Internal Team (hired directly)**
- Same composition, UoP or B2B contracts
- Calculate monthly burn rate in PLN
- Note: employer costs on UoP add ~40% on top of gross salary (ZUS, taxes)

### 5. Calculate AI comparison

**Claude hours** = ask user or estimate from git log:
```bash
# Check git log for development timespan
git -C [DIR] log --oneline --format="%ai" | tail -1  # first commit
git -C [DIR] log --oneline --format="%ai" | head -1  # last commit
git -C [DIR] log --oneline | wc -l  # total commits
```

If Claude hours unknown, estimate: total_commits * 0.25 hours (avg 15 min per productive commit session).

**Claude cost** = hours * ($20/hr for Pro plan, or $100/20hr for Max plan usage)
Use Pro subscription prorated: ~$6.67/day, estimate active days from git log.

**Metrics to calculate:**
- Speed multiplier: human_hours / claude_hours
- Cost savings: human_cost - claude_cost
- ROI: human_cost / claude_cost
- Value per Claude hour: human_cost_solo / claude_hours

### 6. Present the report

Format as a clean terminal-style report:

```
PROJECT COST ESTIMATE -- {project name}
Scanned: {date} | {total_files} files | {total_loc} LOC | {languages}
{if GitHub: Source: github.com/{owner}/{repo} | Stars: {n} | Forks: {n} | Contributors: {n}}
{if GitHub: Created: {date} | Last push: {date} | Age: {n months/years}}

--- CODEBASE ANALYSIS ---

{if GitHub repo metadata available:}
GitHub Stats:     {stars} stars, {forks} forks, {contributors} contributors
GitHub Languages: {language breakdown from API with percentages}
Repository Size:  {size} KB | License: {license}
{end if}

Languages:        {breakdown from local scan}
Dependencies:     {count} packages
API Integrations: {list of detected services}
Infrastructure:   {Vercel/Railway/Supabase/etc}
Complexity Score: {avg}/5

--- ESTIMATED HUMAN EFFORT ---

Base hours:    {hours} (at {rate} LOC/hr avg)
With overhead: {hours * 1.75} hours (planning, review, QA, devops, iteration)

--- COST BREAKDOWN ---

| Scenario              | Calendar Time | Human Hours | Total Cost (USD) |
|-----------------------|---------------|-------------|------------------|
| Solo Dev (US)         | ~{months} mo  | {hours}     | ${cost}          |
| Lean Startup (US)     | ~{months} mo  | {hours}     | ${cost}          |
| Growth Company (US)   | ~{months} mo  | {hours}     | ${cost}          |
| Enterprise (US)       | ~{years} yr   | {hours}     | ${cost}          |
| Polish Software House | ~{months} mo  | {hours}     | ${cost}          |
| Polish Internal Team  | ~{months} mo  | {hours}     | ${cost} ({PLN})  |

--- POLISH MARKET CONTEXT (2026) ---

If built by a Polish software house for a US/EU client:
- Blended rate: ~$55/hr (vs US $125/hr -- 2.3x cheaper)
- Same quality tier as Western Europe, EU timezone overlap
- Monthly team burn: ~{PLN}/mo for {team_size} devs
- Poland: 400,000+ developers, 1,050+ software houses (Clutch)
- #1 IT outsourcing destination in CEE

What Polish devs actually earn (B2B net/month):
- Senior: 25,000 PLN (~$6,250)    | US equivalent: $17,500/mo
- Mid:    17,000 PLN (~$4,250)    | US equivalent: $11,900/mo
- Junior: 10,000 PLN (~$2,500)    | US equivalent: $7,900/mo
- US costs 2.8-3.2x more for equivalent seniority

Highest-paid Polish specializations (B2B net/mo):
- Architecture: 25,200-32,500 PLN    - DevOps: 21,000-28,100 PLN
- Security: 20,600-26,900 PLN        - Data/BI: 21,000-26,900 PLN

Market trends (2025-2026):
- 44% increase in IT job postings YoY (No Fluff Jobs)
- 70.1% of IT workers got raises in past 12 months
- AI/ML specialists: +15% salary growth on B2B
- Go language salaries: +35.7% YoY
- Average annual salary growth: 5-7% (stabilizing)
- B2B dominant in IT. B2B net runs 50-100% above UoP net.

Polish reality check:
- A solo Polish senior dev (B2B) costs ~25K PLN/mo ($6,300)
- For {human_hours} hours of work, that's ~{months} months = ~{cost_pln} PLN
- Same work in US: {cost_usd_solo} -- Poland saves ~{savings_pct}%
- Typical Polish software house quote for this project: ${house_quote}
  (they'd pad timeline 2-3x for safety margin and account management)
- 3-person Polish team (sr+mid+jr): $156K/yr vs $448K in US (saves $292K)
- 5-person Polish team via SW house: $530K/yr vs $1.16M in US (saves $631K)

--- VALUE PER CLAUDE HOUR ---

| Metric                    | Value                    |
|---------------------------|--------------------------|
| Engineering value (avg)   | ${value}                 |
| Full team value (growth)  | ${value}                 |
| Claude active hours       | {hours}                  |
| $/Claude hour             | ${value}/hr              |
| Speed multiplier          | {multiplier}x faster     |
| Claude cost (Pro sub)     | ~${cost}                 |
| Net savings vs Solo (US)  | ${savings}               |
| Net savings vs Polish SH  | ${savings}               |
| ROI                       | {roi}x                   |

--- THE HEADLINE ---

Claude worked for approximately {hours} hours across {days} calendar days
and produced the equivalent of ${solo_cost} in professional engineering value
-- roughly ${per_hour} per Claude hour.

A US growth-stage company would spend ${growth_cost} and {months} months.
A Polish software house would quote ${polish_cost} and {months} months.
A Polish internal team would burn {pln_cost} PLN over {months} months.

---
Assumptions:
1. Rates based on US + Polish market averages (2025-2026)
   Sources: Salary.com, Glassdoor, Bulldogjob, NoFluffJobs, JustJoinIT, Devico, Qubit Labs
2. Senior fullstack developer (5+ years experience) as baseline
3. {test_note}
4. Does not include: marketing, legal, hosting/infrastructure, ongoing maintenance
5. Polish rates: B2B net (developer take-home). Software house rates include 30-40% margin.
6. 1 USD ~ 4.0 PLN (March 2026)
{extra_assumptions}
```

### 7. Clean up

If a GitHub repo was cloned to a temp directory, remove it:
```bash
rm -rf "$SCAN_DIR"  # only if SCAN_DIR is in /tmp/cost-estimate-*
```

### 8. Handle edge cases

- If the directory has no code files, say so and stop
- If it's a monorepo with multiple projects, scan each and sum
- If git history isn't available, skip the Claude hours section and ask the user to provide active hours
- For very small projects (<500 LOC), note that the estimate has high variance
- Always round costs to nearest $100 for US, nearest 1000 PLN for Polish
- If `gh` CLI is not authenticated or not installed, fall back to local-only scanning and warn the user
- If the GitHub repo is private and `gh` has no access, inform the user and stop
- For very large repos (>100K files), warn that scanning may take a while and consider sampling

## Rules
- NEVER fabricate LOC counts or file counts. Always scan real files.
- NEVER guess API integrations. Grep for them.
- Round all dollar amounts to 2 decimal places in tables, nearest $100 in summaries
- Keep the report tight. No filler paragraphs.
- If confidence is low on any estimate, say so explicitly.
- The Polish context section is mandatory. Always include it.
- Show PLN amounts alongside USD for Polish scenarios.
- Present the report in a code block for clean terminal-style rendering.

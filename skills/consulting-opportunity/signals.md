# Automation Signal Detection Reference

## High-Signal Patterns (STRONG indicators)

### Language patterns
- "manage", "coordinate", "oversee" + process/workflow
- "ensure", "maintain", "track" + data/records/compliance
- "liaise between", "bridge", "connect" teams
- "handle", "process", "review" + volume indicators
- "manual", "repetitive" (rare but explicit)
- "spreadsheet", "reporting", "reconciliation"

### Role types
- Operations roles (Ops Manager, Operations Specialist)
- Coordinator roles (Project Coordinator, Sales Coordinator)
- Analyst roles with "reporting" emphasis
- "Specialist" roles that are really process executors
- Integration/Implementation roles (onboarding customers)
- Support roles with technical investigation components

### Structural signals
- Multiple similar roles = scale problem
- 24/7 or shift coverage mentioned = automation candidate
- Cross-functional coordination emphasized
- Compliance/audit responsibilities

## Medium-Signal Patterns

- Customer Success with "onboarding" focus
- Account Management with "support" emphasis
- Data roles focused on "cleaning" or "validation"
- QA roles with repetitive testing patterns

## Low-Signal (Usually Skip)

- Pure engineering roles (unless DevOps/SRE)
- Executive/leadership roles
- Creative roles (design, content)
- Pure sales roles (AE, SDR without ops component)

## Common ATS Selectors

| Platform | Job List Selector | Job Link Pattern |
|----------|------------------|------------------|
| Ashby | `[data-testid="job-posting"]` | `jobs.ashbyhq.com/company/[id]` |
| Lever | `.posting` | `jobs.lever.co/company/[id]` |
| Greenhouse | `.opening` | `boards.greenhouse.io/company/jobs/[id]` |
| Workday | `.css-19uc56f` | varies |

## Smart Deduplication Rules

1. Strip location suffixes (UK, France, EMEA, etc.)
2. Strip seniority prefixes for grouping (Sr., Junior, Lead)
3. Group by normalized title
4. Keep one representative posting per group
5. Note the count of similar roles (indicates team scale)

Example:
- "Account Executive - UK"
- "Account Executive - France"
- "Account Executive - DACH"
-> Analyze ONE, note "3 similar roles = growing sales team"

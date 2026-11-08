---
name: project-status-tool
description: Unified project status dashboard integrating version history, git branches, roadmap milestones, changelog entries, and quality metrics. Generates JSON, Markdown, and HTML status reports tied to releases and deployments.
license: MIT
---

# Project Status Tool

Create a single-pane-of-glass view of your project's health: current version, active branches, milestone progress, changelog entries, quality metrics, and deployment status—all synced to Git and your roadmap documents.

## When to Use

- Generating project health reports for stakeholders
- Tracking release progress across versions
- Monitoring quality gate status before deployments
- Comparing metrics between releases
- Creating status pages and dashboards
- Auditing what changed between versions
- Planning next milestones based on current status

## Core Capabilities

### 1. Version & Release Tracking

Unified view of:
- Current version (semantic versioning)
- Planned next versions from roadmap
- Release dates and status (planned, in-progress, released)
- Changelog entries per version
- Git tags and commits per release
- Breaking changes and deprecations

### 2. Branch & Deployment Status

Track:
- Active development branches
- Branch protection rules compliance
- Deployment status (staging, production)
- CI/CD pipeline status
- Test coverage metrics per branch
- Build duration trends

### 3. Roadmap Milestone Integration

Link to:
- Milestone definitions (features, bugs, improvements)
- Percentage complete calculations
- Dependency tracking between milestones
- Timeline vs. actual progress
- Blocked items and blockers
- Owner/assignee information

### 4. Quality Metrics Dashboard

Monitor:
- Test coverage (unit, integration, e2e)
- Code quality scores (linting, complexity)
- Security audit status
- Performance metrics (bundle size, load time)
- Accessibility compliance
- Error rates in production

### 5. Multi-Format Output

Generate:
- **JSON**: Programmatic access to all status data
- **Markdown**: Version-control friendly reports
- **HTML Dashboard**: Interactive web view with charts
- **Status Badge**: Quick visual indicator for README
- **Slack/Teams**: Ready-to-post status messages
- **Email Report**: Formatted digest for stakeholders

## Usage Examples

### View Current Status

```bash
status view

# Output shows:
# Version: 2.1.0
# Status: Stable
# Active Branches: 3
# Quality: ✅ Passing (95% coverage)
# Next Release: 2.2.0 (3 weeks)
# Roadmap Progress: 72%
```

### Generate Status Report

```bash
status report --version 2.1.0 --format markdown

# Generates: status-2.1.0.md with:
# - Release summary
# - Changelog entries
# - Milestone breakdown
# - Quality metrics
# - Deployment timeline
```

### Track Milestone Progress

```bash
status milestone --milestone "Q2 Goals" --format json

# Output:
{
  "milestone": "Q2 Goals",
  "progress": 72,
  "status": "on-track",
  "completed": 18,
  "total": 25,
  "dueDate": "2026-06-30",
  "issues": [...]
}
```

### Batch Status for All Versions

```bash
status batch --output ./reports/

# Generates:
# reports/status-current.md
# reports/status-current.html
# reports/status-badge.svg
# reports/quality-metrics.json
```

### Continuous Dashboard

```bash
status serve --port 3000 --watch

# Starts live-updating dashboard at localhost:3000
# Auto-refreshes every 5 minutes
```

## Input Schema

### Project Configuration

```yaml
project:
  name: "Project Name"
  repository: "https://github.com/owner/repo"
  homepage: "https://example.com"

versioning:
  scheme: "semantic"  # semantic | calendar
  currentVersion: "2.1.0"
  releaseProcess: "main only"  # main, staging, dev

tracking:
  source: "github"  # github | linear | jira
  roadmapFile: "ROADMAP.md"
  changelogFile: "CHANGELOG.md"
  qualityCheckfile: ".quality.json"

metrics:
  testCoverage:
    target: 80
    current: 92
  performanceBudget:
    bundleSize: "500kb"
    loadTime: "2s"
  securityLevel: "critical"

reporting:
  formats: [json, markdown, html, slack]
  recipients:
    slack: "#status-updates"
    email: "team@example.com"
  frequency: "weekly"
```

### Status Data Structure

```json
{
  "project": {
    "name": "Project Name",
    "version": "2.1.0",
    "status": "stable|beta|alpha|maintenance",
    "generatedAt": "2026-03-26T10:00:00Z"
  },
  "releases": [
    {
      "version": "2.1.0",
      "releaseDate": "2026-03-20",
      "status": "released",
      "commitHash": "abc123...",
      "changelogUrl": "..."
    }
  ],
  "branches": [
    {
      "name": "main",
      "status": "healthy",
      "lastCommit": "2026-03-26T09:30:00Z",
      "ciStatus": "passing",
      "testCoverage": 92
    }
  ],
  "milestones": [
    {
      "name": "Q2 Goals",
      "progress": 72,
      "status": "on-track|at-risk|blocked",
      "dueDate": "2026-06-30",
      "completedItems": 18,
      "totalItems": 25
    }
  ],
  "metrics": {
    "testCoverage": 92,
    "codeQuality": "A",
    "securityScore": 95,
    "performanceIndex": 87
  }
}
```

## Output Examples

### Markdown Status Report

```markdown
# Project Status Report
**Generated**: 2026-03-26
**Project Version**: 2.1.0
**Overall Status**: ✅ Healthy

## Release Summary
- Current: v2.1.0 (Stable)
- Next: v2.2.0 (ETA: April 15)
- Previous: v2.0.0 (2026-03-01)

## Milestone Progress
- Q2 Goals: 72% complete (18/25 items)
- Bug Fixes: 95% complete (19/20 items)
- Performance: 45% complete (9/20 items)

## Quality Metrics
| Metric | Target | Current | Status |
|--------|--------|---------|--------|
| Test Coverage | 80% | 92% | ✅ |
| Code Quality | A | A | ✅ |
| Security Score | 90 | 95 | ✅ |
| Bundle Size | 500kb | 480kb | ✅ |

## Branch Status
| Branch | Status | CI | Coverage | Last Updated |
|--------|--------|----|----|---|
| main | Healthy | ✅ | 92% | 2h ago |
| develop | Healthy | ✅ | 89% | 30m ago |
| hotfix/bug-123 | Healthy | ✅ | 88% | 5m ago |

## Recent Changelog
- **2.1.0** (2026-03-20) - Performance improvements, new API endpoints
- **2.0.0** (2026-03-01) - Major refactor, breaking changes
```

### HTML Dashboard

Interactive dashboard with:
- Real-time metrics visualization
- Timeline/burndown charts
- Commit activity graph
- Branch status board
- Milestone progress indicators
- Quality trend analysis
- Deployment timeline

### Status Badge

```markdown
![Project Status](https://status.example.com/badge.svg)

<!-- Options: passing, at-risk, blocked, maintenance -->
```

## CLI Commands

```bash
# View current status
status view [--format json|markdown|html]

# Generate report
status report --version <version> --output <file>

# Track milestone
status milestone --milestone <name> [--watch]

# Batch generate
status batch [--output <dir>] [--formats json,markdown,html]

# Serve dashboard
status serve [--port 3000] [--watch]

# Compare versions
status compare --from <v1> --to <v2>

# Export metrics
status metrics --metric coverage|quality|performance [--chart]

# Validate roadmap
status validate-roadmap <ROADMAP.md>

# Sync with GitHub
status sync --github <owner/repo>
```

## Integration Examples

### With Pre-Deploy Validator

```bash
# Check quality gates before deployment
status validate && pre-deploy && git tag v2.1.0
```

### With Changelog

```bash
# Auto-generate status from CHANGELOG.md
status sync-changelog CHANGELOG.md --format markdown
```

### With Mermaid Roadmap

```bash
# Render roadmap milestones as timeline
mermaid export ROADMAP.mmd --format html
status metrics --milestone-chart ROADMAP.html
```

### With UX Journey Updates

```bash
# Track journey map version changes in status
status track-versions --include journey-maps/
```

### GitHub Actions Automation

```yaml
- name: Generate Status Report
  run: |
    status report --version ${{ github.ref_name }}
    status batch --output ./reports/

- name: Upload Status
  uses: actions/upload-artifact@v3
  with:
    name: status-reports
    path: reports/
```

## Best Practices

1. **Automate Collection**: Use CI/CD to gather metrics automatically
2. **Real-time Data**: Sync with GitHub/Jira at least hourly
3. **Version Every Report**: Include timestamp and version for audit trails
4. **Multi-format Output**: Generate JSON for automation, Markdown for Git, HTML for dashboards
5. **Trend Analysis**: Compare metrics across releases to identify patterns
6. **Stakeholder Updates**: Automate weekly status reports to Slack/email
7. **Alert Thresholds**: Set up alerts when metrics cross critical thresholds
8. **Milestone Tracking**: Keep roadmap in sync with actual progress

## Attribution

Created by [Fused Gaming](https://github.com/fused-gaming)

# Project Status Tool

> Unified project status dashboard integrating version history, git branches, roadmap milestones, changelog entries, and quality metrics.

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![npm version](https://img.shields.io/npm/v/@fused-gaming/project-status-tool.svg)](https://www.npmjs.com/package/@fused-gaming/project-status-tool)

## Features

- 📊 **Unified Dashboard**: Single view of version, branches, milestones, metrics, and deployments
- 📈 **Quality Metrics Tracking**: Test coverage, code quality, security scores, performance budgets
- 🎯 **Milestone Progress**: Track roadmap completion with dependency visualization
- 🔗 **Git Integration**: Automatic version syncing from tags and branch status
- 📝 **Changelog Management**: Link changelog entries to releases and milestones
- 🚀 **Deployment Status**: Track staging and production deployment status
- 📊 **Multi-format Export**: JSON, Markdown, HTML, Slack, email reports
- 🔄 **Real-time Updates**: Sync with GitHub/Jira automatically
- 📱 **Interactive Dashboard**: Live-updating web view with charts and metrics
- ⚡ **CI/CD Integration**: Seamless GitHub Actions and deployment pipeline hooks

## Installation

```bash
npm install -g @fused-gaming/project-status-tool
```

Or locally in a project:

```bash
npm install --save-dev @fused-gaming/project-status-tool
```

## Quick Start

### Initialize Project Status

```bash
status init
# Creates: .status.config.yaml with your project info
```

### View Current Status

```bash
status view

# Output:
# Project: My App
# Version: 2.1.0 (Stable)
# Status: Healthy ✅
#
# Branches: 3 active (main, develop, hotfix/urgent)
# Test Coverage: 92% (target: 80%)
# Code Quality: A (9.2/10)
# Security Score: 95/100
#
# Milestones: 72% complete (18/25 items)
# Next Release: v2.2.0 (3 weeks away)
```

### Generate Report

```bash
# Current version report
status report

# Specific version
status report --version 2.1.0

# Custom output
status report --format markdown --output ./reports/status-2.1.0.md
```

### Track Milestones

```bash
# View milestone progress
status milestone "Q2 Goals"

# Watch milestone for changes
status milestone "Q2 Goals" --watch

# Export milestone status
status milestone "Q2 Goals" --export json
```

### Serve Interactive Dashboard

```bash
# Start live dashboard
status serve --port 3000

# With auto-refresh from GitHub
status serve --port 3000 --watch --github owner/repo
```

## Usage Examples

### Basic Status View

```bash
status view --format json

# Output:
{
  "project": {
    "name": "My Project",
    "version": "2.1.0",
    "status": "stable",
    "lastUpdated": "2026-03-26T10:30:00Z"
  },
  "metrics": {
    "testCoverage": 92,
    "codeQuality": "A",
    "securityScore": 95,
    "bundleSize": "480kb"
  },
  "branches": [
    {
      "name": "main",
      "status": "healthy",
      "testsPassing": true,
      "ciStatus": "passing"
    }
  ],
  "milestones": [
    {
      "name": "Q2 Goals",
      "progress": 72,
      "status": "on-track"
    }
  ]
}
```

### Release Status Report

```bash
status report --version 2.1.0 --format markdown

# Creates: status-2.1.0.md with:
# - Release summary and date
# - Changelog entries
# - Milestone breakdown
# - Quality metrics snapshot
# - Deployment timeline
# - Contributors and reviewers
```

### Milestone Tracking

```bash
status milestone "v2.2.0 Release" --format json

{
  "milestone": "v2.2.0 Release",
  "status": "on-track",
  "progress": 45,
  "completedItems": 9,
  "totalItems": 20,
  "dueDate": "2026-04-15",
  "blockers": [],
  "items": [
    {
      "id": "GH-123",
      "title": "Implement feature X",
      "status": "completed",
      "assignee": "developer@example.com"
    }
  ]
}
```

### Compare Releases

```bash
status compare --from 2.0.0 --to 2.1.0

# Shows:
# - What changed (features, bugs, improvements)
# - Metrics improvement/regression
# - Performance delta
# - Test coverage change
# - Security audit differences
```

### Export for Stakeholders

```bash
# Generate weekly status email
status report --format email --recipients team@example.com

# Post to Slack
status report --format slack --channel "#status-updates"

# Generate status badge
status badge --version 2.1.0 --status healthy --output ./README.svg
```

### Batch Status for All Versions

```bash
status batch --output ./status-reports/

# Generates:
# status-reports/current.md
# status-reports/current.html
# status-reports/status-badge.svg
# status-reports/metrics.json
# status-reports/branches.json
# status-reports/milestones.json
```

### Integration with CI/CD

```bash
# Validate quality gates before deployment
status validate --quality-threshold 80 --coverage-threshold 85

# Generate status as deployment artifact
status report --version $(git describe --tags) --output ./artifacts/

# Post deployment status
status update-deployment --env production --status success
```

## Configuration

Create `.status.config.yaml` in your project:

```yaml
project:
  name: "My Project"
  repository: "https://github.com/owner/repo"
  homepage: "https://example.com"

versioning:
  scheme: "semantic"
  currentVersion: "2.1.0"
  releaseProcess: "main"

integration:
  github:
    enabled: true
    owner: "owner"
    repo: "repo"
    token: "${GH_TOKEN}"  # Use env var

  roadmap:
    file: "ROADMAP.md"
    format: "markdown"

  changelog:
    file: "CHANGELOG.md"
    format: "keep-a-changelog"

metrics:
  targets:
    testCoverage: 80
    codeQuality: "A"
    securityScore: 90
    bundleSize: "500kb"
    loadTime: "2s"

reporting:
  formats: [json, markdown, html]
  recipients:
    slack: "#status-updates"
    email: "team@example.com"
  frequency: "weekly"
  day: "monday"
  time: "09:00"
```

## CLI Commands

### View & Report

```bash
# View current status
status view [--format json|markdown|html]

# Generate report
status report [--version <v>] [--format <fmt>] [--output <file>]

# Compare versions
status compare --from <v1> --to <v2> [--format <fmt>]

# Batch generate
status batch [--output <dir>] [--formats json,markdown,html]
```

### Tracking

```bash
# Track milestone
status milestone <name> [--watch] [--export json]

# Track branch
status branch <name> [--watch]

# Track metrics
status metrics [--metric coverage|quality|security] [--chart]

# List all milestones
status milestones --list
```

### Dashboard & Monitoring

```bash
# Serve interactive dashboard
status serve [--port 3000] [--watch] [--github owner/repo]

# Generate status badge
status badge [--version <v>] [--status <s>] [--output <file>]

# Export metrics chart
status chart --metric coverage --format png --output ./chart.png
```

### Validation & Sync

```bash
# Validate quality gates
status validate [--quality-threshold <n>] [--coverage-threshold <n>]

# Sync with GitHub
status sync --github owner/repo

# Sync changelog
status sync-changelog CHANGELOG.md

# Validate roadmap
status validate-roadmap ROADMAP.md
```

### Deployment

```bash
# Update deployment status
status update-deployment --env production --status success

# Log release
status log-release --version 2.1.0 --date 2026-03-20

# Archive status
status archive --version 2.1.0
```

## Output Examples

### JSON Output

```json
{
  "generatedAt": "2026-03-26T10:30:00Z",
  "project": {
    "name": "My Project",
    "version": "2.1.0",
    "status": "stable",
    "homepage": "https://example.com"
  },
  "metrics": {
    "testCoverage": {
      "current": 92,
      "target": 80,
      "trend": "increasing"
    },
    "codeQuality": {
      "current": "A",
      "target": "A",
      "score": 9.2
    }
  },
  "branches": [...],
  "milestones": [...]
}
```

### Markdown Output

```markdown
# Project Status Report

**Generated**: 2026-03-26 10:30 UTC
**Project**: My Project
**Version**: 2.1.0 (Stable)

## Quick Summary

✅ **Healthy** - All systems operational

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| Test Coverage | 92% | 80% | ✅ |
| Code Quality | A | A | ✅ |
| Security Score | 95 | 90 | ✅ |

## Release Information

**Release Date**: 2026-03-20
**Previous**: v2.0.0
**Next Planned**: v2.2.0 (April 15)

## Changelog

### New Features
- Performance improvements (30% faster API)
- New dashboard endpoints
- Improved error handling

### Bug Fixes
- Fixed memory leak in cache
- Resolved race condition in auth
- Patched security vulnerability

## Milestone Progress

**Q2 Goals**: 72% complete (18/25)
- Completed: 18 items
- In Progress: 5 items
- Blocked: 2 items

## Branch Status

| Branch | Status | CI | Coverage | Last Update |
|--------|--------|----|----|---|
| main | ✅ Healthy | ✅ | 92% | 30m |
| develop | ✅ Healthy | ✅ | 89% | 5m |
```

### HTML Dashboard

Interactive dashboard featuring:
- Real-time metrics visualization with charts
- Timeline of releases
- Burndown charts for milestones
- Branch status board
- Commit activity graph
- Quality trend analysis
- Deployment timeline
- Links to GitHub issues/PRs

## Integration Examples

### GitHub Actions

```yaml
name: Generate Status Report

on:
  push:
    tags:
      - 'v*'

jobs:
  status:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install status tool
        run: npm install -g @fused-gaming/project-status-tool

      - name: Generate status
        run: |
          status report --version ${{ github.ref_name }}
          status batch --output ./reports/
        env:
          GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}

      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: status-reports
          path: reports/
```

### Slack Notifications

```bash
# Post weekly status to Slack
0 9 * * 1 status report --format slack --channel "#status-updates"
```

### Automated Reporting

```bash
# Generate and email status monthly
status report --format email --recipients team@example.com \
  --template monthly-digest
```

### Pre-Deployment Validation

```bash
#!/bin/bash
# scripts/pre-deploy.sh

# Validate quality thresholds
status validate \
  --quality-threshold 90 \
  --coverage-threshold 85 \
  --security-threshold 95

if [ $? -eq 0 ]; then
  echo "✅ Quality gates passed, proceeding with deployment"
  status update-deployment --env production --status deploying
else
  echo "❌ Quality gates failed, aborting deployment"
  exit 1
fi
```

## Integration with Other Tools

### With UX Journey Mapper

```bash
# Track journey version changes
status track-versions --include journey-maps/ --output ./roadmap-sync.json
```

### With Mermaid Terminal

```bash
# Generate roadmap diagram from status data
status export-roadmap --format mermaid --output ROADMAP.mmd
mermaid export ROADMAP.mmd --format svg
```

### With Pre-Deploy Validator

```bash
# Validate before deployment
pre-deploy --config .pre-deploy.json && \
status report --version $(git describe --tags) && \
git push origin main --tags
```

## Best Practices

1. **Automate Everything**: Use CI/CD to gather metrics and generate reports
2. **Version All Reports**: Include timestamp and version for audit trails
3. **Real-time Sync**: Update status at least hourly from GitHub
4. **Multi-format Output**: JSON for automation, Markdown for Git, HTML for dashboards
5. **Threshold Alerts**: Set up notifications when metrics cross critical values
6. **Trend Analysis**: Compare metrics across releases to identify patterns
7. **Stakeholder Updates**: Automate weekly reports to Slack/email
8. **Archive History**: Keep historical status reports for long-term analysis

## Troubleshooting

### "Failed to sync with GitHub"

Ensure your GitHub token is set:
```bash
export GH_TOKEN=your_github_token
status sync --github owner/repo
```

### "Milestone not found"

Verify milestone exists on GitHub:
```bash
status milestones --list
```

### "Config file not found"

Initialize with defaults:
```bash
status init
# Creates .status.config.yaml
```

## API Reference

See [API_REFERENCE.md](./API_REFERENCE.md) for detailed API documentation.

## Contributing

Contributions welcome! See [CONTRIBUTING.md](./CONTRIBUTING.md).

## License

MIT - See [LICENSE](./LICENSE) file.

## Attribution

Created by [Fused Gaming](https://github.com/fused-gaming)

## Support

- [GitHub Issues](https://github.com/fused-gaming/skills/issues)
- [Discussions](https://github.com/fused-gaming/skills/discussions)

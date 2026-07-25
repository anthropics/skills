# Tech Debt Tracker

A comprehensive technical debt management system that helps engineering teams identify, prioritize, and track technical debt across codebases. This skill provides three interconnected tools for a complete debt management workflow.

## Overview

Technical debt is like financial debt - it compounds over time and reduces team velocity if not managed systematically. This skill provides:

- **Automated Debt Detection**: Scan codebases to identify various types of technical debt
- **Intelligent Prioritization**: Use proven frameworks to prioritize debt based on business impact
- **Trend Analysis**: Track debt evolution over time with executive-friendly dashboards

## Tools

### 1. Debt Scanner (`debt_scanner.py`)

Scans codebases to automatically detect technical debt signals using AST parsing for Python and regex patterns for other languages.

**Features:**
- Detects 15+ types of technical debt (large functions, complexity, duplicates, security issues, etc.)
- Multi-language support (Python, JavaScript, Java, C#, Go, etc.)
- Configurable thresholds and rules
- Dual output: JSON for tools, human-readable for reports

**Usage:**
```bash
# Basic scan
python scripts/debt_scanner.py /path/to/codebase

# With custom config and output
python scripts/debt_scanner.py /path/to/codebase --config config.json --output report.json

# Different output formats
python scripts/debt_scanner.py /path/to/codebase --format both
```

### 2. Debt Prioritizer (`debt_prioritizer.py`)

Takes debt inventory and creates prioritized backlog using proven prioritization frameworks.

**Features:**
- Multiple prioritization frameworks (Cost of Delay, WSJF, RICE)
- Business impact analysis with ROI calculations  
- Sprint allocation recommendations
- Effort estimation with risk adjustment
- Executive and engineering reports

**Usage:**
```bash
# Basic prioritization
python scripts/debt_prioritizer.py debt_inventory.json

# Custom framework and team size
python scripts/debt_prioritizer.py inventory.json --framework wsjf --team-size 8

# Sprint capacity planning
python scripts/debt_prioritizer.py inventory.json --sprint-capacity 80 --output backlog.json
```

### 3. Debt Dashboard (`debt_dashboard.py`)

Analyzes historical debt data to provide trend analysis, health scoring, and executive reporting.

**Features:**
- Health score trending over time
- Debt velocity analysis (accumulation vs resolution)
- Executive summary with business impact
- Forecasting based on current trends
- Strategic recommendations

**Usage:**
```bash
# Single directory of scans
python scripts/debt_dashboard.py --input-dir ./debt_scans/

# Multiple specific files
python scripts/debt_dashboard.py scan1.json scan2.json scan3.json

# Custom analysis period
python scripts/debt_dashboard.py data.json --period quarterly --team-size 6
```

## Quick Start

### 1. Scan Your Codebase

```bash
# Scan your project
python scripts/debt_scanner.py ~/my-project --output initial_scan.json

# Review the results
python scripts/debt_scanner.py ~/my-project --format text
```

### 2. Prioritize Your Debt

```bash
# Create prioritized backlog
python scripts/debt_prioritizer.py initial_scan.json --output backlog.json

# View sprint recommendations
python scripts/debt_prioritizer.py initial_scan.json --format text
```

### 3. Track Over Time

```bash
# After multiple scans, analyze trends
python scripts/debt_dashboard.py scan1.json scan2.json scan3.json --output dashboard.json

# Generate executive report
python scripts/debt_dashboard.py --input-dir ./scans/ --format text
```

## Configuration

### Scanner Configuration

Create `config.json` to customize detection rules:

```json
{
  "max_function_length": 50,
  "max_complexity": 10,
  "max_nesting_depth": 4,
  "ignore_patterns": ["*.test.js", "build/", "node_modules/"],
  "file_extensions": {
    "python": [".py"],
    "javascript": [".js", ".jsx", ".ts", ".tsx"]
  }
}
```

### Team Configuration

Adjust tools for your team size and sprint capacity:

```bash
# 8-person team with 2-week sprints
python scripts/debt_prioritizer.py inventory.json --team-size 8 --sprint-capacity 160
```

## Sample Data

The `assets/` directory contains sample data for testing:

- `sample_codebase/`: Example codebase with various debt types
- `sample_debt_inventory.json`: Example debt inventory
- `historical_debt_*.json`: Sample historical data for trending

Try the tools on sample data:

```bash
# Test scanner
python scripts/debt_scanner.py assets/sample_codebase

# Test prioritizer  
python scripts/debt_prioritizer.py assets/sample_debt_inventory.json

# Test dashboard
python scripts/debt_dashboard.py assets/historical_debt_*.json
```

## Understanding the Output

### Health Score (0-100)

- **85-100**: Excellent - Minimal debt, sustainable practices
- **70-84**: Good - Manageable debt level, some attention needed
- **55-69**: Fair - Debt accumulating, requires focused effort
- **40-54**: Poor - High debt level, impacts productivity
- **0-39**: Critical - Immediate action required

### Priority Levels

- **Critical**: Security issues, blocking problems (fix immediately)
- **High**: Significant impact on quality or velocity (next sprint)
- **Medium**: Moderate impact, plan for upcoming work (next quarter)
- **Low**: Minor issues, fix opportunistically (when convenient)

### Debt Categories

- **Code Quality**: Large functions, complexity, duplicates
- **Architecture**: Design issues, coupling problems
- **Security**: Vulnerabilities, hardcoded secrets
- **Testing**: Missing tests, poor coverage
- **Documentation**: Missing or outdated docs
- **Dependencies**: Outdated packages, license issues

## Integration with Development Workflow

### CI/CD Integration

Add debt scanning to your CI pipeline:

```bash
# In your CI script
python scripts/debt_scanner.py . --output ci_scan.json
# Compare with baseline, fail build if critical issues found
```

### Sprint Planning

1. **Weekly**: Run scanner to detect new debt
2. **Sprint Planning**: Use prioritizer for debt story sizing
3. **Monthly**: Generate dashboard for trend analysis
4. **Quarterly**: Executive review with strategic recommendations

### Code Review Integration

Use scanner output to focus code reviews:

```bash
# Scan PR branch
python scripts/debt_scanner.py . --output pr_scan.json

# Compare with main branch baseline
# Focus review on areas with new debt
```

## Best Practices

### Debt Management Strategy

1. **Prevention**: Use scanner in CI to catch debt early
2. **Prioritization**: Always use business impact for priority
3. **Allocation**: Reserve 15-20% sprint capacity for debt work
4. **Measurement**: Track health score and velocity impact
5. **Communication**: Use dashboard reports for stakeholders

### Common Pitfalls to Avoid

- **Analysis Paralysis**: Don't spend too long on perfect prioritization
- **Technical Focus Only**: Always consider business impact
- **Inconsistent Application**: Ensure all teams use same approach
- **Ignoring Trends**: Pay attention to debt accumulation rate
- **All-or-Nothing**: Incremental debt reduction is better than none

### Success Metrics

- **Health Score Improvement**: Target 5+ point quarterly improvement
- **Velocity Impact**: Keep debt velocity impact below 20%
- **Team Satisfaction**: Survey developers on code quality satisfaction
- **Incident Reduction**: Track correlation between debt and production issues

## Advanced Usage

### Custom Debt Types

Extend the scanner for organization-specific debt patterns:

1. Add patterns to `config.json`
2. Modify detection logic in scanner
3. Update categorization in prioritizer

### Integration with External Tools

- **Jira/GitHub**: Import debt items as tickets
- **SonarQube**: Combine with static analysis metrics
- **APM Tools**: Correlate debt with performance metrics
- **Chat Systems**: Send debt alerts to team channels

### Automated Reporting

Set up automated debt reporting:

```bash
#!/bin/bash
# Daily debt monitoring script
python scripts/debt_scanner.py . --output daily_scan.json
python scripts/debt_dashboard.py daily_scan.json --output daily_report.json
# Send report to stakeholders
```

## Troubleshooting

### Common Issues

**Scanner not finding files**: Check `ignore_patterns` in config
**Prioritizer giving unexpected results**: Verify business impact scoring
**Dashboard shows flat trends**: Need more historical data points

### Performance Tips

- Use `.gitignore` patterns to exclude irrelevant files
- Limit scan depth for large monorepos
- Run dashboard analysis on subset for faster iteration

### Getting Help

1. Check the `references/` directory for detailed documentation
2. Review sample data and expected outputs
3. Examine the tool source code for customization ideas

## Contributing

This skill is designed to be customized for your organization's needs:

1. **Add Detection Rules**: Extend scanner patterns for your tech stack
2. **Custom Prioritization**: Modify scoring algorithms for your business context
3. **New Report Formats**: Add output formats for your stakeholders
4. **Integration Hooks**: Add connectors to your existing tools

The codebase is designed with extensibility in mind - each tool is modular and can be enhanced independently.

---

**Remember**: Technical debt management is a journey, not a destination. These tools help you make informed decisions about balancing new feature development with technical excellence. Start small, measure impact, and iterate based on what works for your team.
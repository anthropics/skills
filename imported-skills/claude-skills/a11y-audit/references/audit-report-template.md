# Audit Report Template

The scanner generates a stakeholder-ready report when run with the `--report` flag:

```bash
python scripts/a11y_scanner.py /path/to/project --report --output audit-report.md
```

## Generated Report Structure

```markdown
# Accessibility Audit Report
**Project:** Acme Dashboard
**Date:** 2026-03-18
**Standard:** WCAG 2.2 Level AA
**Tool:** a11y-audit v2.1.2

## Executive Summary
- Files Scanned: 127
- Total Violations: 14
- Critical: 3 | Major: 7 | Minor: 4
- Estimated Remediation: 8-12 hours
- Compliance Score: 72% (Target: 100%)

## Violations by Category
| Category | Count | Severity Breakdown |
|----------|-------|--------------------|
| Missing Alt Text | 3 | 2 Critical, 1 Minor |
| Keyboard Access | 4 | 2 Critical, 2 Major |
| Color Contrast | 3 | 3 Major |
| Form Labels | 2 | 2 Major |
| ARIA Usage | 2 | 2 Minor |

## Detailed Findings
[Per-violation details with file, line, WCAG criterion, and fix]

## Remediation Priority
1. Fix all Critical issues (blocks release)
2. Fix Major issues in current sprint
3. Schedule Minor issues for next sprint

## Recommendations
- Add a11y linting to CI pipeline (eslint-plugin-jsx-a11y)
- Include keyboard testing in QA checklist
- Schedule quarterly manual audit with assistive technology
```

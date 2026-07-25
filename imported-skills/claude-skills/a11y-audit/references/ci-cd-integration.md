# CI/CD Integration for Accessibility Auditing

## GitHub Actions

```yaml
# .github/workflows/a11y-audit.yml
name: Accessibility Audit

on:
  pull_request:
    paths:
      - 'src/**/*.tsx'
      - 'src/**/*.vue'
      - 'src/**/*.html'
      - 'src/**/*.svelte'

jobs:
  a11y-audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Run A11y Scanner
        run: |
          python scripts/a11y_scanner.py ./src --json > a11y-results.json

      - name: Check for Critical Issues
        run: |
          python -c "
          import json, sys
          with open('a11y-results.json') as f:
              data = json.load(f)
          critical = [v for v in data.get('violations', []) if v['severity'] == 'critical']
          if critical:
              print(f'FAILED: {len(critical)} critical a11y violations found')
              for v in critical:
                  print(f\"  [{v['wcag']}] {v['file']}:{v['line']} - {v['message']}\")
              sys.exit(1)
          print('PASSED: No critical a11y violations')
          "

      - name: Upload Audit Report
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: a11y-audit-report
          path: a11y-results.json

      - name: Comment on PR
        if: failure()
        uses: marocchino/sticky-pull-request-comment@v2
        with:
          header: a11y-audit
          message: |
            ## Accessibility Audit Failed
            Critical WCAG 2.2 violations were found. See the uploaded artifact for details.
            Run `python scripts/a11y_scanner.py ./src` locally to view and fix issues.
```

## GitLab CI

```yaml
# .gitlab-ci.yml
a11y-audit:
  stage: test
  image: python:3.11-slim
  script:
    - python scripts/a11y_scanner.py ./src --json > a11y-results.json
    - python -c "
      import json, sys;
      data = json.load(open('a11y-results.json'));
      critical = [v for v in data.get('violations', []) if v['severity'] == 'critical'];
      sys.exit(1) if critical else print('A11y audit passed')
      "
  artifacts:
    paths:
      - a11y-results.json
    when: always
  rules:
    - changes:
        - "src/**/*.{tsx,vue,html,svelte}"
```

## Azure DevOps

```yaml
# azure-pipelines.yml
- task: PythonScript@0
  displayName: 'Run A11y Audit'
  inputs:
    scriptSource: 'filePath'
    scriptPath: 'scripts/a11y_scanner.py'
    arguments: './src --json --output $(Build.ArtifactStagingDirectory)/a11y-results.json'

- task: PublishBuildArtifacts@1
  condition: always()
  inputs:
    PathtoPublish: '$(Build.ArtifactStagingDirectory)/a11y-results.json'
    ArtifactName: 'a11y-audit-report'
```

## Pre-Commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Run a11y scan on staged files only
STAGED_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep -E '\.(tsx|vue|html|svelte|jsx)$')

if [ -n "$STAGED_FILES" ]; then
  echo "Running accessibility audit on staged files..."
  for file in $STAGED_FILES; do
    python scripts/a11y_scanner.py "$file" --severity critical --quiet
    if [ $? -ne 0 ]; then
      echo "A11y audit FAILED for $file. Fix critical issues before committing."
      exit 1
    fi
  done
  echo "A11y audit passed."
fi
```

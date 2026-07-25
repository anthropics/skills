# Dependency Auditor

A comprehensive toolkit for analyzing, auditing, and managing dependencies across multi-language software projects. This skill provides vulnerability scanning, license compliance checking, and upgrade path planning with zero external dependencies.

## Overview

The Dependency Auditor skill consists of three main Python scripts that work together to provide complete dependency management capabilities:

- **`dep_scanner.py`**: Vulnerability scanning and dependency analysis
- **`license_checker.py`**: License compliance and conflict detection  
- **`upgrade_planner.py`**: Upgrade path planning and risk assessment

## Features

### 🔍 Vulnerability Scanning
- Multi-language dependency parsing (JavaScript, Python, Go, Rust, Ruby, Java)
- Built-in vulnerability database with common CVE patterns
- CVSS scoring and risk assessment
- JSON and human-readable output formats
- CI/CD integration support

### ⚖️ License Compliance
- Comprehensive license classification and compatibility analysis
- Automatic conflict detection between project and dependency licenses
- Risk assessment for commercial usage and distribution
- Compliance scoring and reporting

### 📈 Upgrade Planning
- Semantic versioning analysis with breaking change prediction
- Risk-based upgrade prioritization
- Phased migration plans with rollback procedures
- Security-focused upgrade recommendations

## Installation

No external dependencies required! All scripts use only Python standard library.

```bash
# Clone or download the dependency-auditor skill
cd engineering/dependency-auditor/scripts

# Make scripts executable
chmod +x dep_scanner.py license_checker.py upgrade_planner.py
```

## Quick Start

### 1. Scan for Vulnerabilities

```bash
# Basic vulnerability scan
python dep_scanner.py /path/to/your/project

# JSON output for automation
python dep_scanner.py /path/to/your/project --format json --output scan_results.json

# Fail CI/CD on high-severity vulnerabilities
python dep_scanner.py /path/to/your/project --fail-on-high
```

### 2. Check License Compliance

```bash
# Basic license compliance check
python license_checker.py /path/to/your/project

# Strict policy enforcement
python license_checker.py /path/to/your/project --policy strict

# Use existing dependency inventory
python license_checker.py /path/to/project --inventory scan_results.json --format json
```

### 3. Plan Dependency Upgrades

```bash
# Generate upgrade plan from dependency inventory
python upgrade_planner.py scan_results.json

# Custom timeline and risk filtering
python upgrade_planner.py scan_results.json --timeline 60 --risk-threshold medium

# Security updates only
python upgrade_planner.py scan_results.json --security-only --format json
```

## Detailed Usage

### Dependency Scanner (`dep_scanner.py`)

The dependency scanner parses project files to extract dependencies and check them against a built-in vulnerability database.

#### Supported File Formats
- **JavaScript/Node.js**: package.json, package-lock.json, yarn.lock
- **Python**: requirements.txt, pyproject.toml, Pipfile.lock, poetry.lock  
- **Go**: go.mod, go.sum
- **Rust**: Cargo.toml, Cargo.lock
- **Ruby**: Gemfile, Gemfile.lock

#### Command Line Options

```bash
python dep_scanner.py [PROJECT_PATH] [OPTIONS]

Required Arguments:
  PROJECT_PATH          Path to the project directory to scan

Optional Arguments:
  --format {text,json}  Output format (default: text)
  --output FILE         Output file path (default: stdout)
  --fail-on-high        Exit with error code if high-severity vulnerabilities found
  --quick-scan          Perform quick scan (skip transitive dependencies)

Examples:
  python dep_scanner.py /app
  python dep_scanner.py . --format json --output results.json
  python dep_scanner.py /project --fail-on-high --quick-scan
```

#### Output Format

**Text Output:**
```
============================================================
DEPENDENCY SECURITY SCAN REPORT
============================================================
Scan Date: 2024-02-16T15:30:00.000Z
Project: /example/sample-web-app

SUMMARY:
  Total Dependencies: 23
  Unique Dependencies: 19
  Ecosystems: npm
  Vulnerabilities Found: 1
    High Severity: 1
    Medium Severity: 0
    Low Severity: 0

VULNERABLE DEPENDENCIES:
------------------------------
Package: lodash v4.17.20 (npm)
  • CVE-2021-23337: Prototype pollution in lodash
    Severity: HIGH (CVSS: 7.2)
    Fixed in: 4.17.21

RECOMMENDATIONS:
--------------------
1. URGENT: Address 1 high-severity vulnerabilities immediately
2. Update lodash from 4.17.20 to 4.17.21 to fix CVE-2021-23337
```

**JSON Output:**
```json
{
  "timestamp": "2024-02-16T15:30:00.000Z",
  "project_path": "/example/sample-web-app",
  "dependencies": [
    {
      "name": "lodash",
      "version": "4.17.20",
      "ecosystem": "npm",
      "direct": true,
      "vulnerabilities": [
        {
          "id": "CVE-2021-23337",
          "summary": "Prototype pollution in lodash",
          "severity": "HIGH",
          "cvss_score": 7.2
        }
      ]
    }
  ],
  "recommendations": [
    "Update lodash from 4.17.20 to 4.17.21 to fix CVE-2021-23337"
  ]
}
```

### License Checker (`license_checker.py`)

The license checker analyzes dependency licenses for compliance and detects potential conflicts.

#### Command Line Options

```bash
python license_checker.py [PROJECT_PATH] [OPTIONS]

Required Arguments:
  PROJECT_PATH          Path to the project directory to analyze

Optional Arguments:
  --inventory FILE      Path to dependency inventory JSON file
  --format {text,json}  Output format (default: text)  
  --output FILE         Output file path (default: stdout)
  --policy {permissive,strict}  License policy strictness (default: permissive)
  --warn-conflicts      Show warnings for potential conflicts

Examples:
  python license_checker.py /app
  python license_checker.py . --format json --output compliance.json
  python license_checker.py /app --inventory deps.json --policy strict
```

#### License Classifications

The tool classifies licenses into risk categories:

- **Permissive (Low Risk)**: MIT, Apache-2.0, BSD, ISC
- **Weak Copyleft (Medium Risk)**: LGPL, MPL
- **Strong Copyleft (High Risk)**: GPL, AGPL
- **Proprietary (High Risk)**: Commercial licenses
- **Unknown (Critical Risk)**: Unidentified licenses

#### Compatibility Matrix

The tool includes a comprehensive compatibility matrix that checks:
- Project license vs. dependency licenses
- GPL contamination detection
- Commercial usage restrictions
- Distribution requirements

### Upgrade Planner (`upgrade_planner.py`)

The upgrade planner analyzes dependency inventories and creates prioritized upgrade plans.

#### Command Line Options

```bash
python upgrade_planner.py [INVENTORY_FILE] [OPTIONS]

Required Arguments:
  INVENTORY_FILE        Path to dependency inventory JSON file

Optional Arguments:
  --timeline DAYS       Timeline for upgrade plan in days (default: 90)
  --format {text,json}  Output format (default: text)
  --output FILE         Output file path (default: stdout)
  --risk-threshold {safe,low,medium,high,critical}  Maximum risk level (default: high)
  --security-only       Only plan upgrades with security fixes

Examples:
  python upgrade_planner.py deps.json
  python upgrade_planner.py inventory.json --timeline 60 --format json
  python upgrade_planner.py deps.json --security-only --risk-threshold medium
```

#### Risk Assessment

Upgrades are classified by risk level:

- **Safe**: Patch updates with no breaking changes
- **Low**: Minor updates with backward compatibility
- **Medium**: Updates with potential API changes
- **High**: Major version updates with breaking changes
- **Critical**: Updates affecting core functionality

#### Phased Planning

The tool creates three-phase upgrade plans:

1. **Phase 1 (30% of timeline)**: Security fixes and safe updates
2. **Phase 2 (40% of timeline)**: Regular maintenance updates  
3. **Phase 3 (30% of timeline)**: Major updates requiring careful planning

## Integration Examples

### CI/CD Pipeline Integration

#### GitHub Actions Example

```yaml
name: Dependency Audit
on: [push, pull_request, schedule]

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.9'
      
      - name: Run Vulnerability Scan
        run: |
          python scripts/dep_scanner.py . --format json --output scan.json
          python scripts/dep_scanner.py . --fail-on-high
      
      - name: Check License Compliance
        run: |
          python scripts/license_checker.py . --inventory scan.json --policy strict
      
      - name: Generate Upgrade Plan
        run: |
          python scripts/upgrade_planner.py scan.json --output upgrade-plan.txt
      
      - name: Upload Reports
        uses: actions/upload-artifact@v3
        with:
          name: dependency-reports
          path: |
            scan.json
            upgrade-plan.txt
```

#### Jenkins Pipeline Example

```groovy
pipeline {
    agent any
    
    stages {
        stage('Dependency Audit') {
            steps {
                script {
                    // Vulnerability scan
                    sh 'python scripts/dep_scanner.py . --format json --output scan.json'
                    
                    // License compliance
                    sh 'python scripts/license_checker.py . --inventory scan.json --format json --output compliance.json'
                    
                    // Upgrade planning
                    sh 'python scripts/upgrade_planner.py scan.json --format json --output upgrades.json'
                }
                
                // Archive reports
                archiveArtifacts artifacts: '*.json', fingerprint: true
                
                // Fail build on high-severity vulnerabilities
                sh 'python scripts/dep_scanner.py . --fail-on-high'
            }
        }
    }
    
    post {
        always {
            // Publish reports
            publishHTML([
                allowMissing: false,
                alwaysLinkToLastBuild: true,
                keepAll: true,
                reportDir: '.',
                reportFiles: '*.json',
                reportName: 'Dependency Audit Report'
            ])
        }
    }
}
```

### Automated Dependency Updates

#### Weekly Security Updates Script

```bash
#!/bin/bash
# weekly-security-updates.sh

set -e

echo "Running weekly security dependency updates..."

# Scan for vulnerabilities
python scripts/dep_scanner.py . --format json --output current-scan.json

# Generate security-only upgrade plan
python scripts/upgrade_planner.py current-scan.json --security-only --output security-upgrades.txt

# Check if security updates are available
if grep -q "URGENT" security-upgrades.txt; then
    echo "Security updates found! Creating automated PR..."
    
    # Create branch
    git checkout -b "automated-security-updates-$(date +%Y%m%d)"
    
    # Apply updates (example for npm)
    npm audit fix --only=prod
    
    # Commit and push
    git add .
    git commit -m "chore: automated security dependency updates"
    git push origin HEAD
    
    # Create PR (using GitHub CLI)
    gh pr create \
        --title "Automated Security Updates" \
        --body-file security-upgrades.txt \
        --label "security,dependencies,automated"
else
    echo "No critical security updates found."
fi
```

## Sample Files

The `assets/` directory contains sample dependency files for testing:

- `sample_package.json`: Node.js project with various dependencies
- `sample_requirements.txt`: Python project dependencies
- `sample_go.mod`: Go module dependencies

The `expected_outputs/` directory contains example reports showing the expected format and content.

## Advanced Usage

### Custom Vulnerability Database

You can extend the built-in vulnerability database by modifying the `_load_vulnerability_database()` method in `dep_scanner.py`:

```python
def _load_vulnerability_database(self):
    """Load vulnerability database from multiple sources."""
    db = self._load_builtin_database()
    
    # Load custom vulnerabilities
    custom_db_path = os.environ.get('CUSTOM_VULN_DB')
    if custom_db_path and os.path.exists(custom_db_path):
        with open(custom_db_path, 'r') as f:
            custom_vulns = json.load(f)
            db.update(custom_vulns)
    
    return db
```

### Custom License Policies

Create custom license policies by modifying the license database:

```python
# Add custom license
custom_license = LicenseInfo(
    name='Custom Internal License',
    spdx_id='CUSTOM-1.0',
    license_type=LicenseType.PROPRIETARY,
    risk_level=RiskLevel.HIGH,
    description='Internal company license',
    restrictions=['Internal use only'],
    obligations=['Attribution required']
)
```

### Multi-Project Analysis

For analyzing multiple projects, create a wrapper script:

```python
#!/usr/bin/env python3
import os
import json
from pathlib import Path

projects = ['/path/to/project1', '/path/to/project2', '/path/to/project3']
results = {}

for project in projects:
    project_name = Path(project).name
    
    # Run vulnerability scan
    scan_result = subprocess.run([
        'python', 'scripts/dep_scanner.py', 
        project, '--format', 'json'
    ], capture_output=True, text=True)
    
    if scan_result.returncode == 0:
        results[project_name] = json.loads(scan_result.stdout)

# Generate consolidated report
with open('consolidated-report.json', 'w') as f:
    json.dump(results, f, indent=2)
```

## Troubleshooting

### Common Issues

1. **Permission Errors**
   ```bash
   chmod +x scripts/*.py
   ```

2. **Python Version Compatibility**
   - Requires Python 3.7 or higher
   - Uses only standard library modules

3. **Large Projects**
   - Use `--quick-scan` for faster analysis
   - Consider excluding large node_modules directories

4. **False Positives**
   - Review vulnerability matches manually
   - Consider version range parsing improvements

### Debug Mode

Enable debug logging by setting environment variable:

```bash
export DEPENDENCY_AUDIT_DEBUG=1
python scripts/dep_scanner.py /your/project
```

## Contributing

1. **Adding New Package Managers**: Extend the `supported_files` dictionary and add corresponding parsers
2. **Vulnerability Database**: Add new CVE entries to the built-in database
3. **License Support**: Add new license types to the license database
4. **Risk Assessment**: Improve risk scoring algorithms

## References

- [SKILL.md](SKILL.md): Comprehensive skill documentation
- [references/](references/): Best practices and compatibility guides
- [assets/](assets/): Sample dependency files for testing
- [expected_outputs/](expected_outputs/): Example reports and outputs

## License

This skill is licensed under the MIT License. See the project license file for details.

---

**Note**: This tool provides automated analysis to assist with dependency management decisions. Always review recommendations and consult with security and legal teams for critical applications.
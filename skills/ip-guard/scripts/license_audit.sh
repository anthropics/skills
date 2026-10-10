#!/usr/bin/env bash
# ip-guard: license_audit.sh
# Detects the project type and runs the appropriate license audit tool.
# Outputs a structured report compatible with ip-guard's provenance block format.
#
# Usage: bash license_audit.sh [--output <file>] [--project-license <license>]
# Example: bash license_audit.sh --project-license MIT --output license-report.md

set -euo pipefail

OUTPUT_FILE="ip-guard-license-report.md"
PROJECT_LICENSE="unknown"

# Parse arguments
while [[ $# -gt 0 ]]; do
  case $1 in
    --output) OUTPUT_FILE="$2"; shift 2 ;;
    --project-license) PROJECT_LICENSE="$2"; shift 2 ;;
    *) echo "Unknown argument: $1"; exit 1 ;;
  esac
done

echo "🛡️  ip-guard license audit starting..."
echo "Project license target: $PROJECT_LICENSE"
echo ""

# Detect project type
detect_project_type() {
  if [ -f "package.json" ]; then echo "node"
  elif [ -f "pyproject.toml" ] || [ -f "requirements.txt" ] || [ -f "setup.py" ]; then echo "python"
  elif [ -f "Cargo.toml" ]; then echo "rust"
  elif [ -f "go.mod" ]; then echo "go"
  elif [ -f "pom.xml" ] || [ -f "build.gradle" ]; then echo "java"
  else echo "unknown"
  fi
}

# Licenses incompatible with common project types
get_incompatible_licenses() {
  local target="$1"
  case "$target" in
    MIT|Apache*|BSD*|ISC) echo "GPL-2.0,GPL-3.0,AGPL-3.0,GPL-2.0-only,GPL-3.0-only,AGPL-3.0-only" ;;
    proprietary|Proprietary|UNLICENSED) echo "GPL-2.0,GPL-3.0,AGPL-3.0,LGPL-2.1,LGPL-3.0,GPL-2.0-only,GPL-3.0-only,AGPL-3.0-only" ;;
    *) echo "" ;;
  esac
}

PROJECT_TYPE=$(detect_project_type)
echo "Detected project type: $PROJECT_TYPE"
echo ""

# Run the appropriate tool
{
  echo "# 🛡️ IP Guard — License Audit Report"
  echo ""
  echo "**Generated:** $(date '+%Y-%m-%d %H:%M')"
  echo "**Project license target:** \`$PROJECT_LICENSE\`"
  echo "**Project type:** $PROJECT_TYPE"
  echo ""
  echo "---"
  echo ""
} > "$OUTPUT_FILE"

case "$PROJECT_TYPE" in
  node)
    if ! command -v npx &> /dev/null; then
      echo "❌ npx not found. Install Node.js to run license audits for this project."
      exit 1
    fi
    echo "Running license-checker for Node.js project..."
    npx --yes license-checker --json 2>/dev/null | python3 -c "
import json, sys

data = json.load(sys.stdin)
incompatible = '$(get_incompatible_licenses "$PROJECT_LICENSE")'.split(',')
project_license = '$PROJECT_LICENSE'

rows = []
warnings = []

for pkg, info in sorted(data.items()):
    lic = info.get('licenses', 'UNKNOWN')
    lic_str = str(lic)
    compatible = '✅'
    if lic_str == 'UNKNOWN' or not lic_str:
        compatible = '⚠️ UNKNOWN'
        warnings.append(f'- {pkg}: license unknown — verify before use')
    elif any(i.strip() in lic_str for i in incompatible if i.strip()):
        compatible = '❌ INCOMPATIBLE'
        warnings.append(f'- {pkg}: {lic_str} is incompatible with {project_license}')
    rows.append(f'| {pkg} | {lic_str} | {compatible} |')

print('## Dependency License Summary')
print()
print('| Package | License | Compatible with ' + project_license + ' |')
print('|---|---|---|')
for r in rows:
    print(r)
print()

if warnings:
    print('## ⚠️ Items Requiring Review')
    print()
    for w in warnings:
        print(w)
    print()
else:
    print('## ✅ No Issues Found')
    print()
    print('All dependencies appear compatible with ' + project_license + '.')
    print()

print(f'**Total packages scanned:** {len(rows)}')
print(f'**Issues found:** {len(warnings)}')
" >> "$OUTPUT_FILE"
    ;;

  python)
    if ! command -v pip-licenses &> /dev/null; then
      echo "pip-licenses not found. Installing..."
      pip install pip-licenses --quiet --break-system-packages 2>/dev/null || \
        pip install pip-licenses --quiet 2>/dev/null || \
        { echo "❌ Could not install pip-licenses. Run: pip install pip-licenses"; exit 1; }
    fi
    echo "Running pip-licenses for Python project..."
    {
      echo "## Dependency License Summary"
      echo ""
      pip-licenses --format=markdown 2>/dev/null
      echo ""
    } >> "$OUTPUT_FILE"
    ;;

  rust)
    if ! command -v cargo-license &> /dev/null; then
      echo "cargo-license not found. Install with: cargo install cargo-license"
      exit 1
    fi
    echo "Running cargo-license for Rust project..."
    {
      echo "## Dependency License Summary"
      echo ""
      cargo license --json 2>/dev/null | python3 -c "
import json, sys
data = json.load(sys.stdin)
print('| Crate | License |')
print('|---|---|')
for pkg in sorted(data, key=lambda x: x.get('name','')):
    print(f'| {pkg.get(\"name\",\"?\")} {pkg.get(\"version\",\"\")} | {pkg.get(\"license\",\"UNKNOWN\")} |')
"
      echo ""
    } >> "$OUTPUT_FILE"
    ;;

  go)
    if ! command -v go-licenses &> /dev/null; then
      echo "go-licenses not found. Install with: go install github.com/google/go-licenses@latest"
      exit 1
    fi
    echo "Running go-licenses for Go project..."
    {
      echo "## Dependency License Summary"
      echo ""
      go-licenses report ./... 2>/dev/null | awk 'BEGIN{print "| Package | License URL |"}{print "| "$1" | "$3" |"}'
      echo ""
    } >> "$OUTPUT_FILE"
    ;;

  *)
    {
      echo "## ⚠️ Project Type Not Detected"
      echo ""
      echo "Could not detect a supported package manager (Node.js, Python, Rust, Go)."
      echo "Manual audit required."
      echo ""
      echo "Supported tools:"
      echo "- Node.js: \`npx license-checker --summary\`"
      echo "- Python: \`pip-licenses --format=markdown\`"
      echo "- Rust: \`cargo license\`"
      echo "- Go: \`go-licenses report ./...\`"
      echo ""
    } >> "$OUTPUT_FILE"
    ;;
esac

# Footer
{
  echo ""
  echo "---"
  echo ""
  echo "*Generated by ip-guard skill v1.0 — this report supports audit trails but is not legal advice.*"
  echo "*For commercial use, consult qualified legal counsel.*"
} >> "$OUTPUT_FILE"

echo ""
echo "✅ Audit complete. Report saved to: $OUTPUT_FILE"

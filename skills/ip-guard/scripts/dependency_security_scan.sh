#!/usr/bin/env bash
# ip-guard — Dependency Security Scan
# Usage: bash dependency_security_scan.sh [--output <file>] [--check-pth]
# Example: bash dependency_security_scan.sh --output security-report.json --check-pth
#
# Auto-detects project type (Python / Node.js / Rust) and:
#   1. Resolves the full transitive dependency tree
#   2. Checks every package against the OSV vulnerability database
#   3. Optionally scans site-packages for suspicious .pth files (Python, --check-pth)
#
# Exit codes:
#   0 — all packages CLEAN
#   1 — one or more QUARANTINED or VULNERABLE findings (❌)
#   2 — one or more ADVISORY-only findings, no ❌ (⚠️)

set -euo pipefail

# ── Defaults ──────────────────────────────────────────────────────────────────
OUTPUT_FILE="ip-guard-security-report.json"
CHECK_PTH=false

# ── Argument parsing ──────────────────────────────────────────────────────────
while [[ $# -gt 0 ]]; do
  case "$1" in
    --output)
      OUTPUT_FILE="$2"; shift 2 ;;
    --check-pth)
      CHECK_PTH=true; shift ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: bash dependency_security_scan.sh [--output <file>] [--check-pth]" >&2
      exit 1 ;;
  esac
done

# ── Project type detection ────────────────────────────────────────────────────
detect_project_type() {
  if [ -f "package.json" ]; then echo "node"
  elif [ -f "pyproject.toml" ] || [ -f "requirements.txt" ] || [ -f "setup.py" ]; then echo "python"
  elif [ -f "Cargo.toml" ]; then echo "rust"
  else echo "unknown"
  fi
}

PROJECT_TYPE=$(detect_project_type)
SCANNED_AT=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
TMPDIR_SCAN=$(mktemp -d)
DEPTREE_FILE="$TMPDIR_SCAN/deptree.json"
AUDIT_FILE="$TMPDIR_SCAN/audit.json"

echo "🔒 ip-guard — Dependency Security Scan"
echo "Project type: $PROJECT_TYPE"
echo "Output: $OUTPUT_FILE"
echo ""

# ── Python ────────────────────────────────────────────────────────────────────
run_python() {
  echo "📦 Installing scan tools (pip-audit, pipdeptree)..."
  pip install --quiet pip-audit pipdeptree 2>/dev/null || {
    echo "❌ Failed to install pip-audit / pipdeptree. Run: pip install pip-audit pipdeptree" >&2
    exit 1
  }

  echo "🌳 Resolving transitive dependency tree..."
  pipdeptree --json > "$DEPTREE_FILE"

  echo "🔍 Scanning against OSV database..."
  pip-audit --format=json --output "$AUDIT_FILE" 2>/dev/null || true

  # Parse and emit unified JSON via inline Python
  python3 - <<PYEOF
import json, sys, os

deptree = json.load(open("$DEPTREE_FILE"))
try:
    audit_raw = json.load(open("$AUDIT_FILE"))
    # pip-audit JSON: list of {name, version, vulns: [{id, fix_versions, aliases}]}
    audit_map = {}
    for entry in audit_raw.get("dependencies", []):
        vulns = entry.get("vulns", [])
        if vulns:
            key = entry["name"].lower()
            audit_map[key] = vulns[0]["id"] if vulns else None
except Exception:
    audit_map = {}

# Flatten transitive tree: {pkg_name: {version, installed_via}}
flat = {}
def walk(pkg, chain="(direct)"):
    name = pkg["package_name"].lower()
    ver  = pkg["installed_version"]
    if name not in flat:
        flat[name] = {"version": ver, "installed_via": chain}
    for dep in pkg.get("dependencies", []):
        walk(dep, f"{pkg['package_name']} → {dep['package_name']}")

for top in deptree:
    walk(top)

findings = []
for name, info in flat.items():
    advisory = audit_map.get(name)
    if advisory:
        status = "VULNERABLE"
    else:
        status = "CLEAN"
    findings.append({
        "package": name,
        "version": info["version"],
        "installed_via": info["installed_via"],
        "advisory": advisory or "None",
        "status": status,
    })

total = len(flat)
direct = sum(1 for v in flat.values() if v["installed_via"] == "(direct)")

result = {
    "project_type": "python",
    "scanned_at": "$SCANNED_AT",
    "total_packages": total,
    "direct_packages": direct,
    "findings": findings,
    "pth_findings": [],
}

with open("$OUTPUT_FILE", "w") as f:
    json.dump(result, f, indent=2)

print(json.dumps(result, indent=2))
PYEOF
}

# ── Node.js ───────────────────────────────────────────────────────────────────
run_node() {
  command -v npm >/dev/null 2>&1 || { echo "❌ npm not found." >&2; exit 1; }

  echo "🌳 Resolving transitive dependency tree..."
  npm ls --all --json > "$DEPTREE_FILE" 2>/dev/null || true

  echo "🔍 Scanning against npm advisory database..."
  npm audit --json > "$AUDIT_FILE" 2>/dev/null || true

  python3 - <<PYEOF
import json, sys

try:
    deptree = json.load(open("$DEPTREE_FILE"))
except Exception:
    deptree = {}
try:
    audit_raw = json.load(open("$AUDIT_FILE"))
except Exception:
    audit_raw = {}

# Build advisory map: {package_name: advisory_id}
advisory_map = {}
for vuln_id, vuln in audit_raw.get("vulnerabilities", {}).items():
    advisory_map[vuln["name"].lower()] = vuln_id

# Flatten npm dependency tree
flat = {}
def walk(deps, chain="(direct)"):
    for name, info in deps.items():
        key = name.lower()
        if key not in flat:
            flat[key] = {"version": info.get("version", "unknown"), "installed_via": chain}
        nested = info.get("dependencies", {})
        if nested:
            walk(nested, f"{name} → ...")

walk(deptree.get("dependencies", {}))

findings = []
for name, info in flat.items():
    advisory = advisory_map.get(name)
    status = "VULNERABLE" if advisory else "CLEAN"
    findings.append({
        "package": name,
        "version": info["version"],
        "installed_via": info["installed_via"],
        "advisory": advisory or "None",
        "status": status,
    })

total = len(flat)
direct = sum(1 for v in flat.values() if v["installed_via"] == "(direct)")

result = {
    "project_type": "node",
    "scanned_at": "$SCANNED_AT",
    "total_packages": total,
    "direct_packages": direct,
    "findings": findings,
    "pth_findings": [],
}

with open("$OUTPUT_FILE", "w") as f:
    json.dump(result, f, indent=2)

print(json.dumps(result, indent=2))
PYEOF
}

# ── Rust ──────────────────────────────────────────────────────────────────────
run_rust() {
  command -v cargo >/dev/null 2>&1 || { echo "❌ cargo not found." >&2; exit 1; }

  echo "🌳 Resolving transitive dependency tree..."
  cargo tree --format="{p}" 2>/dev/null > "$TMPDIR_SCAN/deptree.txt" || {
    echo "❌ cargo tree failed. Ensure Cargo.lock exists." >&2; exit 1
  }

  echo "🔍 Scanning against RustSec advisory database..."
  if command -v cargo-audit >/dev/null 2>&1; then
    cargo audit --json > "$AUDIT_FILE" 2>/dev/null || true
  else
    echo "{}" > "$AUDIT_FILE"
    echo "⚠️  cargo-audit not installed. Run: cargo install cargo-audit"
    echo "    Continuing without advisory data."
  fi

  python3 - <<PYEOF
import json, re

# Parse cargo tree flat output: "crate v0.1.0" lines (strip indent markers)
flat = {}
with open("$TMPDIR_SCAN/deptree.txt") as f:
    for line in f:
        line = line.strip().lstrip("│├└─ ")
        m = re.match(r"^(\S+)\s+v([\d.]+.*?)(?:\s.*)?$", line)
        if m:
            name = m.group(1).lower()
            ver  = m.group(2)
            if name not in flat:
                flat[name] = {"version": ver, "installed_via": "(resolved by cargo tree)"}

try:
    audit_raw = json.load(open("$AUDIT_FILE"))
    vuln_list = audit_raw.get("vulnerabilities", {}).get("list", [])
    advisory_map = {v["advisory"]["package"].lower(): v["advisory"]["id"] for v in vuln_list}
except Exception:
    advisory_map = {}

findings = []
for name, info in flat.items():
    advisory = advisory_map.get(name)
    status = "VULNERABLE" if advisory else "CLEAN"
    findings.append({
        "package": name,
        "version": info["version"],
        "installed_via": info["installed_via"],
        "advisory": advisory or "None",
        "status": status,
    })

result = {
    "project_type": "rust",
    "scanned_at": "$SCANNED_AT",
    "total_packages": len(flat),
    "direct_packages": len(flat),  # cargo tree doesn't differentiate easily
    "findings": findings,
    "pth_findings": [],
}

with open("$OUTPUT_FILE", "w") as f:
    json.dump(result, f, indent=2)

print(json.dumps(result, indent=2))
PYEOF
}

# ── Unknown project type ───────────────────────────────────────────────────────
run_unknown() {
  cat >&2 <<EOF
⚠️  Could not detect project type. No manifest file found.

Supported project types and required manifest files:
  Python  — requirements.txt, pyproject.toml, or setup.py
  Node.js — package.json
  Rust    — Cargo.toml

Run this script from the project root directory, or install the appropriate manifest file first.
EOF
  exit 1
}

# ── .pth file detection (Python only) ─────────────────────────────────────────
check_pth_files() {
  echo ""
  echo "🔎 Scanning site-packages for suspicious .pth files..."

  SITE_PKGS=$(python3 -c "import site; print('\n'.join(site.getsitepackages()))" 2>/dev/null || true)
  PTH_FINDINGS=()

  if [ -z "$SITE_PKGS" ]; then
    echo "⚠️  Could not locate site-packages directory."
    return
  fi

  while IFS= read -r site_dir; do
    [ -d "$site_dir" ] || continue
    while IFS= read -r pth_file; do
      # Flag .pth files that contain executable patterns
      if grep -qE "(import |exec\(|os\.|subprocess\.|__import__)" "$pth_file" 2>/dev/null; then
        PTH_FINDINGS+=("$pth_file")
        echo "❌ Suspicious .pth file: $pth_file"
        grep -nE "(import |exec\(|os\.|subprocess\.|__import__)" "$pth_file" | head -5
      fi
    done < <(find "$site_dir" -maxdepth 1 -name "*.pth" 2>/dev/null)
  done <<< "$SITE_PKGS"

  if [ ${#PTH_FINDINGS[@]} -eq 0 ]; then
    echo "✅ No suspicious .pth files found."
  else
    echo ""
    echo "❌ ${#PTH_FINDINGS[@]} suspicious .pth file(s) detected."
    echo "   These files execute code on every Python process startup without requiring an import."
    echo "   See references/dependency-security.md — .pth Persistence section."
    # Inject into output JSON
    python3 - <<PYEOF
import json
data = json.load(open("$OUTPUT_FILE"))
data["pth_findings"] = $(printf '%s\n' "${PTH_FINDINGS[@]+"${PTH_FINDINGS[*]}"}" | python3 -c "import sys,json; lines=[l.strip() for l in sys.stdin if l.strip()]; print(json.dumps(lines))")
json.dump(data, open("$OUTPUT_FILE", "w"), indent=2)
PYEOF
  fi
}

# ── Run the appropriate handler ───────────────────────────────────────────────
case "$PROJECT_TYPE" in
  python)  run_python ;;
  node)    run_node ;;
  rust)    run_rust ;;
  unknown) run_unknown ;;
esac

if $CHECK_PTH && [ "$PROJECT_TYPE" = "python" ]; then
  check_pth_files
fi

# ── Summarize and set exit code ───────────────────────────────────────────────
python3 - <<PYEOF
import json, sys

data = json.load(open("$OUTPUT_FILE"))
findings = data.get("findings", [])
total    = data["total_packages"]
direct   = data["direct_packages"]

critical = [f for f in findings if f["status"] in ("QUARANTINED", "VULNERABLE")]
advisory = [f for f in findings if f["status"] == "ADVISORY"]
pth      = data.get("pth_findings", [])

print()
print("=" * 60)
print(f"🔒 DEPENDENCY SECURITY SCAN SUMMARY")
print(f"   Scanned {total} packages ({direct} direct, {total - direct} transitive)")
print()

if critical:
    print(f"❌ {len(critical)} CRITICAL finding(s):")
    for f in critical:
        print(f"   • {f['package']} {f['version']} — {f['advisory']} [{f['status']}]")
        print(f"     Installed via: {f['installed_via']}")
elif advisory:
    print(f"⚠️  {len(advisory)} advisory finding(s) — no known active exploits:")
    for f in advisory:
        print(f"   • {f['package']} {f['version']} — {f['advisory']}")
else:
    print("✅ No advisories found.")

if pth:
    print()
    print(f"❌ {len(pth)} suspicious .pth file(s) detected (see above)")

print()
print(f"Report saved to: $OUTPUT_FILE")
print("=" * 60)

if critical or pth:
    sys.exit(1)
elif advisory:
    sys.exit(2)
else:
    sys.exit(0)
PYEOF

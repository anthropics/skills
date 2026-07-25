#!/usr/bin/env python3
"""Validate a Kubernetes CRD YAML against operator-pattern best practices.

Checks for status subresource, structural schema, conditions support, printer
columns, version policy, and other operator-grade design rules. Stdlib-only —
parses YAML via a minimal embedded reader (no PyYAML dependency).
"""
import argparse
import json
import os
import re
import sys

CHECKS = [
    ("status_subresource", "Each version must declare subresources.status (otherwise status updates loop spec reconciles)"),
    ("storage_version", "Exactly one version must be storage:true"),
    ("served_version", "At least one version must be served:true"),
    ("schema_present", "Each version must declare schema.openAPIV3Schema"),
    ("schema_typed", "Schema must declare 'type: object' at root (no x-kubernetes-preserve-unknown-fields at root)"),
    ("conditions_array", "Schema should declare a conditions array under status (for metav1.Conditions)"),
    ("printer_columns", "additionalPrinterColumns should include Age and a status indicator"),
    ("scope", "scope should be Namespaced unless cluster-scoped is justified"),
    ("singular_listkind", "names.singular and names.listKind must be declared"),
]


def _load_yaml_minimal(path):
    """Yield top-level YAML documents from a multi-doc file as text blocks.

    Stdlib-only — splits on '---' separators. We grep relevant fields with
    regex rather than fully parse. Crude but enough for the structural
    checks below; a full YAML parser would be the upgrade path."""
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    docs = re.split(r"^---\s*$", text, flags=re.MULTILINE)
    return [d for d in docs if d.strip()]


def _is_crd_doc(doc):
    return bool(re.search(r"^kind:\s*CustomResourceDefinition\s*$", doc, re.MULTILINE))


def _check_one(doc, path):
    findings = []
    has_status_sub = bool(re.search(r"subresources:\s*\n\s*status:\s*\{?\s*\}?", doc))
    if not has_status_sub:
        findings.append(("FAIL", "status_subresource", "no subresources.status block found"))
    storage_count = len(re.findall(r"storage:\s*true\b", doc))
    if storage_count != 1:
        findings.append(("FAIL", "storage_version", f"expected exactly 1 storage:true, found {storage_count}"))
    served_count = len(re.findall(r"served:\s*true\b", doc))
    if served_count < 1:
        findings.append(("FAIL", "served_version", "no served:true version"))
    if "openAPIV3Schema" not in doc:
        findings.append(("FAIL", "schema_present", "no openAPIV3Schema declared"))
    if re.search(r"x-kubernetes-preserve-unknown-fields:\s*true", doc):
        findings.append(("WARN", "schema_typed", "x-kubernetes-preserve-unknown-fields: true present (defeats validation)"))
    if "conditions" not in doc.lower():
        findings.append(("WARN", "conditions_array", "no conditions array referenced (Karpathy: declare an explicit shape)"))
    if "additionalPrinterColumns" not in doc:
        findings.append(("WARN", "printer_columns", "no additionalPrinterColumns (kubectl get UX is poor)"))
    elif not re.search(r"name:\s*Age\b", doc):
        findings.append(("WARN", "printer_columns", "additionalPrinterColumns missing Age column"))
    if not re.search(r"^\s*scope:\s*\w+", doc, re.MULTILINE):
        findings.append(("WARN", "scope", "scope not explicitly set"))
    if not re.search(r"^\s*singular:\s*[\w<]", doc, re.MULTILINE):
        findings.append(("WARN", "singular_listkind", "names.singular not declared"))
    if not re.search(r"^\s*listKind:\s*[\w<]", doc, re.MULTILINE):
        findings.append(("WARN", "singular_listkind", "names.listKind not declared"))
    return findings


def _walk_yaml_files(root):
    if os.path.isfile(root):
        yield root
        return
    for r, _, files in os.walk(root):
        for f in files:
            if f.endswith((".yaml", ".yml")):
                yield os.path.join(r, f)


def audit(target):
    results = []
    for path in _walk_yaml_files(target):
        for doc in _load_yaml_minimal(path):
            if not _is_crd_doc(doc):
                continue
            kind_match = re.search(r"kind:\s*(\w+)\s*$", doc, re.MULTILINE)
            crd_kind = kind_match.group(1) if kind_match else "?"
            name_match = re.search(r"^\s+name:\s*([\w.\-]+)\s*$", doc, re.MULTILINE)
            crd_name = name_match.group(1) if name_match else os.path.basename(path)
            findings = _check_one(doc, path)
            results.append({"path": path, "name": crd_name, "kind": crd_kind, "findings": findings})
    return results


def render_text(results):
    if not results:
        print("No CRD documents found.")
        return 0
    fails = sum(1 for r in results for f in r["findings"] if f[0] == "FAIL")
    warns = sum(1 for r in results for f in r["findings"] if f[0] == "WARN")
    print(f"CRD Validator — {len(results)} CRD(s) inspected, {fails} FAIL, {warns} WARN")
    print("")
    for r in results:
        print(f"== {r['name']}  ({r['path']})")
        if not r["findings"]:
            print("   PASS: all checks green")
            continue
        for level, key, msg in r["findings"]:
            print(f"   [{level}] {key}: {msg}")
        print("")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--crd", required=True, help="Path to a CRD YAML file or a directory of YAMLs")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    args = ap.parse_args()

    if not os.path.exists(args.crd):
        print(f"ERROR: not found: {args.crd}", file=sys.stderr)
        return 2
    results = audit(args.crd)
    if args.format == "json":
        print(json.dumps(results, indent=2))
        return 0
    return render_text(results)


if __name__ == "__main__":
    sys.exit(main())

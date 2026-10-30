#!/usr/bin/env python3
"""Compute DRYness = unique LOC / total LOC.

Requires `scc` to be installed (it reports ULOC in JSON). If scc is not
available, prints `DRYness:unknown` and exits 0 — callers should skip
the deflator rather than invent a number.

Usage: python3 scripts/compute_dryness.py [path]
"""
import json
import shutil
import subprocess
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "."

if not shutil.which("scc"):
    print("SLOC:unknown ULOC:unknown DRYness:unknown")
    sys.exit(0)

try:
    out = subprocess.check_output(["scc", "--format=json", path], timeout=60)
    data = json.loads(out)
except (subprocess.CalledProcessError, subprocess.TimeoutExpired, json.JSONDecodeError):
    print("SLOC:unknown ULOC:unknown DRYness:unknown")
    sys.exit(0)

total = sum(lang["Code"] for lang in data)
# scc reports ULOC at the top level summary in newer versions; fall back to per-language
uniq = sum(lang.get("ULOC", lang["Code"]) for lang in data)
if total == 0:
    print("SLOC:0 ULOC:0 DRYness:unknown")
else:
    print(f"SLOC:{total} ULOC:{uniq} DRYness:{uniq/total:.2f}")

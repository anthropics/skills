#!/usr/bin/env python3
"""An OVERTIGHT check - rejects everything, so a green is impossible.

It demands semver with a build suffix, which neither fixture has. A gate nobody can pass
gets switched off, and then there is no gate at all.
"""
import json, re, sys
doc = json.load(open(sys.argv[1]))
if not re.fullmatch(r"\d+\.\d+\.\d+\+\w+", doc.get("version", "")):
    print("FAIL version must be X.Y.Z+build")
    sys.exit(1)
print("PASS")

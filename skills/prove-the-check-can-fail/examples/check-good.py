#!/usr/bin/env python3
"""A check that actually works: version must be a non-empty string."""
import json, sys
doc = json.load(open(sys.argv[1]))
v = doc.get("version", "")
if not isinstance(v, str) or not v.strip():
    print("FAIL version is empty")
    sys.exit(1)
print("PASS version =", v)

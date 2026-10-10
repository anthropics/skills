#!/usr/bin/env python3
"""A BLIND check - the kind this harness exists to catch.

It only verifies that the KEY EXISTS, not that the value is usable. An empty string has
the key, so the known-bad input sails through. This is the single most common way a check
lies: it asserts presence where the requirement was validity.
"""
import json, sys
doc = json.load(open(sys.argv[1]))
if "version" not in doc:
    print("FAIL version key missing")
    sys.exit(1)
print("PASS version key present")

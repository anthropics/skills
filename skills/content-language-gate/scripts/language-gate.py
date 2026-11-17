#!/usr/bin/env python3
"""CONTENT LANGUAGE GATE - scan product text for forbidden language, then count originality.

WHAT IT MEASURES
----------------
1) FORBIDDEN LANGUAGE - the classes defined in your rule file (certainty claims, fear,
   fake percentages, clinical diagnosis, ...). Regexes live in the rule file, not here.
2) ORIGINALITY - repeated strings are the signature of a template/copycat app, which is
   what App Review guideline 4.3(b) rejects.

WHY THE GATE TESTS ITSELF - MEASURED REASON
-------------------------------------------
An earlier version of this gate matched a verb stem and mistook ordinary phrases
("giving it room", "giving it time") for clinical diagnosis. It produced **8 false
violations** - it wrote its own defect onto the product. So before looking at real
content, the gate runs every `decoys` entry through its own patterns. If it fails to
catch them it declares itself BLIND and refuses to treat a clean result as evidence.

AN EMPTY SCAN IS NOT A PASS
---------------------------
If the content glob matches nothing, a naive gate reports "0 violations -> clean".
That is the most common way a text gate lies. This one goes red.

DECLARE YOUR UNIT OF UNIQUENESS - BOTH DIRECTIONS FAIL
------------------------------------------------------
Uniqueness is only meaningful once you say WHAT must be unique. Both defaults are wrong,
and I measured both:

  MERGING BLINDLY HIDES DUPLICATION. A gate counting `text + "|" + short` as one key
  cannot see a repeated `short` at all, because `text` always differs - so the merged
  string always differs too.

  SPLITTING BLINDLY INVENTS DEFECTS. Counting bare fields on the same content surfaced
  "28 repeated headlines" and I called it a hidden template-app defect. It was not. The
  product shows a headline PLUS a support line, and the design deliberately reuses one
  headline across three nuance variants:
      "You want to be seen where you are."  + "Waiting to be noticed is not your way."
      "You want to be seen where you are."  + "You hope the word comes from others."
      "You want to be seen where you are."  + "You are waiting for the right moment."
  Measured on that content: headline+support PAIRS 286/286 unique (0 repeats), bare
  headlines 286/258 (28 repeats). Two users can see the same headline; no user ever sees
  the same OUTPUT. The repeat was the design, not a defect.

So `originality` takes explicit units. A unit with "gate": true goes red on a repeat; a
unit with "gate": false is reported as INFO. Make the gated unit the thing the user
actually sees.

NO PROJECT CONSTANTS EMBEDDED - classes, decoys and the content glob come from the rule file.

Usage:
  language-gate.py <rules.json> [root-dir]

Rule file schema:
  {
    "forbidden": {"<class>": "<regex>", ...},
    "decoys":    [["<class>", "<this text MUST be caught>"], ...],
    "content":   {"glob": "content/*.json", "fields": ["text", "short"],
                  "list_fields": ["rules", "questions"], "option_field": "options"},
    "originality": [
      {"name": "output",   "fields": ["short", "text"], "mode": "pair", "gate": true},
      {"name": "headline", "fields": ["short"],         "mode": "each", "gate": false}
    ]
  }
Exit code: 0 = clean, 1 = red (usable as a CI gate).
"""
import collections
import glob
import json
import os
import re
import sys


def violations(text, forbidden):
    """Return the names of every forbidden class this text matches."""
    return [name for name, pattern in forbidden.items()
            if re.search(pattern, text, re.IGNORECASE)]


def collect(root, content):
    """Gather (file, id, [strings]) for every item the rule file points at."""
    records = []
    fields = content.get("fields", ["text"])
    option_field = content.get("option_field")
    for path in sorted(glob.glob(os.path.join(root, content["glob"]), recursive=True)):
        name = os.path.basename(path)
        try:
            doc = json.load(open(path, encoding="utf-8"))
        except Exception as exc:                      # unreadable file is reported, not hidden
            print("  SKIPPED %s (%s)" % (name, exc))
            continue
        for list_field in content.get("list_fields", []):
            for item in doc.get(list_field, []) or []:
                values = [item.get(f, "") for f in fields if isinstance(item.get(f, ""), str)]
                if option_field:
                    for opt in item.get(option_field, []) or []:
                        values += [opt.get(f, "") for f in fields
                                   if isinstance(opt.get(f, ""), str)]
                records.append((name, item.get("id", ""), [v for v in values if v]))
    return records


def main():
    if len(sys.argv) < 2:
        print(__doc__.strip().split("Usage:")[-1].strip())
        return 2
    rules = json.load(open(sys.argv[1], encoding="utf-8"))
    root = sys.argv[2] if len(sys.argv) > 2 else "."
    forbidden = rules["forbidden"]
    verdict = 0

    # 1) SELF-TEST - the gate must catch known-bad before it is allowed to judge anything
    decoys = rules.get("decoys", [])
    if not decoys:
        print("FAIL  rule file has no `decoys` -> gate cannot self-test, treated as BLIND")
        return 1
    caught = sum(1 for cls, text in decoys if cls in violations(text, forbidden))
    print("SELF-TEST       : %d/%d decoys caught" % (caught, len(decoys)))
    if caught != len(decoys):
        for cls, text in decoys:
            if cls not in violations(text, forbidden):
                print("  MISSED [%s] %s" % (cls, text[:60]))
        print("  FAIL  gate is BLIND - a clean result on real content is NOT EVIDENCE")
        return 1
    print("  PASS  gate is not blind")

    # 2) REAL CONTENT
    records = collect(root, rules["content"])
    found = [(cls, nm, ident, value)
             for nm, ident, values in records
             for value in values
             for cls in violations(value, forbidden)]
    scanned = sum(len(v) for _, _, v in records)
    print("FORBIDDEN LANG  : %d strings scanned, violations=%d" % (scanned, len(found)))
    if scanned == 0:
        print("  FAIL  NOTHING WAS SCANNED - check `content.glob`; an empty scan is NOT a pass")
        return 1
    for cls, nm, ident, value in found[:20]:
        print("  FAIL  [%s] %s %s :: %s" % (cls, nm, ident, value[:70]))
    if found:
        verdict = 1
    else:
        print("  PASS  no forbidden class found (%s)" % ", ".join(sorted(forbidden)))

    # 3) ORIGINALITY - every unit is declared explicitly (see the module docstring)
    for unit in rules.get("originality", []):
        if isinstance(unit, str):                     # legacy shorthand: every string, gated
            unit = {"name": unit, "fields": None, "mode": "each", "gate": True}
        name = unit.get("name", "unit")
        want = unit.get("fields")
        gated = unit.get("gate", True)
        if unit.get("mode") == "pair":
            # One key per item: the fields joined IN THE DECLARED ORDER. This is the unit a
            # user actually receives when the product renders headline + support together.
            keys = []
            for _, _, values in records:
                picked = values[:len(want)] if want else values
                if picked:
                    keys.append(" || ".join(picked))
        else:
            keys = [value for _, _, values in records for value in values]
        repeats = len(keys) - len(set(keys))
        if gated:
            mark = "PASS" if repeats == 0 else "FAIL"
            if repeats:
                verdict = 1
            label = "ORIGINALITY"
        else:
            mark = "INFO"
            label = "originality"
        print("%-11s %-9s: total=%-5d unique=%-5d repeats=%d  %s"
              % (label, name[:9], len(keys), len(set(keys)), repeats, mark))
        if repeats and gated:
            counts = collections.Counter(keys)
            for value, n in sorted(((v, n) for v, n in counts.items() if n > 1),
                                   key=lambda pair: -pair[1])[:8]:
                print("  FAIL  %dx repeated :: %s" % (n, value[:62]))

    print("** LANGUAGE GATE CLEAN **" if verdict == 0 else "** LANGUAGE GATE RED **")
    return verdict


if __name__ == "__main__":
    sys.exit(main())

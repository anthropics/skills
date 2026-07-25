#!/usr/bin/env python3
"""family_resolver.py — Deduplicate same-invention patent filings across jurisdictions.

Stdlib-only. The same invention is often filed in multiple jurisdictions
(US + EP + JP + CN of one underlying invention). They share a "family" identifier
or a common priority application number.

Without family resolution, a multi-jurisdiction search returns the same invention
multiple times — inflating the perceived prior-art set and wasting reviewer
attention.

Family resolution rules:

  1. If two patents share the same `family_id`, they're family members
  2. If two patents share the same `priority_number`, they're family members
  3. If two patents share the same `priority_date` AND have ≥80% applicant overlap
     AND ≥80% inventor overlap → likely family (heuristic, flag with confidence)

For each family: surface ONE representative member (typically earliest priority OR
US member for US-context users) and list all family-member jurisdictions.

NO LLM CALLS. Pure JSON aggregation + heuristic clustering.

Input file format (`--hits-file`):
[
  {
    "patent_num": "US10000000B2",
    "title": "...",
    "family_id": "F12345678",
    "priority_number": "US15/123,456",
    "priority_date": "2018-03-15",
    "filing_date": "2019-03-14",
    "publication_date": "2020-09-15",
    "grant_date": "2022-01-10",
    "jurisdiction": "US",
    "assignee": "Acme Corp",
    "inventors": ["Smith, J", "Jones, K"]
  }
]

Usage:
    python family_resolver.py --hits-file /tmp/hits.json
    python family_resolver.py --hits-file /tmp/hits.json --output json
    python family_resolver.py --sample
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Set


SAMPLE_HITS = [
    {
        "patent_num": "US10000000B2",
        "title": "Machine learning sepsis prediction system",
        "family_id": "F12345678",
        "priority_number": "US15/123,456",
        "priority_date": "2018-03-15",
        "filing_date": "2019-03-14",
        "jurisdiction": "US",
        "assignee": "Acme Corp",
        "inventors": ["Smith, J", "Jones, K"],
    },
    {
        "patent_num": "EP3500000B1",
        "title": "Système de prédiction sépticémie par apprentissage automatique",
        "family_id": "F12345678",  # same family
        "priority_number": "US15/123,456",  # same priority
        "priority_date": "2018-03-15",
        "filing_date": "2019-03-14",
        "jurisdiction": "EP",
        "assignee": "Acme Corp",
        "inventors": ["Smith, J", "Jones, K"],
    },
    {
        "patent_num": "JP2020100000A",
        "title": "敗血症予測システム",
        "family_id": "F12345678",  # same family
        "priority_number": "US15/123,456",
        "priority_date": "2018-03-15",
        "filing_date": "2019-03-14",
        "jurisdiction": "JP",
        "assignee": "Acme Corp",
        "inventors": ["Smith, J", "Jones, K"],
    },
    {
        "patent_num": "US10500000B2",
        "title": "Different sepsis prediction method using LSTMs",
        "family_id": "F87654321",  # DIFFERENT family
        "priority_number": "US16/200,000",
        "priority_date": "2019-08-22",
        "filing_date": "2020-08-21",
        "jurisdiction": "US",
        "assignee": "Beta Inc",
        "inventors": ["Lee, M"],
    },
    {
        "patent_num": "WO2020/123456",
        "title": "PCT application: sepsis prediction with multi-modal data",
        "family_id": "F87654321",  # same family as US10500000
        "priority_number": "US16/200,000",
        "priority_date": "2019-08-22",
        "jurisdiction": "WO",
        "assignee": "Beta Inc",
        "inventors": ["Lee, M"],
    },
    {
        "patent_num": "US11000000B1",
        "title": "Yet another sepsis ML approach",
        "family_id": "F11111111",  # alone
        "priority_number": "US17/300,000",
        "priority_date": "2021-01-10",
        "jurisdiction": "US",
        "assignee": "Gamma LLC",
        "inventors": ["Park, S", "Kim, J"],
    },
]


def jaccard_similarity(set1: Set[str], set2: Set[str]) -> float:
    if not set1 and not set2:
        return 1.0
    if not set1 or not set2:
        return 0.0
    inter = len(set1 & set2)
    union = len(set1 | set2)
    return inter / union if union > 0 else 0.0


def normalize_name(name: str) -> str:
    """Normalize assignee/inventor names for comparison."""
    return name.lower().strip().replace(",", "").replace(".", "")


def resolve_families(hits: List[Dict[str, Any]]) -> Dict[str, Any]:
    # Pass 1: group by exact family_id
    by_family: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    no_family_id: List[Dict[str, Any]] = []
    for h in hits:
        fid = h.get("family_id")
        if fid:
            by_family[fid].append(h)
        else:
            no_family_id.append(h)

    # Pass 2: group remaining by exact priority_number
    if no_family_id:
        by_priority: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        unmatched: List[Dict[str, Any]] = []
        for h in no_family_id:
            pn = h.get("priority_number")
            if pn:
                by_priority[pn].append(h)
            else:
                unmatched.append(h)
        # Add to family map using priority_number as fallback ID
        for pn, group in by_priority.items():
            by_family[f"PRI:{pn}"] = group
        # Pass 3: heuristic clustering for unmatched (priority_date + applicant + inventor overlap)
        for h in unmatched:
            matched = False
            for fid, group in list(by_family.items()):
                rep = group[0]
                if (h.get("priority_date") == rep.get("priority_date")
                    and jaccard_similarity({normalize_name(h.get("assignee", ""))}, {normalize_name(rep.get("assignee", ""))}) >= 0.8
                    and jaccard_similarity({normalize_name(i) for i in h.get("inventors", [])}, {normalize_name(i) for i in rep.get("inventors", [])}) >= 0.8):
                    by_family[fid].append(h)
                    matched = True
                    break
            if not matched:
                # Solo — use patent_num as family_id
                by_family[f"SOLO:{h.get('patent_num', 'unknown')}"] = [h]

    # For each family: pick representative (earliest priority date, prefer US member if available)
    families: List[Dict[str, Any]] = []
    for fid, members in by_family.items():
        sorted_members = sorted(members, key=lambda m: (m.get("priority_date", "9999"), 0 if m.get("jurisdiction") == "US" else 1))
        rep = sorted_members[0]
        jurisdictions = sorted({m.get("jurisdiction", "?") for m in members})
        family = {
            "family_id": fid,
            "representative": {
                "patent_num": rep.get("patent_num"),
                "title": rep.get("title"),
                "assignee": rep.get("assignee"),
                "priority_date": rep.get("priority_date"),
                "filing_date": rep.get("filing_date"),
                "jurisdiction": rep.get("jurisdiction"),
            },
            "family_member_count": len(members),
            "jurisdictions": jurisdictions,
            "all_patent_nums": [m.get("patent_num") for m in members],
        }
        families.append(family)

    families.sort(key=lambda f: f["representative"].get("priority_date", "9999"))

    return {
        "input_hits": len(hits),
        "unique_families": len(families),
        "deduplication_savings": len(hits) - len(families),
        "families": families,
    }


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"Family resolution complete:")
    out.append(f"  Input hits:              {result['input_hits']}")
    out.append(f"  Unique families:         {result['unique_families']}")
    out.append(f"  Deduplication savings:   {result['deduplication_savings']} duplicate hits removed")
    out.append("")
    out.append("Families (representative + all jurisdictions):")
    for i, f in enumerate(result["families"], 1):
        rep = f["representative"]
        out.append(f"")
        out.append(f"  Family {i} (id: {f['family_id']}):")
        out.append(f"    Representative: {rep['patent_num']} ({rep['jurisdiction']}, priority {rep['priority_date']})")
        out.append(f"    Title:          {rep['title'][:80]}")
        out.append(f"    Assignee:       {rep['assignee']}")
        out.append(f"    Family size:    {f['family_member_count']} member(s) across {len(f['jurisdictions'])} jurisdiction(s)")
        out.append(f"    Jurisdictions:  {', '.join(f['jurisdictions'])}")
        if f['family_member_count'] > 1:
            out.append(f"    All members:    {', '.join(f['all_patent_nums'])}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--hits-file", help="Path to JSON file with patent hits")
    parser.add_argument("--sample", action="store_true", help="Run on embedded sample")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = resolve_families(SAMPLE_HITS)
    elif args.hits_file:
        p = Path(args.hits_file)
        if not p.exists():
            print(f"error: {args.hits_file} not found", file=sys.stderr); return 2
        try:
            hits = json.loads(p.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            print(f"error: invalid JSON: {e}", file=sys.stderr); return 2
        result = resolve_families(hits)
    else:
        parser.print_help(); return 0

    if args.output == "json":
        print(json.dumps(result, indent=2, default=str))
    else:
        print(render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

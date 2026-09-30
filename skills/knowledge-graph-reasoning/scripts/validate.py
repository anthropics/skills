#!/usr/bin/env python3
"""
Adversarial fact validation for knowledge graphs.
Checks new facts against existing graph for contradictions,
antonyms, negations, and consistency issues.

Part of knowledge-graph-reasoning skill by Swarm Labs USA
https://github.com/michaelwinczuk/knowledge-graph-reasoning
"""

import json
import sys
import re
from typing import Any

# Common antonym pairs for relationship detection
ANTONYM_PAIRS = {
    "increase": "decrease", "improve": "worsen", "enable": "disable",
    "create": "destroy", "support": "oppose", "accelerate": "decelerate",
    "strengthen": "weaken", "expand": "contract", "advance": "retreat",
    "cause": "prevent", "require": "exclude", "allow": "forbid",
    "faster": "slower", "better": "worse", "higher": "lower",
    "more": "less", "above": "below", "before": "after",
}
# Build reverse lookup
ANTONYM_PAIRS.update({v: k for k, v in list(ANTONYM_PAIRS.items())})

NEGATION_PATTERNS = [
    r"\bnot\b", r"\bnever\b", r"\bno\b", r"\bnone\b",
    r"\bdoes not\b", r"\bdoesn't\b", r"\bcannot\b", r"\bcan't\b",
    r"\bwithout\b", r"\bfails to\b", r"\blacks?\b", r"\babsence\b",
]


def load_graph(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def find_entity(graph: dict, entity_id: str) -> dict | None:
    for node in graph.get("kg:nodes", []):
        if node.get("@id", "").endswith(entity_id) or entity_id in node.get("kg:label", "").lower():
            return node
    return None


def find_edges_for(graph: dict, entity_id: str) -> list[dict]:
    edges = []
    for edge in graph.get("kg:edges", []):
        src = edge.get("kg:source", "")
        tgt = edge.get("kg:target", "")
        if entity_id in src or entity_id in tgt:
            edges.append(edge)
    return edges


def check_antonyms(claim: str, existing_evidence: list[str]) -> dict:
    claim_lower = claim.lower()
    for evidence in existing_evidence:
        evidence_lower = evidence.lower()
        for word, antonym in ANTONYM_PAIRS.items():
            if word in claim_lower and antonym in evidence_lower:
                return {
                    "check_type": "antonym",
                    "passed": False,
                    "details": f"Antonym detected: claim uses '{word}', existing uses '{antonym}'",
                    "conflicting_fact": {"claim": evidence}
                }
    return {"check_type": "antonym", "passed": True, "details": "No antonym conflicts found"}


def check_negation(claim: str, existing_evidence: list[str]) -> dict:
    claim_lower = claim.lower()
    claim_negated = any(re.search(p, claim_lower) for p in NEGATION_PATTERNS)

    for evidence in existing_evidence:
        evidence_lower = evidence.lower()
        evidence_negated = any(re.search(p, evidence_lower) for p in NEGATION_PATTERNS)

        # One negated, one not = potential contradiction
        if claim_negated != evidence_negated:
            # Check if they're about the same entities
            claim_words = set(re.findall(r'\b\w{4,}\b', claim_lower))
            evidence_words = set(re.findall(r'\b\w{4,}\b', evidence_lower))
            overlap = claim_words & evidence_words
            if len(overlap) >= 2:
                return {
                    "check_type": "negation",
                    "passed": False,
                    "details": f"Negation conflict: claim {'negates' if claim_negated else 'affirms'}, "
                              f"existing {'negates' if evidence_negated else 'affirms'}. "
                              f"Shared concepts: {', '.join(list(overlap)[:5])}",
                    "conflicting_fact": {"claim": evidence}
                }
    return {"check_type": "negation", "passed": True, "details": "No negation conflicts found"}


def check_consistency(new_node: dict, existing_node: dict | None) -> dict:
    if existing_node is None:
        return {"check_type": "consistency", "passed": True, "details": "New entity, no existing data to conflict with"}

    issues = []
    new_props = new_node.get("kg:properties", {})
    existing_props = existing_node.get("kg:properties", {})

    # Check type mismatch
    if new_node.get("@type") and existing_node.get("@type"):
        if new_node["@type"] != existing_node["@type"]:
            issues.append(f"Type mismatch: new={new_node['@type']}, existing={existing_node['@type']}")

    # Check numeric property ranges
    for key in set(new_props.keys()) & set(existing_props.keys()):
        new_val = new_props[key]
        old_val = existing_props[key]
        if isinstance(new_val, (int, float)) and isinstance(old_val, (int, float)):
            if old_val != 0:
                ratio = abs(new_val - old_val) / abs(old_val)
                if ratio > 1.0:  # More than 100% difference
                    issues.append(f"Value '{key}' changed by {ratio*100:.0f}%: {old_val} -> {new_val}")

    if issues:
        return {"check_type": "consistency", "passed": False, "details": "; ".join(issues)}
    return {"check_type": "consistency", "passed": True, "details": "Properties consistent with existing data"}


def check_source(new_source: str | None, existing_sources: list[str]) -> dict:
    if not new_source:
        return {
            "check_type": "source",
            "passed": False,
            "details": "New fact has no source citation. Existing facts have sources: " + ", ".join(existing_sources[:3])
        }
    return {"check_type": "source", "passed": True, "details": f"Source provided: {new_source}"}


def validate_fact(graph_path: str, new_fact: dict) -> dict:
    """
    Validate a new fact against an existing knowledge graph.

    new_fact should have:
      - entity_id: the entity this fact is about
      - claim: text description of the fact
      - source: (optional) where this fact comes from
      - node: (optional) full node to add
    """
    graph = load_graph(graph_path)

    entity_id = new_fact.get("entity_id", "")
    claim = new_fact.get("claim", "")
    source = new_fact.get("source")
    new_node = new_fact.get("node", {})

    # Gather existing evidence
    existing_node = find_entity(graph, entity_id)
    existing_edges = find_edges_for(graph, entity_id)
    existing_evidence = [e.get("kg:evidence", "") for e in existing_edges if e.get("kg:evidence")]
    existing_sources = [e.get("kg:source_doc", "") for e in existing_edges if e.get("kg:source_doc")]

    # Run all checks
    checks = [
        check_antonyms(claim, existing_evidence),
        check_negation(claim, existing_evidence),
        check_consistency(new_node, existing_node),
        check_source(source, existing_sources),
    ]

    all_passed = all(c["passed"] for c in checks)
    has_contradiction = any(not c["passed"] and c["check_type"] in ("antonym", "negation") for c in checks)

    if has_contradiction:
        resolution = "contradiction"
    elif all_passed:
        resolution = "accepted"
    else:
        resolution = "flagged"

    result = {
        "validation_result": resolution,
        "new_fact": {"entity": entity_id, "claim": claim},
        "checks": checks,
        "resolution": "rejected" if has_contradiction else ("accepted" if all_passed else "needs_review"),
        "recommendation": _generate_recommendation(resolution, checks)
    }

    return result


def _generate_recommendation(resolution: str, checks: list[dict]) -> str:
    if resolution == "accepted":
        return "All checks passed. Safe to add to the graph."
    elif resolution == "contradiction":
        failed = [c for c in checks if not c["passed"] and c["check_type"] in ("antonym", "negation")]
        return f"Contradiction detected: {failed[0]['details']}. Present both facts to the user for resolution."
    else:
        failed = [c for c in checks if not c["passed"]]
        return f"Flagged for review: {failed[0]['details']}. Add with reduced confidence or request clarification."


def main():
    if len(sys.argv) < 3:
        print("Usage: python validate.py <graph.json> <new_fact.json>")
        print("  graph.json: Path to existing knowledge graph")
        print("  new_fact.json: Path to JSON with {entity_id, claim, source, node}")
        sys.exit(1)

    graph_path = sys.argv[1]
    fact_path = sys.argv[2]

    with open(fact_path, "r", encoding="utf-8") as f:
        new_fact = json.load(f)

    result = validate_fact(graph_path, new_fact)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

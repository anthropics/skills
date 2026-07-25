#!/usr/bin/env python3
"""build_action_manifest.py -- build + validate an agent action manifest for receipt minting.

Standard library only (argparse, hashlib, json, sys). No crypto, no network, no pip deps.
The actual signing is done by the OpenAgentOntology receipt primitive (pip install
"openagentontology[pq]"); this helper just assembles a well-formed, ASCII-safe action manifest
and prints the exact mint command, so the manifest can never be malformed when it reaches the
signer.

Usage:
  python build_action_manifest.py --agent A --operation deploy --target prod/api \\
      --policy "EU AI Act Art 12" --inputs "service=api;version=1.4.2" --out action.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys

# Side-effecting / consequential verbs. An action carrying one of these is the kind this
# skill exists to receipt. Used only to advise (never to block) -- the caller decides.
HIGH_SIGNAL = {
    "deploy", "release", "delete", "drop", "purge", "pay", "wire", "transfer", "refund",
    "grant", "grant_access", "export", "egress", "send", "approve", "deny", "decide",
    "provision", "migrate", "reconfigure", "escalate",
}

REQUIRED = ("agent_id", "operation", "target", "policy")


def _hash(s: str) -> str:
    return "sha256:" + hashlib.sha256(s.encode("utf-8")).hexdigest()[:16]


def _ascii_safe(obj) -> bool:
    """Evidence must be ASCII so the receipt hash reproduces in any language."""
    try:
        json.dumps(obj, ensure_ascii=True).encode("ascii")
        return True
    except (UnicodeEncodeError, TypeError):
        return False


def build(agent_id, operation, target, policy, inputs, decision) -> dict:
    manifest = {
        "agent_id": agent_id,
        "operation": operation,
        "target": target,
        "policy": policy,
        "inputs_hash": _hash(inputs or ""),
        "decision_label": decision,
    }
    missing = [k for k in REQUIRED if not manifest.get(k)]
    if missing:
        raise ValueError(f"missing required field(s): {', '.join(missing)}")
    if not _ascii_safe(manifest):
        raise ValueError("manifest contains non-ASCII; the receipt hash must be reproducible")
    return manifest


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Build a validated agent action manifest for receipt minting.")
    p.add_argument("--agent", required=True, help="acting agent id")
    p.add_argument("--operation", required=True, help="the verb: deploy / delete / pay / decide / ...")
    p.add_argument("--target", required=True, help="what the action acts on")
    p.add_argument("--policy", required=True, help="the governing rule, e.g. 'EU AI Act Art 12'")
    p.add_argument("--inputs", default="", help="inputs to hash (kept as a hash, not stored in clear)")
    p.add_argument("--decision", default="ACTION_GOVERNED", help="the receipt decision label")
    p.add_argument("--out", default="action.json", help="output manifest path")
    a = p.parse_args(argv)

    try:
        manifest = build(a.agent, a.operation, a.target, a.policy, a.inputs, a.decision)
    except ValueError as e:
        print(f"REJECTED: {e}", file=sys.stderr)
        return 2

    with open(a.out, "w", encoding="ascii") as f:
        json.dump(manifest, f, indent=2)

    op = a.operation.lower()
    advice = "HIGH-SIGNAL: receipt this by default." if op in HIGH_SIGNAL else \
        "low-signal: receipt only if it is consequential + later-provable."
    print(f"manifest -> {a.out}")
    print(f"  operation: {a.operation}  ({advice})")
    print(f"  policy:    {a.policy}")
    print(f"  inputs_hash: {manifest['inputs_hash']}")
    print()
    print("Mint the receipt (Ed25519 + post-quantum legs):")
    print(f'  python -c "import json,openagentontology.receipt as r; '
          f"print(json.dumps(r.mint_receipt(json.load(open('{a.out}')), decision='{a.decision}')))\" > receipt.json")
    print("Verify it from the cert alone:")
    print('  python -c "import json,openagentontology.receipt as r; '
          "print(r.verify_receipt(json.load(open('receipt.json'))))\"")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

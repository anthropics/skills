#!/usr/bin/env python3
"""BRC-31/BRC-29 CLI helpers for use in Claude /x402 skill.

Usage:
  brc31_helpers.py list                            List agents from x402agency.com registry
  brc31_helpers.py identity                        Get wallet identity key
  brc31_helpers.py discover <name_or_url>          Fetch /.well-known/x402-info manifest
  brc31_helpers.py handshake <server_url>          BRC-31 handshake
  brc31_helpers.py session <server_url>            Show stored session JSON
  brc31_helpers.py auth <METHOD> <url> [body]      Authenticated request
  brc31_helpers.py pay <METHOD> <url> [body]       Auth + payment request
  brc31_helpers.py execute-action <json>           Execute a pending action template (broadcasts tx)
"""
import sys
import os
import json
import requests as _requests

# Add project root to path so lib/ imports work
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib.handshake import do_handshake, get_or_create_session
from lib.auth_request import authenticated_request
from lib.payment import paid_request
from lib.session import load_session
from lib.metanet import get_identity_key
from lib import registry


def discover(manifest_url):
    """Fetch an x402-info manifest from a URL. Returns parsed JSON or error."""
    try:
        resp = _requests.get(manifest_url, timeout=10)
        if resp.status_code == 200:
            info = resp.json()
            # Annotate with refund summary for display
            caps = info.get("capabilities", {})
            if caps.get("refunds"):
                info["_refund_summary"] = {
                    "supported": True,
                    "protocol": caps.get("refundProtocol", "unknown"),
                    "endpoints_with_refunds": [
                        ep["path"] for ep in info.get("endpoints", [])
                        if isinstance(ep.get("refund"), dict) and ep["refund"].get("supported")
                    ],
                }
            return info
        else:
            return {"error": f"HTTP {resp.status_code}", "body": resp.text}
    except Exception as e:
        return {"error": str(e)}


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "list":
        agents = registry.list_agents()
        print(json.dumps(agents, indent=2))

    elif cmd == "identity":
        print(get_identity_key())

    elif cmd == "discover":
        identifier = sys.argv[2]
        x402_url = registry.resolve_x402_info(identifier)
        result = discover(x402_url)
        print(json.dumps(result, indent=2))

    elif cmd == "handshake":
        url = sys.argv[2]
        session = do_handshake(url)
        print(json.dumps(session.to_dict(), indent=2))

    elif cmd == "session":
        url = sys.argv[2]
        session = load_session(url)
        if session:
            print(json.dumps(session.to_dict(), indent=2))
        else:
            print("null")
            sys.exit(1)

    elif cmd == "auth":
        method = sys.argv[2].upper()
        url = registry.resolve(sys.argv[3])
        body = sys.argv[4] if len(sys.argv) > 4 else None
        resp = authenticated_request(method, url, body=body)
        result = {
            "status": resp.status_code,
            "headers": dict(resp.headers),
            "body": resp.text,
        }
        print(json.dumps(result, indent=2))

    elif cmd == "pay":
        method = sys.argv[2].upper()
        url = registry.resolve(sys.argv[3])
        body = sys.argv[4] if len(sys.argv) > 4 else None
        resp = paid_request(method, url, body=body)
        result = {
            "status": resp.status_code,
            "headers": dict(resp.headers),
            "body": resp.text,
        }
        # Parse response body once for auto-detection
        body_parsed = None
        try:
            body_parsed = resp.json()
        except Exception:
            pass
        # Auto-detect and process refund in response
        try:
            if isinstance(body_parsed, dict):
                refund_data = body_parsed.get("refund")
                if refund_data and isinstance(refund_data, dict) and not refund_data.get("already_refunded"):
                    from lib.refund import parse_refund, process_refund
                    refund_info = parse_refund(body_parsed)
                    if refund_info:
                        try:
                            refund_result = process_refund(refund_info)
                            result["refund"] = {
                                "processed": True,
                                "accepted": refund_result.get("accepted", False),
                                "satoshis": refund_info.satoshis,
                                "txid": refund_info.txid,
                            }
                        except Exception as e:
                            result["refund"] = {"processed": False, "error": str(e)}
        except Exception:
            pass
        # Detect action template — return for user confirmation, DON'T auto-execute
        try:
            if isinstance(body_parsed, dict):
                action_data = body_parsed.get("action")
                costs_data = body_parsed.get("costs")
                if action_data and isinstance(action_data, dict) and action_data.get("outputs"):
                    result["pending_action"] = {
                        "description": action_data.get("description"),
                        "action": action_data,
                    }
                    if costs_data:
                        result["pending_action"]["costs"] = costs_data
        except Exception:
            pass
        print(json.dumps(result, indent=2))

    elif cmd == "execute-action":
        action_json = sys.argv[2]
        action_data = json.loads(action_json)
        from lib.metanet import _call as wallet_call
        action_result = wallet_call("createAction", {
            "description": action_data.get("description", "Agent action"),
            "outputs": action_data["outputs"],
            "options": action_data.get("options", {}),
            "labels": action_data.get("labels", ["app:x402"]),
        })
        txid = action_result.get("txid")
        print(json.dumps({
            "txid": txid,
            "inscription_id": f"{txid}_0" if txid else None,
            "description": action_data.get("description"),
        }, indent=2))

    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()

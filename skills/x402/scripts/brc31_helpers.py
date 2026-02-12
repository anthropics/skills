#!/usr/bin/env python3
"""BRC-31/BRC-29 CLI helpers for use in Claude /x402 skill.

Usage:
  brc31_helpers.py identity                       Get wallet identity key
  brc31_helpers.py discover <server_url>           Fetch /.well-known/x402-info manifest
  brc31_helpers.py handshake <server_url>          BRC-31 handshake
  brc31_helpers.py session <server_url>            Show stored session JSON
  brc31_helpers.py auth <METHOD> <url> [body]      Authenticated request
  brc31_helpers.py pay <METHOD> <url> [body]       Auth + payment request
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


def discover(server_url):
    """Fetch /.well-known/x402-info from the server. Returns parsed JSON or error."""
    base = server_url.rstrip("/")
    url = f"{base}/.well-known/x402-info"
    try:
        resp = _requests.get(url, timeout=10)
        if resp.status_code == 200:
            return resp.json()
        else:
            return {"error": f"HTTP {resp.status_code}", "body": resp.text}
    except Exception as e:
        return {"error": str(e)}


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    cmd = sys.argv[1]

    if cmd == "identity":
        print(get_identity_key())

    elif cmd == "discover":
        url = sys.argv[2]
        result = discover(url)
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
        url = sys.argv[3]
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
        url = sys.argv[3]
        body = sys.argv[4] if len(sys.argv) > 4 else None
        resp = paid_request(method, url, body=body)
        result = {
            "status": resp.status_code,
            "headers": dict(resp.headers),
            "body": resp.text,
        }
        print(json.dumps(result, indent=2))

    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()

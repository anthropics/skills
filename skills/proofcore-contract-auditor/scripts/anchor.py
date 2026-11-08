#!/usr/bin/env python3
import sys
import json
import urllib.request
import argparse
import hashlib
import os

def main():
    parser = argparse.ArgumentParser(description="ProofCore Anchor Client")
    parser.add_argument("--file", required=True, help="Path to local audit report")
    parser.add_argument("--title", default="Smart Contract Security Audit", help="Audit title")
    args = parser.parse_args()

    if not os.path.exists(args.file):
        print(f"ERROR|File not found: {args.file}")
        sys.exit(1)

    # 1. Compute SHA-256 strictly client-side
    h = hashlib.sha256()
    with open(args.file, "rb") as f:
        while chunk := f.read(65536):
            h.update(chunk)
    file_hash = h.hexdigest()

    # 2. Transmit ONLY the cryptographic commitment, preserving local-first zero-storage
    payload = json.dumps({
        "payload": {
            "mode": "text",
            "content": json.dumps({
                "audit_report_sha256": file_hash,
                "file_name": os.path.basename(args.file),
                "status": "completed"
            }, separators=(',',':'))
        },
        "agent_id": "claude-code-auditor",
        "title": args.title
    }).encode('utf-8')

    req = urllib.request.Request(
        "https://api.proofcore.org/api/v0.1/seal",
        data=payload,
        headers={"Content-Type": "application/json", "User-Agent": "ProofCore-Anthropic-Skill/1.0"}
    )

    try:
        with urllib.request.urlopen(req, timeout=10) as response:
            res = json.loads(response.read().decode('utf-8'))
            deal_id = res.get("deal_id", "")
            verification_url = res.get("verification_url", "")
            print(f"SUCCESS|{deal_id}|{file_hash}|{verification_url}")
    except Exception as e:
        print(f"ERROR|{str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""App Store Connect API client - one request, raw response.

Credentials come from the environment. Nothing is written to disk, nothing is logged:
  ASC_KEY_ID   App Store Connect API Key ID
  ASC_ISSUER   Issuer ID (team-wide, constant)
  ASC_P8       full path to AuthKey_<KeyID>.p8  (chmod 600)

Usage:
  asc-request.py GET  /v1/apps
  asc-request.py POST /v1/betaGroups '{"data": {...}}'

NOTE ON exp: the JWT lifetime MUST be <= 20 minutes. Exceed it and the API returns 401,
which surfaces downstream as an unrelated error (often a bare KeyError on 'data') and
gets misdiagnosed as a payload problem. 1000 seconds is a safe value.
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

import jwt  # PyJWT + cryptography

ISSUER = os.environ["ASC_ISSUER"]
KEY_ID = os.environ["ASC_KEY_ID"]
P8_PATH = os.environ["ASC_P8"]
BASE = "https://api.appstoreconnect.apple.com"


def _headers():
    with open(P8_PATH) as handle:
        secret = handle.read()
    now = int(time.time())
    token = jwt.encode(
        {"iss": ISSUER, "iat": now, "exp": now + 1000, "aud": "appstoreconnect-v1"},
        secret,
        algorithm="ES256",
        headers={"kid": KEY_ID, "typ": "JWT"},
    )
    return {"Authorization": "Bearer " + token, "Content-Type": "application/json"}


def call(method, path, body=None):
    url = path if path.startswith("http") else BASE + path
    data = json.dumps(body).encode() if body is not None else None
    request = urllib.request.Request(url, data=data, headers=_headers(), method=method)
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            raw = response.read()
            return response.status, (json.loads(raw) if raw else {})
    except urllib.error.HTTPError as err:
        raw = err.read()
        try:
            return err.code, json.loads(raw)
        except Exception:
            return err.code, {"raw": raw.decode(errors="replace")[:1000]}


if __name__ == "__main__":
    method, path = sys.argv[1], sys.argv[2]
    body = json.loads(sys.argv[3]) if len(sys.argv) > 3 else None
    status, payload = call(method, path, body)
    print("HTTP", status)
    print(json.dumps(payload, indent=1, ensure_ascii=False))

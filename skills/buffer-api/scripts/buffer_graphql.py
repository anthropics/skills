#!/usr/bin/env python3
"""
buffer_graphql.py — minimal, safe Buffer GraphQL helper.

Dependency-light (stdlib only: urllib + json) so it runs anywhere an agent has
Python, and it AVOIDS the latin-1 / non-ASCII crash by utf-8 encoding the JSON
body explicitly.

Buffer API facts baked in:
- Endpoint: https://api.buffer.com  (POST, Content-Type: application/json)
- Auth: Authorization: Bearer <API_KEY>
- All mutations/queries are GraphQL only (no REST). Legacy REST is retired.
- createPost etc. return UNIONS — spread both success and error members.
- Webhook-style poll uses query post(input:{ id }) { status } — there is NO getPost field.

Usage (run with any python on the host):
  python3 buffer_graphql.py --help
  python3 buffer_graphql.py --query "{ account { id organizations { id } } }"
  python3 buffer_graphql.py --query "query Q($id: ID!){ post(input:{id:$id}){ id status } }" --vars '{"id":"..."}'
  python3 buffer_graphql.py --query "..." --key sk-or-            # or set BUFFER_API_KEY env

Only reads the Buffer API key from env BUFFER_API_KEY or --key. Never echoes it.
"""
import argparse, json, os, sys, urllib.request, urllib.error

ENDPOINT = "https://api.buffer.com"


def post(query: str, variables, key: str, timeout: int = 60):
    payload = {"query": query}
    if variables:
        payload["variables"] = variables
    # UTF-8 encode so non-ASCII (em dashes, quotes) never hit urllib's latin-1 default
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        ENDPOINT, data=body, method="POST",
        headers={"Content-Type": "application/json",
                 "Authorization": f"Bearer {key}",
                 "User-Agent": "buffer-graphql-skill/1.0"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def main() -> int:
    ap = argparse.ArgumentParser(description="Buffer GraphQL helper (see module docstring).")
    ap.add_argument("--query", required=True, help="GraphQL query or mutation")
    ap.add_argument("--vars", default=None, help="JSON object (string) of variables")
    ap.add_argument("--key", default=None, help="Buffer API key (else BUFFER_API_KEY env)")
    ap.add_argument("--pretty", action="store_true", help="pretty-print JSON output")
    args = ap.parse_args()

    key = args.key or os.environ.get("BUFFER_API_KEY")
    if not key:
        print("No Buffer API key: pass --key or set BUFFER_API_KEY env.", file=sys.stderr)
        return 2

    vars_obj = json.loads(args.vars) if args.vars else {}
    try:
        data = post(args.query, vars_obj, key)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", "ignore")
        print(json.dumps({"error": {"status": e.code, "body": body}}, indent=2))
        return 1
    except Exception as e:
        print(json.dumps({"error": type(e).__name__ + ": " + str(e)}, indent=2))
        return 1

    if args.pretty:
        print(json.dumps(data, indent=2))
    else:
        print(json.dumps(data))
    return 0


if __name__ == "__main__":
    sys.exit(main())

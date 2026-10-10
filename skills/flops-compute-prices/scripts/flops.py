#!/usr/bin/env python3
"""Minimal helper for the FLOPS public compute-price API.

Standard library only (urllib), zero dependencies, key-free. Mirrors the public
REST surface used by the flops-compute-prices skill.

Usage:
    python flops.py price   <slug>          e.g. price FLOPS-H100-SPOT
    python flops.py catalog                 list every public index slug
    python flops.py search  <query>         e.g. search h100
    python flops.py verify  <slug> <value>  fact-check a claimed value
    python flops.py cheapest <accelerator>  lowest rate across a chip's markets, e.g. cheapest a100

An optional FLOPS_API_KEY env var upgrades responses to full precision; never
required.
"""
import json
import os
import sys
import urllib.parse
import urllib.request

BASE = "https://app.flopsindex.com"


def _get(path):
    req = urllib.request.Request(BASE + path, headers={"Accept": "application/json"})
    key = os.environ.get("FLOPS_API_KEY")
    if key:
        req.add_header("X-FLOPS-Api-Key", key)
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.load(resp)


def price(slug):
    rec = _get(f"/v1/price/{urllib.parse.quote(slug, safe='')}")
    # Convenience: the API's verify_url carries no value; add a checkable variant so
    # an agent can cite a link that actually resolves to a pass/fail check.
    vurl, val = rec.get("verify_url"), rec.get("value")
    if vurl and val is not None:
        rec["verify_url_checkable"] = vurl + ("&" if "?" in vurl else "?") + f"value={val}"
    return rec


def catalog():
    return _get("/v2/catalog/public")


def search(query):
    return _get("/v1/search?" + urllib.parse.urlencode({"q": query}))


def verify(slug, value):
    return _get("/v1/verify?" + urllib.parse.urlencode({"index_id": slug, "value": value}))


def cheapest(accel):
    """Lowest reference level across a chip's markets (SPOT/OD/DEPIN).

    Finds the chip's slugs from the catalog, then confirms each with the
    authoritative /v1/price call and returns the minimum. accel is the middle
    slug segment, e.g. 'a100' -> FLOPS-A100-*.
    """
    cat = catalog()
    items = cat.get("indices", cat.get("items", cat if isinstance(cat, list) else []))
    want = accel.upper()
    slugs = []
    for i in items:
        s = i.get("index_id") or i.get("slug")
        parts = (s or "").split("-")
        if len(parts) >= 3 and parts[0] == "FLOPS" and parts[1] == want:
            slugs.append(s)
    priced = []
    for s in slugs:
        rec = price(s)
        if rec.get("value") is not None:
            priced.append((rec["value"], s, rec))
    if not priced:
        return {"error": f"no priced FLOPS-{want}-* indices found", "candidates": slugs}
    priced.sort(key=lambda r: r[0])
    val, slug, rec = priced[0]
    market = slug.split("-")[-1]  # SPOT | OD | DEPIN
    vurl = rec.get("verify_url", "")
    out = {
        "cheapest_slug": slug,
        "market": market,
        "value": val,
        "unit": rec.get("unit"),
        "as_of": rec.get("as_of"),
        "citation_url": rec.get("citation_url"),
        "verify_url": (vurl + ("&" if "?" in vurl else "?") + f"value={val}") if vurl else None,
        "all_markets": [{"slug": s, "market": s.split("-")[-1], "value": v} for v, s, _ in priced],
    }
    if market == "DEPIN":
        out["market_class_note"] = (
            "Cheapest is a DEPIN (decentralized) rate — a different reliability/risk class "
            "than on-demand. Caveat this; do not present it as an apples-to-apples cloud rate."
        )
    out["cite_note"] = "Re-pull /v1/price/<cheapest_slug> at cite time for the freshest as_of bucket."
    return out


def main(argv):
    if not argv:
        print(__doc__)
        return 1
    cmd, rest = argv[0], argv[1:]
    try:
        if cmd == "price" and rest:
            out = price(rest[0])
        elif cmd == "catalog":
            out = catalog()
        elif cmd == "search" and rest:
            out = search(rest[0])
        elif cmd == "verify" and len(rest) >= 2:
            out = verify(rest[0], rest[1])
        elif cmd == "cheapest" and rest:
            out = cheapest(rest[0])
        else:
            print("usage: flops.py {price <slug> | catalog | search <q> | "
                  "verify <slug> <value> | cheapest <accelerator>}")
            return 1
    except Exception as exc:  # noqa: BLE001 - surface any transport/HTTP error plainly
        print(f"error: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

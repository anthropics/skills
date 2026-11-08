#!/usr/bin/env python3
"""
Geocode city/region names to lat/lon using Nominatim (no API key required).
"""

import sys
import time
import json
import argparse
import requests

BUILT_IN = {
    "carson city nv":     (39.1638, -119.7674),
    "reno nv":            (39.5296, -119.8138),
    "sparks nv":          (39.5349, -119.7527),
    "las vegas nv":       (36.1699, -115.1398),
    "fernley nv":         (39.6077, -119.2125),
    "elko nv":            (40.8324, -115.7631),
    "henderson nv":       (36.0395, -114.9817),
    "phoenix az":         (33.4484, -112.0740),
    "tucson az":          (32.2226, -110.9747),
    "mesa az":            (33.4152, -111.8315),
    "salt lake city ut":  (40.7608, -111.8910),
    "ogden ut":           (41.2230, -111.9738),
    "provo ut":           (40.2338, -111.6585),
    "boise id":           (43.6150, -116.2023),
    "twin falls id":      (42.5629, -114.4609),
    "portland or":        (45.5051, -122.6750),
    "salem or":           (44.9429, -123.0351),
    "eugene or":          (44.0521, -123.0868),
    "denver co":          (39.7392, -104.9903),
    "colorado springs co":(38.8339, -104.8214),
    "pueblo co":          (38.2544, -104.6091),
    "albuquerque nm":     (35.0844, -106.6504),
    "el paso tx":         (31.7619, -106.4850),
    "dallas tx":          (32.7767, -96.7970),
    "houston tx":         (29.7604, -95.3698),
    "san antonio tx":     (29.4241, -98.4936),
    "austin tx":          (30.2672, -97.7431),
    "charlotte nc":       (35.2271, -80.8431),
    "raleigh nc":         (35.7796, -78.6382),
    "greensboro nc":      (36.0726, -79.7920),
    "memphis tn":         (35.1495, -90.0490),
    "nashville tn":       (36.1627, -86.7816),
    "atlanta ga":         (33.7490, -84.3880),
    "savannah ga":        (32.0835, -81.0998),
    "richmond va":        (37.5407, -77.4360),
    "norfolk va":         (36.8508, -76.2859),
    "chicago il":         (41.8781, -87.6298),
    "columbus oh":        (39.9612, -82.9988),
    "indianapolis in":    (39.7684, -86.1581),
    "kansas city mo":     (39.0997, -94.5786),
    "st louis mo":        (38.6270, -90.1994),
    "minneapolis mn":     (44.9778, -93.2650),
    "omaha ne":           (41.2565, -95.9345),
    "des moines ia":      (41.5868, -93.6250),
    "seattle wa":         (47.6062, -122.3321),
    "spokane wa":         (47.6588, -117.4260),
    "los angeles ca":     (34.0522, -118.2437),
    "san francisco ca":   (37.7749, -122.4194),
    "sacramento ca":      (38.5816, -121.4944),
    "fresno ca":          (36.7378, -119.7871),
    "bakersfield ca":     (35.3733, -119.0187),
    "san bernardino ca":  (34.1083, -117.2898),
    "riverside ca":       (33.9806, -117.3755),
}


def geocode(query: str, retries: int = 2) -> tuple[float, float] | None:
    """Return (lat, lon) for a place string. Returns None if not found."""
    key = query.strip().lower()
    if key in BUILT_IN:
        return BUILT_IN[key]

    url = "https://nominatim.openstreetmap.org/search"
    params = {"q": query, "format": "json", "limit": 1}
    headers = {"User-Agent": "land-acquisition-intel/1.0 (land scouting tool)"}

    for attempt in range(retries + 1):
        try:
            r = requests.get(url, params=params, headers=headers, timeout=10)
            if r.status_code == 429:
                time.sleep(3)
                continue
            r.raise_for_status()
            results = r.json()
            if results:
                return float(results[0]["lat"]), float(results[0]["lon"])
            return None
        except Exception as e:
            if attempt < retries:
                time.sleep(2)
            else:
                print(f"[geocode] ERROR: {e}", file=sys.stderr)
                return None

    return None


def main():
    parser = argparse.ArgumentParser(description="Geocode a place name to lat/lon")
    parser.add_argument("query", help="City/region to geocode (e.g. 'Reno NV')")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    result = geocode(args.query)
    if result is None:
        print(f"ERROR: Could not geocode '{args.query}'", file=sys.stderr)
        sys.exit(1)

    lat, lon = result
    if args.json:
        print(json.dumps({"lat": lat, "lon": lon, "query": args.query}))
    else:
        print(f"{lat},{lon}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Land Acquisition Intel — Data Fetcher
Pulls parcels + infrastructure for any US region.
Usage: python3 fetch_data.py --lat 39.1638 --lon -119.7674 --state NV --output /tmp/land-intel/raw/
"""
import argparse
import json
import math
import os
import time
import sys

import pandas as pd
import requests

# ── CLI ────────────────────────────────────────────────────────────────────────
parser = argparse.ArgumentParser()
parser.add_argument("--lat",    type=float, required=True)
parser.add_argument("--lon",    type=float, required=True)
parser.add_argument("--state",  type=str,   default="NV")
parser.add_argument("--radius", type=float, default=60,   help="miles")
parser.add_argument("--output", type=str,   default="/tmp/land-intel/raw/")
args = parser.parse_args()

os.makedirs(args.output, exist_ok=True)

# ── Bbox from center + radius ──────────────────────────────────────────────────
def bbox_from_center(lat, lon, radius_miles):
    km = radius_miles * 1.60934
    dlat = km / 111.0
    dlon = km / (111.0 * math.cos(math.radians(lat)))
    return lon - dlon, lat - dlat, lon + dlon, lat + dlat

MINX, MINY, MAXX, MAXY = bbox_from_center(args.lat, args.lon, args.radius)
BBOX_OSM = f"{MINY},{MINX},{MAXY},{MAXX}"   # Overpass: s,w,n,e
BBOX_ESRI = f"{MINX},{MINY},{MAXX},{MAXY}"  # ESRI: xmin,ymin,xmax,ymax
OVERPASS = "https://overpass-api.de/api/interpreter"

print(f"Region: center=({args.lat},{args.lon}), radius={args.radius}mi")
print(f"Bbox: {MINX:.3f},{MINY:.3f} → {MAXX:.3f},{MAXY:.3f}\n")


# ── Helpers ────────────────────────────────────────────────────────────────────
def osm_query(query, name, retries=2):
    for attempt in range(retries):
        try:
            r = requests.post(OVERPASS, data={"data": query}, timeout=120)
            if r.status_code == 429:
                print(f"  [{name}] rate limited, sleeping 5s...")
                time.sleep(5)
                continue
            if r.status_code == 200:
                return r.json().get("elements", [])
            print(f"  [{name}] HTTP {r.status_code}")
        except Exception as e:
            print(f"  [{name}] error: {e}")
        time.sleep(3)
    return []


def element_centroid(el):
    geom = el.get("geometry", [])
    if geom:
        lons = [n["lon"] for n in geom if "lon" in n]
        lats = [n["lat"] for n in geom if "lat" in n]
        if lons:
            return sum(lons)/len(lons), sum(lats)/len(lats)
    if "lon" in el:
        return el["lon"], el["lat"]
    return None, None


def poly_area_acres(geom):
    """Shoelace area of polygon geometry list."""
    if not geom or len(geom) < 3:
        return None
    lons = [n["lon"] for n in geom if "lon" in n]
    lats = [n["lat"] for n in geom if "lat" in n]
    n = len(lons)
    if n < 3:
        return None
    area_deg = abs(sum(lons[i]*lats[(i+1)%n] - lons[(i+1)%n]*lats[i] for i in range(n))) / 2
    avg_lat = sum(lats) / n
    area_sqm = area_deg * 111320 * (math.cos(math.radians(avg_lat)) * 111320)
    return area_sqm / 4046.86


def save(rows, filename):
    path = os.path.join(args.output, filename)
    df = pd.DataFrame(rows) if rows else pd.DataFrame()
    df.to_csv(path, index=False)
    print(f"  → saved {len(df)} rows to {filename}")
    return df


def arcgis_query(base_url, name, where="1=1", page_size=2000, bbox=None):
    """Generic ArcGIS FeatureServer/MapServer pager."""
    rows = []
    try:
        r = requests.get(f"{base_url}?f=json", timeout=10)
        info = r.json()
        if "error" in info:
            print(f"  [{name}] layer error: {info['error']}")
            return []
        max_rec = info.get("maxRecordCount", page_size)
        page = min(max_rec, page_size)
    except Exception as e:
        print(f"  [{name}] info fetch failed: {e}")
        page = page_size

    offset = 0
    while True:
        params = {
            "where": where,
            "outFields": "*",
            "returnGeometry": "true",
            "outSR": "4326",
            "f": "json",
            "resultOffset": offset,
            "resultRecordCount": page,
        }
        if bbox:
            params.update({
                "geometry": f"{bbox[0]},{bbox[1]},{bbox[2]},{bbox[3]}",
                "geometryType": "esriGeometryEnvelope",
                "inSR": "4326",
                "spatialRel": "esriSpatialRelIntersects",
            })
        try:
            r = requests.get(f"{base_url}/query", params=params, timeout=90)
            data = r.json()
        except Exception as e:
            print(f"  [{name}] query error at {offset}: {e}")
            break

        if "error" in data:
            print(f"  [{name}] API error: {data['error']}")
            break

        features = data.get("features", [])
        if not features:
            break

        for feat in features:
            row = feat.get("attributes", {})
            geom = feat.get("geometry", {})
            if geom:
                if "rings" in geom:
                    ring = geom["rings"][0]
                    lons = [p[0] for p in ring]
                    lats = [p[1] for p in ring]
                    row["_lat"] = sum(lats)/len(lats)
                    row["_lon"] = sum(lons)/len(lons)
                    n = len(ring)
                    area_deg = abs(sum(ring[i][0]*ring[(i+1)%n][1] - ring[(i+1)%n][0]*ring[i][1] for i in range(n))) / 2
                    area_sqm = area_deg * 111320 * (math.cos(math.radians(row["_lat"])) * 111320)
                    row["area_acres"] = area_sqm / 4046.86
                elif "x" in geom:
                    row["_lat"] = geom.get("y")
                    row["_lon"] = geom.get("x")
                elif "paths" in geom:
                    path = geom["paths"][0]
                    row["_lat"] = sum(p[1] for p in path) / len(path)
                    row["_lon"] = sum(p[0] for p in path) / len(path)
            rows.append(row)

        print(f"  [{name}] offset={offset} batch={len(features)} total={len(rows)}")
        if len(features) < page:
            break
        offset += page
        time.sleep(0.3)

    return rows


# ── State → parcel endpoint map ────────────────────────────────────────────────
STATE_PARCEL_ENDPOINTS = {
    # Nevada: statewide layer (Water Division)
    "NV": [
        ("https://arcgis.water.nv.gov/arcgis/rest/services/BaseLayers/County_Parcels_in_Nevada/MapServer/0", "nv_water_div"),
    ],
    # Utah: AGRC statewide
    "UT": [
        ("https://services1.arcgis.com/99sOBtuHyNDeQOMz/arcgis/rest/services/Utah_Parcels/FeatureServer/0", "ut_agrc"),
    ],
    # Arizona: county-level varies, try Maricopa first
    "AZ": [
        ("https://services.arcgis.com/K0p6RxP1r6x91jvO/arcgis/rest/services/Maricopa_Parcels/FeatureServer/0", "az_maricopa"),
    ],
    # Colorado: DOLA statewide
    "CO": [
        ("https://services3.arcgis.com/66aUo8zsujfVXRIT/arcgis/rest/services/Colorado_Parcels/FeatureServer/0", "co_dola"),
    ],
    # Oregon: ORGEO
    "OR": [
        ("https://services.arcgis.com/uUvqNMGPm7axC2dD/arcgis/rest/services/Oregon_Statewide_Parcels/FeatureServer/0", "or_geo"),
    ],
    # Idaho
    "ID": [
        ("https://services1.arcgis.com/jUJYIo9tSA7EHvfZ/arcgis/rest/services/Idaho_Parcels/FeatureServer/0", "id_parcels"),
    ],
}

# NC OneMap (east coast demo)
STATE_PARCEL_ENDPOINTS["NC"] = [
    ("https://services.nconemap.gov/secure/rest/services/NC1Map_Parcels/FeatureServer/0", "nc_onemap"),
]


def fetch_parcels():
    print(f"[1/8] Parcels ({args.state})...")
    all_rows = []

    endpoints = STATE_PARCEL_ENDPOINTS.get(args.state.upper(), [])
    for url, name in endpoints:
        print(f"  Trying {name}...")
        rows = arcgis_query(url, name, bbox=(MINX, MINY, MAXX, MAXY))
        if rows:
            all_rows.extend(rows)
            break  # one working source is enough

    if not all_rows:
        print(f"  No ArcGIS parcel source for {args.state} — using OSM fallback")

    # Always add OSM land use features (industrial/farmland/etc.)
    osm_rows = fetch_osm_landuse()
    all_rows.extend(osm_rows)

    save(all_rows, "parcels_raw.csv")
    return all_rows


def fetch_osm_landuse():
    """OSM building footprints + land use as parcel proxy."""
    print("  [OSM] land use features...")
    queries = {
        "industrial": f"[out:json][timeout:60];(way[\"landuse\"~\"industrial|commercial\"]({BBOX_OSM});way[\"building\"~\"warehouse|industrial|data_center\"]({BBOX_OSM}););out body geom;",
        "agricultural": f"[out:json][timeout:60];(way[\"landuse\"~\"farmland|farmyard|farm|meadow|pasture\"]({BBOX_OSM}););out body geom;",
        "vacant": f"[out:json][timeout:60];(way[\"landuse\"~\"vacant|brownfield|greenfield\"]({BBOX_OSM}););out body geom;",
    }
    rows = []
    for qname, q in queries.items():
        time.sleep(2)
        elements = osm_query(q, qname)
        for el in elements:
            tags = el.get("tags", {})
            lon, lat = element_centroid(el)
            area_acres = poly_area_acres(el.get("geometry", []))
            rows.append({
                "osm_id": el["id"], "source": "osm",
                "building": tags.get("building", ""), "landuse": tags.get("landuse", qname),
                "name": tags.get("name", ""), "addr_city": tags.get("addr:city", ""),
                "addr_street": tags.get("addr:street", ""), "operator": tags.get("operator", ""),
                "_lat": lat, "_lon": lon, "area_acres": round(area_acres, 2) if area_acres else None,
            })
    return rows


def fetch_highways():
    print("[2/8] Highways...")
    q = f"""[out:json][timeout:60];
(way["highway"~"motorway|trunk|primary"]({BBOX_OSM}););out body geom;"""
    elements = osm_query(q, "highways")
    rows = []
    for el in elements:
        tags = el.get("tags", {})
        geom = el.get("geometry", [])
        if not geom: continue
        lons = [n["lon"] for n in geom]; lats = [n["lat"] for n in geom]
        rows.append({
            "osm_id": el["id"], "highway_type": tags.get("highway", ""),
            "name": tags.get("name", ""), "ref": tags.get("ref", ""),
            "_lat": sum(lats)/len(lats), "_lon": sum(lons)/len(lons),
            "start_lat": lats[0], "start_lon": lons[0],
        })
    save(rows, "highways.csv")


def fetch_interchanges():
    print("[3/8] Interchanges...")
    q = f"""[out:json][timeout=30];(node["highway"="motorway_junction"]({BBOX_OSM}););out body;"""
    elements = osm_query(q, "interchanges")
    rows = [{"osm_id": e["id"], "name": e.get("tags", {}).get("name", ""),
              "ref": e.get("tags", {}).get("ref", ""),
              "_lat": e.get("lat"), "_lon": e.get("lon")} for e in elements]
    save(rows, "interchanges.csv")


def fetch_rail():
    print("[4/8] Rail...")
    q = f"""[out:json][timeout=60];(way["railway"~"rail|narrow_gauge"]({BBOX_OSM}););out body geom;"""
    elements = osm_query(q, "rail")
    rows = []
    for el in elements:
        tags = el.get("tags", {})
        geom = el.get("geometry", [])
        if not geom: continue
        lons = [n["lon"] for n in geom]; lats = [n["lat"] for n in geom]
        rows.append({
            "osm_id": el["id"], "railway": tags.get("railway", ""),
            "name": tags.get("name", ""), "operator": tags.get("operator", ""),
            "usage": tags.get("usage", ""),
            "_lat": sum(lats)/len(lats), "_lon": sum(lons)/len(lons),
        })
    save(rows, "rail.csv")


def fetch_power():
    print("[5/8] Power infrastructure...")
    q = f"""[out:json][timeout=90];(
node["power"="substation"]({BBOX_OSM});
way["power"="substation"]({BBOX_OSM});
way["power"="line"]({BBOX_OSM});
way["power"="minor_line"]({BBOX_OSM});
);out body geom;"""
    elements = osm_query(q, "power")
    substations, lines = [], []
    for el in elements:
        tags = el.get("tags", {})
        ptype = tags.get("power", "")
        lon, lat = element_centroid(el)
        if not lat: continue
        row = {"osm_id": el["id"], "power_type": ptype,
                "name": tags.get("name", ""), "operator": tags.get("operator", ""),
                "voltage": tags.get("voltage", ""), "_lat": lat, "_lon": lon}
        if ptype == "substation":
            substations.append(row)
        elif ptype in ("line", "minor_line"):
            geom = el.get("geometry", [])
            if geom:
                row["start_lat"] = geom[0].get("lat")
                row["start_lon"] = geom[0].get("lon")
            lines.append(row)
    save(substations, "substations.csv")
    save(lines, "transmission_lines.csv")


def fetch_water():
    print("[6/8] Water infrastructure...")
    q = f"""[out:json][timeout=60];(
way["waterway"~"river|stream|canal"]({BBOX_OSM});
node["man_made"="water_tower"]({BBOX_OSM});
node["amenity"="water_point"]({BBOX_OSM});
way["man_made"="reservoir"]({BBOX_OSM});
);out body geom;"""
    elements = osm_query(q, "water")
    rows = []
    for el in elements:
        tags = el.get("tags", {})
        lon, lat = element_centroid(el)
        rows.append({
            "osm_id": el["id"], "type": el["type"],
            "feature": tags.get("waterway", tags.get("man_made", tags.get("natural", ""))),
            "name": tags.get("name", ""), "_lat": lat, "_lon": lon,
        })
    save(rows, "water_infra.csv")


def fetch_fiber():
    print("[7/8] Fiber/telecom...")
    q = f"""[out:json][timeout=30];(
way["telecom"~"fiber|fibre|cable"]({BBOX_OSM});
way["communication:fibre_optic"="yes"]({BBOX_OSM});
way["utility"="telecom"]({BBOX_OSM});
);out body geom;"""
    elements = osm_query(q, "fiber")
    rows = []
    for el in elements:
        tags = el.get("tags", {})
        lon, lat = element_centroid(el)
        rows.append({"osm_id": el["id"], "operator": tags.get("operator", ""),
                      "name": tags.get("name", ""), "_lat": lat, "_lon": lon})
    save(rows, "fiber.csv")


def fetch_solar_irradiance_proxy():
    """Mark regions with high solar potential based on latitude/state."""
    print("[8/8] Solar irradiance proxy...")
    # Southwest US is highest GHI. Simple flag based on bbox.
    # In a full impl: pull NREL NSRDB data via API
    avg_lat = (MINY + MAXY) / 2
    solar_score = 0
    if avg_lat < 37 and MINX > -115:  # AZ/NV/NM sweet spot
        solar_score = 90
    elif avg_lat < 40:
        solar_score = 75
    else:
        solar_score = 60
    meta = [{"region_avg_lat": avg_lat, "solar_ghi_score": solar_score,
              "note": "proxy score — use NREL NSRDB for real GHI data"}]
    save(meta, "solar_meta.csv")


# ── Main ───────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    fetch_parcels()
    time.sleep(1)
    fetch_highways()
    time.sleep(1)
    fetch_interchanges()
    time.sleep(1)
    fetch_rail()
    time.sleep(1)
    fetch_power()
    time.sleep(1)
    fetch_water()
    time.sleep(1)
    fetch_fiber()
    fetch_solar_irradiance_proxy()

    print(f"\nAll data fetched → {args.output}")
    for f in os.listdir(args.output):
        path = os.path.join(args.output, f)
        rows = len(open(path).readlines()) - 1
        print(f"  {f}: {rows} rows")

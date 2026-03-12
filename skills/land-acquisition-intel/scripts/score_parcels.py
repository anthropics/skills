#!/usr/bin/env python3
"""
Land Acquisition Intel — Scoring Engine
Vectorized scoring: no row loops, handles 300K+ parcels fast.
Usage: python3 score_parcels.py --raw /tmp/land-intel/raw/ --use-case datacenter --output /tmp/land-intel/output/
"""
import argparse
import math
import os

import numpy as np
import pandas as pd

# ── CLI ────────────────────────────────────────────────────────────────────────
parser = argparse.ArgumentParser()
parser.add_argument("--raw",      type=str, default="/tmp/land-intel/raw/")
parser.add_argument("--use-case", type=str, default="datacenter",
                    choices=["datacenter", "warehouse", "solar", "agricultural", "industrial", "custom"])
parser.add_argument("--output",   type=str, default="/tmp/land-intel/output/")
parser.add_argument("--center-lat", type=float, default=None)
parser.add_argument("--center-lon", type=float, default=None)
args = parser.parse_args()

os.makedirs(args.output, exist_ok=True)
RAW = args.raw
USE_CASE = args.use_case

print(f"=== Land Acquisition Scoring: {USE_CASE} ===\n")

# ── Weight tables ──────────────────────────────────────────────────────────────
WEIGHTS = {
    "datacenter":   {"power": 35, "tx": 5, "highway": 15, "interchange": 5, "rail": 0,  "acreage": 20, "zoning": 15, "water": 5, "fiber": 5, "labor": 0,  "solar": 0,  "climate": 5},
    "warehouse":    {"power": 5,  "tx": 3, "highway": 25, "interchange": 15,"rail": 15, "acreage": 20, "zoning": 15, "water": 5, "fiber": 0, "labor": 10, "solar": 0,  "climate": 0},
    "solar":        {"power": 15, "tx": 10,"highway": 5,  "interchange": 0, "rail": 0,  "acreage": 25, "zoning": 10, "water": 5, "fiber": 0, "labor": 0,  "solar": 25, "climate": 5},
    "agricultural": {"power": 5,  "tx": 2, "highway": 10, "interchange": 0, "rail": 5,  "acreage": 30, "zoning": 15, "water": 20,"fiber": 0, "labor": 0,  "solar": 0,  "climate": 5},
    "industrial":   {"power": 15, "tx": 5, "highway": 20, "interchange": 10,"rail": 10, "acreage": 20, "zoning": 15, "water": 5, "fiber": 0, "labor": 5,  "solar": 0,  "climate": 0},
    "custom":       {"power": 14, "tx": 3, "highway": 14, "interchange": 7, "rail": 7,  "acreage": 20, "zoning": 15, "water": 5, "fiber": 5, "labor": 5,  "solar": 5,  "climate": 0},
}

W = WEIGHTS[USE_CASE]

# Ideal acreage ranges per use case
ACREAGE_IDEALS = {
    "datacenter":   (10, 500),
    "warehouse":    (5,  200),
    "solar":        (50, 5000),
    "agricultural": (40, 5000),
    "industrial":   (5,  500),
    "custom":       (5,  1000),
}
AC_MIN, AC_MAX = ACREAGE_IDEALS[USE_CASE]


# ── Helpers ────────────────────────────────────────────────────────────────────
def load(filename, lat_options=None, lon_options=None):
    path = os.path.join(RAW, filename)
    if not os.path.exists(path):
        print(f"  [missing] {filename}")
        return pd.DataFrame()
    df = pd.read_csv(path, low_memory=False)
    print(f"  [load] {filename}: {len(df)} rows")
    if df.empty:
        return df

    # Normalize lat/lon
    lat_cols = lat_options or ["_lat", "centroid_lat", "lat", "LATITUDE", "LAT", "y"]
    lon_cols = lon_options or ["_lon", "centroid_lon", "lon", "LONGITUDE", "LON", "x"]

    if "_lat" not in df.columns:
        for c in lat_cols:
            if c in df.columns:
                df["_lat"] = pd.to_numeric(df[c], errors="coerce")
                break
    if "_lon" not in df.columns:
        for c in lon_cols:
            if c in df.columns:
                df["_lon"] = pd.to_numeric(df[c], errors="coerce")
                break

    if "_lat" not in df.columns: df["_lat"] = np.nan
    if "_lon" not in df.columns: df["_lon"] = np.nan

    return df.dropna(subset=["_lat", "_lon"])


def batch_min_dist(plats, plons, ref_df, chunk=5000):
    """Vectorized: for each (plat,plon) find min km distance to any point in ref_df."""
    if ref_df.empty or "_lat" not in ref_df.columns:
        return np.full(len(plats), 999.0)
    rlats = ref_df["_lat"].values.astype(float)
    rlons = ref_df["_lon"].values.astype(float)
    mask = ~(np.isnan(rlats) | np.isnan(rlons))
    rlats, rlons = rlats[mask], rlons[mask]
    if len(rlats) == 0:
        return np.full(len(plats), 999.0)

    R = 6371.0
    result = np.full(len(plats), 999.0)
    for i in range(0, len(plats), chunk):
        clats = plats[i:i+chunk]
        clons = plons[i:i+chunk]
        valid = ~(np.isnan(clats) | np.isnan(clons))
        if not valid.any():
            continue
        dlat = np.radians(rlats[None, :] - clats[:, None])
        dlon = np.radians(rlons[None, :] - clons[:, None])
        a = (np.sin(dlat/2)**2 +
             np.cos(np.radians(clats[:, None])) * np.cos(np.radians(rlats[None, :])) * np.sin(dlon/2)**2)
        d = R * 2 * np.arcsin(np.sqrt(np.clip(a, 0, 1)))
        result[i:i+chunk] = np.min(d, axis=1)
        result[i:i+chunk][~valid] = 999.0
    return result


def dist_to_point(lats, lons, plat, plon):
    R = 6371.0
    dlat = np.radians(lats - plat)
    dlon = np.radians(lons - plon)
    a = np.sin(dlat/2)**2 + np.cos(np.radians(plat)) * np.cos(np.radians(lats)) * np.sin(dlon/2)**2
    return R * 2 * np.arcsin(np.sqrt(np.clip(a, 0, 1)))


def normalize_zoning(df):
    """Map raw field values to 6 categories."""
    cats = []
    for _, row in df.iterrows():
        text = " ".join(str(v).upper() for c in
            ["ZONING","ZONE","LAND_USE","LANDUSE","USE_CODE","building","landuse","query_type"]
            if c in row for v in [row[c]] if pd.notna(v))
        if any(x in text for x in ["IND","M-1","M-2","M1","M2","INDUSTRIAL","MANUFACTURING","WAREHOUSE","BUSINESS PARK"]):
            cats.append("industrial")
        elif any(x in text for x in ["COM","C-1","C-2","COMMERCIAL","RETAIL","OFFICE"]):
            cats.append("commercial")
        elif any(x in text for x in ["MU","PD","PUD","MIXED","PLANNED","TECH"]):
            cats.append("mixed_use")
        elif any(x in text for x in ["AG","FARM","AGRI","RURAL","FARMLAND","PASTURE","MEADOW"]):
            cats.append("agricultural")
        elif any(x in text for x in ["VAC","VACANT","UNDEVELOPED","BROWNFIELD","GREENFIELD"]):
            cats.append("vacant")
        elif any(x in text for x in ["RES","R-1","R-2","RESIDENTIAL","SFR"]):
            cats.append("residential")
        else:
            cats.append("unknown")
    return np.array(cats)


def zoning_score(cats, use_case):
    """Map zone categories to scores based on use case."""
    maps = {
        "datacenter":   {"industrial":15,"commercial":12,"mixed_use":10,"vacant":8,"agricultural":5,"unknown":5,"residential":0},
        "warehouse":    {"industrial":15,"commercial":10,"mixed_use":8, "vacant":6,"agricultural":4,"unknown":4,"residential":0},
        "solar":        {"agricultural":10,"vacant":10,"unknown":8,"industrial":6,"commercial":4,"mixed_use":4,"residential":0},
        "agricultural": {"agricultural":15,"vacant":12,"unknown":8,"mixed_use":5,"industrial":3,"commercial":3,"residential":0},
        "industrial":   {"industrial":15,"commercial":10,"mixed_use":8,"vacant":8,"agricultural":4,"unknown":5,"residential":0},
        "custom":       {"industrial":12,"commercial":10,"mixed_use":8,"vacant":8,"agricultural":6,"unknown":5,"residential":0},
    }
    m = maps.get(use_case, maps["custom"])
    return np.array([m.get(z, 5) for z in cats])


def motivated_seller(df):
    scores = []
    for _, row in df.iterrows():
        s = 0
        owner = str(row.get("OWNER", row.get("owner", ""))).upper()
        if any(x in owner for x in ["ESTATE","TRUST","DECEASED","HEIR"]): s += 20
        if any(x in owner for x in ["LLC","CORP","INC","LP","LTD"]): s += 5
        tax = str(row.get("TAX_STATUS", "")).upper()
        if any(x in tax for x in ["DELINQUENT","LIEN","UNPAID"]): s += 30
        mail_st = str(row.get("MAIL_STATE", row.get("OWNER_STATE", ""))).upper()
        if mail_st and mail_st not in ["NV","UT","AZ","CO","OR","ID","CA","","NAN"]: s += 15
        try:
            yr = int(float(str(row.get("YEAR_ACQUIRED", row.get("SALE_YEAR", 0)))))
            if 0 < yr < 2010: s += 15
            elif yr < 2015: s += 8
        except: pass
        scores.append(min(100, s))
    return scores


# ── Load all data ──────────────────────────────────────────────────────────────
print("Loading infrastructure...")
infra = {
    "substations":    load("substations.csv"),
    "transmission":   load("transmission_lines.csv"),
    "highways":       load("highways.csv"),
    "interchanges":   load("interchanges.csv"),
    "rail":           load("rail.csv"),
    "water":          load("water_infra.csv"),
    "fiber":          load("fiber.csv"),
}

print("\nLoading parcels...")
parcel_dfs = []
for fname in ["parcels_raw.csv", "osm_buildings.csv"]:
    df = load(fname)
    if not df.empty:
        parcel_dfs.append(df)

if not parcel_dfs:
    print("ERROR: no parcel data found. Run fetch_data.py first.")
    exit(1)

parcels = pd.concat(parcel_dfs, ignore_index=True)
# Filter to valid coords
parcels = parcels.dropna(subset=["_lat", "_lon"])
parcels = parcels[parcels["_lat"].between(-90, 90) & parcels["_lon"].between(-180, 180)]
print(f"\nTotal parcels: {len(parcels)}")

lats = parcels["_lat"].values.astype(float)
lons = parcels["_lon"].values.astype(float)

# ── Compute all distances (vectorized) ────────────────────────────────────────
print("\nComputing distances...")
sub_d    = batch_min_dist(lats, lons, infra["substations"])
tx_d     = batch_min_dist(lats, lons, infra["transmission"])
hw_d     = batch_min_dist(lats, lons, infra["highways"])
ic_d     = batch_min_dist(lats, lons, infra["interchanges"])
rail_d   = batch_min_dist(lats, lons, infra["rail"])
water_d  = batch_min_dist(lats, lons, infra["water"])
fiber_d  = batch_min_dist(lats, lons, infra["fiber"])

# Center distance (if provided)
if args.center_lat and args.center_lon:
    center_d = dist_to_point(lats, lons, args.center_lat, args.center_lon)
else:
    # Infer from parcel median if no center given
    center_d = np.zeros(len(lats))

# Nearest metro (Reno as proxy for western NV; adapt per region)
metro_lats = np.array([39.5296, 36.1699, 33.4484, 40.7608, 45.5051, 43.6150, 39.7392])
metro_lons = np.array([-119.8138, -115.1398, -112.0740, -111.8910, -122.6750, -116.2023, -104.9903])
metro_ref = pd.DataFrame({"_lat": metro_lats, "_lon": metro_lons})
metro_d  = batch_min_dist(lats, lons, metro_ref)

print("  All distances computed.")

# ── Acreage ────────────────────────────────────────────────────────────────────
ac_col = next((c for c in ["area_acres","Acres","acres","ACRES","ACREAGE"] if c in parcels.columns), None)
acres_arr = pd.to_numeric(parcels[ac_col], errors="coerce").fillna(0).values if ac_col else np.zeros(len(parcels))

def score_acreage(acres, wmax, ac_min, ac_max):
    """Score acreage fit: ideal range = full marks, taper outside."""
    s = np.zeros(len(acres))
    s = np.where((acres >= ac_min) & (acres <= ac_max), wmax, s)
    # below min: scale down
    below = acres < ac_min
    s = np.where(below, np.maximum(0, wmax * (acres / ac_min)), s)
    # above max: taper slowly (big parcels still useful)
    above = acres > ac_max
    s = np.where(above, np.maximum(wmax * 0.5, wmax * (ac_max / acres)**0.3), s)
    return s.astype(int)

acre_s = score_acreage(acres_arr, W["acreage"], AC_MIN, AC_MAX)

# ── Zoning ─────────────────────────────────────────────────────────────────────
print("Computing zoning categories...")
zone_cats = normalize_zoning(parcels)
zone_s = zoning_score(zone_cats, USE_CASE)

# ── Distance → component scores ────────────────────────────────────────────────
def dist_score(d, wmax, thresholds):
    """thresholds: [(km, pts), ...] in ascending order"""
    s = np.zeros(len(d))
    prev_pts = 0
    for km, pts in sorted(thresholds, reverse=True):
        s = np.where(d <= km, pts, s)
    return np.minimum(wmax, s.astype(int))

power_s = dist_score(sub_d, W["power"],
    [(1, W["power"]), (3, int(W["power"]*0.86)),
     (5, int(W["power"]*0.71)), (10, int(W["power"]*0.51)), (20, int(W["power"]*0.29))])

tx_s = np.maximum(0, (W["tx"] - tx_d).astype(int))

hw_s = dist_score(hw_d, W["highway"],
    [(0.5, W["highway"]), (1, int(W["highway"]*0.88)),
     (2, int(W["highway"]*0.72)), (5, int(W["highway"]*0.52)), (10, int(W["highway"]*0.32))])

ic_s = dist_score(ic_d, W["interchange"],
    [(1, W["interchange"]), (2, int(W["interchange"]*0.80)),
     (5, int(W["interchange"]*0.53)), (10, int(W["interchange"]*0.27))])

rail_s = dist_score(rail_d, W["rail"],
    [(1, W["rail"]), (2, int(W["rail"]*0.80)),
     (5, int(W["rail"]*0.53)), (10, int(W["rail"]*0.27))]) if W["rail"] > 0 else np.zeros(len(lats))

water_s = np.maximum(0, (W["water"] - water_d).astype(int))

fiber_s = np.maximum(0, (W["fiber"] - fiber_d * 2).astype(int)) if W["fiber"] > 0 else np.zeros(len(lats))

labor_s = np.where(metro_d < 10, W["labor"],
           np.where(metro_d < 25, int(W["labor"]*0.8),
           np.where(metro_d < 50, int(W["labor"]*0.5), int(W["labor"]*0.2)))) if W["labor"] > 0 else np.zeros(len(lats))

# Solar: use lat as proxy (lower lat in SW US = more sun)
if W["solar"] > 0:
    solar_s = np.where(lats < 35, W["solar"],
               np.where(lats < 37, int(W["solar"]*0.9),
               np.where(lats < 40, int(W["solar"]*0.75), int(W["solar"]*0.6))))
else:
    solar_s = np.zeros(len(lats))

# Climate bonus (Western NV: dry, altitude, no state income tax)
climate_s = np.where(
    (lats > 38.5) & (lats < 40.5) & (lons > -120.5) & (lons < -118.5),
    W["climate"],  # Nevada core zone
    np.where(
        (lats > 37) & (lats < 42) & (lons > -116) & (lons < -110),
        int(W["climate"] * 0.6),  # Utah/AZ/ID
        0
    )
) if W["climate"] > 0 else np.zeros(len(lats))

# ── Composite ──────────────────────────────────────────────────────────────────
raw_score = (power_s + tx_s + hw_s + ic_s + rail_s.astype(int) +
             acre_s + zone_s + water_s + fiber_s.astype(int) +
             labor_s.astype(int) + solar_s.astype(int) + climate_s.astype(int))

final_score = np.minimum(100, np.maximum(0, raw_score)).astype(int)

# ── Assign columns ─────────────────────────────────────────────────────────────
parcels["score"] = final_score
parcels["score_power"] = power_s
parcels["score_highway"] = hw_s
parcels["score_rail"] = rail_s.astype(int)
parcels["score_acreage"] = acre_s
parcels["score_zoning"] = zone_s
parcels["zone_category"] = zone_cats
parcels["dist_substation_km"] = np.round(sub_d, 2)
parcels["dist_highway_km"] = np.round(hw_d, 2)
parcels["dist_interchange_km"] = np.round(ic_d, 2)
parcels["dist_rail_km"] = np.round(rail_d, 2)
parcels["dist_water_km"] = np.round(water_d, 2)
parcels["dist_metro_km"] = np.round(metro_d, 2)
parcels["acres_scored"] = np.round(acres_arr, 2)
parcels["maps_link"] = [f"https://maps.google.com/?q={la:.6f},{lo:.6f}" for la, lo in zip(lats, lons)]

print("\nComputing motivated seller signals...")
parcels["motivated_seller"] = motivated_seller(parcels)

# ── Output ─────────────────────────────────────────────────────────────────────
# Drop heavy geometry columns
drop_cols = [c for c in parcels.columns if any(x in c.lower() for x in ["geometry","rings","Shape","shape"])]
out = parcels.drop(columns=drop_cols, errors="ignore")

# Separate: parcel-backed vs OSM proxy
has_parcel = out["APN"].notna() if "APN" in out.columns else pd.Series(False, index=out.index)

# Top candidates: prefer parcel-backed within same score tier
out["_sort"] = out["score"] * 10 + has_parcel.astype(int) * 3
out_sorted = out.sort_values("_sort", ascending=False).drop("_sort", axis=1)

top_candidates = out_sorted[out_sorted["score"] > 25].head(5000)
all_ranked = out_sorted[out_sorted["score"] > 10]

# Save
fname1 = os.path.join(args.output, f"{USE_CASE}_candidates.csv")
fname2 = os.path.join(args.output, "all_candidates_ranked.csv")
top_candidates.to_csv(fname1, index=False)
all_ranked.to_csv(fname2, index=False)

print(f"\n=== DONE ===")
print(f"Use case: {USE_CASE}")
print(f"Total parcels scored: {len(parcels)}")
print(f"Candidates (score>25): {len(top_candidates)}")
print(f"Score distribution: min={final_score[final_score>0].min() if (final_score>0).any() else 0} "
      f"median={int(np.median(final_score[final_score>0])) if (final_score>0).any() else 0} "
      f"max={final_score.max()}")
print(f"\nFiles:")
print(f"  {fname1}")
print(f"  {fname2}")

print(f"\nTop 20 sites:")
id_cols = [c for c in ["APN","PIN","County","SiteCity","source","name","addr_city"] if c in top_candidates.columns]
show_cols = id_cols + ["score","zone_category","acres_scored","dist_substation_km","dist_highway_km","dist_rail_km","maps_link"]
show_cols = [c for c in show_cols if c in top_candidates.columns]
print(top_candidates[show_cols].head(20).to_string(index=False))

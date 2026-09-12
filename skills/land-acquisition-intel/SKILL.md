---
name: land-acquisition-intel
description: >
  Runs a land acquisition intelligence pipeline that scores and ranks parcels
  for any land use type: datacenters, warehouses, logistics hubs, industrial
  parks, solar farms, agricultural operations, mixed-use development, or custom
  criteria. Use when user asks to find land for any purpose, score parcels,
  scout land, identify plots, run site selection, or asks "find me land for X
  in Y area". Triggers on phrases like "find land", "scout land", "parcel
  scoring", "site selection", "land acquisition", "identify plots", "score
  parcels", "land intel", "best sites for", "where should I build", or any
  request to evaluate parcels in a specific city, county, region, or state.
  Fetches real parcel data from public ArcGIS/OSM sources (no paid APIs),
  scores by proximity to infrastructure (power, highway, rail, fiber, water),
  acreage fit, zoning, and user-defined criteria, and outputs ranked CSVs of
  top candidate sites with Google Maps links. Do NOT use for residential
  property searches, general real estate questions, or permitting research.
metadata:
  author: Maksim Soltan
  version: 1.0.0
  category: real-estate
  tags:
    - land
    - parcel-scoring
    - site-selection
    - gis
    - acquisition
    - industrial
    - datacenter
    - warehouse
    - solar
---

# Land Acquisition Intelligence Skill

Fetches real parcel data + infrastructure, scores every parcel against your use case criteria, outputs ranked CSVs of top sites. Zero paid APIs. Runs fully local.

## Critical: Always Follow This Order

1. **Understand intent** — what land use, what region, any custom requirements
2. **Resolve region** — get center lat/lon + bbox
3. **Run fetch script** — parcels + infrastructure
4. **Run score script** — vectorized scoring with use-case weights
5. **Report top candidates** — table + Google Maps links + file paths

Never skip steps. Never invent scores without running the scripts.

---

## Step 1: Understand Intent

Ask (or infer from context) before running:

**Required:**
- What is the land for? (datacenter / warehouse / solar / industrial / agricultural / custom)
- What region? (city, county, state, or coordinates)

**Optional (infer defaults if not given):**
- Minimum acreage? (default: none)
- Maximum distance from highway? (default: none)
- Any specific infrastructure required? (power/rail/fiber/water)
- Budget tier? (high-value = prefer smaller parcels near infra; land-banking = larger, more remote OK)

If use case is custom or unclear: ask "What's the primary value driver for this site? Power access, logistics, labor, cost, or something else?"

---

## Step 2: Resolve Region

Extract city/county/state from user input. Map to coordinates:

**Built-in coords (Western US defaults):**
- Carson City NV: 39.1638, -119.7674
- Reno NV: 39.5296, -119.8138
- Las Vegas NV: 36.1699, -115.1398
- Sparks NV: 39.5349, -119.7527
- Fernley NV: 39.6077, -119.2125
- Phoenix AZ: 33.4484, -112.0740
- Salt Lake City UT: 40.7608, -111.8910
- Boise ID: 43.6150, -116.2023
- Denver CO: 39.7392, -104.9903
- Portland OR: 45.5051, -122.6750

**For any other city:** use Nominatim geocoder (free, no key):
```
https://nominatim.openstreetmap.org/search?q=CITY+STATE&format=json&limit=1
```

**Default bbox:** ~60-mile radius from center point.

---

## Step 3: Fetch Data

Run: `python3 scripts/fetch_data.py --lat LAT --lon LON --state STATE --output /tmp/land-intel/raw/`

**Fetches (all free, no API keys):**

| Layer | Source | Notes |
|-------|--------|-------|
| Parcels | State/county ArcGIS REST APIs | APN, acres, owner, address |
| Parcels fallback | OSM building + landuse footprints | Always works |
| Highways | OSM Overpass | motorway, trunk, primary |
| Interchanges | OSM motorway junctions | exact ramp locations |
| Rail lines | OSM | freight rail, usage tag |
| Substations + power lines | OSM power layer | voltage included |
| Water infrastructure | OSM | rivers, reservoirs, water towers |
| Farmland / vacant land | OSM landuse | agricultural, brownfield, greenfield |
| Industrial zones | OSM landuse=industrial | existing industrial parks |

**Expected raw files:**
```
/tmp/land-intel/raw/
├── parcels_raw.csv         # APN, acres, lat/lon, county
├── osm_buildings.csv       # OSM land use proxy
├── highways.csv
├── interchanges.csv
├── rail.csv
├── substations.csv
├── transmission_lines.csv
├── water_infra.csv
```

If a fetch fails: log it, skip that layer, continue. Missing infra = 999km default = lower score for that factor only.

---

## Step 4: Score Parcels

Run: `python3 scripts/score_parcels.py --raw /tmp/land-intel/raw/ --use-case USE_CASE --output /tmp/land-intel/output/`

**USE_CASE options:** `datacenter`, `warehouse`, `solar`, `agricultural`, `industrial`, `custom`

### Scoring Factors (all vectorized, no loops)

**Universal factors (all use cases):**
- Acreage fit: 0-20pts — calibrated to use-case ideal range
- Highway access: 0-20pts — distance to nearest major road
- Zoning compatibility: 0-15pts — industrial > commercial > agricultural > unknown > residential
- Water access: 0-5pts — nearest water body or tower

**Use-case specific weights:**

| Factor | Datacenter | Warehouse | Solar | Agricultural |
|--------|-----------|-----------|-------|--------------|
| Power substation | **35pts** | 5pts | 15pts | 5pts |
| Transmission line | 5pts | 3pts | 10pts | 2pts |
| Highway access | 15pts | **25pts** | 5pts | 10pts |
| Interchange proximity | 5pts | **15pts** | 0pts | 0pts |
| Rail access | 0pts | **15pts** | 0pts | 5pts |
| Acreage | 20pts | 20pts | **25pts** | **30pts** |
| Zoning | 15pts | 15pts | 10pts | 15pts |
| Water | 5pts | 5pts | 5pts | **20pts** |
| Fiber/telecom | 5pts | 0pts | 0pts | 0pts |
| Climate bonus | 5pts | 0pts | 5pts | 5pts |
| Labor market | 0pts | 10pts | 0pts | 0pts |

**Custom use case:** prompt user for 3-5 scoring priorities, assign 100pts across them.

**Scoring outputs:**
- `[use_case]_candidates.csv` — top 5,000 sites, all score components
- `all_candidates_ranked.csv` — full dataset with composite score

**Motivated seller signals** (added to every parcel where data available):
- Out-of-state owner: +15pts signal
- Estate/trust in owner name: +20pts signal
- Tax delinquent: +30pts signal
- Long hold (pre-2010 acquisition): +15pts signal

---

## Step 5: Report Results

After scripts complete, present findings in this format:

```
## Land Scouting Results: [USE CASE] in [REGION]

### Data Summary
- Parcels scored: X across N counties
- Infrastructure layers: highways ✓, rail ✓, power ✓, water ✓

### Top 10 Sites

| # | Score | Location | County | Acres | Key Factor | APN | Map |
|---|-------|----------|--------|-------|------------|-----|-----|
| 1 | 94 | 39.1638,-119.7674 | Carson City | 42ac | sub=0.3km | 1004169 | [link] |
...

### Score Distribution
Min: X | Median: X | Max: X | Sites >80: X

### Files Saved
- /tmp/land-intel/output/[use_case]_candidates.csv
- /tmp/land-intel/output/all_candidates_ranked.csv
```

Google Maps link format: `https://maps.google.com/?q=LAT,LON`

Always include top 10 in the response. Offer to show more or filter by criteria.

---

## Error Handling

**No parcel data:**
- Use OSM buildings + 500m synthetic grid as fallback
- Note: "County parcel data unavailable, using OSM proxy — APN/owner data will be missing"

**OSM rate limited (HTTP 429):**
- Sleep 3s, retry once
- Split into smaller bbox quadrants
- Skip layer if still failing

**Dependencies missing:**
```bash
pip install pandas numpy requests tqdm shapely pyproj geopandas --break-system-packages
```

**Region not found:**
- Use Nominatim geocoder on city name
- If still fails: ask user for coordinates directly

---

## Optional Enrichment

After base scoring, offer these if user wants to go deeper:

- **Zoning details**: actual zoning codes from county assessor (Municode or county GIS)
- **Ownership lookup**: cross-reference APN with county assessor for owner name/address
- **Active listings overlay**: Redfin CSV endpoint (recursive bbox subdivision, no API key)
- **BLM/federal ownership**: PADUS or BLM NILS layer — critical for Western US
- **Power capacity**: substation IDs from OSM → call utility for available MW
- **Environmental flags**: FEMA flood zones, EPA brownfields, wetlands

Prompt: "Base scoring complete. Want me to enrich the top 20 with zoning codes, ownership data, or active listing prices?"

---

## Scope

**Works well for:**
- Any US county with public ArcGIS parcel data (most do)
- Western US: Nevada, Utah, Arizona, Idaho, Oregon, Colorado, California
- Eastern US: NC OneMap, county GIS portals (see references/state-endpoints.md)
- Any use case expressible as infrastructure proximity + acreage

**Doesn't cover:**
- International parcels
- Permitting or entitlement research
- Environmental impact analysis
- Residential property or single-family land
- Title/lien searches

**Data freshness:**
- OSM: real-time
- County parcel layers: typically updated annually (check SourceDate field)
- Infrastructure: OSM community-maintained, generally reliable

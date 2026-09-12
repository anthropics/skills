# State ArcGIS Parcel Endpoints

Free, publicly accessible ArcGIS REST parcel layers by state. No API keys. Use with `resultOffset`/`resultRecordCount` paging and `f=json`.

---

## Western US

### Nevada (NV)
**Statewide (all 17 counties) — RECOMMENDED**
```
https://arcgis.water.nv.gov/arcgis/rest/services/BaseLayers/County_Parcels_in_Nevada/MapServer/0
```
- Fields: APN, Acres, County, SiteCity, PIN, OBJECTID, centroid_lat/lon computed
- Filter by county: `where=County='Carson City'`
- Max record count: 2000 per page (use resultOffset)
- Note: NRS 250 compliant, statewide, annually updated

**Clark County (Las Vegas metro) — alternative with more fields**
```
https://maps.clarkcountynv.gov/arcgis/rest/services/Parcel/MapServer/0
```

**Washoe County (Reno/Sparks) — alternative**
```
https://www.washoecounty.gov/assessor/gis/
```
Check ArcGIS Online: `https://www.arcgis.com/home/search.html?q=Washoe+County+Parcels`

---

### Utah (UT)
**AGRC Statewide Parcels — RECOMMENDED**
```
https://services1.arcgis.com/99lidPhWCzftIe9K/arcgis/rest/services/UtahStatewideParcels/FeatureServer/0
```
- Fields: PARCEL_ID, ACRES, COUNTY, ADDRESS, OWNER_TYPE
- Also available: `https://opendata.gis.utah.gov/datasets/utah-parcels`

**Salt Lake County**
```
https://services6.arcgis.com/JJzESW51TqeY9uat/arcgis/rest/services/SLCo_Parcels/FeatureServer/0
```

---

### Arizona (AZ)
**Maricopa County (Phoenix metro)**
```
https://mcassessor.maricopa.gov/mcassessor/
```
ArcGIS: Search `site:arcgis.com maricopa county parcels`
```
https://services2.arcgis.com/abYnqW7LM4GfGPAe/arcgis/rest/services/Maricopa_County_Parcels/FeatureServer/0
```

**Pima County (Tucson)**
```
https://assessor.pima.gov/
```
GIS Portal: `https://webcms.pima.gov/government/assessor/online_services/`

**Statewide Arizona (partial)**
```
https://azgeo-open-data-agic.hub.arcgis.com/
```

---

### Colorado (CO)
**Jefferson County (Denver metro)**
```
https://services1.arcgis.com/ibRKm6C6QnWUAOkn/arcgis/rest/services/Parcels/FeatureServer/0
```

**El Paso County (Colorado Springs)**
```
https://services1.arcgis.com/bdxGEbAiKkR6bN4s/arcgis/rest/services/Parcels/FeatureServer/0
```

**Statewide CO via DOLA**
```
https://storage.googleapis.com/co-publicdata/parcels_statewide.csv
```
(Bulk download, not ArcGIS paged)

---

### Oregon (OR)
**Metro Portland (regional)**
```
https://rlismetro.opendata.arcgis.com/
```

**Multnomah County (Portland)**
```
https://www.portlandmaps.com/arcgis/rest/services/Public/Landbase/MapServer/6
```

**Statewide OR (ORMAP)**
```
https://www.oregon.gov/geo/pages/parcels.aspx
```
Individual county GeoJSON downloads available

---

### Idaho (ID)
**Ada County (Boise)**
```
https://services3.arcgis.com/cXCe1cMkMsnpnBVP/arcgis/rest/services/ParcelBoundaries/FeatureServer/0
```

**Canyon County**
```
https://services.arcgis.com/USGSBNP0yZVY4bwE/arcgis/rest/services/Canyon_County_Parcels/FeatureServer/0
```

---

### Washington (WA)
**King County (Seattle)**
```
https://gismaps.kingcounty.gov/arcgis/rest/services/Property/KingCo_Parcels/MapServer/0
```

**Spokane County**
```
https://services.arcgis.com/pGfbNJoYypmNq86F/arcgis/rest/services/Spokane_Parcels/FeatureServer/0
```

**Statewide WA (partial)**
```
https://geo.wa.gov/datasets/parcels
```

---

### California (CA)
**No statewide layer — use county portals**

**Riverside County (Inland Empire)**
```
https://gis.rctlma.org/arcgis/rest/services/PublicGIS/ParcelSearch/MapServer/0
```

**San Bernardino County**
```
https://opendata-sbcounty.opendata.arcgis.com/
```

**Sacramento County**
```
https://portal.gis.saccounty.net/arcgis/rest/services/Parcels/MapServer/0
```

**Los Angeles County**
```
https://assessor.lacounty.gov/maps/
```
ArcGIS: `https://services3.arcgis.com/uknczv4jhbtsvyB1/arcgis/rest/services/LACounty_Parcels/FeatureServer/0`

---

## Eastern US

### North Carolina (NC)
**NC OneMap Statewide — BEST EASTERN US LAYER**
```
https://services.nconemap.gov/secure/rest/services/NC1Map_Parcels/MapServer/0
```
- All 100 NC counties, consistent schema
- Fields: REID, OWNER, DEED_ACRES, ADDR, CITY, zip, land_use_code
- Updated quarterly
- Note: Public access, no auth required

**Wake County (Raleigh)**
```
https://opendata.wakegov.com/datasets/parcels
```

**Mecklenburg County (Charlotte)**
```
https://mcmap.org/api/
```
ArcGIS: Search `site:arcgis.com mecklenburg parcels`

---

### Virginia (VA)
**Fairfax County (DC metro)**
```
https://www.fairfaxcounty.gov/maps/open-geospatial-data
```
ArcGIS: `https://services1.arcgis.com/ioennV6PpG5Xodq0/arcgis/rest/services/Fairfax_County_Parcels/FeatureServer/0`

**Richmond City**
```
https://www.arcgis.com/home/search.html?q=richmond+virginia+parcels
```

---

### Georgia (GA)
**Fulton County (Atlanta)**
```
https://services1.arcgis.com/Hp6G80Pky0om7QvQ/arcgis/rest/services/Fulton_County_Parcels/FeatureServer/0
```

**Chatham County (Savannah)**
```
https://www.chathamcounty.org/Portals/CivicaGIS/
```

---

### Florida (FL)
**No statewide — use county portals**

**Orange County (Orlando)**
```
https://www.ocpafl.org/growthmanagement/parcel.aspx
```

**Miami-Dade**
```
https://gisweb.miamidade.gov/arcgis/rest/services/Parcels/MapServer/0
```

**Hillsborough County (Tampa)**
```
https://gis.hcpafl.org/arcgis/rest/services/Parcels/MapServer/0
```

---

### Texas (TX)
**Harris County (Houston)**
```
https://arcgis.hctx.net/arcgis/rest/services/Public/Parcels/MapServer/0
```

**Dallas County**
```
https://opendata.arcgis.com/datasets/dallas-county-parcels
```

**Bexar County (San Antonio)**
```
https://opendata-cosagis.opendata.arcgis.com/
```

---

## Fallback: ArcGIS Online Search

If state-specific endpoint unknown:
1. Go to `https://www.arcgis.com/home/search.html`
2. Search: `[county name] [state] parcels`
3. Filter: Owner = Public, Type = Feature Layer
4. Click item → REST URL → test with `?f=json`

---

## Generic ArcGIS Paging Pattern

```python
import requests

BASE = "https://{server}/arcgis/rest/services/{service}/MapServer/0"
params = {
    "where": "1=1",
    "outFields": "*",
    "f": "json",
    "resultOffset": 0,
    "resultRecordCount": 2000,
}

all_features = []
while True:
    r = requests.get(BASE + "/query", params=params, timeout=30)
    data = r.json()
    features = data.get("features", [])
    if not features:
        break
    all_features.extend(features)
    if not data.get("exceededTransferLimit"):
        break
    params["resultOffset"] += len(features)
```

---

## Notes

- Max record counts vary: 1000 (old servers), 2000 (common), 5000 (modern ESRI 10.8+)
- Always test endpoint with `?f=json` before scripting — some require auth or have changed
- BLM/federal land: use PADUS (Protected Area Database) — `https://www.usgs.gov/programs/gap-analysis-project/science/pad-us-data-overview`
- For counties not listed: Google `[county] GIS parcels ArcGIS REST` — most have public layers

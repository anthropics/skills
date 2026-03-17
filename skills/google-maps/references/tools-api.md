# Google Maps Tools - Parameter & Response Reference

## maps_geocode

Convert an address or landmark name to GPS coordinates.

```bash
exec maps_geocode '{"address": "Tokyo Tower"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| address | string | yes | Address or landmark name |

Response:
```json
{
  "success": true,
  "data": {
    "location": { "lat": 35.6585805, "lng": 139.7454329 },
    "formatted_address": "4-chome-2-8 Shibakoen, Minato City, Tokyo 105-0011, Japan",
    "place_id": "ChIJCewJkL2LGGAR3Qmk0vCTGkg"
  }
}
```

---

## maps_batch_geocode

Geocode multiple addresses in one call (max 50).

```bash
exec maps_batch_geocode '{"addresses": ["Tokyo Tower", "Eiffel Tower", "Statue of Liberty"]}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| addresses | string[] | yes | List of addresses or landmarks (max 50) |

Response:
```json
{
  "total": 3,
  "succeeded": 3,
  "failed": 0,
  "results": [
    { "address": "Tokyo Tower", "success": true, "data": { "location": { "lat": 35.658, "lng": 139.745 }, "formatted_address": "..." } },
    ...
  ]
}
```

---

## maps_reverse_geocode

Convert GPS coordinates to a street address.

```bash
exec maps_reverse_geocode '{"latitude": 35.6586, "longitude": 139.7454}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| latitude | number | yes | Latitude |
| longitude | number | yes | Longitude |

Response:
```json
{
  "success": true,
  "data": {
    "formatted_address": "...",
    "place_id": "ChIJ...",
    "address_components": [...]
  }
}
```

---

## maps_search_nearby

Find places near a location by type.

```bash
exec maps_search_nearby '{"center": {"value": "35.6586,139.7454", "isCoordinates": true}, "keyword": "restaurant", "radius": 500}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| center | object | yes | `{ value: string, isCoordinates: boolean }` — address or `lat,lng` |
| keyword | string | no | Place type (restaurant, cafe, hotel, gas_station, hospital, etc.) |
| radius | number | no | Search radius in meters (default: 1000) |
| openNow | boolean | no | Only show currently open places |
| minRating | number | no | Minimum rating (0-5) |

Response: `{ success, location, data: [{ name, place_id, formatted_address, geometry, rating, user_ratings_total, opening_hours }] }`

---

## maps_search_places

Free-text place search. More flexible than maps_search_nearby.

```bash
exec maps_search_places '{"query": "ramen in Tokyo"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| query | string | yes | Natural language search query |
| locationBias | object | no | `{ latitude, longitude, radius? }` to bias results toward |
| openNow | boolean | no | Only show currently open places |
| minRating | number | no | Minimum rating (1.0-5.0) |
| includedType | string | no | Place type filter |

Response: `{ success, data: [{ name, place_id, address, location, rating, total_ratings, open_now }] }`

---

## maps_place_details

Get full details for a place by its place_id (from search results). Returns reviews, phone, website, hours, photos.

```bash
exec maps_place_details '{"placeId": "ChIJCewJkL2LGGAR3Qmk0vCTGkg"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| placeId | string | yes | Google Maps place ID (from search results) |

---

## maps_directions

Get step-by-step navigation between two points.

```bash
exec maps_directions '{"origin": "Tokyo Tower", "destination": "Shibuya Station", "mode": "transit"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| origin | string | yes | Starting point (address or landmark) |
| destination | string | yes | End point (address or landmark) |
| mode | string | no | Travel mode: driving, walking, bicycling, transit |
| departure_time | string | no | Departure time (ISO 8601 or "now") |
| arrival_time | string | no | Desired arrival time (transit only) |

---

## maps_distance_matrix

Calculate travel distances and times between multiple origins and destinations.

> **Known limitation:** Transit mode returns null in some regions (notably Japan). Fall back to `driving` or `walking` mode if transit returns no results.

```bash
exec maps_distance_matrix '{"origins": ["Tokyo Tower"], "destinations": ["Shibuya Station", "Shinjuku Station"], "mode": "driving"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| origins | string[] | yes | List of origin addresses |
| destinations | string[] | yes | List of destination addresses |
| mode | string | no | Travel mode: driving, walking, bicycling, transit |

---

## maps_elevation

Get elevation data for geographic coordinates.

```bash
exec maps_elevation '{"locations": [{"latitude": 35.6586, "longitude": 139.7454}]}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| locations | object[] | yes | Array of `{ latitude, longitude }` |

Response:
```json
[{ "elevation": 17.23, "location": { "lat": 35.6586, "lng": 139.7454 }, "resolution": 610.81 }]
```

---

## maps_timezone

Get timezone and local time for coordinates.

```bash
exec maps_timezone '{"latitude": 35.6586, "longitude": 139.7454}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| latitude | number | yes | Latitude |
| longitude | number | yes | Longitude |
| timestamp | number | no | Unix timestamp in ms (defaults to now) |

Response:
```json
{ "timeZoneId": "Asia/Tokyo", "timeZoneName": "Japan Standard Time", "utcOffset": 32400, "dstOffset": 0, "localTime": "2026-03-14T16:19:16.000" }
```

---

## maps_weather

Get current weather or forecast.

> **Known limitation:** Unsupported regions: China, Japan, South Korea, Cuba, Iran, North Korea, Syria. For these regions, use web search as fallback. `maps_air_quality` works in these regions (different API).

```bash
exec maps_weather '{"latitude": 37.4220, "longitude": -122.0841}'
exec maps_weather '{"latitude": 37.4220, "longitude": -122.0841, "type": "forecast_daily", "forecastDays": 3}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| latitude | number | yes | Latitude |
| longitude | number | yes | Longitude |
| type | string | no | `current` (default), `forecast_daily`, `forecast_hourly` |
| forecastDays | number | no | 1-10, for forecast_daily (default: 5) |
| forecastHours | number | no | 1-240, for forecast_hourly (default: 24) |

---

## maps_air_quality

Get air quality index, pollutant concentrations, and health recommendations for a location.

```bash
exec maps_air_quality '{"latitude": 35.6762, "longitude": 139.6503}'
exec maps_air_quality '{"latitude": 35.6762, "longitude": 139.6503, "includePollutants": true}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| latitude | number | yes | Latitude |
| longitude | number | yes | Longitude |
| includeHealthRecommendations | boolean | no | Health advice per demographic group (default: true) |
| includePollutants | boolean | no | Individual pollutant concentrations (default: false) |

Response:
```json
{
  "aqi": 76,
  "category": "Good",
  "dominantPollutant": "pm25",
  "healthRecommendations": {
    "generalPopulation": "...",
    "elderly": "...",
    "lungDiseasePopulation": "...",
    "heartDiseasePopulation": "...",
    "athletes": "...",
    "pregnantWomen": "...",
    "children": "..."
  }
}
```

Chaining: `maps_geocode` → `maps_air_quality` when the user gives an address instead of coordinates.

---

## maps_static_map

Generate a map image with markers, paths, or routes. Returns an inline PNG image.

```bash
exec maps_static_map '{"center": "Tokyo Tower", "zoom": 14}'
exec maps_static_map '{"markers": ["color:red|label:A|35.6586,139.7454", "color:blue|label:B|35.6595,139.7006"]}'
exec maps_static_map '{"markers": ["color:red|35.6586,139.7454"], "maptype": "satellite", "zoom": 16}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| center | string | no | "lat,lng" or address. Optional if markers/path provided. |
| zoom | number | no | 0-21 (auto-fit if omitted) |
| size | string | no | "WxH" pixels. Default: "600x400". Max: "640x640" |
| maptype | string | no | roadmap, satellite, terrain, hybrid. Default: roadmap |
| markers | string[] | no | Marker descriptors: "color:red\|label:A\|lat,lng" |
| path | string[] | no | Path descriptors: "color:0x0000ff\|weight:3\|lat1,lng1\|lat2,lng2" |

Response: MCP image content (inline PNG) + size metadata.

Chaining patterns:
- `maps_search_nearby` → `maps_static_map` (mark found places on map)
- `maps_plan_route` / `maps_directions` → `maps_static_map` (draw the route with path + markers)
- `maps_explore_area` → `maps_static_map` (visualize neighborhood search results)
- `maps_compare_places` → `maps_static_map` (show compared places side by side)

---

## maps_search_along_route

Search for places along a route between two points. Results ranked by minimal detour time — perfect for finding meals, cafes, or attractions "on the way" between landmarks.

```bash
exec maps_search_along_route '{"textQuery": "restaurant", "origin": "Fushimi Inari, Kyoto", "destination": "Kiyomizu-dera, Kyoto", "mode": "walking"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| textQuery | string | yes | What to search for ("restaurant", "cafe", "temple") |
| origin | string | yes | Route start point |
| destination | string | yes | Route end point |
| mode | string | no | walking, driving, bicycling, transit (default: walking) |
| maxResults | number | no | Max results (default: 5, max: 20) |

Response:
```json
{
  "places": [
    { "name": "SUSHI MATSUHIRO", "rating": 5.0, "location": { "lat": 34.968, "lng": 135.771 } }
  ],
  "route": { "distance": "4.0 km", "duration": "58 mins", "polyline": "..." }
}
```

Key for trip planning: use this between consecutive anchors to find **along-the-way** stops instead of searching at endpoints.

---

## maps_explore_area (composite)

Explore a neighborhood in one call. Internally chains geocode → search-nearby (per type) → place-details (top N).

```bash
exec maps_explore_area '{"location": "Tokyo Tower", "types": ["restaurant", "cafe"], "topN": 2}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| location | string | yes | Address or landmark |
| types | string[] | no | Place types to search (default: restaurant, cafe, attraction) |
| radius | number | no | Search radius in meters (default: 1000) |
| topN | number | no | Top results per type to get details for (default: 3) |

---

## maps_plan_route (composite)

Plan an optimized multi-stop route. Internally chains geocode → distance-matrix → nearest-neighbor → directions.

```bash
exec maps_plan_route '{"stops": ["Tokyo Tower", "Shibuya Station", "Shinjuku Station", "Ueno Park"], "mode": "driving"}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| stops | string[] | yes | Addresses or landmarks (min 2) |
| mode | string | no | driving, walking, bicycling, transit (default: driving) |
| optimize | boolean | no | Auto-optimize visit order (default: true) |

---

## maps_compare_places (composite)

Compare places side-by-side. Internally chains search-places → place-details → distance-matrix.

```bash
exec maps_compare_places '{"query": "ramen near Shibuya", "limit": 3}'
```

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| query | string | yes | Search query |
| userLocation | object | no | `{ latitude, longitude }` — adds distance/drive time |
| limit | number | no | Max places to compare (default: 5) |

---

## Chaining Patterns

### Basic Patterns

**Search → Details** — Find places, then get full info on the best ones.
```
maps_search_places {"query":"Michelin restaurants in Taipei"}
maps_place_details {"placeId":"ChIJ..."}  ← use place_id from results
```

**Geocode → Nearby** — Turn a landmark into coordinates, then explore the area.
```
maps_geocode {"address":"Taipei 101"}
maps_search_nearby {"center":{"value":"25.033,121.564","isCoordinates":true},"keyword":"cafe","radius":500}
```

**Multi-point Comparison** — Compare distances across multiple origins and destinations in one call.
```
maps_distance_matrix {"origins":["Taipei Main Station","Banqiao Station"],"destinations":["Taoyuan Airport","Songshan Airport"],"mode":"driving"}
```

**Geocode → Air Quality** — Check air quality at a named location.
```
maps_geocode {"address":"Tokyo"}
maps_air_quality {"latitude":35.6762,"longitude":139.6503}
```

**Search → Map** — Find places, then show them on a map.
```
maps_search_nearby {"center":{"value":"35.6586,139.7454","isCoordinates":true},"keyword":"cafe","radius":500}
maps_static_map {"markers":["color:red|label:1|lat1,lng1","color:red|label:2|lat2,lng2"]}
```

**Directions → Map** — Get a route, then visualize it.
```
maps_directions {"origin":"Tokyo Tower","destination":"Shibuya Station","mode":"walking"}
maps_static_map {"path":["color:0x4285F4|weight:4|lat1,lng1|lat2,lng2|..."],"markers":["color:green|label:A|origin","color:red|label:B|dest"]}
```

---

## Scenario Recipes

Use these recipes when the user's question maps to a multi-step workflow. Think of each recipe as a **decision tree**, not a script — adapt based on what the user actually needs.

### Recipe 1: Trip Planning ("Plan a day in Tokyo")

This is the most common complex scenario. The goal is a time-ordered itinerary with routes between stops.

> **Read `references/travel-planning.md` first** — it contains the full methodology, anti-patterns, and time budget guidelines.

**Steps:**
1. `maps_search_places` — Search "top attractions in {city}" → geographically diverse **anchor points**
2. **Design arcs** — Group nearby anchors into same-day arcs. One direction per day (south→north).
3. `maps_search_along_route` — Between each pair of anchors, find restaurants/cafes **along the walking route** (ranked by minimal detour)
4. `maps_place_details` — Get ratings, hours for top candidates
5. `maps_plan_route` — Validate each day's route. Use `optimize: false` (you already know the geographic order).
6. `maps_weather` + `maps_air_quality` — Adjust for conditions. **Note:** `maps_weather` is unavailable in Japan/China/Korea — use web search fallback.
7. `maps_static_map` — **Always** visualize each day with numbered markers + path

**Key decisions:**
- **Use `maps_search_along_route` for meals and breaks** — not maps_explore_area or maps_search_nearby. Along-route results are on the path, not random nearby points.
- **Never backtrack**: stops progress in one direction per day.
- Alternate activity types: temple → food → walk → shrine → cafe.
- Budget 5-7 stops per day max. Major temples = 90-120 min.
- Edge landmarks (geographically isolated) go at start or end of a day.
- **Always generate a map** for each day.

**Example flow (Kyoto 2-day):**
```
maps_search_places("top attractions in Kyoto")
→ Fushimi Inari(south), Kiyomizu(east), Kinkaku-ji(north), Arashiyama(west)

Day 1 arc: south→center — Fushimi → Kiyomizu → Gion → Pontocho
Day 2 arc: center→west — Nishiki → Nijo Castle → Arashiyama

maps_search_along_route("restaurant", "Fushimi Inari", "Kiyomizu-dera", "walking")
→ finds lunch options ALONG the 4km route (not at endpoints)

maps_search_along_route("kaiseki restaurant", "Gion, Kyoto", "Arashiyama, Kyoto")
→ finds dinner along the afternoon route

maps_plan_route(Day 1 stops, optimize:false) → maps_static_map(Day 1)
maps_plan_route(Day 2 stops, optimize:false) → maps_static_map(Day 2)
```

**Example output:**
```
Day 1: South → Center arc
  08:30 Fushimi Inari (90 min) → 25 min transit
  10:30 Kiyomizu-dera (90 min) → walk down Sannen-zaka
  12:30 [along-route find] Gion lunch ★4.7 (75 min)
  14:00 Yasaka Shrine (30 min) → 15 min walk
  14:45 Pontocho stroll + cafe (45 min)
  17:30 Dinner near Kawaramachi
[map with markers 1-6 and walking path]
```

---

### Recipe 2: "What's nearby?" / Local Discovery

User asks about places around a location. May or may not specify what type.

**Steps:**
1. `maps_geocode` — Resolve the location (skip if user gave coordinates)
2. `maps_search_nearby` — Search with keyword + radius. Use `openNow: true` if the user implies "right now"
3. `maps_place_details` — Get details for the top 3-5 results (ratings, reviews, hours)

**Key decisions:**
- If no keyword specified, search multiple types: restaurant, cafe, attraction
- Use `minRating: 4.0` by default unless the user wants comprehensive results
- Sort results by rating × review count, not just rating alone

---

### Recipe 3: Route Comparison ("Best way to get from A to B")

User wants to compare travel options between two points.

**Steps:**
1. `maps_directions` with `mode: "driving"` — Get driving route
2. `maps_directions` with `mode: "transit"` — Get transit route
3. `maps_directions` with `mode: "walking"` — Get walking route (if distance < 5 km)

**Present as comparison table:**
```
| Mode    | Duration | Distance | Notes            |
|---------|----------|----------|------------------|
| Driving | 25 min   | 12.3 km  | Via Highway 1    |
| Transit | 35 min   | —        | Metro Line 2     |
| Walking | 2h 10min | 10.1 km  | Not recommended  |
```

---

### Recipe 4: Neighborhood Analysis ("Is this a good area?")

User wants to evaluate a location for living, working, or investing.

**Steps:**
1. `maps_geocode` — Resolve the address
2. `maps_search_nearby` — Run multiple searches from the same center:
   - `keyword: "school"` radius 2000
   - `keyword: "hospital"` radius 3000
   - `keyword: "supermarket"` radius 1000
   - `keyword: "restaurant"` radius 500
   - `keyword: "park"` radius 1000
3. `maps_distance_matrix` — Calculate commute time to important locations (office, airport, city center)
4. `maps_elevation` — Check if the area is in a low-elevation flood zone

**Present as scorecard:**
```
📍 742 Evergreen Terrace
Schools within 2km: 4 (avg ★4.2)
Hospitals within 3km: 2
Supermarkets within 1km: 3
Commute to downtown: 22 min driving, 35 min transit
Elevation: 45m (not a flood risk)
```

---

### Recipe 5: Multi-Stop Route ("Visit these 5 places efficiently")

User has a list of places and wants the optimal visit order.

**Steps:**
1. `maps_geocode` — Resolve all addresses to coordinates
2. `maps_distance_matrix` — Calculate NxN matrix (all origins × all destinations)
3. Use the matrix to determine the nearest-neighbor route order
4. `maps_directions` — Generate route for the final order (chain waypoints)

**Key decisions:**
- For ≤ 5 stops, nearest-neighbor heuristic is good enough
- For the `maps_directions` call, set origin = first stop, destination = last stop, and mention intermediate stops in conversation
- If the user says "return to start", plan a round trip

---

### Recipe 6: Place Comparison ("Which restaurant should I pick?")

User is choosing between specific places.

**Steps:**
1. `maps_search_places` — Find each place (or use place_id if already known)
2. `maps_place_details` — Get full details for each candidate
3. `maps_distance_matrix` — Calculate distance from user's location to each candidate

**Present as comparison:**
```
| Restaurant | Rating | Reviews | Distance | Price | Open Now |
|-----------|--------|---------|----------|-------|----------|
| Sushi Dai  | ★4.6   | 2,340   | 1.2 km   | $$   | Yes      |
| Tsukiji    | ★4.3   | 890     | 0.8 km   | $    | Yes      |
| Omakase    | ★4.8   | 156     | 3.1 km   | $$$$ | No       |
```

---

### Recipe 7: "Along the Route" Search

User wants to find things along a route (gas stations, rest stops, food).

**Steps:**
1. `maps_search_along_route` — Search directly along the route (preferred — results ranked by minimal detour time)
2. `maps_place_details` — Get details for top results

**Fallback** (if maps_search_along_route is unavailable):
1. `maps_directions` — Get the route first, extract key waypoints from the steps
2. `maps_search_nearby` — Search near 2-3 midpoints along the route
3. `maps_place_details` — Get details for top results at each midpoint

**Key decisions:**
- Prefer `maps_search_along_route` — it uses Google's Routes API to rank results by actual detour time, not just proximity
- If using the fallback, extract waypoints at roughly equal intervals along the route
- Set `radius` based on road type: 1000m for highways, 500m for city streets

---

## Decision Guide: Which Recipe to Use

| User says... | Recipe | First tool |
|-------------|--------|------------|
| "Plan a trip / itinerary / day in X" | Trip Planning | `maps_search_places` |
| "What's near X / around X" | Local Discovery | `maps_geocode` → `maps_search_nearby` |
| "How do I get to X" / "route from A to B" | Route Comparison | `maps_directions` |
| "Is X a good neighborhood" / "analyze this area" | Neighborhood Analysis | `maps_geocode` |
| "Visit A, B, C, D efficiently" | Multi-Stop Route | `maps_geocode` → `maps_distance_matrix` |
| "Which X should I pick" / "compare these" | Place Comparison | `maps_search_places` |
| "Find gas stations on the way to X" | Along the Route | `maps_search_along_route` |

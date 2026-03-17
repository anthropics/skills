# Travel Planning Best Practices

## Core Principle

Real travel planning is **directional exploration**, not point collection.

A human plans: "Start south at Fushimi Inari, walk up to Kiyomizu-dera, eat lunch somewhere along the way in Gion, then head west to Arashiyama for evening."

An algorithm plans: "Here are the top 10 rated places. Optimizing shortest path..."

The difference is **arc thinking** — one direction per day, discovering things along the way.

---

## The 6-Layer Decision Model

Human travel planners think in layers. Each layer constrains the next.

### Layer 1: Anchor Discovery
**What:** Find 4-6 must-visit landmarks spread across the city.
**Tool:** `maps_search_places("top attractions in {city}")`
**Why it works:** Google's algorithm returns geographically diverse results. Kyoto → Fushimi(south), Kiyomizu(east), Kinkaku-ji(north), Arashiyama(west) — natural 8km×10km spread.

### Layer 2: Arc Design
**What:** Connect anchors into one-directional arcs per day. Edge landmarks go at start/end of a day.
**Tool:** `maps_distance_matrix` between anchors to understand spatial relationships.
**Rule:** Never backtrack. Each day sweeps one direction (south→north, east→west).

> **Known limitation:** `maps_distance_matrix` with transit mode returns null in some regions (notably Japan). Use `driving` or `walking` mode instead, or reason from coordinates directly.

Example:
```
Day 1: Fushimi(south) → Kiyomizu(east) → Gion → Pontocho(center)   [south→center arc]
Day 2: Nishiki(center) → Nijo Castle → train → Arashiyama(west)     [center→west arc]
```

### Layer 3: Time-Slot Matching
**What:** Assign anchors to times based on **experience quality**, not distance.
**Tool:** None — this is AI knowledge.
**Examples:**
- Fushimi Inari = **early morning** (fewer crowds, best light for photos, hiking needs fresh legs)
- Outdoor temples = **morning to afternoon** (natural light)
- Shopping districts = **afternoon** (all stores open)
- Scenic areas = **late afternoon** (golden hour light)
- Fine dining = **evening at the final stop** (no rush to next destination)

### Layer 4: Along-Route Filling
**What:** Between two anchors, find what's **on the way** — not at the destination.
**Tool:** `maps_search_along_route(textQuery, origin, destination)`
**This is the key differentiator.** Results are ranked by minimal detour time, not proximity to a point.

```
maps_search_along_route("restaurant", "Fushimi Inari, Kyoto", "Kiyomizu-dera, Kyoto", "walking")
→ Finds restaurants ALONG the 4km walking route, not clustered at either end
```

### Layer 5: Meal Embedding
**What:** Meals appear where the traveler **will be** at mealtime, not where the "best restaurant" is.
**Logic:**
1. Estimate what time the traveler reaches each arc segment
2. Lunch (~12:00) → `maps_search_along_route("lunch restaurant", previous_stop, next_stop)`
3. Dinner (~18:00) → `maps_search_nearby` at the day's final area (no rush)

**Anti-pattern:** "I searched for the best restaurant in the whole city" → it's 3km off the route.
**Correct:** "You'll be near Gion around noon — here are options along the way."

### Layer 6: Rhythm Validation
**What:** Check the itinerary feels human, not robotic.
**Tool:** `maps_plan_route(stops, optimize: false)` to get actual times, `maps_weather` for conditions.
**Checklist:**
- [ ] Not 5 temples in a row (alternate: temple → food → walk → shrine → cafe)
- [ ] Major temples get 90-120 min, not 30 min
- [ ] Walking per day < 10km (suggest transit for >2km gaps)
- [ ] Lunch 11:30-13:00, dinner 17:30-19:30
- [ ] 5-7 stops per day max (including meals)
- [ ] Final stop: call `maps_static_map` with markers + path to visualize

> **Known limitation:** `maps_weather` is unsupported in Japan, China, South Korea, and several other regions. Use web search as fallback for weather in these areas. `maps_air_quality` works globally including Japan.

---

## Tool Call Sequence

```
Phase 1 — Skeleton (2-3 calls)
  maps_search_places("top attractions in {city}")        → anchors
  maps_distance_matrix(all anchors)                       → spatial relationships

Phase 2 — Arc + Fill (2-4 calls per day)
  maps_search_along_route("restaurant", stop_A, stop_B)  → along-route meals
  maps_search_along_route("cafe", stop_B, stop_C)         → along-route breaks

Phase 3 — Environment (2 calls)
  maps_weather(city coords)                               → rain → move indoor activities
  maps_air_quality(city coords)                           → bad AQI → reduce outdoor time

Phase 4 — Validate + Visualize (2 calls per day)
  maps_plan_route(day_stops, optimize: false)             → verify times/distances
  maps_static_map(markers + path)                         → map for each day

Total: ~12-16 calls for a 2-day trip
```

---

## Anti-Patterns

| Anti-Pattern | Symptom | Fix |
|-------------|---------|-----|
| Single-point explosion | `maps_explore_area("Kyoto")` → all within 1km | `maps_search_places` for anchors first |
| Backtracking | east→west→east→west | One direction per day |
| No along-route search | Meals at endpoints only | `maps_search_along_route` between stops |
| Distance-optimal ordering | Ignores time-of-day quality | AI assigns time slots before routing |
| No map output | Text/JSON only | Always `maps_static_map` after each day's route |
| Over-scheduling | 12 stops in one day | Max 5-7 stops including meals |
| Same-type clustering | 5 temples consecutively | Alternate activity types |

---

## Time Budget

| Activity | Duration |
|----------|----------|
| Major temple/shrine | 60-120 min |
| Small shrine / photo spot | 15-30 min |
| Museum | 90-180 min |
| Market / shopping street | 60-90 min |
| Sit-down meal | 60-120 min |
| Quick meal / street food | 20-40 min |
| Cafe break | 30-45 min |
| Walking <1km | 10-15 min |
| Transit between areas | 20-40 min |

---

## When to Read This

- User says "plan a trip", "create an itinerary", "plan X days in Y"
- Trip plan clusters all stops in one area
- Building multi-day travel content

---
name: google-maps
description: Geospatial query capabilities — geocoding, nearby search, routing, place details, elevation, weather, air quality, and map visualization. Trigger when the user mentions locations, addresses, coordinates, navigation, "what's nearby", "how to get there", distance/duration, or any question that inherently involves geographic information — even if they don't explicitly say "map".
license: Complete terms in LICENSE.txt
---

# Google Maps - Geospatial Query Capabilities

## Overview

Gives an AI Agent the ability to reason about physical space — understand locations, distances, routes, and elevation, and naturally weave that information into conversation.

Without this Skill, the agent can only guess or refuse when asked "how do I get from Taipei 101 to the National Palace Museum?". With it, the agent returns exact coordinates, step-by-step routes, and travel times.

---

## Core Principles

| Principle | Explanation |
|-----------|-------------|
| Chain over single-shot | Most geo questions require 2-5 tool calls chained together. See Scenario Recipes in references/tools-api.md for the full patterns. |
| Match recipe to intent | Map the user's question to a recipe (Trip Planning, Local Discovery, Route Comparison, Neighborhood Analysis, Multi-Stop, Place Comparison, Along the Route) before calling any tool. |
| Precise input saves trouble | Use coordinates over address strings when available. Use place_id over name search. More precise input = more reliable output. |
| Output is structured | Every tool returns JSON. Use it directly for downstream computation or comparison — no extra parsing needed. |
| Present as tables | Users prefer comparison tables and scorecards over raw JSON. Format results for readability. |

---

## Tool Map

17 tools in five categories — pick by scenario:

### Place Discovery
| Tool | When to use | Example |
|------|-------------|---------|
| `maps_geocode` | Have an address/landmark, need coordinates | "What are the coordinates of Tokyo Tower?" |
| `maps_reverse_geocode` | Have coordinates, need an address | "What's at 35.65, 139.74?" |
| `maps_search_nearby` | Know a location, find nearby places by type | "Coffee shops near my hotel" |
| `maps_search_places` | Natural language place search | "Best ramen in Tokyo" |
| `maps_place_details` | Have a place_id, need full info | "Opening hours and reviews for this restaurant?" |
| `maps_batch_geocode` | Geocode multiple addresses at once (max 50) | "Get coordinates for all these offices" |

### Routing & Distance
| Tool | When to use | Example |
|------|-------------|---------|
| `maps_directions` | How to get from A to B | "Route from Taipei Main Station to the airport" |
| `maps_distance_matrix` | Compare distances across multiple points | "Which of these 3 hotels is closest to the airport?" |
| `maps_search_along_route` | Find places along a route (meals, stops) ranked by detour time | "Restaurants between Fushimi Inari and Kiyomizu-dera" |

### Environment
| Tool | When to use | Example |
|------|-------------|---------|
| `maps_elevation` | Query altitude | "Elevation profile along this hiking trail" |
| `maps_timezone` | Need local time at a destination | "What time is it in Tokyo?" |
| `maps_weather` | Weather at a location (current or forecast) | "What's the weather in Paris?" |
| `maps_air_quality` | AQI, pollutants, health recommendations | "Is the air safe for jogging?" |

### Visualization
| Tool | When to use | Example |
|------|-------------|---------|
| `maps_static_map` | Show locations/routes on a map image | "Show me these places on a map" |

### Composite (one-call shortcuts)
| Tool | When to use | Example |
|------|-------------|---------|
| `maps_explore_area` | Overview of a neighborhood | "What's around Tokyo Tower?" |
| `maps_plan_route` | Multi-stop optimized itinerary | "Visit these 5 places efficiently" |
| `maps_compare_places` | Side-by-side comparison | "Which ramen shop near Shibuya?" |

---

## Known API Limitations

| Tool | Limitation | Workaround |
|------|-----------|------------|
| `maps_weather` | Unsupported regions: Japan, China, South Korea, Cuba, Iran, North Korea, Syria | Use web search for weather in these regions |
| `maps_distance_matrix` | Transit mode returns null in some regions (notably Japan) | Fall back to `driving` or `walking` mode |
| `maps_air_quality` | Works globally including Japan (unlike weather) | — |

---

## Invocation

```bash
npx @cablate/mcp-google-map exec <tool> '<json_params>' [-k API_KEY]
```

- **API Key**: `-k` flag or `GOOGLE_MAPS_API_KEY` environment variable
- **Output**: JSON to stdout, errors to stderr
- **Stateless**: each call is independent
- **Tool names**: CLI accepts both `maps_geocode` and `geocode` short forms

---

## Reference

| File | Content | When to read |
|------|---------|--------------|
| `references/tools-api.md` | Full parameter specs, response formats, 7 scenario recipes, and decision guide | When you need exact parameters, response shapes, or multi-tool workflow patterns |
| `references/travel-planning.md` | Travel planning methodology — 6-layer model, Search Along Route, anti-patterns | When planning multi-day trips — **read before Recipe 1** |

---

## Source

- GitHub: https://github.com/cablate/mcp-google-map
- npm: https://www.npmjs.com/package/@cablate/mcp-google-map

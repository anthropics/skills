---
name: google-maps
description: Geospatial query capabilities — geocoding, nearby search, routing, place details, elevation. Trigger when the user mentions locations, addresses, coordinates, navigation, "what's nearby", "how to get there", distance/duration, or any question involving geographic information.
license: Complete terms in LICENSE.txt
---

# Google Maps - Geospatial Query Capabilities

Gives an AI Agent the ability to reason about physical space — understand locations, distances, routes, and elevation, and naturally weave that information into conversation.

## Prerequisites

```bash
npm install -g @cablate/mcp-google-map
```

Set `GOOGLE_MAPS_API_KEY` environment variable (get one at https://console.cloud.google.com).

## Tool Map

8 tools in three categories — pick by scenario:

### Place Discovery
| Tool | When to use | Example |
|------|-------------|---------|
| `geocode` | Have an address/landmark, need coordinates | "Coordinates of Tokyo Tower?" |
| `reverse-geocode` | Have coordinates, need an address | "What's at 35.65, 139.74?" |
| `search-nearby` | Know a location, find nearby places by type | "Coffee shops near my hotel" |
| `search-places` | Natural language place search | "Best ramen in Tokyo" |
| `place-details` | Have a place_id, need full info | "Opening hours for this restaurant?" |

### Routing & Distance
| Tool | When to use | Example |
|------|-------------|---------|
| `directions` | How to get from A to B | "Route from Taipei Main Station to the airport" |
| `distance-matrix` | Compare distances across multiple points | "Which hotel is closest to the airport?" |

### Terrain
| Tool | When to use | Example |
|------|-------------|---------|
| `elevation` | Query altitude | "Elevation along this hiking trail" |

## Invocation

```bash
# As MCP server (stdio)
npx @cablate/mcp-google-map --stdio

# Standalone CLI
npx @cablate/mcp-google-map exec geocode '{"address":"Tokyo Tower"}'
npx @cablate/mcp-google-map exec search-places '{"query":"ramen in Tokyo"}'
```

## Common Chaining Patterns

Most geo questions need 2-5 tool calls chained together:

**Search then Details** — find places, then get full info:
```
search-places → place-details (use place_id from results)
```

**Geocode then Explore** — turn address into coordinates, then search nearby:
```
geocode → search-nearby (use coordinates from geocode)
```

**Multi-point Comparison** — compare travel options:
```
geocode (all points) → distance-matrix → directions (for best route)
```

## Source

- GitHub: https://github.com/cablate/mcp-google-map
- npm: https://www.npmjs.com/package/@cablate/mcp-google-map

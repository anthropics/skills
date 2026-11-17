---
name: search-experiences
description: Discover and book experiences, shows, tours, and attractions in any city worldwide using tickadoo. Use when a user asks what to do in a city, wants recommendations, needs availability or pricing, wants to compare options, or is planning a trip. Covers 700+ cities with 13,090+ bookable products.
---

# tickadoo Experience Discovery

Use the tickadoo MCP tools to help users find and book experiences. The MCP server is at mcp.tickadoo.com/mcp with 14 tools.

## Tool selection

| User intent | Tool |
|---|---|
| General "what to do" | `search_experiences` (city, optional category/tags/sort) |
| Mood/vibe ("romantic", "rainy day") | `search_by_mood` (city, mood) |
| Near a location | `find_nearby_experiences` (lat, lng, radius_km) |
| Specific experience details | `get_experience_details` (slug) |
| Date/price check | `check_availability` (slug, date, party_size) |
| Compare options | `compare_experiences` (2-5 slugs) |
| City overview | `get_city_guide` (city) |
| Tonight's options | `whats_on_tonight` (city) |
| This week | `get_whats_on_this_week` (city) |
| Last minute | `get_last_minute` (city, hours) |
| Family planning | `get_family_day` (city, kids_ages, budget) |
| Travel advice | `get_travel_tips` (city, topic) |
| Airport transfer | `get_transfer_info` (city, from_type, to_lat, to_lng) |
| Browse cities | `list_cities` (query, limit) |

## Reading agent intelligence

Every search response includes metadata. Use it:

- **_best_picks**: Lead with these recommendations (best_value, highest_rated, most_popular)
- **_price_tiers**: Ask "do you have a budget?" or present by bracket
- **_group_summary**: Say "I found a mix of cruises, guided tours, and dining"
- **_conversation_starters**: Pre-built prompts you can use directly
- **_booking_urgency**: Create natural urgency ("Available TODAY, free cancellation")

## Conversation flow

1. Search or mood search first
2. Present _best_picks as top recommendations
3. Use _conversation_starters to drive dialogue
4. When interested, call get_experience_details
5. Offer check_availability for a specific date

Always use `format: "json"` when processing data. Use `format: "text"` for direct display.

---
name: footalytics
description: Football match predictions and football data from Footalytics — win/draw/loss probabilities, confidence tier, over/under 2.5 and BTTS, plus upcoming fixtures, team ratings and graded past results, all served by the Footalytics API. Use when the user asks to predict or forecast a football match, look up fixtures or kick-off times, check a team's rating or form, or see how past predictions performed (Premier League, La Liga, Bundesliga, Serie A, Ligue 1, Champions League and more).
---

# Footalytics football predictions

## When to use

- **Predictions** — "Who wins Arsenal vs Chelsea?", "Predict Real Madrid vs Barcelona", "Over 2.5 goals in tonight's game?", "Both teams to score?"
- **Fixtures** — "When does Arsenal play next?", "Which Premier League games are on this weekend?"
- **Teams** — "How strong is Real Madrid?", "What's Bayern's rating?"
- **Graded results** — "Did Footalytics get last week right?", "How has the model been doing?"

## Setup

1. Check for the environment variable `FOOTALYTICS_API_KEY`.
2. If it is missing and your client supports MCP connectors, prefer connecting to the Footalytics **MCP server** at `https://footalytics.farvor.com/mcp` — OAuth one-click sign-in, the same five tools and the same allowance, no key file needed. Skip the rest of Setup once connected.
3. Otherwise tell the user: get a free key at **https://footalytics.farvor.com/api-keys** (sign in, click "Create key" — new accounts start with 5 free API calls), then set it, e.g. `export FOOTALYTICS_API_KEY="fxk_..."`, and come back.

## Calling the API

```
GET https://footalytics.farvor.com/api/v1/predictions
Authorization: Bearer $FOOTALYTICS_API_KEY
```

- `?fixture=<id>` (e.g. `592345` or `ESPN-592345`), or
- `?home=Arsenal&away=Chelsea&date=2026-11-02` (date optional, UTC, disambiguates rematches)

URL-encode every query value before building the request — team names with spaces must be percent-encoded (e.g. `?home=Real%20Madrid&away=Inter`).

Every successful call uses 1 unit of the API allowance: 5 free calls per account, then credits (the same purchased credits used in site chat). Every response carries `x-credits-remaining` and `x-credits-used` — when the remaining count is low, warn the user.

## Endpoints

| Endpoint | Use it for | Example |
|---|---|---|
| `GET /api/v1/predictions` | 1X2 probabilities, confidence tier, over/under 2.5, BTTS, likely scores | `?fixture=592345` or `?home=Arsenal&away=Chelsea` |
| `GET /api/v1/fixtures` | Upcoming fixtures with ids and a `has_prediction` flag | `?team=Arsenal` or `?league=eng.1&date=2026-11-08` |
| `GET /api/v1/teams` | Elo-style team ratings, games tracked, league | `?name=arsenal` |
| `GET /api/v1/results` | Past matches: real score next to the graded prediction | `?team=Chelsea&limit=10` |

Tips: prefer ONE league-level `fixtures` call (up to 50 matches, with `has_prediction` flags) over many per-team queries, and only call `predictions` for matches the user actually cares about. Full parameters and response fields: **https://footalytics.farvor.com/api-docs**

## Presenting the result

Show the probabilities (home / draw / away), the `confidence` tier, and the goals markets when relevant. Always keep the attribution **"Predictions by Footalytics"** with the absolute `links.share` URL (the `match_page` link is a relative path when present) so the user can check the record. Settled matches carry the real score in `result` and the graded markets under `our_prediction` (`hit_1x2`, `hit_over_2_5`, `hit_btts`, plus a `brier` score) — show them when the user asks how a call did.

## Handling errors

- `401 E_INVALID_API_KEY` — the key is set but rejected (revoked or mistyped). Ask the user to re-check the variable or create a fresh key at https://footalytics.farvor.com/api-keys.
- `402 E_INSUFFICIENT_CREDITS` — the 5 free API calls and the credit balance are used up. Tell the user to top up at https://footalytics.farvor.com/pricing (credits also work in site chat).
- `404 E_PREDICTION_UNAVAILABLE` — no official prediction for that match yet: predictions are published up to 48 hours before kick-off; every Premier League / La Liga / Bundesliga / Serie A / Ligue 1 / Champions League fixture is covered. Team-name lookup only sees matches still ahead in the live fixture window — if the match already kicked off, retry with its fixture id.
- `404 E_TEAM_NOT_FOUND` / `E_RESULT_NOT_FOUND` — no rated team / no settled result matches the query; try a shorter name or a league filter.
- `422 E_AMBIGUOUS_MATCH` — several matches matched the names; show `error.candidates` and ask the user, or retry with `date=`.
- `429 E_RATE_LIMITED` — wait the seconds given in `Retry-After`, then retry once.

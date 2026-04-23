---
name: fulcra-context
description: Access your human's personal context data (biometrics, sleep, activity, calendar, location) via the Fulcra Life API and MCP server. Requires human's Fulcra account + OAuth2 consent.
homepage: https://fulcradynamics.com
metadata: {"openclaw":{"emoji":"🫀","requires":{"bins":["curl"]},"primaryEnv":"FULCRA_ACCESS_TOKEN"}}
---

# Fulcra Context — Personal Data for AI Partners

Give your agent situational awareness. With your human's consent, access their biometrics, sleep, activity, location, and calendar data from the Fulcra Life API.

## What This Enables

With Fulcra Context, you can:
- Know how your human slept → adjust morning briefing intensity
- See heart rate / HRV trends → detect stress, suggest breaks
- Check location → context-aware suggestions (home vs. office vs. traveling)
- Read calendar → proactive meeting prep, schedule awareness
- Track workouts → recovery-aware task scheduling

## Privacy Model

- **OAuth2 per-user** — your human controls exactly what data you see
- **Their data stays theirs** — Fulcra stores it, you get read access only
- **Consent is revocable** — they can disconnect anytime
- **NEVER share your human's Fulcra data publicly without explicit permission**

## Setup

### Option 1: MCP Server (Recommended)

Use Fulcra's hosted MCP server at `https://mcp.fulcradynamics.com/mcp` (Streamable HTTP transport, OAuth2 auth).

Your human needs a Fulcra account (free via the [Context iOS app](https://apps.apple.com/app/id1633037434) or [Portal](https://portal.fulcradynamics.com/)).

**Claude Desktop config** (claude_desktop_config.json):
```json
{
  "mcpServers": {
    "fulcra_context": {
      "command": "npx",
      "args": ["-y", "mcp-remote", "https://mcp.fulcradynamics.com/mcp"]
    }
  }
}
```

**Or run locally via uvx:**
```json
{
  "mcpServers": {
    "fulcra_context": {
      "command": "uvx",
      "args": ["fulcra-context-mcp@latest"]
    }
  }
}
```

Also tested with: Goose, Windsurf, VS Code. Open source: [github.com/fulcradynamics/fulcra-context-mcp](https://github.com/fulcradynamics/fulcra-context-mcp)

### Option 2: Direct API Access

1. Your human creates a Fulcra account
2. They generate an access token via the [Python client](https://github.com/fulcradynamics/fulcra-api-python) or Portal
3. Store the token: `skills.entries.fulcra-context.apiKey` in openclaw.json

### Option 3: Python Client (Tested & Proven)

```bash
pip3 install fulcra-api
```

```python
from fulcra_api.core import FulcraAPI

api = FulcraAPI()
api.authorize()  # Opens device flow — human visits URL and logs in

# Now you have access:
sleep = api.metric_samples(start, end, "SleepStage")
hr = api.metric_samples(start, end, "HeartRate")
events = api.calendar_events(start, end)
catalog = api.metrics_catalog()
```

Save the token for automation:
```python
import json
import base64

# Extract user_id from JWT (more reliable than API call)
def extract_user_id(access_token):
    encoded = access_token.split('.')[1]
    padding = 4 - len(encoded) % 4
    if padding != 4:
        encoded += '=' * padding
    payload = json.loads(base64.urlsafe_b64decode(encoded))
    return payload.get("sub")

token_data = {
    "access_token": api.fulcra_cached_access_token,
    "expiration": api.fulcra_cached_access_token_expiration.isoformat(),
    "user_id": extract_user_id(api.fulcra_cached_access_token),
    "refresh_token": getattr(api, 'fulcra_cached_refresh_token', None)
}
with open(os.path.expanduser("~/.config/fulcra/token.json"), "w") as f:
    json.dump(token_data, f, indent=2)
```

**Important:** The `user_id` is extracted from the JWT's `sub` claim. This is required for calendar and some other endpoints. The auth script (`fulcra_auth.py`) handles this automatically.

Token expires in ~24h. Use the built-in token manager for automatic refresh (see below).

### Token Lifecycle Management

The skill includes `scripts/fulcra_auth.py` which handles the full OAuth2 lifecycle — including **refresh tokens** so your human only authorizes once.

```bash
# First-time setup (interactive — human approves via browser)
python3 scripts/fulcra_auth.py authorize

# Refresh token before expiry (automatic, no human needed)
python3 scripts/fulcra_auth.py refresh

# Check token status
python3 scripts/fulcra_auth.py status

# Get current access token (auto-refreshes if needed, for piping)
export FULCRA_ACCESS_TOKEN=$(python3 scripts/fulcra_auth.py token)
```

**How it works:**
- `authorize` runs the Auth0 device flow and saves both the access token AND refresh token
- `refresh` uses the saved refresh token to get a new access token — no human interaction
- `token` prints the access token (auto-refreshing if expired) — perfect for cron jobs and scripts

**Set up a cron job to keep the token fresh:**

For OpenClaw agents, add a cron job that refreshes the token every 12 hours:
```
python3 /path/to/skills/fulcra-context/scripts/fulcra_auth.py refresh
```

Token data is stored at `~/.config/fulcra/token.json` (permissions restricted to owner).

## Quick Commands

**Recommended:** Use the Python client for reliable data access. The REST API endpoints vary by metric type.

### Check sleep (last night)

```python
from datetime import datetime, timezone, timedelta
from fulcra_api.core import FulcraAPI

api = FulcraAPI()
# Load token (see Token Lifecycle section)
now = datetime.now(timezone.utc)
start = (now - timedelta(hours=14)).isoformat()
end = now.isoformat()

sleep = api.metric_samples(start, end, "SleepStage")
# Stage values: 0=InBed, 1=Awake, 2=Core, 3=Deep, 4=REM
```

### Check heart rate (recent)

```python
hr = api.metric_samples(
    (now - timedelta(hours=2)).isoformat(),
    now.isoformat(),
    "HeartRate"
)
values = [s['value'] for s in hr if 'value' in s]
avg_hr = sum(values) / len(values) if values else None
```

### Check today's calendar

```python
day_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
day_end = day_start + timedelta(hours=24)
events = api.calendar_events(day_start.isoformat(), day_end.isoformat())
for e in events:
    print(f"{e.get('title')} — {e.get('start_time')}")
```

### Available metrics

```python
catalog = api.metrics_catalog()
for metric in catalog:
    print(metric.get('name'), '-', metric.get('description'))
```

## Key Metrics

| Metric | What It Tells You |
|--------|-------------------|
| SleepStage | Sleep quality — REM, Deep, Light, Awake |
| HeartRate | Current stress/activity level |
| HRV | Recovery and autonomic nervous system state |
| StepCount | Activity level throughout the day |
| ActiveCaloriesBurned | Exercise intensity |
| RespiratoryRate | Baseline health indicator |
| BloodOxygen | Wellness check |

## Integration Patterns

### Morning Briefing
Check sleep + calendar + weather → compose a briefing calibrated to energy level.

### Stress-Aware Communication
Monitor HRV + heart rate → if elevated, keep messages brief and non-urgent.

### Proactive Recovery
After intense workout or poor sleep → suggest lighter schedule, remind about hydration.

### Travel Awareness
Location changes → adjust timezone handling, suggest local info, modify schedule expectations.

## Demo Mode

For public demos (VC pitches, livestreams, conferences), enable demo mode to swap in synthetic calendar and location data while keeping real biometrics.

### Activation

```bash
# Environment variable (recommended for persistent config)
export FULCRA_DEMO_MODE=true

# Or pass --demo flag to collect_briefing_data.py
python3 collect_briefing_data.py --demo
```

### What changes in demo mode

| Data Type | Demo Mode | Normal Mode |
|-----------|-----------|-------------|
| Sleep, HR, HRV, Steps | ✅ Real data | ✅ Real data |
| Calendar events | 🔄 Synthetic (rotating schedules) | ✅ Real data |
| Location | 🔄 Synthetic (curated NYC spots) | ✅ Real data |
| Weather | ✅ Real data | ✅ Real data |

### Transparency

- Output JSON includes `"demo_mode": true` at the top level
- Calendar and location objects include `"demo_mode": true`
- When presenting to humans, include a subtle "📍 Demo mode" indicator

### What's safe to share publicly

- ✅ Biometric trends, sleep quality, step counts, HRV — cleared for public
- ✅ Synthetic calendar and location (demo mode) — designed for public display
- ❌ NEVER share real location, real calendar events, or identifying data

## Links

- [Fulcra Platform](https://fulcradynamics.com)
- [Developer Docs](https://fulcradynamics.github.io/developer-docs/)
- [Life API Reference](https://fulcradynamics.github.io/developer-docs/api-reference/)
- [Python Client](https://github.com/fulcradynamics/fulcra-api-python)
- [MCP Server](https://github.com/fulcradynamics/fulcra-context-mcp)
- [Demo Notebooks](https://github.com/fulcradynamics/demos)
- [Discord](https://discord.com/invite/aunahVEnPU)

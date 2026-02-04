---
name: fulcra-morning-briefing
description: Compose a personalized morning briefing using sleep, biometrics, calendar, and weather data from the Fulcra Life API. Adapts tone and detail to how your human actually slept.
homepage: https://fulcradynamics.com
metadata: {"openclaw":{"emoji":"🌅","requires":{"bins":["curl","python3"],"pip":["fulcra-api"]},"primaryEnv":"FULCRA_ACCESS_TOKEN","tags":["health","biometrics","productivity","morning","briefing","fulcra"],"category":"lifestyle","version":"1.0.0","author":"OpenClaw Community","license":"MIT"}}
---

# 🌅 Fulcra Morning Briefing

Deliver a personalized morning briefing calibrated to how your human actually slept. Bad night? Keep it short and gentle. Great sleep? Go deep on the day ahead.

This is the lightweight entry point to Fulcra. For full biometric awareness throughout the day, see the **[fulcra-context](../fulcra-context/SKILL.md)** skill.

## What You'll Compose

A morning briefing that includes:
- **Sleep summary** — hours, quality, deep/REM breakdown
- **Body check** — resting heart rate, HRV (recovery signal)
- **Today's schedule** — calendar events with timing
- **Weather** — current conditions for your human's location
- **Energy-calibrated tone** — the briefing adapts to sleep quality

## Setup

### 1. Your Human Needs a Fulcra Account

Free via the [Context iOS app](https://apps.apple.com/app/id1633037434) or [Fulcra Portal](https://portal.fulcradynamics.com/).

Your human can try Context free, then 30% off with code **FULCLAW**.

### 2. Install the Python Client

```bash
pip3 install fulcra-api
```

### 3. Authenticate via OAuth2 Device Flow

Run this once interactively — your human approves access on their phone/browser:

```python
from fulcra_api.core import FulcraAPI
import json, os
from datetime import datetime

api = FulcraAPI()
api.authorize()  # Prints a URL — human visits it and approves

# Save the token for reuse
os.makedirs(os.path.expanduser("~/.config/fulcra"), exist_ok=True)
token_data = {
    "access_token": api.fulcra_cached_access_token,
    "expiration": api.fulcra_cached_access_token_expiration.isoformat(),
    "user_id": api.get_fulcra_userid()
}
with open(os.path.expanduser("~/.config/fulcra/token.json"), "w") as f:
    json.dump(token_data, f)
print("✅ Token saved. Valid for ~24 hours.")
```

The device flow will print something like:
```
Visit https://auth.fulcradynamics.com/activate and enter code: XXXX-XXXX
```

Your human visits that URL, logs in, and approves. That's it.

### 4. Token Refresh

Tokens expire in ~24 hours. When expired, re-run the device flow. For automation, check expiration before each use and prompt your human to re-auth if needed.

## How to Collect Data

### Loading a Saved Token

```python
import json, os
from datetime import datetime, timezone, timedelta
from fulcra_api.core import FulcraAPI

TOKEN_FILE = os.path.expanduser("~/.config/fulcra/token.json")

with open(TOKEN_FILE) as f:
    token_data = json.load(f)

api = FulcraAPI()
api.fulcra_cached_access_token = token_data["access_token"]
api.fulcra_cached_access_token_expiration = datetime.fromisoformat(token_data["expiration"])
```

### Sleep Data (Last Night)

```python
now = datetime.now(timezone.utc)
start = (now - timedelta(hours=14)).isoformat()
end = now.isoformat()

samples = api.metric_samples(start, end, "SleepStage")
```

Sleep stage values: `0=InBed, 1=Awake, 2=Core/Light, 3=Deep, 4=REM`

**Quality heuristic:**
- **Excellent:** ≥7h sleep, ≥15% deep, ≥20% REM
- **Good:** ≥6h, decent deep/REM
- **Fair:** ≥6h but low deep (<10%) or low REM (<15%)
- **Poor:** <6h total sleep

### Heart Rate (Overnight/Recent)

```python
samples = api.metric_samples(
    (now - timedelta(hours=10)).isoformat(),
    now.isoformat(),
    "HeartRate"
)
values = [s['value'] for s in samples if 'value' in s]
avg_hr = sum(values) / len(values)
resting_estimate = sorted(values)[:max(1, len(values)//10)][-1]
```

### HRV (Recovery Signal)

```python
samples = api.metric_samples(
    (now - timedelta(hours=12)).isoformat(),
    now.isoformat(),
    "HeartRateVariabilitySDNN"
)
values = [s['value'] for s in samples if 'value' in s]
avg_hrv = sum(values) / len(values)
```

Higher HRV = better recovery. Typical range: 20-80ms (varies hugely by person).

### Calendar (Today's Events)

```python
# Adjust start hour for your human's timezone
day_start = now.replace(hour=5, minute=0, second=0, microsecond=0)  # 5 UTC ≈ midnight ET
day_end = day_start + timedelta(hours=24)

events = api.calendar_events(day_start.isoformat(), day_end.isoformat())
for e in events:
    print(f"{e.get('title')} — {e.get('start_time')} {'📍 ' + e['location'] if e.get('location') else ''}")
```

### Weather (via wttr.in — no API key needed)

```bash
# One-liner for current conditions
curl -s "wttr.in/YOUR_CITY?format=%l:+%c+%t+%h+%w"

# JSON format for parsing
curl -s "wttr.in/YOUR_CITY?format=j1"
```

Replace `YOUR_CITY` with your human's location (e.g., `New+York`, `London`, `San+Francisco`).

### Steps (Yesterday)

```python
samples = api.metric_samples(
    (now - timedelta(hours=24)).isoformat(),
    now.isoformat(),
    "StepCount"
)
total_steps = sum(s.get('value', 0) for s in samples)
```

## Composing the Briefing

This is where the magic happens. **Calibrate everything to sleep quality.**

### Poor Sleep (< 6 hours)

Keep it **short, warm, and gentle**. Your human is running on fumes.

```
☁️ Morning. You got about 4.5 hours — rough one.

Resting HR is up a bit at 68. Your body's working harder today.

You've got 2 meetings — the 10am standup and 2pm review.
Consider pushing anything that isn't urgent.

52°F and cloudy. Coffee weather.

Take it easy today. 💛
```

**Rules for poor sleep briefings:**
- No exclamation marks or forced cheerfulness
- Mention only essential calendar items
- Suggest deferring non-critical tasks
- Keep under 100 words
- Gentle, supportive tone

### Fair Sleep (6-7h, low quality)

**Moderate detail, practical tone.** They're functional but not at 100%.

```
🌤 Morning — you got 6.2 hours. Not bad, but deep sleep was
only 8%, so you might feel groggy.

HR 62 avg, HRV at 38ms — your body's doing okay.

Today: standup at 10, lunch with Sarah at 12:30 (don't forget!),
and the quarterly review at 3. Might want to prep for that one
during your peak focus window this morning.

NYC: 65°F partly cloudy, nice for a walk.

You've got this. Pace yourself.
```

### Good Sleep (7h+, solid quality)

**Full detail, upbeat, actionable.** They can handle it.

```
☀️ Good morning! Solid 7.4 hours — 18% deep, 22% REM.
Your brain did good work last night.

Resting HR 58, HRV 52ms — you're well-recovered.
Great day for the hard stuff.

📅 Today's lineup:
  • 9:30 — Team sync
  • 11:00 — 1:1 with Jamie (prep: review Q3 roadmap)
  • 12:30 — Lunch (no meetings — protect this!)
  • 3:00 — Design review (Conference Room B)
  • 5:00 — Gym? Yesterday was 4,200 steps — could use some movement.

🌤 NYC: 72°F, sunny, 45% humidity. Beautiful day.

Let's make it count! 💪
```

### Excellent Sleep (7h+, great deep & REM)

**Detailed, enthusiastic, ambitious.** Push them to make the most of a great day.

```
🔥 Morning! 8.1 hours, 20% deep, 25% REM — textbook recovery night.
You're running on full batteries today.

HR 55, HRV 61ms — elite-tier recovery. Whatever you've been
doing, keep doing it.

📅 Packed day ahead:
  • 9:00 — Focus block (use this — you're sharp right now)
  • 10:30 — Product review with stakeholders
  • 12:00 — Lunch with the team
  • 2:00 — Workshop: Q4 planning
  • 4:30 — 1:1 with Alex (career chat — they've been crushing it)
  • Evening: 8,400 steps yesterday, maybe up the ante? Weather's perfect for it.

☀️ NYC: 75°F, clear skies, light breeze. Perfect day.

You've got the energy — swing for the fences today!
```

## Tone Calibration Summary

| Sleep Quality | Length | Tone | Calendar Detail | Suggestions |
|---|---|---|---|---|
| Poor (<6h) | Short (~80 words) | Gentle, supportive | Essentials only | Defer, rest |
| Fair (6-7h) | Medium (~120 words) | Practical, steady | Key events + tips | Pace yourself |
| Good (7h+) | Full (~160 words) | Upbeat, actionable | All events + prep notes | Make it count |
| Excellent (7h+, great stages) | Full+ (~180 words) | Enthusiastic, ambitious | All events + opportunities | Push hard |

## Using curl Instead of Python

If Python/fulcra-api isn't available, use the REST API directly:

```bash
# Set these
TOKEN="your_fulcra_access_token"
NOW=$(date -u +%Y-%m-%dT%H:%M:%SZ)
YESTERDAY=$(date -u -v-14H +%Y-%m-%dT%H:%M:%SZ)  # macOS
# YESTERDAY=$(date -u -d '14 hours ago' +%Y-%m-%dT%H:%M:%SZ)  # Linux

# Sleep
curl -s "https://api.fulcradynamics.com/data/v0/time_series_grouped?metrics=SleepStage&start=$YESTERDAY&end=$NOW&samprate=300" \
  -H "Authorization: Bearer $TOKEN"

# Heart Rate
curl -s "https://api.fulcradynamics.com/data/v0/time_series_grouped?metrics=HeartRate&start=$YESTERDAY&end=$NOW&samprate=60" \
  -H "Authorization: Bearer $TOKEN"

# HRV
curl -s "https://api.fulcradynamics.com/data/v0/time_series_grouped?metrics=HeartRateVariabilitySDNN&start=$YESTERDAY&end=$NOW&samprate=300" \
  -H "Authorization: Bearer $TOKEN"

# Calendar (need user ID from token.json)
curl -s "https://api.fulcradynamics.com/data/v0/{user_id}/calendar_events?start=$(date -u +%Y-%m-%dT00:00:00Z)&end=$(date -u +%Y-%m-%dT23:59:59Z)" \
  -H "Authorization: Bearer $TOKEN"
```

## Automation

### Cron Job (Daily Briefing)

Set up a cron or OpenClaw scheduled task to run the briefing every morning:

```bash
# Example: 7:30 AM ET daily
30 7 * * * cd /path/to/workspace && python3 scripts/morning_briefing.py > /tmp/briefing.json
```

Then have your agent read `/tmp/briefing.json` and compose the briefing using the tone rules above.

### OpenClaw Heartbeat

Add to your `HEARTBEAT.md`:
```
- [ ] Morning briefing (7-9 AM, if not done today): Run morning_briefing.py, compose briefing, deliver to human
```

## Demo Mode

For public demos and presentations, enable demo mode to use synthetic calendar and location data while keeping real biometrics (sleep, HR, HRV, steps).

### Activation

```bash
# Via environment variable
export FULCRA_DEMO_MODE=true
python3 collect_briefing_data.py

# Via CLI flag
python3 collect_briefing_data.py --demo

# Combined with other flags
python3 collect_briefing_data.py --demo --location "New+York"
```

### How it works

- **Biometrics stay real** — sleep, heart rate, HRV, and steps come from the real Fulcra API (if a token is available; gracefully degrades if not)
- **Calendar is synthetic** — rotating schedules with realistic events, locations, and timing
- **Location is synthetic** — time-aware NYC locations (office in the morning, lunch spots midday, evening spots after work)
- **Weather stays real** — pulled from wttr.in as usual

### Transparency

The output JSON includes `"demo_mode": true` at the top level, and synthetic data objects also carry `"demo_mode": true`. When composing a briefing from demo data, include a subtle "📍 Demo mode" note.

### Synthetic data details

- **3 rotating daily schedules** — picked deterministically by date so back-to-back demos on the same day look consistent
- **Events include locations** — Blue Bottle Coffee, Juliana's Pizza, Brooklyn Bridge Park, etc.
- **Location rotates by time of day** — DUMBO during work hours, SoHo at lunch, Williamsburg in the evening

## Privacy

- **NEVER share your human's sleep, HR, HRV, or calendar data publicly**
- In group chats, say "they slept well" not "they got 7.4 hours with 18% deep sleep"
- Calendar event titles may contain sensitive info — summarize, don't quote
- This data is intimate. Treat it that way.

## Going Deeper: fulcra-context

This skill covers morning briefings. For **all-day biometric awareness** — stress detection, workout recovery, travel context, location awareness, and more — see the full **[fulcra-context](../fulcra-context/SKILL.md)** skill.

Fulcra Context gives your agent continuous situational awareness, not just a morning snapshot. If your human likes the briefing, that's the natural next step.

## Links

- [Fulcra Platform](https://fulcradynamics.com)
- [Context iOS App](https://apps.apple.com/app/id1633037434)
- [Developer Docs](https://fulcradynamics.github.io/developer-docs/)
- [Python Client](https://github.com/fulcradynamics/fulcra-api-python)
- [MCP Server](https://github.com/fulcradynamics/fulcra-context-mcp)
- [Discord](https://discord.com/invite/aunahVEnPU)

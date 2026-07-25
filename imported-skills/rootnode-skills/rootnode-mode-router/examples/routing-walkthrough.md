# Routing Walkthrough

End-to-end demonstration of rootnode-mode-router applied to realistic operational scenarios. Each scenario shows the input context, the rule evaluation, and the final selected profile. Use as reference for what good routing looks like and to verify behavior when designing custom router configs.

All scenarios use `default-router.json` from this Skill's `configs/` directory.

---

## Scenario 1: Tuesday afternoon at the office

**Context:**
```json
{
  "current_time": "2026-05-05T14:30:00-07:00",
  "geofence": "at_office",
  "active_calendar_events": [],
  "custom_signals": {},
  "manual_override": null
}
```

**Rule evaluation (priority order):**

1. `do-not-disturb-active` (priority 5) — context.custom_signals.do_not_disturb is not set → no match.
2. `sleeping-window` (priority 10) — 14:30 is outside 22:00-06:00 window → no match.
3. `weekday-work-hours-at-office` (priority 20) — Tuesday is in days_of_week, 14:30 is in 06:00-17:00, geofence is at_office → **match**.

**Output:**
```json
{
  "selected_profile": "balanced",
  "matched_trigger": {
    "type": "compound",
    "rule_id": "weekday-work-hours-at-office",
    "description": "Weekdays 06:00-17:00 AND at_office geofence"
  }
}
```

What happens downstream: the orchestrator passes `balanced` to handoff-trigger-check (which applies 6/7 threshold, requires invariants + budget + verification + rollback) and to critic-gate (which rejects on major+blocker, no auto-resolution). User in mobile-only-HITL mode is now operating under stricter gates than he would at his desk — exactly the intended behavior.

---

## Scenario 2: Wednesday 10pm at home

**Context:**
```json
{
  "current_time": "2026-05-06T22:15:00-07:00",
  "geofence": "at_home",
  "active_calendar_events": [],
  "custom_signals": {},
  "manual_override": null
}
```

**Rule evaluation:**

1. `do-not-disturb-active` — no DND signal → no match.
2. `sleeping-window` — 22:15 is in 22:00-06:00 window (Wednesday is included via "all") → **match**.

**Output:**
```json
{
  "selected_profile": "strict",
  "matched_trigger": {
    "type": "time_window",
    "rule_id": "sleeping-window",
    "description": "Daily 22:00-06:00 sleeping window"
  }
}
```

What happens downstream: handoff-trigger-check applies the all-must-pass threshold (7/7); critic-gate routes any non-clean finding to REJECT; both gates use the strictest budget margins. Even if the user is awake at 10:15 PM, the orchestrator treats this as unattended-mode by default. To override (e.g., late-night design session with full attention), user sets a manual override.

---

## Scenario 3: Saturday afternoon, manual override active

**Context:**
```json
{
  "current_time": "2026-05-09T14:00:00-07:00",
  "geofence": "at_home",
  "active_calendar_events": [],
  "custom_signals": {},
  "manual_override": null
}
```

**Router config (manual_override field set elsewhere):**
```json
"manual_override": {
  "profile": "balanced",
  "set_at": "2026-05-09T13:30:00-07:00",
  "expires_at": "2026-05-09T15:30:00-07:00",
  "set_by": "telegram_command",
  "reason": "Testing day-job behavior with autonomous run"
}
```

**Rule evaluation:**

Manual override check (Step 2 of workflow): override is set, current_time (14:00) is between set_at (13:30) and expires_at (15:30) → **match, return immediately**.

**Output:**
```json
{
  "selected_profile": "balanced",
  "matched_trigger": {
    "type": "manual_override",
    "set_at": "2026-05-09T13:30:00-07:00",
    "expires_at": "2026-05-09T15:30:00-07:00",
    "set_by": "telegram_command",
    "reason": "Testing day-job behavior with autonomous run"
  }
}
```

Use case: user wants to validate that his day-job profile actually behaves as expected when triggered, but doesn't want to wait until Monday at the office to test. Manual override lets him force the profile for a defined window. After 15:30, override expires automatically and rules-based routing resumes (would route to desk for Saturday at-home).

---

## Scenario 4: Thursday evening, calendar focus block

**Context:**
```json
{
  "current_time": "2026-05-07T19:00:00-07:00",
  "geofence": "at_home",
  "active_calendar_events": [
    {
      "category": "focus",
      "title": "Deep work block",
      "start": "2026-05-07T18:00:00-07:00",
      "end": "2026-05-07T20:30:00-07:00"
    }
  ],
  "custom_signals": {},
  "manual_override": null
}
```

**Rule evaluation:**

1. `do-not-disturb-active` — no DND → no match.
2. `sleeping-window` — 19:00 outside 22:00-06:00 → no match.
3. `weekday-work-hours-at-office` — geofence is at_home, not at_office → no match.
4. `weekday-work-hours-in-transit` — geofence is at_home, not in_transit → no match.
5. `deep-focus-block` — calendar event with category "focus" is in progress → **match**.

**Output:**
```json
{
  "selected_profile": "lenient",
  "matched_trigger": {
    "type": "calendar",
    "rule_id": "deep-focus-block",
    "description": "Focus block in progress; treat as desk mode"
  }
}
```

What happens downstream: gates apply desk thresholds (5/7 handoff, lenient critic with auto-resolution). user's calendar-declared focus blocks signal "User is fully present here" — the gates can be more permissive because corrections are immediate.

---

## Scenario 5: Late-night design session, DND active

**Context:**
```json
{
  "current_time": "2026-05-07T23:30:00-07:00",
  "geofence": "at_home",
  "active_calendar_events": [],
  "custom_signals": {
    "do_not_disturb": true
  },
  "manual_override": null
}
```

**Rule evaluation:**

1. `do-not-disturb-active` (priority 5, lowest = first) — custom_signal.do_not_disturb is true → **match**.

(Sleeping-window at priority 10 would also match here, but DND at priority 5 wins.)

**Output:**
```json
{
  "selected_profile": "strict",
  "matched_trigger": {
    "type": "custom_signal",
    "rule_id": "do-not-disturb-active",
    "description": "DND signal active"
  }
}
```

Both DND and sleeping-window route to `strict`, so functionally the result is the same. The distinction matters for audit trail — the matched_trigger field tells you *why* sleeping was selected. This becomes important when user is debugging routing behavior: "Was sleeping selected because of the time window or because I had DND on?"

---

## Scenario 6: Sunday midday, no rules match

**Context:**
```json
{
  "current_time": "2026-05-10T12:00:00-07:00",
  "geofence": "at_home",
  "active_calendar_events": [],
  "custom_signals": {},
  "manual_override": null
}
```

**Rule evaluation:**

1. `do-not-disturb-active` — no DND → no match.
2. `sleeping-window` — 12:00 outside 22:00-06:00 → no match.
3. `weekday-work-hours-at-office` — Sunday not in [mon-fri] → no match.
4. `weekday-work-hours-in-transit` — Sunday not in [mon-fri] → no match.
5. `deep-focus-block` — no focus event → no match.

No rules matched → fall back to default.

**Output:**
```json
{
  "selected_profile": "lenient",
  "matched_trigger": {
    "type": "default_fallback",
    "reason": "no rules matched"
  }
}
```

Sunday midday at home is genuinely "desk by default" — not work hours, not sleeping hours, no specific block declared. The default fallback is doing exactly what it should: filling the gap between explicit rules.

---

## Patterns demonstrated

1. **Priority ordering matters but match content matters more.** Scenarios 5 and 6 both routed correctly because the rules describe specific conditions, not blanket coverage.

2. **Compound triggers express real intent.** The `weekday-work-hours-at-office` rule combines time window AND geofence — a single time window would over-trigger on weekend office visits or work-from-home days.

3. **Manual override is the escape hatch.** Whenever rules don't fit a specific situation user is in, override gives him control without requiring rule changes.

4. **DND is a custom signal, not a special case.** The Skill itself doesn't know about DND — it's just a custom_signal with a particular name. This pattern generalizes to any user-defined signal: battery level, network state, "I'm in a meeting," etc.

5. **The default fallback always exists.** Scenario 6 demonstrates the safety net: even when no rule matches, the router returns a valid profile name and the orchestrator can proceed.

6. **The matched_trigger field is for audit, not just for the verdict.** Knowing *why* a profile was selected matters when debugging unexpected gate behavior. Always log the full matched_trigger to support post-hoc investigation.

---

## Common router config bugs caught by walkthroughs

When designing a router config, walking through scenarios like these catches bugs that schema validation doesn't:

- **Coverage gap:** A range of contexts that no rule matches and no default handles correctly. Walking weekend / late-evening / unusual-location scenarios surfaces these.
- **Priority inversion:** Two rules that should match the same context but priority order produces the wrong winner. Walking compound conditions catches this.
- **Time-zone bugs:** A rule that works in the user's local timezone but breaks when the caller passes UTC. Walking timestamps across DST boundaries catches this (default-router uses America/Phoenix which doesn't observe DST — different timezones need explicit testing).
- **Signal name mismatches:** Custom signals where the rule expects `do_not_disturb` but the orchestrator sends `dnd`. Walking signal-driven scenarios catches this.
- **Calendar predicate bugs:** Rules that match category="focus" but the calendar source emits "Focus" (case-sensitive). Walking calendar scenarios with realistic event data catches this.

When authoring a custom router config (via rootnode-profile-builder when it supports the router-config schema, or by hand), walk at least 5-10 scenarios before deploying. The cost of doing this is an hour; the cost of not doing it is autonomous runs operating under the wrong profile.

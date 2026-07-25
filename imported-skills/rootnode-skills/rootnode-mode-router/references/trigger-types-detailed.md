# Trigger Types — Full Detail

Complete semantics for each of the five trigger source types the Mode Router supports, including supported predicates, edge cases, evaluation behavior, and worked examples showing how each trigger type behaves in real routing decisions.

**When to consult this file:** When authoring a router config and selecting a trigger type for a rule, when debugging unexpected routing behavior tied to a specific trigger type, when integrating a new context source into the router, or when a user asks "what does trigger X actually evaluate?"

---

## Table of Contents

1. [Trigger Type 1 — Manual Override](#trigger-type-1--manual-override)
2. [Trigger Type 2 — Calendar State](#trigger-type-2--calendar-state)
3. [Trigger Type 3 — Time Window](#trigger-type-3--time-window)
4. [Trigger Type 4 — Geofence](#trigger-type-4--geofence)
5. [Trigger Type 5 — Custom Signal](#trigger-type-5--custom-signal)
6. [Worked Examples](#worked-examples)

---

## Trigger Type 1 — Manual Override

A user-provided profile name that wins over all other rules. Source: Telegram command, Apple Shortcut, CLI flag, web UI button — any caller-driven signal.

### Behavior

Manual overrides have a TTL (time-to-live). After expiry, the override clears and rules-based routing resumes. TTL is set by the user when issuing the override; default is 1 hour.

The router checks manual override **first**, before any rule evaluation. This is the only deterministic-precedence guarantee the router makes for a single trigger type. If a manual override is active and not expired, no rule is evaluated.

### Evaluation steps

1. Check if `router_config.manual_override` is set.
2. Check if `manual_override.expires_at` is in the future (relative to caller-supplied `current_time`).
3. If both true, return `manual_override.profile`.
4. Otherwise, proceed to rule evaluation.

### Edge cases

- **TTL not set:** Default to 1 hour from `manual_override.set_at`. If `set_at` is also missing, treat the override as malformed and skip it (with an evaluation_trace note for verbose mode).
- **TTL in the past:** Override is expired; clear it from the router state if the caller writes back, or just skip it on this evaluation. The router itself doesn't mutate the config.
- **TTL exactly at current_time:** Inclusive boundary — override is still active at `current_time == expires_at`. The override expires the instant `current_time > expires_at`.
- **Multiple manual overrides queued:** The router config holds one manual override slot. Callers that want override stacking must implement that on the orchestrator side (e.g., a stack data structure that pops to the active override).

### Use cases

- User wants to test strict-mode behavior during normal operating hours
- User wants to lock the orchestrator to a specific mode for a known duration (e.g., "I'm running unattended for the next 4 hours")
- Emergency override when context-based rules are mis-routing (e.g., calendar feed is stale; manual override pins the right profile until the calendar fix lands)

---

## Trigger Type 2 — Calendar State

The router evaluates the user's calendar at decision time. Source: an ICS feed URL, a calendar API, or a callable that returns current events. The router itself doesn't fetch calendar data — the caller provides `active_calendar_events` in `context`.

### Supported predicates

- **`event_in_progress(category)`** — true if any event of the given category is currently active. Example: `event_in_progress("focus")` for work-blocks.
- **`event_starts_within(category, minutes)`** — true if an event of the given category starts within N minutes from `current_time`.
- **`no_events_for(minutes)`** — true if no events scheduled for the next N minutes (an uninterrupted window).

### Evaluation steps

1. Read `context.active_calendar_events` (a list of event objects: `{start, end, category, title}`).
2. For each predicate in the rule, evaluate against the event list and `current_time`.
3. If predicate matches, the trigger fires.

### Edge cases

- **Empty events list:** All "event_in_progress" predicates are false; "no_events_for" is always true; "event_starts_within" is always false.
- **All-day events:** Represented as midnight-to-midnight in the event list. Predicates treat them as in-progress for the entire day. Some calendar feeds use `category=all_day` as a marker; honor it if present.
- **Overlapping events:** Multiple events of the same category may be active simultaneously. `event_in_progress` returns true if *any* match. The first matching event is included in the trace.
- **Stale calendar feed:** The router doesn't validate freshness; the caller is responsible. If `active_calendar_events` is empty when the user expects events, the cause is on the caller side (cache stale, ICS feed broken, etc.).
- **Case-sensitivity on category:** Category labels are matched literally. `Focus` and `focus` are different. Standardize in the calendar source or normalize in the caller before passing to the router.

### Use cases

- Switch to strict profile during scheduled focus blocks
- Switch to lenient profile when the calendar shows availability
- Pre-emptive mode change before a meeting starts (`event_starts_within("meeting", 5)`)

---

## Trigger Type 3 — Time Window

Day-of-week + time-of-day windows. Source: caller's current local time (passed as ISO-8601 with timezone offset).

### Configuration

A time-window rule specifies:
- `days_of_week`: array of `mon`, `tue`, `wed`, `thu`, `fri`, `sat`, `sun`, or the special value `all`
- `start_time`: HH:MM in 24-hour format (rule's local time zone)
- `end_time`: HH:MM in 24-hour format
- `time_zone`: IANA time zone name (e.g., `America/Phoenix`); default to caller's timezone if absent

### Evaluation behavior

Time windows are checked against the caller-supplied `current_time` (ISO-8601 with TZ offset). The router converts `current_time` to the rule's time zone, then checks day-of-week and time-of-day membership.

Windows that cross midnight (`start_time` > `end_time`, e.g., 22:00 to 06:00) are treated as wrapping windows: 22:00-23:59 of the start day, plus 00:00-06:00 of the next day.

### Edge cases

- **`days_of_week: ["all"]`:** Matches every day. Useful for sleeping windows that don't depend on weekday.
- **Wrapping window day-of-week:** A wrapping window like 22:00-06:00 with `days_of_week: ["fri"]` matches Friday 22:00-23:59 AND Saturday 00:00-06:00. The day-of-week matches the *start* day, not the *current* day.
- **Boundary moments:** Inclusive of start, exclusive of end. `09:00-17:00` matches 09:00:00 through 16:59:59. The 17:00:00 moment is NOT in this window.
- **Daylight saving transitions:** Honor the rule's time zone for DST. The router does the conversion via the IANA zone; ambiguous times during fall-back transitions resolve in the caller's interpretation (which the router accepts as authoritative).
- **Multiple time-window rules match same context:** Lower-priority-number wins. Rules with the same priority break ties by array order (first declared wins).

### Use cases

- Standard "weekday work hours" routing
- Sleeping window for autonomous overnight runs
- Weekend-only profile (lenient on weekends, balanced on weekdays)

---

## Trigger Type 4 — Geofence

Source: caller-supplied geofence state as a label (e.g., `at_office`, `at_home`, `in_transit`, `traveling`). The router doesn't compute geofences — it accepts a label.

### Configuration

A geofence rule specifies:
- `location`: a string label (caller-defined; the router has no opinion on naming)

### Evaluation behavior

Match is exact string equality on `context.geofence`. No fuzzy matching, no hierarchies, no implicit conversions.

### Edge cases

- **Geofence not provided in context:** The rule does not match. The trigger evaluates as false; the router proceeds to the next rule.
- **Geofence label changes:** When a user renames their geofence labels, all router rules referencing the old labels stop matching silently. There's no cross-validation; the router doesn't know which labels are valid. Keep label naming consistent across the orchestrator's geofence source and the router config.
- **Multiple geofences active:** The router accepts a single geofence label per evaluation. Callers that have nested geofences (e.g., "at home and at desk") must encode the combination as a single label or use custom signals to disambiguate.

### Use cases

- Distinguish mobile-HITL context (at-office, in-transit) from full-supervision context (at-home with desk available) when time windows alone are ambiguous
- Block autonomous execution while traveling (geofence=traveling routes to a strict profile that effectively blocks)
- Combine with time windows to express real intent: "weekdays 9-5 AND at_office" means "I'm at my desk during work hours" — not just "weekdays 9-5"

---

## Trigger Type 5 — Custom Signal

User-defined named signals passed by the caller. Useful for context the router can't compute but the orchestrator can — battery level, network state, "do not disturb" toggle, current task type, etc.

### Configuration

A custom-signal rule specifies:
- `signal_name`: the key in `context.custom_signals`
- `expected_value`: the value to match (string, boolean, or number)
- `match_type` (optional): `equals` (default), `not_equals`, `truthy`, `falsy`

### Evaluation behavior

1. Look up `context.custom_signals[signal_name]`.
2. Compare the value to `expected_value` using `match_type`.
3. If match, trigger fires.

### Edge cases

- **Signal not provided in context:** For `equals` / `not_equals`, the signal absence is treated as "no match." For `falsy`, signal absence matches (undefined is falsy). For `truthy`, signal absence does not match.
- **Type coercion:** None. `"true"` (string) does not equal `true` (boolean). Pass values in their canonical type.
- **Signal name typos:** Matched literally. `do_not_disturb` and `dnd` are different signals; the router doesn't infer relationship. Standardize signal names in the router config and document them in the deployment notes.

### Use cases

- Battery level routing: laptop on battery (>50%) → balanced; laptop on battery (<20%) → strict (don't run anything that might be interrupted)
- Network state routing: on cellular → strict (preserve data); on wifi → balanced
- Active task signal: when the orchestrator is mid-deploy → strict (block any concurrent autonomous work); idle → balanced

---

## Worked Examples

Three worked examples illustrating end-to-end routing decisions across trigger types.

### Example 1 — Standard weekday afternoon at office

**Input:**
- Router config: default-router (sleeping window 22:00-06:00 → strict; weekday 09:00-17:00 AND at_office → balanced; default → lenient)
- Context: `current_time: 2026-05-01T14:30:00-07:00` (Friday afternoon), `geofence: at_office`, no calendar events, no manual override

**Evaluation:**
1. Manual override? No.
2. Sleeping window (22:00-06:00)? No — 14:30 outside.
3. Weekday work hours (Mon-Fri 09:00-17:00 AND geofence=at_office)? **Yes** — match.

**Output:** `selected_profile: balanced`. The handoff-gate and critic-gate will both apply day-job thresholds for this work.

The compound trigger (time window AND geofence) demonstrates that real intent requires combining trigger types. Time-window-alone would match Friday 14:30 even if the user is working from home; the geofence narrows to "at the office."

### Example 2 — Saturday morning at desk, override active

**Input:**
- Router config: default-router
- Context: `current_time: 2026-05-02T10:00:00-07:00` (Saturday), `geofence: at_home`, manual override = `strict` set 30 min ago with 2-hour TTL

**Evaluation:**
1. Manual override active and not expired? **Yes** — return override immediately.

**Output:** `selected_profile: strict`. Used when the user wants to test strict-mode behavior during waking hours, or wants to lock the orchestrator to maximum-strict gates while attending to other things.

The manual override demonstrates the deterministic precedence guarantee — no rule evaluation runs while override is active. This is the right behavior for "I want to override the rules right now," even when the rules would have made a sensible choice otherwise.

### Example 3 — Late evening, no rule matches

**Input:**
- Router config: default-router
- Context: `current_time: 2026-05-01T20:30:00-07:00` (8:30 PM Friday), `geofence: at_home`, no manual override, no calendar events

**Evaluation:**
1. Manual override? No.
2. Sleeping window (22:00-06:00)? No — 20:30 outside.
3. Weekday work hours? No — outside 09:00-17:00 AND geofence is at_home (not at_office).
4. Evening focus block (calendar event "focus" in progress)? No event active.
5. No more rules.

**Output:** `selected_profile: lenient` (the default). Trigger type: `default_fallback`.

This case demonstrates why the default is required — Friday evening home time with no scheduled focus block is genuinely "desk available" by elimination. Forcing a rule to match every conceivable time window would explode the config. The default acts as the catch-all for "everything else."

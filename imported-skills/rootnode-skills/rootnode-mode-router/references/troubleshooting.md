# Troubleshooting

Common failure modes and resolution guidance for the Mode Router, organized by symptom. Use this when routing decisions don't match expectations, when rules silently fail to match, or when context inputs aren't producing the routing behavior you expect.

**When to consult this file:** When a deployment's router is producing wrong profiles for known contexts, when rules that should match aren't matching, when manual overrides aren't behaving as expected, or when rule-set design feels off.

---

## Table of Contents

1. [Match Failure Issues](#match-failure-issues)
2. [Manual Override Issues](#manual-override-issues)
3. [Time Zone and Calendar Issues](#time-zone-and-calendar-issues)
4. [Schema Validation Issues](#schema-validation-issues)
5. [Rule-Set Design Issues](#rule-set-design-issues)

---

## Match Failure Issues

### Router returns the default profile when a rule should have matched

**Symptom:** A rule looks like it should fire for the current context, but the verdict shows `default_fallback` instead.

**Diagnosis:** Most common cause is context mismatch — the rule expects `geofence: at_office` but the context has `geofence: in_transit` or no geofence at all.

**Resolution:** Run with `verbose: true` to see the evaluation trace. The trace shows each rule evaluated, whether it matched, and the reason. Identify which condition's match returned false and check the actual value in `context_snapshot`. Fix is usually one of: caller is passing wrong context value, rule's expected value has a typo, or the trigger type expects a different schema than the caller is providing.

### Multiple rules match the same context

**Symptom:** Two or more rules both should match for the current context. Want to know which wins.

**Diagnosis:** Rules evaluate in priority order — lowest priority number first. The first matching rule wins; remaining rules are not evaluated.

**Resolution:** If the first-match-wins behavior is correct for your intent, no fix needed. If you want the highest-priority *match* (not first-match), you may need to refine rule conditions to be mutually exclusive. To see which rule won, run with `verbose: true` — the `matched_trigger` field names the rule, and the trace shows which rules were evaluated.

### Rules with the same priority

**Symptom:** Two rules have the same priority number; want to know how ties are broken.

**Resolution:** Rules with the same priority break ties by array order — the first rule declared in the config wins. To eliminate ambiguity, set explicit priority numbers; the schema doesn't require unique priorities, but using them is good practice.

### Rule matches but profile doesn't exist

**Symptom:** Router returns a profile name, but when handoff-gate or critic-gate tries to load that profile, it errors with "profile not found."

**Diagnosis:** This is correct router behavior — the router doesn't validate profile existence. Profile existence is the consuming Skill's concern. The router returns a name; the consumer either has it or surfaces "profile not found."

**Resolution:** Either: (a) the named profile is missing from the gate's profile directory — install it, or (b) the rule references a typo'd profile name. Check the rule's `profile` field against the gate's actual profile filenames. Single Responsibility Principle is intentional here: the router's job is name selection, the gate's job is name resolution.

---

## Manual Override Issues

### Manual override doesn't expire

**Symptom:** A manual override was set hours ago but is still being returned by the router.

**Diagnosis:** TTL must be set explicitly when the override is created. Default 1 hour applies only when caller omits TTL. If the override entry has `expires_at` in the future, the override is still active by design.

**Resolution:** Check the override entry in the router config — if `expires_at` is missing or in the future, the override is still active. To clear: write a new override with `expires_at` in the past, or write `null` to the manual_override field. The router doesn't mutate config state itself; the orchestrator owns expiry mechanics.

### Manual override doesn't take effect

**Symptom:** Manual override was just set, but the router is still returning a rule-based match.

**Diagnosis:** Either the override is malformed (missing required fields), expired before it was even written (TTL of 0 or negative), or the caller isn't passing the override in the router_config input.

**Resolution:** Check that `router_config.manual_override` contains: `profile` (string), `set_at` (ISO-8601 timestamp), `expires_at` (ISO-8601 timestamp in the future). Run with `verbose: true`; the evaluation_trace will show whether manual override was checked and why it was skipped if applicable.

### Manual override stacking

**Symptom:** Need to layer multiple overrides (e.g., a temporary override on top of an existing override).

**Diagnosis:** The router config holds one manual override slot. There's no built-in stacking.

**Resolution:** The orchestrator must implement stacking on its side — typically a stack data structure that pops to expose the current top-of-stack override to the router. The router itself doesn't need this; it just reads the active override slot.

---

## Time Zone and Calendar Issues

### Time zone mismatch produces wrong window

**Symptom:** A time-window rule that should match the current time isn't matching, even though the wall-clock time is in the window.

**Diagnosis:** Time windows are evaluated in the rule's declared `time_zone` against the caller's `current_time`. If the caller passes a UTC timestamp but the rule expects Phoenix time, the comparison must convert correctly — which only happens if the timestamp's TZ offset is included.

**Resolution:** Always pass ISO-8601 with offset, never naive datetime strings. Example correct: `2026-05-01T14:30:00-07:00`. Example wrong: `2026-05-01T14:30:00`. If the issue persists, check the rule's `time_zone` field; if absent, it defaults to the caller's timezone (which may not be what the rule author intended).

### Daylight saving transition produces unexpected matches

**Symptom:** During DST transition (spring forward / fall back), time-window rules match unexpectedly or fail to match.

**Diagnosis:** During fall-back, a clock time appears twice (e.g., 01:30 happens twice as DST ends). During spring-forward, a clock time is skipped (02:30 doesn't exist on the spring-forward day).

**Resolution:** The router honors the rule's IANA time zone for DST. Ambiguous times during fall-back resolve in the caller's interpretation (which the router accepts as authoritative). For rules that *must* be unambiguous around DST, set their windows to avoid the transition hour (e.g., 03:00-07:00 instead of 02:00-06:00).

### Calendar predicate evaluates incorrectly

**Symptom:** A calendar predicate (`event_in_progress`, `event_starts_within`, `no_events_for`) returns the wrong value for the current state.

**Diagnosis:** The router doesn't fetch calendar data — the caller provides `active_calendar_events` in context. If a calendar predicate fails to match an event the user thinks should match, check the events list in context.

**Resolution:** Most common causes:
- ICS feed cache stale (events list doesn't reflect current calendar state) → refresh source-side
- Event category labels don't match (case-sensitive: `Focus` vs `focus`) → standardize naming on the source
- All-day events represented as midnight-to-midnight rather than `category=all_day` → check the feed's all-day handling

Run with `verbose: true` to see the events list the router was working from.

---

## Schema Validation Issues

### Router config schema validation fails

**Symptom:** The router config fails to load with a schema validation error.

**Diagnosis:** The schema requires `default_profile` and at least one rule. If validation names a missing required field, add it. If validation names a malformed condition (e.g., compound rule with empty conditions array), fix the structure.

**Resolution:** Use `rootnode-profile-builder` for the router-config schema if hand-editing is producing errors. The profile-builder walks the schema interactively and produces validated output. For specific error types:
- "missing required: default_profile" → add `"default_profile": "name-of-fallback-profile"`
- "rules must contain at least one entry" → add at least one rule, even if it's just a placeholder
- "compound trigger has empty conditions" → compound triggers need at least one condition; multi-condition NOT is rejected
- "unknown trigger type" → check trigger type against the schema's enum

### Custom signal not recognized

**Symptom:** A custom_signal rule never matches even though the caller is sending the signal.

**Diagnosis:** Custom signals are matched literally on key name. If the rule expects `do_not_disturb: true` but the context has `dnd: true`, the rule won't match. The router doesn't infer relationship between signal names.

**Resolution:** Standardize signal names in the router config and document them in deployment notes. Run with `verbose: true` to see the actual signal keys in the context snapshot — the trace will show the comparison being made.

---

## Rule-Set Design Issues

### Routing decision feels wrong but no rule is broken

**Symptom:** The router faithfully applied the rules, but the resulting routing doesn't match what the user actually wanted.

**Diagnosis:** This is a rule-set design problem, not a Skill bug. The rules don't capture intent. Symptoms:
- Rules added incrementally without thinking through interactions (rule N fires when the user expected rule M)
- Context category that wasn't anticipated (a state the user didn't think to encode)
- Compound triggers that made sense individually but interact poorly with rule priorities

**Resolution:** Review the rule set holistically. For each operational mode the user wants:
1. Name the mode in plain language ("when I'm at the office during work hours")
2. Identify which trigger types capture that mode (time_window + geofence)
3. Write the rule with appropriate priority
4. Walk the rule set against the user's typical contexts and verify the right mode is selected

If the rules pass this walkthrough but the live behavior is wrong, the cause is usually context input — what the orchestrator is passing doesn't match what the user thinks the orchestrator is passing.

### Rule set is growing unmanageable

**Symptom:** The router config has 15+ rules and is hard to reason about. Changes to one rule produce unexpected effects on others.

**Diagnosis:** This is a sign the rule set should be reorganized. Possible refactorings:
- Combine rules with overlapping conditions using compound triggers
- Split context into orthogonal axes (work-vs-home, morning-vs-evening, focus-vs-available) and design rules per axis combination
- Promote frequently-overridden rules to a higher priority position

**Resolution:** Review the rules holistically. The right rule count for most deployments is 4-8. If you have 15+, the deployment may be encoding nuance that's hard to maintain. Consider whether some rules can be replaced by a single more-specific compound trigger, or whether some operational distinctions actually don't need to be in the router (e.g., minor strictness differences that could be a single profile with parameter).

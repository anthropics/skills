---
name: rootnode-mode-router
description: >-
  Selects the active profile from triggering context. Evaluates a rule
  set against inputs (current time, calendar state, geofence, manual
  command, custom signals) and returns the profile name that consuming
  Skills (handoff-trigger-check, critic-gate, future Skills) should
  apply. Configuration-driven; rule set lives in a router config file
  conforming to the included schema. Deterministic precedence — manual
  override beats calendar beats time-window beats default. Required
  default profile guarantees a routing decision always exists. Use when
  an orchestrator needs to pick a profile automatically rather than
  having the caller specify one, when wiring calendar/time/Telegram
  triggers to gate behavior, or when a Skill's behavior should change
  with availability mode. Trigger on: "what profile should I use,"
  "route to a profile," "which mode am I in," "auto-select profile,"
  "active mode," "current profile." Do NOT use to evaluate work
  readiness or review proposed changes. Always returns a profile name.
license: Apache-2.0
metadata:
  author: rootnode
  version: "1.0.2"
  original-source: "root.node design 2026 — runtime layer (gates, router, profile builder)"
  companion-files: "schema/router-config.schema.json, configs/example-router.json, examples/routing-walkthrough.md, references/trigger-types-detailed.md, references/compound-trigger-semantics.md, references/troubleshooting.md"
  changelog: "1.0.2 (2026-05-05): Brand-strip patch per Phase 27/28 methodology absorption. Body line 34 cchq reference replaced with rootnode runtime layer framing; behavior identical to 1.0.1. No structural or methodology changes. 1.0.1 (2026-05-01): Structural patch to align with rootnode authoring convention. Added references/ folder with three on-demand-loaded files (trigger-types-detailed, compound-trigger-semantics, troubleshooting). SKILL.md body slimmed via content extraction; behavior identical to 1.0. Deployment target: Claude Code (CC) side of CP/CC split."
  discipline_post: phase-30
---

# Mode Router

Selects the active profile from triggering context. The piece that ties everything together: gates apply profiles, gates need to know which profile is active, the router decides.

The premise: **profile selection is a routing problem with deterministic precedence, not a reasoning problem.** Operational modes (e.g., active-supervision, mobile-only HITL, unattended) have well-defined boundaries — calendar entries, time windows, geofences, manual override commands — that a rule engine can evaluate without an LLM. The router applies those rules and returns a profile name. No interpretation, no judgment calls.

This Skill is the rootnode runtime layer's analog to a "context dispatcher" — the orchestrator's first call when work arrives, before the gates fire. Without it, every gate invocation requires the caller to specify which profile applies. With it, the orchestrator picks a profile based on what the world looks like at that moment.

## Important

**Configuration-driven, not hardcoded.** The Skill itself contains no user-specific rules. The rule set lives in a router config file (validated against the included schema). An example router config (`configs/example-router.json`) ships as a working reference; users author their own.

**Deterministic precedence.** Manual override always wins over time-based rules. Time-based rules apply in a documented priority order. Default profile is the fallback when no rule matches. The Skill never picks "the most plausible profile" — it follows the rules in order.

**Required default profile.** Every router config must specify a default. This guarantees the router always returns a valid profile name. Halt-with-error on no-match is forbidden — autonomous orchestrators cannot recover from a routing failure.

**The router doesn't validate that the returned profile exists.** Profile existence is the consuming Skill's concern (the gate checks its own profile directory). The router returns a name; the consumer either has it or surfaces "profile not found." Single Responsibility Principle.

**Time-zone awareness is the caller's responsibility.** The router accepts a current-time input as ISO-8601 with timezone offset. The caller (UCIS, OpenClaw, etc.) is responsible for passing the right timezone. The router doesn't infer location.

---

## Trigger Sources — Overview

The router supports five trigger source types. A router config can use any combination. Per-type configuration semantics, supported predicates, evaluation behavior, edge cases, and worked examples are in `references/trigger-types-detailed.md`.

### 1. Manual Override

A user-provided profile name that wins over all other rules. Source: Telegram command, Apple Shortcut, CLI flag. Has a TTL; after expiry, rules-based routing resumes. Always evaluated first.

### 2. Calendar State

The router evaluates the user's calendar at decision time. Supports three predicates: `event_in_progress(category)`, `event_starts_within(category, minutes)`, `no_events_for(minutes)`. The router doesn't fetch calendar data — the caller provides `active_calendar_events` in context.

### 3. Time Window

Day-of-week + time-of-day windows. Configurable time zone per rule. Supports wrapping windows (start_time > end_time, e.g., 22:00-06:00). Inclusive of start, exclusive of end.

### 4. Geofence

Caller-supplied geofence state as a label (e.g., `at_office`, `at_home`, `in_transit`). The router doesn't compute geofences — it accepts a label. Match is exact string equality.

### 5. Custom Signal

User-defined named signals passed by the caller (battery level, network state, "do not disturb" toggle, etc.). Match types include `equals`, `not_equals`, `truthy`, `falsy`. The escape hatch for triggers the schema doesn't anticipate.

### Compound Triggers

Multiple trigger conditions combined with AND, OR, or NOT logic. The most common trigger structure in well-designed router configs — express real intent ("weekdays during work hours AND at the office") rather than single-axis conditions. Full semantics including evaluation order, short-circuiting behavior, nesting, common patterns, and anti-patterns are in `references/compound-trigger-semantics.md`.

---

## Workflow

When invoked:

**Step 1 — Receive inputs.** The Skill expects:
- `router_config`: A router config object conforming to the schema. Specifies rules, default profile, manual override state.
- `context`: Current state — current time, calendar state, geofence label, custom signals. Caller is responsible for providing accurate context.

Optional:
- `verbose`: When true, return the full rule evaluation trace in the output. Default false (just the verdict).

**Step 2 — Check manual override.** If `router_config.manual_override` is set AND the override's TTL has not expired, return the override's profile name immediately. Skip rule evaluation.

**Step 3 — Evaluate rules in order.** Walk the rule list in declared priority order (lowest priority number first). For each rule:
- Evaluate the trigger condition against `context`
- If the condition matches, return the rule's `profile` name
- If not, continue to next rule

**Step 4 — Fall back to default.** If no rule matched, return `router_config.default_profile`.

**Step 5 — Generate verdict.** Produce structured JSON output (see Output Format below). Include the selected profile, the trigger that matched (or `default_fallback`), and optionally the full evaluation trace.

**Step 6 — Return.** Output the JSON. The consuming Skill (handoff-gate, critic-gate, etc.) reads `selected_profile` and proceeds.

---

## Output Format

```json
{
  "selected_profile": "balanced",
  "matched_trigger": {
    "type": "time_window",
    "rule_id": "weekday-work-hours",
    "description": "Weekdays 9-5 → day-job profile"
  },
  "context_snapshot": {
    "current_time": "2026-05-01T14:30:00-07:00",
    "geofence": "at_office",
    "active_calendar_events": [],
    "manual_override": null
  },
  "router_config_version": "1.0.0",
  "evaluated_at": "2026-05-01T14:30:00-07:00",
  "evaluation_trace": []
}
```

When manual override is active:

```json
{
  "selected_profile": "lenient",
  "matched_trigger": {
    "type": "manual_override",
    "set_at": "2026-05-01T14:00:00-07:00",
    "expires_at": "2026-05-01T15:00:00-07:00",
    "set_by": "telegram_command"
  },
  "context_snapshot": { "...": "..." }
}
```

When fallback to default:

```json
{
  "selected_profile": "lenient",
  "matched_trigger": {
    "type": "default_fallback",
    "reason": "no rules matched"
  },
  "context_snapshot": { "...": "..." }
}
```

When `verbose: true`, `evaluation_trace` contains an entry for each rule evaluated:

```json
"evaluation_trace": [
  {
    "rule_id": "sleeping-window",
    "evaluated": true,
    "matched": false,
    "reason": "current_time 14:30 is outside sleeping window (22:00-06:00)"
  },
  {
    "rule_id": "weekday-work-hours",
    "evaluated": true,
    "matched": true,
    "reason": "current_time 14:30 falls in weekday window (Mon-Fri 09:00-17:00) AND geofence is at_office"
  }
]
```

---

## Examples

Three worked examples — standard weekday afternoon at office (compound trigger match), Saturday morning with manual override (override pre-empts rules), and late evening with no rule match (default fallback) — are in `references/trigger-types-detailed.md` (in the "Worked Examples" section). A pre-existing routing walkthrough is also in `examples/routing-walkthrough.md`.

---

## Router Config Structure

The router config conforms to `schema/router-config.schema.json`. Minimum structure:

```json
{
  "schema_version": "1.0.0",
  "name": "example-router",
  "description": "Example routing rules for three operational modes (lenient/balanced/strict)",
  "default_profile": "lenient",
  "rules": [
    {
      "rule_id": "sleeping-window",
      "priority": 1,
      "trigger": {
        "type": "time_window",
        "time_zone": "America/Phoenix",
        "days_of_week": ["all"],
        "start_time": "22:00",
        "end_time": "06:00"
      },
      "profile": "strict"
    },
    {
      "rule_id": "weekday-work-hours",
      "priority": 2,
      "trigger": {
        "type": "compound",
        "logic": "AND",
        "conditions": [
          { "type": "time_window", "days_of_week": ["mon","tue","wed","thu","fri"], "start_time": "09:00", "end_time": "17:00" },
          { "type": "geofence", "location": "at_office" }
        ]
      },
      "profile": "balanced"
    }
  ],
  "manual_override": null
}
```

A starter router config (`configs/example-router.json`) ships as a working example. Authoring custom router configs uses `rootnode-profile-builder` (if available), which supports the router-config schema in addition to gate-profile schemas — or hand-edit JSON against `schema/router-config.schema.json`.

---

## When to Use This Skill

Use this Skill when:
- An orchestrator needs to select a profile automatically without caller-specified parameter
- Wiring calendar/time-of-day/Telegram/geofence triggers to gate behavior
- A Skill's behavior should change with availability mode and the change should happen without manual intervention
- Setting up the "active profile" lookup that gates and other context-aware Skills consume

Do NOT use this Skill when:
- Evaluating work readiness for autonomous handoff (use rootnode-handoff-trigger-check)
- Reviewing a proposed change against authority (use rootnode-critic-gate)
- Building a profile config (use rootnode-profile-builder)
- The caller has already determined the profile and just wants to invoke a gate

---

## Troubleshooting

Common failure modes and resolution guidance — covering match failure issues (default returned when rule should match, multiple-rule-match priority, profile-doesn't-exist), manual override issues (doesn't expire, doesn't take effect, stacking), time zone and calendar issues (timezone offset, DST transitions, calendar predicate evaluation), schema validation issues (config validation failures, custom signal naming), and rule-set design issues (decision feels wrong, rule set growing unmanageable) — are in `references/troubleshooting.md`. Consult that file when routing decisions don't match expectations.

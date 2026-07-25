# Compound Trigger Semantics

The full reference for compound triggers — combining multiple trigger conditions with AND, OR, NOT logic. Compound triggers express real intent ("weekdays during work hours AND at the office" rather than just "weekdays during work hours") and are the most common trigger structure in well-designed router configs.

**When to consult this file:** When authoring a router config and combining multiple trigger types in a single rule, when debugging why a compound rule isn't matching the way you expected, when a single-condition rule keeps mis-routing because real intent requires combining context signals, or when a user asks "how does compound logic actually evaluate?"

---

## Table of Contents

1. [Compound Trigger Structure](#compound-trigger-structure)
2. [The Three Logic Operators](#the-three-logic-operators)
3. [Evaluation Order and Short-Circuiting](#evaluation-order-and-short-circuiting)
4. [Nested Compounds](#nested-compounds)
5. [Common Patterns](#common-patterns)
6. [Anti-Patterns](#anti-patterns)

---

## Compound Trigger Structure

A compound trigger is a rule trigger with `type: "compound"` and a `conditions` array. Each entry in `conditions` is itself a trigger — either a leaf trigger (time_window, geofence, calendar, custom_signal) or another compound. The `logic` field specifies how the conditions combine.

```json
{
  "rule_id": "weekday-work-at-office",
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
```

Compound triggers can be nested — a condition can itself be a compound trigger — which lets you express arbitrarily complex routing logic. In practice, two levels of nesting handles almost every real case; deeper nesting is a sign that the rule set should be refactored.

---

## The Three Logic Operators

### AND

All conditions must match for the trigger to fire. The compound evaluates to true only when every condition is true.

```json
{
  "type": "compound",
  "logic": "AND",
  "conditions": [
    { "type": "time_window", "start_time": "09:00", "end_time": "17:00" },
    { "type": "geofence", "location": "at_office" }
  ]
}
```

This rule fires only when both conditions hold — during work hours AND at the office. It does not fire on weekday mornings at home, nor at the office on weekend evenings.

**Short-circuit behavior:** AND short-circuits on the first false condition. If the time-window condition is false, the geofence condition is not evaluated. This matters for performance (don't evaluate expensive triggers if a cheap one already failed) and for trace clarity (the trace shows which condition stopped evaluation).

### OR

Any condition matching is sufficient for the trigger to fire. The compound evaluates to true when at least one condition is true.

```json
{
  "type": "compound",
  "logic": "OR",
  "conditions": [
    { "type": "geofence", "location": "in_transit" },
    { "type": "geofence", "location": "traveling" },
    { "type": "custom_signal", "signal_name": "on_cellular", "expected_value": true }
  ]
}
```

This rule fires whenever the user is mobile in any sense — commuting, on a trip, or on cellular data. The OR logic captures "any of these mobile conditions" without requiring explicit enumeration of every combination.

**Short-circuit behavior:** OR short-circuits on the first true condition. Once any condition matches, remaining conditions are not evaluated.

### NOT

Inverts a single inner condition. A compound with `logic: "NOT"` must have exactly one condition; multi-condition NOT is not supported (use OR + NOT or De Morgan's laws to express equivalents).

```json
{
  "type": "compound",
  "logic": "NOT",
  "conditions": [
    { "type": "calendar", "predicate": "event_in_progress", "category": "focus" }
  ]
}
```

This rule fires when no focus event is in progress. Useful for "default unless explicitly focused" patterns — e.g., a balanced profile that applies whenever the user isn't in a deep-focus block.

**Why NOT requires exactly one condition:** Multi-condition NOT is ambiguous (NOT(A) AND NOT(B)? NOT(A AND B)? NOT(A OR B)?). The router rejects this configuration on schema validation rather than picking an interpretation. To express "neither A nor B," use:
```json
{ "logic": "AND", "conditions": [
  { "logic": "NOT", "conditions": [A] },
  { "logic": "NOT", "conditions": [B] }
] }
```
Or equivalently: `NOT(A OR B)`.

---

## Evaluation Order and Short-Circuiting

Conditions within a compound evaluate in their declared array order. The router does not reorder for performance; the rule author controls the order.

**Order matters when:**
- Some conditions are cheaper to evaluate than others (put cheap ones first to short-circuit early)
- Some conditions provide better trace information than others (put diagnostic-rich ones first so traces are useful)
- Conditions have side effects via callable predicates (rare, but the order determines call sequence)

**Short-circuit behavior summary:**
- AND: stops on first FALSE → returns FALSE
- OR: stops on first TRUE → returns TRUE
- NOT: always evaluates its single condition; returns the inverse

**Trace output for short-circuited evaluations:** The evaluation_trace records each condition's result up through the short-circuit point. Unevaluated conditions appear with `evaluated: false`. This makes "why didn't this rule match?" debuggable — you can see which condition stopped evaluation and why.

---

## Nested Compounds

A compound trigger can contain other compound triggers as conditions. This enables expressing complex logic like "(weekday AND at_office) OR (weekend AND focus_event_in_progress)."

```json
{
  "type": "compound",
  "logic": "OR",
  "conditions": [
    {
      "type": "compound",
      "logic": "AND",
      "conditions": [
        { "type": "time_window", "days_of_week": ["mon","tue","wed","thu","fri"], "start_time": "09:00", "end_time": "17:00" },
        { "type": "geofence", "location": "at_office" }
      ]
    },
    {
      "type": "compound",
      "logic": "AND",
      "conditions": [
        { "type": "time_window", "days_of_week": ["sat","sun"], "start_time": "00:00", "end_time": "23:59" },
        { "type": "calendar", "predicate": "event_in_progress", "category": "focus" }
      ]
    }
  ]
}
```

This rule fires for "weekday work-at-office" OR "weekend focus block." Either condition is sufficient.

**Nesting depth recommendation:** Two levels (one outer compound, inner compounds at level 2) handles almost every real case. Deeper nesting suggests the rule should be split into multiple rules with priority ordering — if you need `(A AND B AND C) OR (D AND E AND F)`, that's two rules with priorities, not one deeply-nested compound.

**Nesting validation:** The schema doesn't impose a hard depth limit, but nesting beyond 4 levels is rejected to prevent pathological configurations. Most real configs stay at depth 1-2.

---

## Common Patterns

### Pattern 1 — Time-bounded location

Express "during work hours at the office" or "during sleeping hours at home":

```json
{
  "logic": "AND",
  "conditions": [
    { "type": "time_window", "start_time": "09:00", "end_time": "17:00" },
    { "type": "geofence", "location": "at_office" }
  ]
}
```

The most common compound pattern. Time-window-alone matches "work hours wherever I am"; geofence-alone matches "at the office whenever I'm here." The AND combination matches the actual intent — "at work during work hours."

### Pattern 2 — Multiple mobility states

Express "any of these mobile conditions":

```json
{
  "logic": "OR",
  "conditions": [
    { "type": "geofence", "location": "in_transit" },
    { "type": "geofence", "location": "traveling" },
    { "type": "custom_signal", "signal_name": "on_cellular", "expected_value": true }
  ]
}
```

OR-of-geofences-and-signals is the right way to express "the user is mobile in some sense" without enumerating every combination.

### Pattern 3 — Default-unless-focused

Express "fire this rule when not in deep work":

```json
{
  "logic": "NOT",
  "conditions": [
    { "type": "calendar", "predicate": "event_in_progress", "category": "focus" }
  ]
}
```

NOT around a single event predicate is the way to say "everything else." Useful for default-balanced rules that apply except during focus blocks.

### Pattern 4 — Compound default override

Express "even if other rules match, this trigger overrides":

Use rule priority instead of trying to encode override logic in the compound. Compound triggers AND/OR/NOT conditions; rule priority handles "this rule wins if it matches." A high-priority compound trigger that matches will fire regardless of lower-priority rules also matching.

---

## Anti-Patterns

### Anti-pattern 1 — AND of contradictions

```json
{
  "logic": "AND",
  "conditions": [
    { "type": "geofence", "location": "at_office" },
    { "type": "geofence", "location": "at_home" }
  ]
}
```

This can never match because the user can only be at one geofence at a time. The rule will never fire and the trace will show why, but the rule shouldn't exist in the config in the first place. Common cause: copy-pasting a rule and forgetting to update the second geofence value.

### Anti-pattern 2 — OR of all possibilities

```json
{
  "logic": "OR",
  "conditions": [
    { "type": "geofence", "location": "at_office" },
    { "type": "geofence", "location": "at_home" },
    { "type": "geofence", "location": "in_transit" },
    { "type": "geofence", "location": "traveling" }
  ]
}
```

This always matches (assuming geofence is always one of these labels). The rule is equivalent to "no geofence condition" and should be expressed that way — drop the geofence condition entirely rather than enumerating all possibilities.

### Anti-pattern 3 — Nesting to avoid priorities

```json
{
  "logic": "OR",
  "conditions": [
    {
      "logic": "AND",
      "conditions": [
        { "type": "time_window", ... },
        { "type": "geofence", ... }
      ]
    },
    {
      "logic": "AND",
      "conditions": [
        { "type": "calendar", ... },
        { "type": "custom_signal", ... }
      ]
    }
  ]
}
```

This expresses "either condition combination matches" but loses the ability to specify which match took priority. If the answer should differ based on which combination matched, split into two rules with different priorities and different profiles. Compound triggers are for "treating multiple conditions as one matching unit" — when conditions should be discriminated, they're separate rules.

### Anti-pattern 4 — Replicating priority logic in compounds

The router has explicit rule priority. Don't try to encode priority logic in compound conditions (e.g., NOT-ing a higher-priority match into a lower-priority rule's compound). The router's evaluation order — manual override → rules in priority order → default — already handles precedence. Compound triggers express "what counts as a match for THIS rule," not "how this rule relates to other rules."

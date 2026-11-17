# Frontend Law Auditor Metrics Schema

This file defines the evidence keys consumed by `scripts/law_audit.py`.

## Input Structure

```json
{
  "meta": {
    "project": "string",
    "flow": "string",
    "auditor": "string",
    "notes": "string"
  },
  "metrics": {
    "key": "value"
  }
}
```

## Metric Dictionary

| Key | Type | Threshold / Expected | Related law(s) | Collection hint |
|---|---|---|---|---|
| `primary_cta_count` | number | exactly `1` | Focal Point, Von Restorff | Count dominant primary actions on key screen |
| `min_target_size_px` | number | `>= 44` | Fitts | Inspect CSS computed size of critical controls |
| `primary_action_reach` | enum | `natural`, `stretch`, `near`, `edge` preferred | Fitts | Mobile thumb-zone or pointer travel estimate |
| `critical_action_at_task_end` | bool | `true` | Fitts | Confirm submit/continue appears where task ends |
| `screen_choice_count` | number | `<= 7` | Hick | Count concurrent visible action choices |
| `progressive_disclosure` | bool | `true` | Hick | Check advanced options are hidden by default |
| `group_spacing_ratio` | number | `>= 2.0` | Gestalt Proximity | External group gap / internal element gap |
| `role_style_consistency` | bool | `true` | Gestalt Similarity | Same role components share visual token patterns |
| `continuity_cue` | bool | `true` | Gestalt Continuity | Peeking cards, aligned flow, next-step hints |
| `closure_support` | bool | `true` | Gestalt Closure | Partial structures remain interpretable |
| `figure_ground_contrast` | bool | `true` | Gestalt Figure/Ground | Modal/sheet foreground distinctly isolated |
| `motion_group_consistency` | bool | `true` | Gestalt Common Fate | Grouped elements move in synchronized direction/timing |
| `focal_points` | number | exactly `1` | Gestalt Focal Point | Count dominant attention anchors per screen |
| `isolated_key_element_count` | number | `1` to `2` | Von Restorff | Count intentionally isolated memory anchors |
| `pattern_familiarity` | bool | `true` | Jakob | Evaluate critical conventions vs user expectations |
| `chunk_count` | number | `3` to `9` | Miller | Count meaningful information chunks |
| `progress_visible` | bool | `true` | Goal-Gradient | Presence of stepper/progress indicators |
| `unfinished_resume_path` | bool | `true` | Zeigarnik | Presence of resume link/state for interrupted flow |
| `system_handles_complexity` | bool | `true` | Tesler | Autocomplete/default/mask/parser support |
| `positive_end_state` | bool | `true` | Peak-End | Clear completion feedback and next step |
| `input_tolerant_parsing` | bool | `true` | Postel | Multi-format tolerant parsing and normalization |
| `feedback_ms_p95` | number | `<= 400` | Doherty | p95 click-to-feedback latency |
| `critical_actions_boundary_placement` | bool | `true` | Serial Position | Critical items at start/end positions |
| `inline_validation_clear` | bool | `true` | Postel, Peak-End | Requirements visible + field-level actionable errors |
| `simplicity_score` | number | `>= 80` | Occam | Internal heuristic simplification score |
| `scope_creep_signals` | bool | `false` | Parkinson | Feature creep indicators present or not |

## Practical Guidance

- Use real measurements whenever possible (DevTools, analytics, session replay, Playwright captures).
- If a metric cannot be measured, leave it out and document why. The audit will mark corresponding laws as `unknown`.
- For strict release gates, require:
  - zero fast-gate failures
  - score >= team threshold (default 85)
  - no unresolved unknowns on P0/P1 laws

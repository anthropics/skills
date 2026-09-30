# Theory Playbook: Human-Centered Frontend Laws

Use this playbook when generating deep-dive diagnosis after running the automated audit.

## 1) Fitts's Law
- **Mechanism**: Target acquisition time depends on distance and size.
- **Failure pattern**: tiny controls, far-away submit button, high mis-tap.
- **Fix pattern**: enlarge hit area, reduce travel distance, place critical action at endpoint.

## 2) Hick's Law
- **Mechanism**: More visible options increase decision latency.
- **Failure pattern**: overloaded menus/forms, stalled first action.
- **Fix pattern**: reduce concurrent choices, stage options with progressive disclosure.

## 3) Gestalt Principles

### Proximity
- **Mechanism**: Near elements are interpreted as related.
- **Fix**: tighten internal spacing, widen inter-group spacing.

### Similarity
- **Mechanism**: Visual sameness implies functional sameness.
- **Fix**: enforce role-based style tokens.

### Continuity
- **Mechanism**: Eyes follow uninterrupted paths.
- **Fix**: align flow lines and continuation cues.

### Closure
- **Mechanism**: Users complete partial structures mentally.
- **Fix**: keep simplification interpretable; avoid ambiguous partials.

### Figure/Ground
- **Mechanism**: Clear foreground/background separation drives focus.
- **Fix**: stronger scrim, contrast, and layer hierarchy for overlays.

### Common Fate
- **Mechanism**: Co-moving elements are perceived as one group.
- **Fix**: synchronize direction/timing for grouped animations.

### Focal Point
- **Mechanism**: strongest contrast wins first attention.
- **Fix**: keep exactly one dominant visual target per screen.

## 4) Von Restorff Effect
- **Mechanism**: Distinct items are remembered better than uniform items.
- **Failure pattern**: everything highlighted, nothing memorable.
- **Fix pattern**: isolate one key action/info against stable baseline.

## 5) Jakob's Law
- **Mechanism**: Users expect familiar patterns from other products.
- **Failure pattern**: unconventional critical flow causing trust friction.
- **Fix pattern**: preserve conventions in high-risk journeys; innovate in low-risk zones.

## 6) Miller's Law
- **Mechanism**: Working memory handles limited chunks.
- **Failure pattern**: dense, all-at-once forms and settings.
- **Fix pattern**: chunk content and split long tasks into steps.

## 7) Goal-Gradient Hypothesis
- **Mechanism**: Motivation increases near completion.
- **Failure pattern**: hidden progress, late-stage abandonment.
- **Fix pattern**: visible progress bars/counters and milestone reinforcement.

## 8) Zeigarnik Effect
- **Mechanism**: Incomplete tasks remain cognitively active.
- **Failure pattern**: interrupted sessions never resumed.
- **Fix pattern**: explicit unfinished state and easy resume path.

## 9) Tesler's Law
- **Mechanism**: Complexity is conserved; someone must carry it.
- **Failure pattern**: users forced to handle formatting and consistency burden.
- **Fix pattern**: shift complexity into system defaults, parsing, and structured controls.

## 10) Peak-End Rule
- **Mechanism**: Memory is dominated by peak and ending moments.
- **Failure pattern**: successful flow ends with uncertainty.
- **Fix pattern**: strong closure state with clear confirmation and next step.

## 11) Postel's Law
- **Mechanism**: Be tolerant in input, strict in normalized output.
- **Failure pattern**: brittle validation and vague errors.
- **Fix pattern**: accept common variants, normalize internally, return specific errors.

## 12) Doherty Threshold
- **Mechanism**: Fast feedback preserves cognitive flow.
- **Failure pattern**: no immediate acknowledgment, repeated taps.
- **Fix pattern**: instant pressed/loading state and perceived-performance optimizations.

## 13) Serial Position Effect
- **Mechanism**: First and last sequence items are recalled best.
- **Failure pattern**: key actions buried mid-list.
- **Fix pattern**: place critical actions at sequence boundaries.

## 14) Occam's Razor
- **Mechanism**: Simplest sufficient path minimizes cognitive tax.
- **Failure pattern**: UI clutter and optional complexity in core flow.
- **Fix pattern**: remove non-essential elements and decision branches.

## 15) Parkinson's Law
- **Mechanism**: Work expands without constraints.
- **Failure pattern**: feature creep and bloated release scope.
- **Fix pattern**: enforce scope guardrails and defer non-core additions.

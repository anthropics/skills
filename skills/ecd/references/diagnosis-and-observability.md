# Diagnosis and Observability v2

## Purpose

This reference is for bug, failure, regression, anomaly, and systems-diagnosis requests.

It is not a default lens for every product-planning request.

## Core Position

- The user's description is input, not truth.
- A request may mix:
  - symptoms
  - guesses
  - wrong causal stories
  - missing facts
  - non-technical wording
- Diagnose the nature of the problem before proposing metrics or instrumentation.

## When To Apply This Reference

Use this reference when the request is about:

- bugs
- regressions
- operational failures
- anomalies
- incident patterns
- unexplained system behavior

Do not force this reference onto:

- ordinary greenfield product ideation
- feature scoping
- concept exploration

## A-Stage Guidance For Diagnosis Cases

- Separate:
  - user-reported symptoms
  - objective facts
  - suspected but unproven causes
  - missing observability
- Ask questions that improve localization, not questions that force the user into implementation talk.
- Prefer questions like:
  - what is happening now
  - what should happen instead
  - where it first becomes visible
  - how often it happens
  - what environment or input seems related

## Observability Principle

- The goal is not "add more logs".
- The goal is better localization:
  - where did it fail
  - where did it pass
  - what state was flowing through the system
  - which dependency or branch caused the failure

## Weak Moves To Reject

- taking the user's causal story as fact
- jumping straight to counters or thresholds before understanding the failure shape
- proposing logs everywhere with no localization model
- pretending missing facts are minor when they change the diagnosis direction

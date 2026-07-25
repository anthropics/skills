---
name: alphaear-signal-tracker
description: Track finance investment signal evolution and update logic based on new finance market information. Use when monitoring finance signals and determining if they are strengthened, weakened, or falsified.
---

# AlphaEar Signal Tracker Skill

## Overview

This skill provides logic to track and update investment signals. It assesses how new market information impacts existing signals (Strengthened, Weakened, Falsified, or Unchanged).

## Capabilities

### 1. Track Signal Evolution

### 1. Track Signal Evolution (Agentic Workflow)

**YOU (the Agent)** are the Tracker. Use the prompts in `references/PROMPTS.md`.

**Workflow:**
1.  **Research**: Use **FinResearcher Prompt** to gather facts/price for a signal.
2.  **Analyze**: Use **FinAnalyst Prompt** to generate the initial `InvestmentSignal`.
3.  **Track**: For existing signals, use **Signal Tracking Prompt** to assess evolution (Strengthened/Weakened/Falsified) based on new info.

**Tools:**
- Use `alphaear-search` and `alphaear-stock` skills to gather the necessary data.
- Use `scripts/fin_agent.py` helper `_sanitize_signal_output` if needing to clean JSON.

**Key Logic:**

-   **Input**: Existing Signal State + New Information (News/Price).
-   **Process**:
    1.  Compare new info with signal thesis.
    2.  Determine impact direction (Positive/Negative/Neutral).
    3.  Update confidence and intensity.
-   **Output**: Updated Signal.

**Example Usage (Conceptual):**

```python
# This skill is currently a pattern extracted from FinAgent.
# In a future refactor, it should be a standalone utility class.
# For now, refer to `scripts/fin_agent.py`'s `track_signal` method implementation.
```

## Dependencies

-   `agno` (Agent framework)
-   `sqlite3` (built-in)

Ensure `DatabaseManager` is initialized correctly.

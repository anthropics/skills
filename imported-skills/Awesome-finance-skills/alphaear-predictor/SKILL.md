---
name: alphaear-predictor
description: Market prediction skill using Kronos. Use when user needs finance market time-series forecasting or news-aware finance market adjustments.
---

# AlphaEar Predictor Skill

## Overview

This skill utilizes the Kronos model (via `KronosPredictorUtility`) to perform time-series forecasting and adjust predictions based on news sentiment.

## Capabilities

### 1. Forecast Market Trends

### 1. Forecast Market Trends

**Workflow:**
1.  **Generate Base Forecast**: Use `scripts/kronos_predictor.py` (via `KronosPredictorUtility`) to generate the technical/quantitative forecast.
2.  **Adjust Forecast (Agentic)**: Use the **Forecast Adjustment Prompt** in `references/PROMPTS.md` to subjectively adjust the numbers based on latest news/logic.

**Key Tools:**
-   `KronosPredictorUtility.get_base_forecast(df, lookback, pred_len, news_text)`: Returns `List[KLinePoint]`.

**Example Usage (Python):**

```python
from scripts.utils.kronos_predictor import KronosPredictorUtility
from scripts.utils.database_manager import DatabaseManager

db = DatabaseManager()
predictor = KronosPredictorUtility()

# Forecast
forecast = predictor.predict("600519", horizon="7d")
print(forecast)
```


## Configuration

This skill requires the **Kronos** model and an embedding model.

1.  **Kronos Model**:
    -   Ensure `exports/models` directory exists in the project root.
    -   Place trained news projector weights (e.g., `kronos_news_v1.pt`) in `exports/models/`.
    -   Or depend on the base model (automatically downloaded).

> [!CAUTION]
> **Model Security**: This skill loads model weights from `exports/models`. We use `weights_only=True` and only scan for the `kronos_news_*.pt` pattern. Ensure you only place trusted checkpoints in this directory.

2.  **Environment Variables**:
    -   `EMBEDDING_MODEL`: Path or name of the embedding model (default: `sentence-transformers/all-MiniLM-L6-v2`).
    -   `KRONOS_MODEL_PATH`: Optional path to override model loading.

## Dependencies

-   `torch`
-   `transformers`
-   `sentence-transformers`
-   `pandas`
-   `numpy`
-   `scikit-learn`

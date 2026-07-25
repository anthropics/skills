---
name: alphaear-sentiment
description: Analyze finance text sentiment using FinBERT or LLM. Use when the user needs to determine the sentiment (positive/negative/neutral) and score of financial text markets.
---

# AlphaEar Sentiment Skill

## Overview

This skill provides sentiment analysis capabilities tailored for financial texts, supporting both FinBERT (local model) and LLM-based analysis modes.

## Capabilities

## Capabilities

### 1. Analyze Sentiment (FinBERT / Local)

Use `scripts/sentiment_tools.py` for high-speed, local sentiment analysis using FinBERT.

**Key Methods:**

-   `analyze_sentiment(text)`: Get sentiment score and label using localized FinBERT model.
    -   **Returns**: `{'score': float, 'label': str, 'reason': str}`.
    -   **Score Range**: -1.0 (Negative) to 1.0 (Positive).
-   `batch_update_news_sentiment(source, limit)`: Batch process unanalyzed news in the database (FinBERT only).

### 2. Analyze Sentiment (LLM / Agentic)

For higher accuracy or reasoning capabilities, **YOU (the Agent)** should perform the analysis using the Prompt below, calling the LLM directly, and then update the database if necessary.

#### Sentiment Analysis Prompt

Use this prompt to analyze financial texts if the local tool is insufficient or if reasoning is required.

```markdown
请分析以下金融/新闻文本的情绪极性。
返回严格的 JSON 格式:
{"score": <float: -1.0到1.0>, "label": "<positive/negative/neutral>", "reason": "<简短理由>"}

文本: {text}
```

**Scoring Guide:**
- **Positive (0.1 to 1.0)**: Optimistic news, profit growth, policy support, etc.
- **Negative (-1.0 to -0.1)**: Losses, sanctions, price drops, pessimism.
- **Neutral (-0.1 to 0.1)**: Factual reporting, sideways movement, ambiguous impact.

#### Helper Methods
- `update_single_news_sentiment(id, score, reason)`: Use this to save your manual analysis to the database.

## Dependencies

-   `torch` (for FinBERT)
-   `transformers` (for FinBERT)
-   `sqlite3` (built-in)

Ensure `DatabaseManager` is initialized correctly.

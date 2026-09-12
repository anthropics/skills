---
name: economics
description: Calculate unit economics for your AI product. Revenue per action, API cost per action, gross margin, and free tier damage. Use when model pricing changes, rethinking credit pricing, or evaluating profitability.
license: Apache-2.0
---


Calculate the current unit economics for your AI product.

## Steps

### 1. Get pricing from the codebase
Search for credit/pricing constants:
```bash
grep -rn "CREDIT\|credit_cost\|COST\|FREE_CREDITS\|signup_bonus\|price\|PRICE" --include="*.py" --include="*.ts" -i
```

Find:
- How much users pay (e.g. $5 = 100 credits → $0.05/credit)
- How many credits each action costs (generation, image, regen, etc.)
- How many free credits new users get on signup

### 2. Get current model pricing
Search the web for current pricing for every model you use. Common ones to look up:
- OpenAI: `site:openai.com pricing`
- Anthropic: `site:anthropic.com pricing`
- Google Gemini: `site:ai.google.dev pricing`

Get input $/1M tokens, output $/1M tokens, and image generation cost if applicable.

### 3. Estimate tokens per action
Make reasonable assumptions based on your prompts (or read the actual prompt files):
- A typical text generation call: X input tokens, Y output tokens
- An embedding call: Z tokens
- An image generation: flat cost per image

If you can find the actual prompts in the codebase, read them and estimate more precisely.

### 4. Calculate cost per action
For each user-facing action:
```
API cost = (input_tokens / 1M × input_price) + (output_tokens / 1M × output_price)
Revenue  = credits_charged × price_per_credit
Margin   = (revenue - api_cost) / revenue × 100
```

### 5. Output the table

```
UNIT ECONOMICS — [your product]
════════════════════════════════════════════════════════════════
USER PRICING
  [price] = [credits] credits → $X.XX per credit
  Signup bonus: [N] free credits

ACTION ECONOMICS
────────────────────────────────────────────────────────────────
Action              Credits   Revenue   API Cost   Margin
────────────────────────────────────────────────────────────────
[action name]         [N]     $X.XX     $X.XXX     XX%
[action name]         [N]     $X.XX     $X.XXX     XX%
────────────────────────────────────────────────────────────────

FREE TIER DAMAGE (N signup credits)
  Conservative user:   costs you ~$X.XX
  Typical user:        costs you ~$X.XX
  Heavy user:          costs you ~$X.XX

PAYBACK POINT
  One paying user covers ~X non-converting free users
════════════════════════════════════════════════════════════════
```

### 6. Flag anything concerning
- Any action with margin below 50% — flag it prominently
- Free tier cost above $1 per signup — flag it
- If a model price changed since this was last run, call it out

### 7. Pricing sensitivity (if asked)
Show what margins look like at ±20% credit price. Helps decide whether to change pricing without rebuilding the whole spreadsheet.

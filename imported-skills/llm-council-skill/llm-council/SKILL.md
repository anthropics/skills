---
name: llm-council
description: Multi-LLM collaborative brainstorming and planning. Use when user explicitly requests consultation with multiple AI models (ChatGPT, Gemini, other LLMs) before presenting an implementation plan, or asks to "consult the council", "ask other models", or "get perspectives from other AIs". Queries external LLM APIs, synthesizes their perspectives, and presents an adapted implementation plan.
---

# LLM Council

Consult multiple AI models (ChatGPT and Gemini) for their perspectives before presenting implementation plans to users.

## Workflow

When user requests consultation with other AI models, use phrases like:
- "Consult with ChatGPT and Gemini about..."
- "Ask other AI models what they think about..."
- "Get perspectives from the council on..."
- "Consult the LLM council: [your question]"

**Process:**

1. **Query external LLMs**: Run `scripts/query_llms.py` with the user's prompt to get perspectives from both ChatGPT and Gemini
2. **Analyze responses**: Review what each model suggests, identifying valuable insights, alternative approaches, and potential concerns
3. **Synthesize plan**: Create an implementation plan that incorporates the best ideas from all three models (Claude's own analysis + ChatGPT + Gemini)
4. **Present to user**: Show the final plan along with a brief summary of key contributions from each model

## Setup Requirements

The skill requires API keys and optional model configuration stored in a `.env` file in the working directory:

```
OPENAI_API_KEY=sk-...
GEMINI_API_KEY=...

# Optional: Specify which models to use (defaults shown below)
OPENAI_MODEL=gpt-5-nano
GEMINI_MODEL=gemini-3-flash-preview
```

**Default Models:**
- ChatGPT: `gpt-5-nano` (fastest, most cost-efficient - $0.05/1M input, $0.40/1M output)
- Gemini: `gemini-3-flash-preview` (balanced speed and intelligence)

**Upgrade Options for Better Collaboration:**

*OpenAI models (ordered by capability and cost):*
- `gpt-5-nano` - Fastest, most cost-efficient ($0.05/1M in, $0.40/1M out) - **DEFAULT**
- `gpt-5-mini` - Faster, cost-efficient for well-defined tasks ($0.25/1M in, $2.00/1M out)
- `gpt-5.2` - Best for coding and agentic tasks ($1.75/1M in, $14.00/1M out)
- `gpt-5.2-pro` - Smarter, more precise for complex problems ($21.00/1M in, $168.00/1M out)

All models support reasoning tokens, 400K context window, and image input.

*Gemini models (ordered by capability):*
- `gemini-2.5-flash-lite` - Ultra-fast, optimized for throughput
- `gemini-2.5-flash` - Best price-performance, large-scale processing
- `gemini-3-flash-preview` - Balanced speed and frontier intelligence (default)
- `gemini-3-pro-preview` - Most intelligent multimodal model, best for complex reasoning

Higher-tier models provide more sophisticated analysis but cost more per API call.

If the `.env` file doesn't exist or keys are missing, inform the user and provide setup instructions.

## Usage Example

**User input:** "Consult the council: How should I architect a real-time data pipeline for IoT sensors?"

**Claude's process:**
1. Execute: `python3 scripts/query_llms.py "How should I architect a real-time data pipeline for IoT sensors?"`
2. Parse JSON responses from ChatGPT and Gemini
3. Analyze their suggestions (e.g., ChatGPT suggests Kafka, Gemini recommends considering edge computing)
4. Synthesize final plan incorporating valuable insights from all models
5. Present the adapted plan to user with attribution

## Output Format

Present the final implementation plan naturally, mentioning key insights from other models inline where relevant. For example:

"Based on consultation with ChatGPT and Gemini, here's the recommended architecture:

[Implementation plan with inline references like "ChatGPT highlighted the importance of..." or "Gemini suggested..."]

Key contributions:
- ChatGPT: [brief summary]
- Gemini: [brief summary]"

## Error Handling

- If API keys are missing, inform user and provide setup instructions
- If an API call fails, note which model's perspective is unavailable and proceed with available responses
- If both APIs fail, inform user and offer to provide Claude's own analysis without external consultation
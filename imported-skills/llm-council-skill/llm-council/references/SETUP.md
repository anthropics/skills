# Setup Guide

## Required API Keys

To use the LLM Council skill, you need API keys for both OpenAI and Google Gemini.

### Getting Your API Keys

1. **OpenAI API Key**
   - Visit: https://platform.openai.com/api-keys
   - Sign in or create an account
   - Click "Create new secret key"
   - Copy the key (starts with `sk-`)

2. **Gemini API Key**
   - Visit: https://aistudio.google.com/app/apikey
   - Sign in with your Google account
   - Click "Create API key"
   - Copy the key

### Creating the .env File

Create a file named `.env` in your working directory with the following content:

```
OPENAI_API_KEY=sk-your-openai-key-here
GEMINI_API_KEY=your-gemini-key-here
OPENAI_MODEL=gpt-5-nano-2025-08-07
GEMINI_MODEL=gemini-3-flash-preview
```

**Model Configuration:**

The default models (`gpt-5-nano-2025-08-07` and `gemini-3-flash-preview`) are optimized for:
- Fast response times
- High cost-effectiveness
- Good quality for most brainstorming tasks

**Upgrade to more powerful models** for complex technical decisions:

**OpenAI Options (ordered by capability):**
- `gpt-5-nano` - Ultra-fast, optimized for cost and throughput (default)
- `gpt-5-mini` - Advanced GPT-5 family model, efficient and capable
- `gpt-5` - Most capable general-purpose model in GPT-5 family
- `gpt-5.2` - State-of-the-art for professional knowledge work and long-running tasks

**Gemini Options (ordered by capability):**
- `gemini-2.5-flash-lite` - Ultra-fast, optimized for cost and throughput
- `gemini-2.5-flash` - Best price-performance for large-scale processing
- `gemini-3-flash-preview` - Balanced speed and frontier intelligence (default)
- `gemini-3-pro-preview` - Most intelligent multimodal model, best for complex reasoning

**Example Configurations:**

*Budget-conscious (defaults):*
```
OPENAI_MODEL=gpt-5-nano
GEMINI_MODEL=gemini-3-flash-preview
```

*Balanced quality/cost:*
```
OPENAI_MODEL=gpt-5-mini
GEMINI_MODEL=gemini-2.5-flash
```

*High-quality analysis:*
```
OPENAI_MODEL=gpt-5
GEMINI_MODEL=gemini-3-flash-preview
```

*Premium (best reasoning):*
```
OPENAI_MODEL=o3
GEMINI_MODEL=gemini-3-pro-preview
```

*Professional knowledge work:*
```
OPENAI_MODEL=gpt-5.2
GEMINI_MODEL=gemini-3-pro-preview
```

**Important Notes:**
- Replace the placeholder values with your actual API keys
- Keep this file secure and never commit it to version control
- Add `.env` to your `.gitignore` file if using git
- The `.env` file should be in the same directory where you run Claude

### Verification

To verify your setup is correct, you can test the script directly:

```bash
python3 scripts/query_llms.py "Test prompt"
```

If successful, you'll see JSON output with responses from both ChatGPT and Gemini.

## API Costs

Both APIs have usage costs:
- **OpenAI**: Charges per token (input + output)
- **Gemini**: Has a free tier with rate limits, then charges per token

Check the respective pricing pages for current rates and consider setting usage limits in your API dashboards.
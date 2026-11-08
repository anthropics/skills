# model-discoverability

**Make your website and content discoverable and computable by AI models.**

When someone asks ChatGPT, Claude, Gemini, or Perplexity a question your content answers, will the AI find you? This skill deploys a complete AI discoverability stack: llms.txt, Schema.org JSON-LD, companion data files with computation guides, and OpenAPI specs.

## Install

Copy the `model-discoverability` folder to your project's `.claude/skills/` directory:

```bash
cp -r model-discoverability /path/to/your/project/.claude/skills/
```

## Usage

```
/model-discoverability           # Full audit + generate + deploy
/model-discoverability audit     # Check what's missing
/model-discoverability add-data data/my_rankings.csv  # Make a data file computable
```

## What It Deploys

| File | Purpose |
|------|---------|
| `/llms.txt` | AI model discovery (llmstxt.org standard) |
| `/robots.txt` | Updated with llms.txt reference |
| Schema.org JSON-LD | Structured metadata on HTML pages |
| `/data/*.json` | Companion data with computation guides |
| `/data/*.csv` | Same data in CSV format |
| `/data/api.json` | OpenAPI 3.0 spec for data endpoints |

## The Key Innovation: Computation Guides

Most publishers stop at discoverability (can the AI find my content?). This skill goes further with **computability** (can the AI analyze my data?).

Every companion data file includes a `_computation_guide` that tells AI models with code execution what analyses to perform on the data. The AI doesn't just recommend your content — it uses your data to answer questions directly.

## Supports

- Apache reverse proxy (Alias + ProxyPass exclusions)
- Nginx (location blocks)
- Static hosting (Vercel, Netlify, S3)
- Streamlit, Flask, Express

## Author

Fred Zimmerman / [Nimble Books LLC](https://bigfivekiller.online)

## License

MIT

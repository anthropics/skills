---
name: web-researcher
description: "Use when gathering web research context via Tavily or DuckDuckGo before content generation or topic summarization"
---

# NoteMD Pro - Web Research

## Overview

This feature researches topics using web search providers and provides summarized context. It supports both Tavily (API-based) and DuckDuckGo (scraper-based) providers.

## When to Use

- **Research before writing**: Gather context for content generation
- **Summarize topics**: Get overview of any subject
- **Fact-checking**: Verify information from web sources
- **Literature review**: Collect information from multiple sources

## Function Call Chain

```
_performResearch (searchUtils.ts)
├── SearchManager.getProvider(settings)
│   ├── TavilyProvider (if searchProvider='tavily')
│   └── DuckDuckGoProvider (if searchProvider='duckduckgo')
├── provider.search(query, settings)
│   └── Returns SearchResult[]
├── fetchContentFromUrl(url)  [For DuckDuckGo only]
│   └── requestUrl({url, method: 'GET'})
│   └── Extract text from HTML
├── Combine research context
└── Return combined context string
```

## Search Providers

### Tavily Provider

- API-based search (requires API key)
- Returns snippets/summaries
- Faster, more reliable
- Configuration: `tavilyApiKey`, `tavilyMaxResults`, `tavilySearchDepth`

### DuckDuckGo Provider

- Web scraping (no API key needed)
- Returns URLs, fetches full content
- More results, slower
- Configuration: `ddgMaxResults`, `ddgFetchTimeout`

## Key Functions (from searchUtils.ts)

### \_performResearch

Performs web research for a topic and returns combined context.

```typescript
export async function _performResearch(
  settings: NotemdSettings,
  topic: string,
  progressReporter: ProgressReporter,
): Promise<string | null>;
```

### fetchContentFromUrl

Fetches content from a URL and extracts text.

```typescript
export async function fetchContentFromUrl(
  url: string,
  progressReporter: ProgressReporter,
  debugMode?: boolean,
): Promise<string>;
// Returns extracted text or error message
```

### SearchManager (search/SearchManager.ts)

Factory for getting search provider.

```typescript
export class SearchManager {
  static getProvider(settings: NotemdSettings): SearchProvider;
  // Returns TavilyProvider or DuckDuckGoProvider
}
```

## Settings

### Provider Settings

| Setting          | Description              |
| ---------------- | ------------------------ |
| `searchProvider` | 'tavily' or 'duckduckgo' |
| `tavilyApiKey`   | API key for Tavily       |

### Tavily Settings

| Setting             | Description                    |
| ------------------- | ------------------------------ |
| `tavilyMaxResults`  | Number of results (default: 5) |
| `tavilySearchDepth` | 'basic' or 'advanced'          |

### DuckDuckGo Settings

| Setting           | Description                      |
| ----------------- | -------------------------------- |
| `ddgMaxResults`   | Number of results (default: 5)   |
| `ddgFetchTimeout` | Timeout in seconds (default: 10) |

### Contextual Context (Macro Settings)

| Setting                 | Description                                              |
| ----------------------- | -------------------------------------------------------- |
| `enableFocusedLearning` | Inject macro user domain preferences globally            |
| `focusedLearningDomain` | The specific domain context (e.g., "Physics", "History") |

### Research Limits

| Setting                    | Description                     |
| -------------------------- | ------------------------------- |
| `maxResearchContentTokens` | Max tokens for research context |
| `enableApiErrorDebugMode`  | Enable detailed error logging   |

## Prompt Template (researchSummarize)

From `promptUtils.ts`:

```
Summarize the following search results for the topic "{TOPIC}".
Provide a concise yet comprehensive overview.
Focus on key findings, data, and important conclusions.
Format the summary in Markdown.
The output language should be {LANGUAGE}.

Search Results:
{SEARCH_RESULTS_CONTEXT}
```

## Output Format

Research context is formatted as:

```
Research context for "{query}" (via {provider}):

Result 1:
Title: {title}
URL: {url}
Content: {content}

Result 2:
Title: {title}
...
```

## Error Handling

### Common Errors

1. **No API key for Tavily**
   - Error: "Tavily API key not configured"
   - Solution: Add API key in settings or switch to DuckDuckGo

2. **Network timeout**
   - Error: "Timeout fetching {url}"
   - Solution: Increase `ddgFetchTimeout`

3. **No search results**
   - Warning: "Search returned no results"
   - Solution: Try different search query

### Debug Mode

Enable `enableApiErrorDebugMode` for detailed error information including:

- Full API request/response
- HTTP status codes
- Error stack traces

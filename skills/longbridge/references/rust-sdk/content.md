# Rust SDK — Content (News, Filings, Topics)

## ContentContext

Used for news and community discussion topics. Requires a separate context from QuoteContext.

```rust
use longbridge::{Config, content::ContentContext};
use std::sync::Arc;

let config = Arc::new(Config::from_apikey_env()?);
let content_ctx = ContentContext::try_new(config)?;
```

### news

```rust
let news = content_ctx.news("TSLA.US").await?;  // Vec<NewsItem>
for item in &news {
    println!("{}: {} ({})", item.published_at, item.title, item.url);
}
```

**NewsItem fields:**
- `id: String` — News ID
- `title: String` — Headline
- `description: String` — Summary
- `url: String` — Full article URL
- `published_at: OffsetDateTime`
- `comments_count: i32`
- `likes_count: i32`
- `shares_count: i32`

### topics

```rust
let topics = content_ctx.topics("700.HK").await?;  // Vec<TopicItem>
for item in &topics {
    println!("{}: {} ({} likes)", item.published_at, item.title, item.likes_count);
}
```

**TopicItem fields:** same structure as `NewsItem`.

---

## Filings (via QuoteContext)

Regulatory filings are accessed through `QuoteContext`, not `ContentContext`.

```rust
let (quote_ctx, _rx) = QuoteContext::new(config.clone());

let filings = quote_ctx.filings("AAPL.US").await?;  // Vec<FilingItem>
for f in &filings {
    println!("{}: {} — files: {:?}", f.published_at, f.title, f.file_urls);
}
```

**FilingItem fields:**
- `id: String` — Filing ID
- `title: String` — Filing title
- `description: String` — Summary
- `file_name: String` — Primary file name
- `file_urls: Vec<String>` — Download URLs
- `published_at: OffsetDateTime`

---

## Complete Example

```rust
use std::sync::Arc;
use longbridge::{Config, QuoteContext, content::ContentContext};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let config = Arc::new(Config::from_apikey_env()?);
    let content = ContentContext::try_new(config.clone())?;
    let (quote, _rx) = QuoteContext::new(config);

    // Fetch all content in parallel
    let (news, topics, filings) = tokio::join!(
        content.news("TSLA.US"),
        content.topics("TSLA.US"),
        quote.filings("TSLA.US"),
    );

    println!("News: {}", news?.len());
    println!("Topics: {}", topics?.len());
    println!("Filings: {}", filings?.len());
    Ok(())
}
```

---

## Note: Python SDK

The Python SDK does not expose a `ContentContext`. For news/filings/topics in Python, use:

1. **CLI** — `longbridge news SYMBOL`, `longbridge filing SYMBOL`, `longbridge topic SYMBOL`
2. **HttpClient** — raw HTTP calls to `/v1/content/{symbol}/news`, `/v1/content/{symbol}/topics`, `/v1/quote/filings`
3. **MCP** — `news`, `topics`, `filings` tools

```python
# Python: via HttpClient
http = HttpClient.from_oauth(oauth)
news = http.request("get", "/v1/content/TSLA.US/news")
topics = http.request("get", "/v1/content/TSLA.US/topics")
filings = http.request("get", "/v1/quote/filings", body={"symbol": "TSLA.US"})
```

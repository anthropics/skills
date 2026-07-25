# Data Extraction Recipes

Practical patterns for extracting structured data from web pages using Playwright. Each recipe is a self-contained pattern you can adapt to your target site.

## CSS Selector Patterns for Common Structures

### E-Commerce Product Listings

```python
PRODUCT_SELECTORS = {
    "container": "div.product-card, article.product, li.product-item",
    "fields": {
        "title": "h2.product-title, h3.product-name, [data-testid='product-title']",
        "price": "span.price, .product-price, [data-testid='price']",
        "original_price": "span.original-price, .was-price, del",
        "rating": "span.rating, .star-rating, [data-rating]",
        "review_count": "span.review-count, .num-reviews",
        "image_url": "img.product-image::attr(src), img::attr(data-src)",
        "product_url": "a.product-link::attr(href), h2 a::attr(href)",
        "availability": "span.stock-status, .availability",
    }
}
```

### News/Blog Article Listings

```python
ARTICLE_SELECTORS = {
    "container": "article, div.post, div.article-card",
    "fields": {
        "headline": "h2 a, h3 a, .article-title",
        "summary": "p.excerpt, .article-summary, .post-excerpt",
        "author": "span.author, .byline, [rel='author']",
        "date": "time, span.date, .published-date",
        "category": "span.category, a.tag, .article-category",
        "url": "h2 a::attr(href), .article-title a::attr(href)",
        "image_url": "img.thumbnail::attr(src), .article-image img::attr(src)",
    }
}
```

### Job Listings

```python
JOB_SELECTORS = {
    "container": "div.job-card, li.job-listing, article.job",
    "fields": {
        "title": "h2.job-title, a.job-link, [data-testid='job-title']",
        "company": "span.company-name, .employer, [data-testid='company']",
        "location": "span.location, .job-location, [data-testid='location']",
        "salary": "span.salary, .compensation, [data-testid='salary']",
        "job_type": "span.job-type, .employment-type",
        "posted_date": "time, span.posted, .date-posted",
        "url": "a.job-link::attr(href), h2 a::attr(href)",
    }
}
```

### Search Engine Results

```python
SERP_SELECTORS = {
    "container": "div.g, .search-result, li.result",
    "fields": {
        "title": "h3, .result-title",
        "url": "a::attr(href), cite",
        "snippet": "div.VwiC3b, .result-snippet, .search-description",
        "displayed_url": "cite, .result-url",
    }
}
```

## Table Extraction Recipes

### Simple HTML Table to JSON

The most common extraction pattern. Works for any standard `<table>` with `<thead>` and `<tbody>`.

```python
async def extract_table(page, table_selector="table"):
    """Extract an HTML table into a list of dictionaries."""
    data = await page.evaluate(f"""
        (selector) => {{
            const table = document.querySelector(selector);
            if (!table) return null;

            // Get headers
            const headers = Array.from(table.querySelectorAll('thead th, thead td'))
                .map(th => th.textContent.trim());

            // If no thead, use first row as headers
            if (headers.length === 0) {{
                const firstRow = table.querySelector('tr');
                if (firstRow) {{
                    headers.push(...Array.from(firstRow.querySelectorAll('th, td'))
                        .map(cell => cell.textContent.trim()));
                }}
            }}

            // Get data rows
            const rows = Array.from(table.querySelectorAll('tbody tr'));
            return rows.map(row => {{
                const cells = Array.from(row.querySelectorAll('td'));
                const obj = {{}};
                cells.forEach((cell, i) => {{
                    if (i < headers.length) {{
                        obj[headers[i]] = cell.textContent.trim();
                    }}
                }});
                return obj;
            }});
        }}
    """, table_selector)
    return data or []
```

### Table with Links and Attributes

When table cells contain links or data attributes, not just text:

```python
async def extract_rich_table(page, table_selector="table"):
    """Extract table including links and data attributes."""
    return await page.evaluate(f"""
        (selector) => {{
            const table = document.querySelector(selector);
            if (!table) return [];

            const headers = Array.from(table.querySelectorAll('thead th'))
                .map(th => th.textContent.trim());

            return Array.from(table.querySelectorAll('tbody tr')).map(row => {{
                const obj = {{}};
                Array.from(row.querySelectorAll('td')).forEach((cell, i) => {{
                    const key = headers[i] || `col_${{i}}`;
                    obj[key] = cell.textContent.trim();

                    // Extract link if present
                    const link = cell.querySelector('a');
                    if (link) {{
                        obj[key + '_url'] = link.href;
                    }}

                    // Extract data attributes
                    for (const attr of cell.attributes) {{
                        if (attr.name.startsWith('data-')) {{
                            obj[key + '_' + attr.name] = attr.value;
                        }}
                    }}
                }});
                return obj;
            }});
        }}
    """, table_selector)
```

### Multi-Page Table (Paginated)

```python
async def extract_paginated_table(page, table_selector, next_selector, max_pages=50):
    """Extract data from a table that spans multiple pages."""
    all_rows = []
    headers = None

    for page_num in range(max_pages):
        # Extract current page
        page_data = await page.evaluate(f"""
            (selector) => {{
                const table = document.querySelector(selector);
                if (!table) return {{ headers: [], rows: [] }};

                const hs = Array.from(table.querySelectorAll('thead th'))
                    .map(th => th.textContent.trim());

                const rs = Array.from(table.querySelectorAll('tbody tr')).map(row =>
                    Array.from(row.querySelectorAll('td')).map(td => td.textContent.trim())
                );

                return {{ headers: hs, rows: rs }};
            }}
        """, table_selector)

        if headers is None and page_data["headers"]:
            headers = page_data["headers"]

        for row in page_data["rows"]:
            all_rows.append(dict(zip(headers or [], row)))

        # Check for next page
        next_btn = page.locator(next_selector)
        if await next_btn.count() == 0 or await next_btn.is_disabled():
            break

        await next_btn.click()
        await page.wait_for_load_state("networkidle")
        await page.wait_for_timeout(random.randint(800, 2000))

    return all_rows
```

## Product Listing Extraction

### Generic Listing Extractor

Works for any repeating card/list pattern:

```python
async def extract_listings(page, container_sel, field_map):
    """
    Extract data from repeating elements.

    field_map: dict mapping field names to CSS selectors.
    Special suffixes:
        ::attr(name)  — extract attribute instead of text
        ::html        — extract innerHTML
    """
    items = []
    cards = await page.query_selector_all(container_sel)

    for card in cards:
        item = {}
        for field_name, selector in field_map.items():
            try:
                if "::attr(" in selector:
                    sel, attr = selector.split("::attr(")
                    attr = attr.rstrip(")")
                    el = await card.query_selector(sel)
                    item[field_name] = await el.get_attribute(attr) if el else None
                elif selector.endswith("::html"):
                    sel = selector.replace("::html", "")
                    el = await card.query_selector(sel)
                    item[field_name] = await el.inner_html() if el else None
                else:
                    el = await card.query_selector(selector)
                    item[field_name] = (await el.text_content()).strip() if el else None
            except Exception:
                item[field_name] = None
        items.append(item)

    return items
```

### With Price Parsing

```python
import re

def parse_price(text):
    """Extract numeric price from text like '$1,234.56' or '1.234,56 EUR'."""
    if not text:
        return None
    # Remove currency symbols and whitespace
    cleaned = re.sub(r'[^\d.,]', '', text.strip())
    if not cleaned:
        return None
    # Handle European format (1.234,56)
    if ',' in cleaned and '.' in cleaned:
        if cleaned.rindex(',') > cleaned.rindex('.'):
            cleaned = cleaned.replace('.', '').replace(',', '.')
        else:
            cleaned = cleaned.replace(',', '')
    elif ',' in cleaned:
        # Could be 1,234 or 1,23 — check decimal places
        parts = cleaned.split(',')
        if len(parts[-1]) <= 2:
            cleaned = cleaned.replace(',', '.')
        else:
            cleaned = cleaned.replace(',', '')
    try:
        return float(cleaned)
    except ValueError:
        return None

async def extract_products_with_prices(page, container_sel, field_map, price_field="price"):
    """Extract listings and parse prices into floats."""
    items = await extract_listings(page, container_sel, field_map)
    for item in items:
        if price_field in item and item[price_field]:
            item[f"{price_field}_raw"] = item[price_field]
            item[price_field] = parse_price(item[price_field])
    return items
```

## Pagination Handling

### Next-Button Pagination

The most common pattern. Click "Next" until the button disappears or is disabled.

```python
async def paginate_via_next_button(page, next_selector, content_selector, max_pages=100):
    """
    Yield page objects as you paginate through results.

    next_selector: CSS selector for the "Next" button/link
    content_selector: CSS selector to wait for after navigation (confirms new page loaded)
    """
    pages_scraped = 0

    while pages_scraped < max_pages:
        yield page  # Caller extracts data from current page
        pages_scraped += 1

        next_btn = page.locator(next_selector)
        if await next_btn.count() == 0:
            break

        try:
            is_disabled = await next_btn.is_disabled()
        except Exception:
            is_disabled = True

        if is_disabled:
            break

        await next_btn.click()
        await page.wait_for_selector(content_selector, state="attached")
        await page.wait_for_timeout(random.randint(500, 1500))
```

### URL-Based Pagination

When pages follow a predictable URL pattern:

```python
async def paginate_via_url(page, url_template, start=1, max_pages=100):
    """
    Navigate through pages using URL parameters.

    url_template: URL with {page} placeholder, e.g., "https://example.com/search?page={page}"
    """
    for page_num in range(start, start + max_pages):
        url = url_template.format(page=page_num)
        response = await page.goto(url, wait_until="networkidle")

        if response and response.status == 404:
            break

        yield page, page_num
        await page.wait_for_timeout(random.randint(800, 2500))
```

### Infinite Scroll

For sites that load content as you scroll:

```python
async def paginate_via_scroll(page, item_selector, max_scrolls=100, no_change_limit=3):
    """
    Scroll to load more content until no new items appear.

    item_selector: CSS selector for individual items (used to count progress)
    no_change_limit: Stop after N scrolls with no new items
    """
    previous_count = 0
    no_change_streak = 0

    for scroll_num in range(max_scrolls):
        # Count current items
        current_count = await page.locator(item_selector).count()

        if current_count == previous_count:
            no_change_streak += 1
            if no_change_streak >= no_change_limit:
                break
        else:
            no_change_streak = 0

        previous_count = current_count

        # Scroll to bottom
        await page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
        await page.wait_for_timeout(random.randint(1000, 2500))

        # Check for "Load More" button that might appear
        load_more = page.locator("button:has-text('Load More'), button:has-text('Show More')")
        if await load_more.count() > 0 and await load_more.is_visible():
            await load_more.click()
            await page.wait_for_timeout(random.randint(1000, 2000))

    return current_count
```

### Load-More Button

Simpler variant of infinite scroll where content loads via a button:

```python
async def paginate_via_load_more(page, button_selector, item_selector, max_clicks=50):
    """Click a 'Load More' button repeatedly until it disappears."""
    for click_num in range(max_clicks):
        btn = page.locator(button_selector)
        if await btn.count() == 0 or not await btn.is_visible():
            break

        count_before = await page.locator(item_selector).count()
        await btn.click()

        # Wait for new items to appear
        try:
            await page.wait_for_function(
                f"document.querySelectorAll('{item_selector}').length > {count_before}",
                timeout=10000,
            )
        except Exception:
            break  # No new items loaded

        await page.wait_for_timeout(random.randint(500, 1500))

    return await page.locator(item_selector).count()
```

## Nested Data Extraction

### Comments with Replies (Threaded)

```python
async def extract_threaded_comments(page, parent_selector=".comments"):
    """Recursively extract threaded comments."""
    return await page.evaluate(f"""
        (parentSelector) => {{
            function extractThread(container) {{
                const comments = [];
                const directChildren = container.querySelectorAll(':scope > .comment');

                for (const comment of directChildren) {{
                    const authorEl = comment.querySelector('.author, .username');
                    const textEl = comment.querySelector('.comment-text, .comment-body');
                    const dateEl = comment.querySelector('time, .date');
                    const repliesContainer = comment.querySelector('.replies, .children');

                    comments.push({{
                        author: authorEl ? authorEl.textContent.trim() : null,
                        text: textEl ? textEl.textContent.trim() : null,
                        date: dateEl ? (dateEl.getAttribute('datetime') || dateEl.textContent.trim()) : null,
                        replies: repliesContainer ? extractThread(repliesContainer) : [],
                    }});
                }}

                return comments;
            }}

            const root = document.querySelector(parentSelector);
            return root ? extractThread(root) : [];
        }}
    """, parent_selector)
```

### Nested Categories (Sidebar/Menu)

```python
async def extract_category_tree(page, root_selector="nav.categories"):
    """Extract nested category structure from a sidebar or menu."""
    return await page.evaluate(f"""
        (rootSelector) => {{
            function extractLevel(container) {{
                const items = [];
                const directItems = container.querySelectorAll(':scope > li, :scope > div.category');

                for (const item of directItems) {{
                    const link = item.querySelector(':scope > a');
                    const subMenu = item.querySelector(':scope > ul, :scope > div.sub-categories');

                    items.push({{
                        name: link ? link.textContent.trim() : item.textContent.trim().split('\\n')[0],
                        url: link ? link.href : null,
                        children: subMenu ? extractLevel(subMenu) : [],
                    }});
                }}

                return items;
            }}

            const root = document.querySelector(rootSelector);
            return root ? extractLevel(root.querySelector('ul') || root) : [];
        }}
    """, root_selector)
```

### Accordion/Expandable Content

Some content is hidden behind accordion/expand toggles. Click to reveal, then extract.

```python
async def extract_accordion(page, toggle_selector, content_selector):
    """Expand all accordion items and extract their content."""
    items = []
    toggles = await page.query_selector_all(toggle_selector)

    for toggle in toggles:
        title = (await toggle.text_content()).strip()

        # Click to expand
        await toggle.click()
        await page.wait_for_timeout(300)

        # Find the associated content panel
        content = await toggle.evaluate_handle(
            f"el => el.closest('.accordion-item, .faq-item')?.querySelector('{content_selector}')"
        )

        body = None
        if content:
            body = (await content.text_content())
            if body:
                body = body.strip()

        items.append({"title": title, "content": body})

    return items
```

## Data Cleaning Utilities

### Post-Extraction Cleaning

```python
import re

def clean_text(text):
    """Normalize whitespace, remove zero-width characters."""
    if not text:
        return None
    # Remove zero-width characters
    text = re.sub(r'[\u200b\u200c\u200d\ufeff]', '', text)
    # Normalize whitespace
    text = re.sub(r'\s+', ' ', text).strip()
    return text if text else None

def clean_url(url, base_url=None):
    """Convert relative URLs to absolute."""
    if not url:
        return None
    url = url.strip()
    if url.startswith("//"):
        return "https:" + url
    if url.startswith("/") and base_url:
        return base_url.rstrip("/") + url
    return url

def deduplicate(items, key_field):
    """Remove duplicate items based on a key field."""
    seen = set()
    unique = []
    for item in items:
        key = item.get(key_field)
        if key and key not in seen:
            seen.add(key)
            unique.append(item)
    return unique
```

### Output Formats

```python
import json
import csv
import io

def to_jsonl(items, file_path):
    """Write items as JSON Lines (one JSON object per line)."""
    with open(file_path, "w") as f:
        for item in items:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")

def to_csv(items, file_path):
    """Write items as CSV."""
    if not items:
        return
    headers = list(items[0].keys())
    with open(file_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        writer.writerows(items)

def to_json(items, file_path, indent=2):
    """Write items as a JSON array."""
    with open(file_path, "w") as f:
        json.dump(items, f, indent=indent, ensure_ascii=False)
```

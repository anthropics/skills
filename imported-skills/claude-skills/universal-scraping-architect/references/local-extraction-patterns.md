# Local Extraction Patterns (BeautifulSoup + pandas)

Patterns for Mode 2 (local Python) and the local half of Mode 3 (hybrid). Use these
when extracting from static HTML, local files (PDF/Excel/CSV), private/sensitive
data, or simple pages where Firecrawl is overkill. See `scripts/local_bs4_example.py`.

## Fetch safely
Use `requests` with an identifying `User-Agent`, a timeout, and bounded retries with
backoff. Always call `raise_for_status()` and handle the specific exception types
(`HTTPError`, `ConnectionError`, `Timeout`) rather than a bare `except`.

## Select robustly, not brittly
Anchor on stable signals — `id`, `data-*` attributes, semantic tags — not deep
positional chains. **Anti-pattern:** `div > span > ul > li:nth-child(3)` breaks the
moment the layout shifts. Prefer `soup.find("table", {"id": "..."})` or attribute
selectors, and fail loudly (with a message telling the user to update the selector)
when the target isn't found.

## Parse tables with pandas
`pd.read_html(str(table))[0]` turns an HTML `<table>` into a DataFrame. Scope it to
the specific table element you located with BeautifulSoup rather than letting pandas
guess across the whole page.

## Normalize then validate
1. **Column names** → snake_case (`strip().lower()`, collapse whitespace, drop
   non-word chars) so downstream code is stable.
2. **Clean** → strip string cells, drop fully-empty rows, coerce dtypes.
3. **Validate before saving** → assert the frame is non-empty *and* every required
   column is present. Never blindly write an empty or malformed result to disk.

## Choose the output format
- **CSV** — flat/tabular data.
- **JSON** — nested or typed structures (validate it with `scripts/validate_extraction.py`).
- **Markdown** — clean prose destined for an LLM.

## Privacy
Local processing keeps sensitive data on-machine — this is the safe default whenever
the source is private. Don't ship local files to an external API just for convenience.

### Authoritative Sources
1. [Beautiful Soup Documentation](https://www.crummy.com/software/BeautifulSoup/bs4/doc/)
2. [pandas.read_html — API reference](https://pandas.pydata.org/docs/reference/api/pandas.read_html.html)
3. [Requests: HTTP for Humans](https://requests.readthedocs.io/en/latest/)
4. [WHATWG HTML Living Standard — Tabular data](https://html.spec.whatwg.org/multipage/tables.html)
5. [MDN: CSS selectors](https://developer.mozilla.org/en-US/docs/Web/CSS/CSS_selectors)
6. [pandas — Working with missing data](https://pandas.pydata.org/docs/user_guide/missing_data.html)

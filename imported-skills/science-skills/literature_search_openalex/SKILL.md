---
name: literature-search-openalex
description: >
  Query the OpenAlex scholarly database for research papers, authors,
  institutions, topics, sources, publishers, funders, geo-locations, and
  keywords. Use when searching academic papers, resolving DOIs, downloading
  open-access PDFs, finding an author's publications, aggregating bibliometric
  data (citation counts, h-index, impact factor), exploring the research
  taxonomies, or performing DOI lookups.
---

# OpenAlex Skill

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/literature_search_openalex_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at https://developers.openalex.org/ and
    to always check the license of the papers retrieved by the skill for any
    restrictions, then (2) create the file recording the notification text and
    timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`OPENALEX_API_KEY`** (optional but recommended): Enables the OpenAlex
    Premium API with higher rate limits. The skill works without it (using the
    free "polite pool"). You can obtain a key at OpenAlex.org → account
    settings. You **MUST** use the safe credentials protocol in the
    `credentials` skill to check for and request this key if this skill looks
    relevant to the user's request.

## Core Rules

1.  **List Sources.** If this skill is used, ensure this is mentioned in the
    output AND list the URLs of all papers that were used in producing the
    output.
2.  **Resolve before filter.** NEVER filter by name. Always `resolve` a name to
    an ID first, then use that ID in `--filter`.
3.  **Use the CLI only.** Never call the API via `curl`/`urllib`. The CLI
    handles retries and rate limiting.
4.  **No fabrication.** Never invent OpenAlex IDs or DOIs. Use `resolve`/`get`
    to look them up. Report empty results accurately.
5.  **API key.** If a command returns 401/429 or you need high-volume queries,
    you **MUST** use the safe credentials protocol in the `credentials` skill to
    check for and request the `OPENALEX_API_KEY` to help the user add it to
    their `.env` file.
6.  **Keep output small.** Always use `--select` and `--per-page 5–10` for
    overview queries. Pipe `filter` output to a file (`> results.json`), then
    slim with `jq` before reading into context.

## Rate Limits

-   **With key:** ~10 req/s, $1/day free budget.
-   **Without key:** Very limited, $0.01/day budget.

Operation              | Cost
---------------------- | -------
Singleton `get`        | Free
`filter`               | $0.0001
`--search` / `resolve` | $0.001
`download-pdf`         | $0.01

## CLI Reference

```
uv run scripts/openalex_cli.py [--api-key KEY] <command> [flags]
```

Entity types (shared across commands): `works`, `authors`, `sources`,
`institutions`, `topics`, `domains`, `fields`, `subfields`, `sdgs`, `countries`,
`continents`, `languages`, `keywords`, `publishers`, `funders`, `work-types`,
`source-types`, `institution-types`, `licenses`

### Commands

**resolve** `<entity> <query>` — Name → ID candidates. Returns `id`,
`display_name`, `hint`. Use `--per-page N` for more candidates.

**get** `<entity> <id>` — Full metadata for one entity. Accepts short ID
(`W2741809807`), full URL, or DOI URL. Use `--select` to limit fields.

**filter** `<entity>` — Search/filter entities. Key flags are:

-   `--search <query>`: Full-text search (10× cost of `--filter`)
-   `--filter <expr>`: Filter expressions. Use `,` for AND and `|` for OR.
-   `--sort <field:dir>`: Sort results (e.g., `cited_by_count:desc`)
-   `--select <fields>`: Limit the fields returned in the output.
-   `--group-by <field>`: Aggregate results by a specific field.
-   `--per-page <N>`: Number of results per page (default 25, max 100).
-   `--page <N>`: Specify the page number to retrieve.
-   `--sample <N>`: Get a random sample of up to 10,000 results.
-   `--seed <N>`: Seed for reproducible sampling.

**download-pdf** `<work-id> <output-path>` — Download PDF (requires API key).
Falls back to alternative `pdf_url` locations if primary fails. Whenever you
download a PDF, verify it is not empty or corrupted.

**rate-limit** — Check current rate limit status (requires API key).

### Search Tips

-   If `resolve` returns no matches, try alternate spellings or abbreviations.
-   If `--search` returns 0 results, try broader terms (max 3 retries).
-   If `resolve` returns multiple candidates, present them to the user with
    `display_name` and `hint` for manual selection.

## Entity References

Consult `references/` for valid filter, sort, and group-by fields per entity:

-   [Works](references/works.md) — [Authors](references/authors.md) —
    [Sources](references/sources.md)
-   [Institutions](references/institutions.md) — [Topics](references/topics.md)
    — [Taxonomy](references/taxonomy.md)
-   [Geo & Language](references/geo_and_language.md) —
    [Publishers & Funders](references/publishers_funders.md)
-   [Type Values](references/type_values.md)

## Common Workflows

```bash
# Author's works (resolve → filter)
uv run scripts/openalex_cli.py resolve authors "Geoffrey Hinton"
uv run scripts/openalex_cli.py filter works \
  --filter "authorships.author.id:A5108093963" \
  --sort "cited_by_count:desc" --per-page 10 > papers.json
cat papers.json | jq '[.results[] | {id, title: .display_name, year: .publication_year, citations: .cited_by_count}]'

# DOI lookup
uv run scripts/openalex_cli.py get works "https://doi.org/10.1038/s41586-021-03819-2"

# Bulk DOI lookup (up to 100)
uv run scripts/openalex_cli.py filter works \
  --filter "doi:10.1234/a|10.1234/b|10.1234/c" --per-page 100 > results.json

# Institutional impact by year
uv run scripts/openalex_cli.py resolve institutions "MIT"
uv run scripts/openalex_cli.py filter works \
  --filter "authorships.institutions.id:I63966007" \
  --group-by "publication_year" > mit_by_year.json

# Random sample
uv run scripts/openalex_cli.py filter works \
  --filter "publication_year:2023,is_oa:true" \
  --sample 100 --seed 42 > results.json
```

## Error Handling

| Code | Meaning             | Action                        |
| ---- | ------------------- | ----------------------------- |
| 401  | Unauthorized        | You MUST use safe credentials |
:      :                     : protocol in credentials skill :
:      :                     : to help user add API key to   :
:      :                     : `.env`                        :
| 403  | Plan upgrade needed | Inform user; see              |
:      :                     : https\://openalex.org/pricing :
| 404  | Not found           | Verify ID; try `resolve`      |
:      :                     : first                         :
| 429  | Rate limited        | Wait and retry; you MUST use  |
:      :                     : safe credentials protocol in  :
:      :                     : credentials skill to help     :
:      :                     : user add API key to `.env`    :

Known premium-only filters: `from_updated_date`, `to_updated_date`.

Never fabricate results on empty responses — report accurately and suggest
alternate search terms.

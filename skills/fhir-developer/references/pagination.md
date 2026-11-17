# FHIR Pagination

All search results MUST support pagination. Return a Bundle with navigation links.

## Table of Contents
- [Search Response Structure](#search-response-structure)
- [Pagination Parameters](#pagination-parameters)
- [Link Relations](#link-relations)
- [Implementation Example](#implementation-example)
- [Additional Search Modifiers](#additional-search-modifiers)

## Search Response Structure

```json
{
  "resourceType": "Bundle",
  "type": "searchset",
  "total": 150,
  "link": [
    {
      "relation": "self",
      "url": "https://fhir.example.org/Patient?name=Smith&_count=10"
    },
    {
      "relation": "next",
      "url": "https://fhir.example.org/Patient?name=Smith&_count=10&_offset=10"
    }
  ],
  "entry": [
    {
      "fullUrl": "https://fhir.example.org/Patient/123",
      "resource": { "resourceType": "Patient", "id": "123" },
      "search": { "mode": "match" }
    }
  ]
}
```

## Pagination Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `_count` | Number of results per page | Server-defined (often 10-100) |
| `_offset` | Starting index (0-based) | 0 |
| `_page` | Alternative to offset (1-based page number) | 1 |

## Link Relations

| Relation | Description |
|----------|-------------|
| `self` | Current page URL |
| `first` | First page |
| `previous` | Previous page (if not on first) |
| `next` | Next page (if more results exist) |
| `last` | Last page |

## Implementation Example

```python
@app.get("/Patient")
async def search_patients(
    name: str = None,
    _count: int = 10,
    _offset: int = 0
):
    # Query with limit + 1 to detect if there are more results
    results = db.query_patients(name=name, limit=_count + 1, offset=_offset)
    has_more = len(results) > _count
    results = results[:_count]  # Trim to requested count

    base_url = f"{BASE_URL}/Patient"
    params = f"name={name}&_count={_count}" if name else f"_count={_count}"

    links = [
        {"relation": "self", "url": f"{base_url}?{params}&_offset={_offset}"}
    ]

    if _offset > 0:
        prev_offset = max(0, _offset - _count)
        links.append({"relation": "previous", "url": f"{base_url}?{params}&_offset={prev_offset}"})

    if has_more:
        links.append({"relation": "next", "url": f"{base_url}?{params}&_offset={_offset + _count}"})

    return {
        "resourceType": "Bundle",
        "type": "searchset",
        "total": db.count_patients(name=name),
        "link": links,
        "entry": [
            {"fullUrl": f"{base_url}/{p['id']}", "resource": p, "search": {"mode": "match"}}
            for p in results
        ]
    }
```

## Additional Search Modifiers

| Parameter | Description | Example |
|-----------|-------------|---------|
| `_sort` | Sort by field (prefix `-` for descending) | `_sort=-date,name` |
| `_elements` | Return only specified fields | `_elements=name,birthDate` |
| `_summary` | Return summary view | `_summary=true` |
| `_include` | Include referenced resources | `_include=Observation:patient` |
| `_revinclude` | Include resources that reference this | `_revinclude=Observation:patient` |

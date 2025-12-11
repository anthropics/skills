---
name: marklogic-development
description: Provides expert guidance for MarkLogic XQuery development, REST API resource endpoints, JSON handling patterns, query construction, and database configuration. Use this skill when working with MarkLogic Server, writing XQuery modules, creating REST resource endpoints, debugging XDMP errors, or configuring MarkLogic databases.
---

# MarkLogic Development

## Overview

This skill provides comprehensive guidance for MarkLogic Server development, covering XQuery patterns, REST API resource endpoints, JSON handling, CTS query construction, and database configuration. Use when working with MarkLogic-specific code, debugging errors, or implementing search and data manipulation features.

## Related Skills

When working with MarkLogic XQuery, load these complementary skills as needed:

### marklogic-xquery-stdlib

**Contains:** 103 standard XQuery/XPath built-in functions including string manipulation (fn:concat, fn:substring, fn:replace), sequence operations (fn:distinct-values, fn:reverse, fn:subsequence), numeric functions (fn:sum, fn:avg, fn:round), boolean logic, date/time functions, and higher-order functions (fn:map, fn:filter, fn:fold-left).

**Load when:** Working with standard XQuery string processing, sequence manipulation, numeric calculations, or date/time operations. If the task involves fundamental XQuery operations like string concatenation, filtering sequences, or formatting dates, load this skill.

### marklogic-search-and-query

**Contains:** 393 MarkLogic search and query functions including CTS query constructors (cts:word-query, cts:and-query, cts:or-query), lexicon operations, range queries, field queries, vector search capabilities, and semantic/RDF functions. Covers the entire cts: namespace for building complex search queries.

**Load when:** Building search queries, constructing CTS queries for full-text search, implementing faceted search, working with lexicons, or building semantic/RDF queries. If the task involves cts:search, query construction, or search optimization, load this skill.

### marklogic-data-manipulation

**Contains:** 256 MarkLogic data manipulation functions including document operations (xdmp:document-insert, xdmp:document-delete, xdmp:node-replace), JSON processing (json:array, xdmp:to-json, xdmp:from-json), collection management, permissions handling, metadata operations, locks, properties, and XQuery evaluation functions (xdmp:eval, xdmp:invoke).

**Load when:** Inserting, updating, or deleting documents; managing collections and permissions; working with JSON data structures; manipulating node trees; or executing dynamic XQuery code. If the task involves database updates, document management, or JSON transformation, load this skill.


## Core XQuery Patterns

### Native JSON Construction

**Prefer native object-node and array-node constructors over map-based approaches:**

```xquery
(: Preferred - Native constructors :)
document {
  object-node {
    "total": 100,
    "results": array-node {
      for $item in $items
      return object-node {
        "id": $item/@id,
        "name": $item/name/text()
      }
    },
    "metadata": object-node {
      "timestamp": fn:current-dateTime()
    }
  }
}

(: Avoid - Map-based approach :)
xdmp:to-json(
  map:new((
    map:entry("total", 100),
    map:entry("results", json:to-array(...)),
    map:entry("metadata", map:new(...))
  ))
)
```

**Benefits:**
- More declarative and readable JSON structure
- Better performance (native constructors are more efficient)
- Simpler code (no need for conditional empty array handling)
- Empty sequences automatically become empty arrays

### Default Values Pattern

**Use sequence-based default values instead of repetitive if-then-else:**

```xquery
(: Preferred - Clean default values :)
map:new((
  map:entry("field-name", (map:get($options, "field-name"), "default-value")[1]),
  map:entry("page-size", (map:get($options, "page-size"), 10)[1]),
  map:entry("enabled", (map:get($options, "enabled"), fn:true())[1])
))

(: Avoid - Verbose conditionals :)
map:new((
  map:entry("field-name",
    if (exists($options)) then map:get($options, "field-name")
    else "default-value"),
  map:entry("page-size",
    if (exists($options)) then map:get($options, "page-size")
    else 10)
))
```

**Pattern:** `(map:get($map, "key"), $default)[1]` returns the first non-empty value.

### Module Organization

**Separate concerns into focused functions:**

```xquery
(: Configuration builder - handles defaults :)
declare function lib:build-config($options as map:map?) as map:map { ... };

(: Core business logic - executes operation :)
declare function lib:execute-search($config as map:map) as item()* { ... };

(: Formatting - transforms results to output format :)
declare function lib:format-results($results as item()*, $config as map:map) as document-node() { ... };
```

**Benefits:**
- Single responsibility per function
- Easier testing and maintenance
- Clear separation between validation, logic, and formatting

## REST Resource Endpoints

### POST Input Handling

**REST API passes document-node with object-node child:**

```xquery
declare function resource:post(
  $context as map:map,
  $params as map:map,
  $input as document-node()*
) as document-node()?
{
  (: Extract object-node and convert to map :)
  let $json-map := xdmp:from-json($input/object-node())

  (: Access fields from map :)
  let $field1 := map:get($json-map, "field_name")
  let $field2 := map:get($json-map, "other_field")

  (: Process and return result :)
  ...
};
```

**Key Points:**
- `$input` is `document-node()` containing `object-node()` child
- Use `$input/object-node()` to extract the JSON object
- Convert with `xdmp:from-json()` to get map:map
- **Do not** use `rh:objectify-post-input()` then convert - extract directly

**Alternative: Work with object-node directly:**

```xquery
let $json-node := $input/object-node()
let $field := $json-node/fieldName/xs:string(.)
```

### Validation and Error Handling

**Manual validation for REST resources:**

```xquery
(: Manual validation without validation-helper :)
return
  if (fn:empty($json-map)) then (
    rh:set-output-status($context, map:new((
      map:entry("response-code", $const:HTTP_BAD_REQUEST),
      map:entry("response-message", "Request body is required")
    )))
  )
  else if (fn:empty($field1) and fn:empty($field2)) then (
    rh:set-output-status($context, map:new((
      map:entry("response-code", $const:HTTP_BAD_REQUEST),
      map:entry("response-message", "At least one field is required")
    )))
  )
  else (
    lib:execute-operation($json-map, $options)
  )
```

**Avoid validation-helper for complex types:**
- `validation:not-empty()` uses `xs:string($value)` which fails on document-node/object-node
- Implement manual validation for JSON inputs

### HTTP Method Restrictions

```xquery
declare function resource:get(
  $context as map:map,
  $params as map:map
) as document-node()*
{
  fn:error(xs:QName("UNSUPPORTED-HTTP-METHOD"),
    "GET method is not supported for this endpoint")
};
```

## CTS Query Construction

### Tiered Search Pattern

**Implement weighted multi-tier search:**

```xquery
(: Tier 1: ALL must match (required terms) :)
let $tier1-queries :=
  for $term in $must-have-all
  return cts:field-word-query("field-name", $term, ("case-insensitive", "stemmed"), 16.0)

(: Tier 2: At least ONE must match :)
let $tier2-queries :=
  for $term in $must-have-any
  return cts:field-word-query("field-name", $term, ("case-insensitive", "stemmed"), 8.0)

(: Tier 3: Optional boost (not required) :)
let $tier3-queries :=
  for $term in $boost-ranking
  return cts:field-word-query("field-name", $term, ("case-insensitive", "stemmed"), 1.0)

(: Combine tiers :)
let $content-query := cts:and-query((
  if (fn:exists($tier1-queries)) then cts:and-query($tier1-queries) else (),
  if (fn:exists($tier2-queries)) then cts:or-query($tier2-queries) else (),
  if (fn:exists($tier3-queries)) then
    cts:boost-query(cts:true-query(), cts:or-query($tier3-queries))
  else ()
))
```

### Recency Boosting

**Boost recent documents with granular year-based weights:**

```xquery
declare function lib:build-recency-boost-query($config as map:map) as cts:query
{
  let $current-year := fn:year-from-date(fn:current-date())
  let $year-path := "/document/date-field"

  return cts:or-query((
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year)), (), 8.0),
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year - 1)), (), 6.0),
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year - 2)), (), 4.0),
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year - 3)), (), 3.0),
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year - 4)), (), 2.0),
    cts:path-range-query($year-path, "=", xs:gYear(fn:string($current-year - 5)), (), 1.0)
  ))
};

(: Apply recency boost :)
let $main-query := cts:boost-query($content-query, lib:build-recency-boost-query($config))
```

### Search Execution

**Execute search with scoring and pagination:**

```xquery
let $scoped-query := cts:and-query((
  cts:collection-query("my-collection"),
  $main-query
))

let $results := cts:search(
  fn:doc(),
  $scoped-query,
  (
    "score-logtfidf",
    cts:score-order("descending"),
    "unfiltered"
  ),
  0  (: quality - 0 for speed, increase for accuracy :)
)[map:get($config, "start") to (map:get($config, "start") + map:get($config, "page-size") - 1)]

let $total := xdmp:estimate(cts:search(fn:doc(), $scoped-query))
```

## Database Configuration

### Field Definitions

**Define weighted fields for multi-path search:**

```json
{
  "field": [
    {
      "field-name": "reference-search",
      "include-root": true,
      "field-path": [
        {
          "path": "/document/document-biblio/document-title",
          "weight": 8.0
        },
        {
          "path": "//abstract",
          "weight": 4.0
        },
        {
          "path": "//keyword-phrase",
          "weight": 2.0
        },
        {
          "path": "/document/document-biblio/source-publication/source-title",
          "weight": 1.5
        }
      ]
    }
  ]
}
```

### Word Lexicons

**Enable word lexicons for field-based search:**

```json
{
  "field-value-searches": true,
  "field-value-positions": false,
  "word-lexicon": [
    "reference-search"
  ]
}
```

## Common Error Patterns

### XDMP-CAST Errors

**Problem:** `xs:string($value)` fails on complex types

```xquery
(: Problematic :)
declare function validation:not-empty($value) {
  xs:string($value) != ""  (: Fails on document-node, object-node :)
};

(: Solution: Check type first :)
declare function safe:not-empty($value) {
  fn:exists($value) and
  (
    typeswitch($value)
      case xs:string return fn:string-length($value) > 0
      case document-node() return fn:exists($value/node())
      case object-node() return fn:exists(map:keys(xdmp:from-json($value)))
      default return fn:true()
  )
};
```

### XDMP-ARGTYPE Errors

**Problem:** Passing wrong type to map:get

```xquery
(: Problematic :)
let $json-map := xdmp:from-json($document-node)  (: Returns empty :)
let $value := map:get($json-map, "key")  (: Error: arg1 not map:map :)

(: Solution: Extract object-node first :)
let $json-map := xdmp:from-json($document-node/object-node())
let $value := map:get($json-map, "key")  (: Works :)
```

### Digest Authentication and POST Bodies

**Problem:** curl digest auth consumes POST body on first request

```bash
# Problematic - body not sent
curl -u user:pass --digest -d '{"data":"value"}' http://host/endpoint

# Solution 1: Use basic auth for testing
curl -u user:pass -d '{"data":"value"}' http://host/endpoint

# Solution 2: Use --data-binary with stdin
echo '{"data":"value"}' | curl -u user:pass --digest --data-binary @- http://host/endpoint
```

## Deployment with ml-gradle

### Standard Deployment

```bash
# Set Java home
export JAVA_HOME=/path/to/jdk

# Deploy modules
./gradlew mlLoadModules

# Reload modules (forces refresh)
./gradlew mlReloadModules

# Watch for changes (auto-deploy)
./gradlew mlWatch
```

### Checking mlWatch Status

```bash
# List background jobs
jobs

# Kill mlWatch if needed
pkill -f mlWatch
```

## References

This skill includes reference documentation in the `references/` directory:

- `references/common-errors.md` - Detailed XDMP error explanations and solutions
- `references/json-patterns.md` - Comprehensive JSON handling patterns
- `references/query-examples.md` - CTS query construction examples

Load these references when deeper understanding or additional examples are needed.

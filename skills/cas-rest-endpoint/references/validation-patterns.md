# CAS REST Endpoint Validation Patterns

This document describes common validation patterns used in CAS REST endpoints.

## Common Validation Functions

The `rest-helper` module provides standard validation functions:

### not-empty
Validates that a value is not empty.

```xquery
map:new()
    => map:with("value", $param)
    => map:with("validation-function", "not-empty")
    => map:with("response-code", $const:HTTP_BAD_REQUEST)
    => map:with("response-message", "param is required")
```

### list-contains-item
Validates that an item is in a list of valid options.

```xquery
let $type-in-list :=
    map:new()
        => map:with("item", $type)
        => map:with("list", ("option1", "option2", "option3"))

let $rule :=
    map:new()
        => map:with("value", $type-in-list)
        => map:with("validation-function", "list-contains-item")
        => map:with("response-code", $const:HTTP_BAD_REQUEST)
        => map:with("response-message", "A valid type is required: " || xdmp:to-json(map:get($type-in-list, "list")))
```

### is-valid-search-keyword
Validates that text is at least 3 characters for search.

```xquery
map:new()
    => map:with("value", $text)
    => map:with("validation-function", "is-valid-search-keyword")
    => map:with("response-code", $const:HTTP_BAD_REQUEST)
    => map:with("response-message", "text must be at least 3 characters")
```

### document-exists
Validates that a document exists in the database.

```xquery
map:new()
    => map:with("value", $uri)
    => map:with("validation-function", "document-exists")
    => map:with("response-code", $const:HTTP_NOT_FOUND)
    => map:with("response-message", "document does not exist")
```

## Helper Validation Functions

The `rest-helper` module also provides composite validation helpers:

### query-single-uri-validation
Validates query parameters for endpoints that accept a single URI with type.

```xquery
rh:query-single-uri-validation($params-map, ("protein", "ligand", "scaffold"), fn:true())
```

### filters-validation
Validates filter parameters from request body.

```xquery
let $filters := $json-obj/query/filters/node()
let $rules := rh:filters-validation($filters)
```

### sort-validation
Validates sort parameters against allowed sort keys.

```xquery
let $sorts := $json-obj/query/sort
let $rules := rh:sort-validation($sorts, $sort-keys)
```

## Extracting Parameters

### From Query Parameters (GET)
```xquery
let $param1 := map:get($params, "param1")
let $limit := (map:get($params, "limit"), 10)[1]  (: with default :)
```

### From Request Body (POST)
```xquery
let $json-obj := rh:objectify-post-input($input)
let $field1 := $json-obj/field1/string()
let $limit := ($json-obj/limit/xs:int(.), 50)[1]  (: with default :)
```

### From Query and URI Parameters
```xquery
let $params-map := rh:extract-query-single-uri-params($json-obj)
```

### From Filters
```xquery
let $filters := $json-obj/query/filters/node()
let $filters-map := rh:extract-filters-params($filters)
```

## Response Patterns

### Success with JSON
```xquery
xdmp:to-json($result-data)
```

### Success with Status Code
```xquery
(
    xdmp:to-json($result),
    map:put($context, "output-status", ($const:HTTP_OK, "OK"))
)
```

### No Content
```xquery
map:put($context, "output-status", ($const:HTTP_NO_CONTENT, "No content"))
```

### Validation Error
```xquery
if (not(empty($validation-result))) then
    rh:set-output-status($context, $validation-result)
else
    (: success path :)
```

## Logging

Always log request parameters at the end:

```xquery
log:trace("ENDPOINT_NAME", $params)  (: for GET :)
log:trace("ENDPOINT_NAME", $input)   (: for POST :)
```

## Common HTTP Status Constants

- `$const:HTTP_OK` - 200
- `$const:HTTP_NO_CONTENT` - 204
- `$const:HTTP_BAD_REQUEST` - 400
- `$const:HTTP_NOT_FOUND` - 404

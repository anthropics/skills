---
name: cas-rest-endpoint
description: Creates new MarkLogic REST API endpoints for the CAS application following established patterns. Use this skill when creating new REST service endpoints in the marklogic/src/main/ml-modules/services/ directory.
---

# CAS REST Endpoint

## Overview

This skill provides templates and guidance for creating new MarkLogic REST API endpoints following the CAS application's established patterns. It includes templates for both the XQuery endpoint module and the metadata descriptor, along with common validation patterns.

## When to Use This Skill

Use this skill when:
- Creating a new REST API endpoint in the CAS application
- The endpoint needs to follow the standard MarkLogic REST API extension pattern
- Validation, parameter extraction, and error handling should follow CAS conventions

## Creating a New Endpoint

### Step 1: Gather Requirements

Before creating the endpoint, determine:
1. **Endpoint name** - The resource name (e.g., `ligand-summary`, `cas-search`, `autosuggest`)
2. **HTTP methods** - Which methods to support (GET, POST, PUT, DELETE)
3. **Parameters** - What parameters the endpoint accepts (query params for GET, body fields for POST)
4. **Validation rules** - What validation is needed for parameters
5. **Business logic** - What the endpoint should do (reference to utility modules)
6. **Response format** - What data structure to return

### Step 2: Generate Files from Templates

Create two files from the provided templates:

#### XQuery Endpoint File
**Location:** `marklogic/src/main/ml-modules/services/{endpoint-name}.xqy`

Copy the template from [assets/endpoint-template.xqy](assets/endpoint-template.xqy) and replace placeholders:
- `{{MODULE_PREFIX}}` - Short module prefix (e.g., `s` for summary, `ls` for ligand-summary, `p` for pharmacology)
- `{{ENDPOINT_NAME}}` - The endpoint name as used in the URL (e.g., `ligand-summary`)
- `{{ENDPOINT_NAME_UPPER}}` - Uppercase version for logging (e.g., `LIGAND_SUMMARY`)

#### Metadata File
**Location:** `marklogic/src/main/ml-modules/services/metadata/{endpoint-name}.xml`

Copy the template from [assets/metadata-template.xml](assets/metadata-template.xml) and replace placeholders:
- `{{ENDPOINT_NAME}}` - The endpoint name
- `{{ENDPOINT_DESCRIPTION}}` - Brief description of what the endpoint does

Update the `<method>` elements to include only the HTTP methods your endpoint supports. Add `<param>` elements for any query parameters.

### Step 3: Implement Endpoint Logic

Follow this pattern for each HTTP method handler:

1. **Extract parameters** from `$params` (GET) or `$input` (POST)
2. **Define validation rules** using the `rest-helper` validation patterns
3. **Validate** the request using `rh:validate($rules)`
4. **Handle validation failures** with `rh:set-output-status($context, $validation-result)`
5. **Implement business logic** - typically by calling utility module functions
6. **Return response** as JSON using `xdmp:to-json()`
7. **Log the request** using `log:trace()`

### Step 4: Common Patterns

#### Standard Imports
All endpoints should import these core modules:

```xquery
import module namespace rh = "https://pubs.cas.org/modules/lib/rest-helper" at "/lib/rest-helper.xqy";
import module namespace const = "https://pubs.cas.org/modules/lib/constants" at "/lib/constants.xqy";
import module namespace log = "https://pubs.cas.org/modules/lib/logger" at "/lib/logger.xqy";
```

Import additional utility modules as needed for business logic.

#### Parameter Extraction

**GET endpoints** - extract from `$params` map:
```xquery
let $uri := map:get($params, "uri")
let $limit := (map:get($params, "limit"), 10)[1]  (: with default value :)
```

**POST endpoints** - parse JSON and extract from body:
```xquery
let $json-obj := rh:objectify-post-input($input)
let $text := $json-obj/text/string()
let $filters := $json-obj/filters/node()
```

#### Validation

Refer to [references/validation-patterns.md](references/validation-patterns.md) for detailed validation examples. Common patterns:

**Required parameter:**
```xquery
map:new()
    => map:with("value", $uri)
    => map:with("validation-function", "not-empty")
    => map:with("response-code", $const:HTTP_BAD_REQUEST)
    => map:with("response-message", "uri is required")
```

**Value must be in list:**
```xquery
let $type-in-list :=
    map:new()
        => map:with("item", $type)
        => map:with("list", ("ligand", "protein", "disease"))

let $rule :=
    map:new()
        => map:with("value", $type-in-list)
        => map:with("validation-function", "list-contains-item")
        => map:with("response-code", $const:HTTP_BAD_REQUEST)
        => map:with("response-message", "A valid type is required")
```

**Apply validation:**
```xquery
let $validation-result := rh:validate($rules)
return (
    if (not(empty($validation-result))) then
        rh:set-output-status($context, $validation-result)
    else
        (: success path :)
)
```

#### Response Handling

**Success with data:**
```xquery
xdmp:to-json($result-data)
```

**Success with explicit status:**
```xquery
(
    xdmp:to-json($result),
    map:put($context, "output-status", ($const:HTTP_OK, "OK"))
)
```

**No content found:**
```xquery
map:put($context, "output-status", ($const:HTTP_NO_CONTENT, "No content"))
```

#### Unsupported Methods

For HTTP methods not supported by your endpoint:
```xquery
declare function prefix:delete(
    $context as map:map,
    $params as map:map
) as document-node()? {
    fn:error(xs:QName("UNSUPPORTED-HTTP-METHOD"), "DELETE method is not supported for this endpoint")
}
```

### Step 5: Testing

After creating the endpoint:
1. Deploy to MarkLogic using the build process
2. Test each HTTP method with valid parameters
3. Test validation by sending invalid parameters
4. Verify error responses have appropriate status codes
5. Check logs to ensure trace logging is working

## Resources

### assets/
- **endpoint-template.xqy** - Template for the XQuery endpoint module
- **metadata-template.xml** - Template for the endpoint metadata descriptor

### references/
- **validation-patterns.md** - Comprehensive guide to validation patterns, parameter extraction, and response handling used throughout the CAS application

## Examples

### Simple GET Endpoint
See [ligand-summary.xqy](../../marklogic/src/main/ml-modules/services/ligand-summary.xqy) in the codebase for a straightforward GET endpoint that:
- Accepts `uri` and `type` parameters
- Validates parameters with `not-empty` and `list-contains-item`
- Calls a utility function to get data
- Returns JSON response

### Complex POST Endpoint
See [cas-search.xqy](../../marklogic/src/main/ml-modules/services/cas-search.xqy) in the codebase for a POST endpoint that:
- Accepts JSON request body with multiple fields
- Uses composite validation helpers
- Extracts and processes filters
- Handles sorting and pagination
- Implements unsupported method handlers

### Simple GET with Minimal Validation
See [autosuggest.xqy](../../marklogic/src/main/ml-modules/services/autosuggest.xqy) for a GET endpoint with basic parameter validation and direct utility function call.

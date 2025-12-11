---
name: cas-ls-prime-project
description: Project-specific knowledge for the CAS LS Prime scientific literature search platform. Covers project structure, document schemas, library modules, REST endpoints, deployment workflows, and integration with AWS Bedrock. Use when working on the ls-prime codebase at /Users/lpollington/Dev/cas/repos/ls-prime.
---

# CAS LS Prime Project

## Overview

This skill provides project-specific knowledge for the CAS LS Prime platform - a MarkLogic-based scientific literature search system. Use when working on this specific codebase, understanding document structures, implementing search features, or integrating with external services.

## Project Structure

### Repository Layout

```
/Users/lpollington/Dev/cas/repos/ls-prime/
├── marklogic/                          # MarkLogic application
│   ├── src/main/
│   │   ├── ml-config/                  # Database and app server config
│   │   │   └── databases/
│   │   │       └── prime-content.json  # Main database configuration
│   │   └── ml-modules/
│   │       ├── root/
│   │       │   ├── lib/                # Library modules (reusable)
│   │       │   │   ├── reference-search/
│   │       │   │   ├── search/
│   │       │   │   ├── validation-helper.xqy
│   │       │   │   ├── rest-helper.xqy
│   │       │   │   └── logger.xqy
│   │       │   └── prototypes/         # Experimental endpoints
│   │       │       └── reference-search/
│   │       └── services/               # REST resource endpoints
│   │           └── reference-search.xqy
│   ├── gradle.properties               # Environment-specific config
│   └── build.gradle                    # Build configuration
├── prime-ui/                           # Frontend application
├── prime-test/                         # Test suites
│   └── ui/                             # Playwright tests
└── useful_scripts/                     # Utility scripts
```

### Key Configuration Files

**gradle.properties**: Environment-specific settings
- `mlHost`: MarkLogic server host
- `mlRestPort`: REST API port (typically 9324)
- `mlUsername/mlPassword`: Admin credentials

**Java Version**: Requires Java 17
```bash
export JAVA_HOME=/Library/Java/JavaVirtualMachines/temurin-17.jdk/Contents/Home
```

## Document Structure

### Scientific Literature Schema

Documents are stored in XML format with this structure:

```xml
<document>
  <document-biblio>
    <document-title>Title of paper</document-title>

    <source-publication>
      <source-title>Journal name</source-title>
      <content-date date-context="publication">
        <display-year>2024</display-year>
      </content-date>
    </source-publication>

    <contributors>
      <contributor contributor-type="author">
        <name>
          <given-name>John</given-name>
          <surname>Doe</surname>
        </name>
        <affiliation>
          <organization>University Name</organization>
        </affiliation>
      </contributor>
    </contributors>

    <abstract>
      <sentence>First sentence of abstract.</sentence>
      <sentence>Second sentence.</sentence>
    </abstract>

    <keyword-phrase>cancer breast AKT1</keyword-phrase>
    <keyword-phrase>mutation clinical trial</keyword-phrase>
  </document-biblio>

  <document-types>
    <document-type>Journal</document-type>
  </document-types>
</document>
```

### Collections

- `source/journal`: Journal articles
- `source/patent`: Patent documents
- `source/medline`: Medical literature

### URIs

Format: `/document/{source}/{type}/{id}`
- `/document/pt/document/63319825` - Journal article
- `/document/pt/patent/70646134` - Patent
- `/document/pt/medline/31139698` - Medical literature

## Library Modules

### Helper Libraries

**rest-helper.xqy** (`https://pubs.cas.org/modules/lib/rest-helper`)
- `rh:validate($rules)`: Rule-based validation
- `rh:set-output-status($context, $result)`: Set HTTP response status
- `rh:extract-filters-params($filters)`: Extract filter parameters
- `rh:objectify-post-input($input)`: Wrap input in document node

**validation-helper.xqy** (`https://pubs.cas.org/modules/lib/validation-helper`)
- `validation:not-empty($value)`: Check non-empty (caveat: uses xs:string cast)
- `validation:document-exists($uri)`: Check document exists
- `validation:is-integer($value)`: Validate integer
- `validation:list-contains-item($map)`: Check if list contains item

**Note**: validation-helper has limitations with complex types. For JSON inputs, prefer manual validation.

**constants.xqy** (`https://pubs.cas.org/modules/lib/constants`)
- `$const:HTTP_OK`: 200
- `$const:HTTP_BAD_REQUEST`: 400
- `$const:HTTP_NOT_FOUND`: 404
- `$const:HTTP_INTERNAL_SERVER_ERROR`: 500

**logger.xqy** (`https://pubs.cas.org/modules/lib/logger`)
- `log:trace($label, $data)`: Log trace message
- `log:debug($label, $data)`: Log debug message
- `log:error($label, $data)`: Log error message

### Search Libraries

**cas-search-lib.xqy**: Main search library for disease/protein/ligand contexts

**reference-search-lib.xqy** (`https://pubs.cas.org/modules/lib/reference-search`)
- `rsl:build-config($options)`: Build configuration with defaults
- `rsl:search-and-format($search-terms, $options)`: Execute tiered search
- `rsl:format-search-results(...)`: Format results as JSON
- `rsl:build-field-query($term, $config, $tier)`: Build field query
- `rsl:build-recency-boost-query($config)`: Build recency boost
- `rsl:extract-document-fields($biblio, $uri, $query)`: Extract and format document

## REST Resource Endpoints

### Endpoint Pattern

Located in: `marklogic/src/main/ml-modules/services/`

Each endpoint must declare these functions (even if unsupported):

```xquery
module namespace resource = "http://marklogic.com/rest-api/resource/{name}";

declare function resource:get($context, $params) { ... };
declare function resource:post($context, $params, $input) { ... };
declare function resource:put($context, $params, $input) { ... };
declare function resource:delete($context, $params) { ... };
```

### Standard Endpoint Structure

```xquery
xquery version "1.0-ml";

module namespace resource = "http://marklogic.com/rest-api/resource/my-endpoint";

import module namespace lib = "https://pubs.cas.org/modules/lib/my-lib" at "/lib/my-lib.xqy";
import module namespace const = "https://pubs.cas.org/modules/lib/constants" at "/lib/constants.xqy";

declare function resource:post(
  $context as map:map,
  $params as map:map,
  $input as document-node()*
) as document-node()?
{
  (: Extract and validate input :)
  let $json-map := xdmp:from-json($input/object-node())

  (: Validate required fields :)
  return
    if (fn:empty($json-map)) then
      (: Set error status :)
    else
      (: Call library function :)
      lib:execute-operation($json-map, ())
};

declare function resource:get($context, $params) {
  fn:error(xs:QName("UNSUPPORTED-HTTP-METHOD"), "GET not supported")
};
```

### Accessing Endpoints

**URL Pattern**: `http://localhost:9324/v1/resources/{endpoint-name}`

**Example**:
```bash
curl -X POST 'http://localhost:9324/v1/resources/reference-search' \
  -H 'Content-Type: application/json' \
  -u admin:admin \
  -d '{"must_have_all": ["AKT1", "cancer"]}'
```

## Prototype Endpoints

### Purpose

Prototypes are experimental endpoints located in `marklogic/src/main/ml-modules/root/prototypes/`. They can use any HTTP method and don't follow REST resource conventions.

### URL Pattern

`http://localhost:9324/prototypes/{folder}/{script}.xqy`

### Example Structure

```
prototypes/
└── reference-search/
    ├── index.html          # UI for testing
    ├── search.xqy          # GET endpoint with query string
    ├── extract-terms.xqy   # LLM integration
    └── README.md           # Documentation
```

### Accessing Prototypes

```bash
# GET request with query parameter
curl 'http://localhost:9324/prototypes/reference-search/search.xqy?q=AKT1+cancer'

# Or open in browser
open http://localhost:9324/prototypes/reference-search/index.html
```

## AWS Bedrock Integration

### Configuration

AWS Bedrock credentials and configuration are loaded from environment or stored in library modules.

**bedrock-config.xqy** pattern:
```xquery
module namespace bedrock = "https://pubs.cas.org/modules/lib/bedrock-config";

declare variable $bedrock:region := "us-east-1";
declare variable $bedrock:model-id := "anthropic.claude-haiku-20250318-v1:0";
declare variable $bedrock:endpoint := "https://bedrock-runtime.us-east-1.amazonaws.com";
```

### Calling Bedrock API

```xquery
let $request-body := xdmp:to-json(object-node {
  "anthropic_version": "bedrock-2023-05-31",
  "max_tokens": 1000,
  "system": $system-prompt,
  "messages": array-node {
    object-node {
      "role": "user",
      "content": $user-query
    }
  }
})

let $response := xdmp:http-post(
  $bedrock:endpoint || "/model/" || $bedrock:model-id || "/invoke",
  <options xmlns="xdmp:http">
    <headers>
      <Authorization>{$auth-header}</Authorization>
      <Content-Type>application/json</Content-Type>
    </headers>
  </options>,
  $request-body
)

let $result := $response[2]/object-node()
```

## Database Configuration

### Prime Content Database

**Location**: `marklogic/src/main/ml-config/databases/prime-content.json`

### Field Definitions

Fields allow weighted multi-path search:

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
        },
        {
          "path": "//contributor/name",
          "weight": 1.5
        },
        {
          "path": "//affiliation/organization",
          "weight": 1.5
        }
      ]
    }
  ]
}
```

### Adding Word Lexicons

```json
{
  "field-value-searches": true,
  "field-value-positions": false,
  "word-lexicon": [
    "reference-search"
  ]
}
```

## Deployment Workflow

### Standard Workflow

```bash
# 1. Navigate to marklogic directory
cd /Users/lpollington/Dev/cas/repos/ls-prime/marklogic

# 2. Set Java home
export JAVA_HOME=/Library/Java/JavaVirtualMachines/temurin-17.jdk/Contents/Home

# 3. Deploy changes
./gradlew mlLoadModules

# 4. For database config changes
./gradlew mlUpdateIndexes
./gradlew mlReloadModules  # Force reload after index updates
```

### Development with Auto-Deploy

```bash
# Start watch mode (auto-deploys on file changes)
./gradlew mlWatch

# In another terminal, make code changes
# mlWatch will automatically deploy them

# To stop: Ctrl+C or pkill -f mlWatch
```

### Common Gradle Tasks

- `mlLoadModules`: Deploy XQuery modules
- `mlReloadModules`: Force reload (clears cache)
- `mlUpdateIndexes`: Update database indexes and fields
- `mlDeploy`: Full deployment (app servers, databases, modules)
- `mlWatch`: Watch for changes and auto-deploy
- `mlUndeploy`: Remove application from MarkLogic

## Testing

### Playwright Tests

**Location**: `prime-test/ui/src/tests/`

**Running tests**:
```bash
cd /Users/lpollington/Dev/cas/repos/ls-prime/prime-test/ui

# Run all tests
npm test

# Run specific test file
npx playwright test src/tests/referenceSearch/referenceSearch_api.spec.ts

# Run in UI mode
npx playwright test --ui
```

### Test Structure

```typescript
test.describe('API Endpoint Tests', () => {
  test('should handle valid request', async ({request}) => {
    const response = await request.post(API_ENDPOINT, {
      headers: { 'Content-Type': 'application/json' },
      data: { field: 'value' },
      auth: { username: 'admin', password: 'admin' }
    });

    expect(response.status()).toBe(200);
    const body = await response.json();
    expect(body).toHaveProperty('results');
  });
});
```

## Git Workflow

### Branch Strategy

- `main`: Production-ready code
- `feature/*`: Feature development branches
- `feature/reference-search-v1`: Current reference search work

### Common Operations

```bash
# Check status
git status

# Stage changes
git add path/to/file

# Commit with co-authorship
git commit -m "Description

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>"

# Push to remote
git push origin feature/branch-name

# Create pull request
gh pr create --title "Title" --body "Description"
```

### Large File Handling

Large files (>100MB) cannot be pushed to GitHub. Add to `.gitignore`:

```
# Large document list files
useful_scripts/documents-10K.txt
```

If accidentally committed, remove from history:
```bash
git rm --cached path/to/large/file
git commit --amend
# or use git reset --soft to redo commits
```

## Common Patterns

### Search Result Formatting

Standard JSON response format:

```json
{
  "total": 100,
  "returned": 10,
  "start": 1,
  "pageSize": 10,
  "searchTerms": {
    "mustHaveAll": ["term1", "term2"],
    "mustHaveAny": ["term3", "term4"],
    "boostRanking": ["term5"]
  },
  "documents": [
    {
      "uri": "/document/pt/document/123",
      "documentTitle": "Title",
      "abstract": "Abstract with <mark>highlighted</mark> terms",
      "authors": ["Author1", "Author2"],
      "journalTitle": "Journal Name",
      "publicationDate": "2024",
      "score": 12345,
      "confidence": 0.75,
      "hits": [...]
    }
  ]
}
```

### Error Log Location

MarkLogic error logs: `/Users/lpollington/Dev/cas/bf-marklogic/ml-data/Logs/9324_ErrorLog.txt`

**Reading logs**:
```bash
# View recent errors
tail -100 /Users/lpollington/Dev/cas/bf-marklogic/ml-data/Logs/9324_ErrorLog.txt

# Search for specific error
grep "XDMP-CAST" /Users/lpollington/Dev/cas/bf-marklogic/ml-data/Logs/9324_ErrorLog.txt
```

## Project Conventions

### Code Style

1. **Use native MarkLogic constructors** for JSON (object-node, array-node)
2. **Imperative comments** with clear explanations
3. **Separate library modules** from endpoint logic
4. **Manual validation** for REST resources (avoid validation-helper with complex types)
5. **CamelCase** for JSON field names in responses

### Naming Conventions

- **Library modules**: `{domain}-lib.xqy` (e.g., `reference-search-lib.xqy`)
- **REST resources**: `{feature-name}.xqy` (e.g., `reference-search.xqy`)
- **Namespaces**: `https://pubs.cas.org/modules/lib/{name}`
- **Functions**: `prefix:verb-noun` (e.g., `rsl:build-config`)

### Documentation

- Add XQDoc comments for public functions
- Include parameter types and return types
- Document configuration options with examples
- Create README.md for prototype endpoints

## References

This skill includes detailed reference documentation:

- `references/document-schema.md` - Complete XML schema with examples
- `references/rest-endpoints.md` - All available REST endpoints and usage
- `references/deployment-guide.md` - Detailed deployment procedures

Load these references when working on specific aspects of the project.

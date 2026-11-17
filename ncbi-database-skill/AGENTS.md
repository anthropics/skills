# AGENTS.md - Development Guidelines

## Project Overview

This is the `ncbi-database-skill` npm package - a Node.js client for NCBI (National Center for Biotechnology Information) databases and APIs.

## Tech Stack

- **Runtime**: Node.js (ES Modules)
- **HTTP Client**: axios
- **CLI**: Commander.js pattern with parseArgs

## Key Files

| File | Purpose |
|------|---------|
| `src/ncbi-client.js` | Core API client (668 lines) |
| `bin/cli.js` | CLI entry point (613 lines) |
| `src/index.js` | Main exports |
| `src/errors.js` | Error classes |
| `src/validators.js` | Input validators |
| `src/rate-limiter.js` | Rate limiting |

## Commands

The CLI provides these commands:
- `search` - Search NCBI databases
- `fetch` - Fetch records by ID
- `summary` - Get database summaries
- `link` - Find linked records
- `info` - Get database info
- `config` - Configure settings
- `assembly` - Assembly database queries
- `gene-panorama` - Gene Panorama queries
- `variant` - Variant database queries
- `blast` - BLAST searches
- `sra` - SRA queries

## Development Guidelines

### Adding New Commands

1. Add command handler in `bin/cli.js`
2. Use `ncbi-client.js` methods for API calls
3. Follow existing error handling patterns

### Rate Limiting

- Default: 3 requests/second
- Configurable via CLI: `ncbi config set rateLimit <value>`

### Testing

```bash
# Test CLI
node bin/cli.js --help

# Test specific command
node bin/cli.js search -d pubmed -q "cancer"
```

### Publishing

```bash
npm version patch  # Bump version
npm publish        # Publish to npm
```

## Architecture

```
bin/cli.js
    └── src/ncbi-client.js
            ├── src/errors.js
            ├── src/validators.js
            └── src/rate-limiter.js
```

## Code Style Guidelines

### Import Order

Always order imports exactly as shown:
1. External libraries (axios)
2. Node.js built-in modules (node:xxx)
3. Local modules (../src/xxx)

```javascript
// ✅ Correct order
import axios from 'axios';
import { parseArgs } from 'node:util';
import { NCBIClient } from '../src/ncbi-client.js';
import { ValidationError } from '../src/errors.js';
```

### Naming Conventions

- **Variables/Functions**: camelCase
- **Classes**: PascalCase
- **Constants**: UPPER_SNAKE_CASE
- **Files**: kebab-case.js

```javascript
const maxRetries = 3;
const API_BASE_URL = 'https://eutils.ncbi.nlm.nih.gov';

function fetchRecord() { }
class NCBIClient { }
```

### Error Handling

Use the custom error hierarchy for all errors:

```javascript
import { 
  NCBIError, 
  ValidationError, 
  APIError, 
  NetworkError,
  TimeoutError,
  RateLimitError,
  AuthenticationError,
  parseNcbiError 
} from '../src/errors.js';

// Throw specific errors
if (!id) {
  throw new ValidationError('ID is required');
}

// Catch and wrap with parseNcbiError
try {
  const response = await axios.get(url);
} catch (error) {
  throw parseNcbiError(error);
}
```

### Validators

Simple functions with early returns - no try/catch:

```javascript
// ✅ Correct validator pattern
export function validateDatabase(db) {
  const VALID_DATABASES = ['pubmed', 'gene', 'protein', 'nucleotide'];
  if (!VALID_DATABASES.includes(db)) {
    throw new ValidationError(`Invalid database: ${db}`);
  }
  return db;
}

// ❌ Wrong - validators should not catch errors
export function validateDatabase(db) {
  try {
    // ... validation logic
  } catch (e) {
    // Don't do this in validators
  }
}
```

### JSDoc

Use JSDoc for public APIs (index.js):

```javascript
/**
 * Creates an NCBIClient instance
 * @param {Object} [options] - Configuration options
 * @param {string} [options.email] - User email for NCBI
 * @param {string} [options.apiKey] - NCBI API key
 * @param {number} [options.rateLimit=3] - Requests per second
 * @returns {NCBIClient} Configured client instance
 */
export function createClient(options) { }
```

### Formatting

- **Indentation**: 2 spaces
- **Semicolons**: None (use ASI)
- **Quotes**: Single quotes for strings
- **Commas**: Trailing commas

### Async/Await

Always use async/await over .then() chains:

```javascript
// ✅ Preferred
async function fetchData(id) {
  const result = await client.fetch(id);
  return result;
}

// ❌ Avoid
function fetchData(id) {
  return client.fetch(id).then(result => result);
}
```

### Rate Limiting

Use the built-in rate limiter for all NCBI API calls:

```javascript
import { RateLimiter } from '../src/rate-limiter.js';

const limiter = new RateLimiter(3); // 3 requests/second
await limiter.wait();
const response = await axios.get(url);
```

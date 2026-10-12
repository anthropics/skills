# Technical Patterns

Error handling, security considerations, and dependency documentation.

---

## Error Handling

### Error Handling Table

Document error scenarios and actions:

```markdown
## Error Handling

| Scenario | Detection | Action |
|----------|-----------|--------|
| Invalid input | Validation fails | Return error with specifics |
| File not found | FileNotFoundError | Clear message, suggest fix |
| Network failure | Timeout/ConnectionError | Retry 3x with backoff |
| Auth failure | 401/403 response | Prompt re-authentication |
| Unknown error | Catch-all exception | Log context, safe default |
```

### Retry Pattern

```python
import time
import random

def retry_with_backoff(func, max_retries=3, base_delay=0.1):
    """Retry with exponential backoff and jitter."""
    for attempt in range(max_retries):
        try:
            return func()
        except Exception as e:
            if attempt == max_retries - 1:
                raise
            delay = base_delay * (2 ** attempt) + random.uniform(0, 0.1)
            time.sleep(delay)
```

### Error Response Format

```typescript
// Consistent error response structure
interface ErrorResponse {
  isError: true;
  content: [{ type: 'text', text: string }];  // User-friendly message
  _meta?: {
    errorCode: string;      // Machine-readable code
    details: unknown;       // Debug info (not shown to user)
    retryable: boolean;     // Can user retry?
  };
}

// Example
return {
  isError: true,
  content: [{ type: 'text', text: 'Could not process file. Please check the format.' }],
  _meta: {
    errorCode: 'INVALID_FORMAT',
    details: { expected: 'PDF', received: 'PNG' },
    retryable: false
  }
};
```

### Graceful Degradation

```markdown
## Fallback Strategy

1. **Primary**: Execute main logic
2. **Retry**: On transient failure, retry with backoff
3. **Cache**: If available, serve cached result
4. **Fallback**: Return safe default or partial result
5. **Fail**: Clear error message with next steps
```

---

## Security Considerations

### Secrets Management

```markdown
## Secrets Handling

### Never Do
- Hardcode API keys, tokens, passwords in code
- Commit .env files to version control
- Log sensitive values
- Include secrets in error messages

### Always Do
- Use environment variables
- Keep .env in .gitignore
- Provide .env.example template
- Rotate compromised credentials immediately
```

### Input Validation

```markdown
## Input Validation

Validate ALL external input:

### File Paths
```python
import os

def safe_path(base_dir: str, user_path: str) -> str:
    """Prevent path traversal attacks."""
    full_path = os.path.normpath(os.path.join(base_dir, user_path))
    if not full_path.startswith(os.path.normpath(base_dir)):
        raise ValueError("Invalid path: traversal detected")
    return full_path
```

### User Input
```typescript
import { z } from 'zod';

const InputSchema = z.object({
  name: z.string().min(1).max(100),
  email: z.string().email(),
  count: z.number().int().positive().max(1000),
});

// Validate before use
const result = InputSchema.safeParse(userInput);
if (!result.success) {
  return { error: result.error.format() };
}
```

### SQL Queries
```python
# NEVER: String concatenation
query = f"SELECT * FROM users WHERE id = {user_id}"  # SQL injection!

# ALWAYS: Parameterized queries
cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
```
```

### Output Escaping

```markdown
## Output Escaping

Prevent XSS in generated content:

```typescript
function escapeHtml(text: string): string {
  const map: Record<string, string> = {
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    "'": '&#039;'
  };
  return text.replace(/[&<>"']/g, m => map[m]);
}

// Use when inserting user content into HTML
const safeContent = escapeHtml(userInput);
```
```

---

## Dependency Documentation

### Dependencies Section

```markdown
## Dependencies

### Required
- Python 3.10+ (for match statements)
- Node.js 18+ (for fetch API)
- TypeScript 5.0+ (for satisfies operator)

### Optional
- Redis 7+ (for caching, improves performance)
- Docker (for containerized deployment)

### External APIs
| API | Purpose | Rate Limit | Auth |
|-----|---------|------------|------|
| OpenAI | Embeddings | 3000/min | API key |
| GitHub | Repo access | 5000/hour | OAuth |

### System Requirements
- Memory: 512MB minimum, 2GB recommended
- Disk: 100MB for installation
- Network: Outbound HTTPS access
```

### Version Compatibility

```markdown
## Version Compatibility

| Component | Minimum | Recommended | Notes |
|-----------|---------|-------------|-------|
| Python | 3.10 | 3.11+ | Match statements required |
| Node.js | 18 | 20 LTS | Native fetch required |
| npm | 9 | 10 | Workspaces support |
```

### Installation Notes

```markdown
## Installation

### Prerequisites
```bash
# Verify versions
python --version  # 3.10+
node --version    # 18+
```

### Setup
```bash
# Install dependencies
pip install -r requirements.txt
npm install

# Configure environment
cp .env.example .env
# Edit .env with your values
```

### Verification
```bash
# Run tests to verify installation
pytest tests/
npm test
```
```

---

## Testing Guidance

### Script Testing

```markdown
## Testing Scripts

All scripts in `scripts/` must be tested before inclusion.

### Test Process
1. Run with sample input
2. Verify output matches expected
3. Test error cases (invalid input, missing files)
4. Check cleanup (no temp files left behind)

### Test Documentation
```bash
# scripts/extract_text.py
# Tested with:
# - Single page PDF ✓
# - Multi-page PDF ✓
# - Scanned PDF (OCR) ✓
# - Encrypted PDF → Returns clear error ✓
# - Non-PDF file → Returns clear error ✓
```
```

### Edge Cases

```markdown
## Common Edge Cases

Always handle:

| Category | Edge Cases |
|----------|------------|
| **Input** | Empty, null, undefined, very large |
| **Files** | Missing, locked, wrong format, empty |
| **Network** | Timeout, DNS failure, rate limited |
| **Data** | Unicode, special chars, injection attempts |
| **State** | Concurrent access, stale data, race conditions |
```

---

## Performance Considerations

### Timeout Protection

```typescript
async function withTimeout<T>(
  promise: Promise<T>,
  ms: number,
  message = 'Operation timed out'
): Promise<T> {
  const timeout = new Promise<never>((_, reject) =>
    setTimeout(() => reject(new Error(message)), ms)
  );
  return Promise.race([promise, timeout]);
}

// Usage
const result = await withTimeout(fetchData(), 5000);
```

### Resource Limits

```markdown
## Resource Limits

| Resource | Limit | Reason |
|----------|-------|--------|
| Request timeout | 25s | Platform limit |
| File size | 10MB | Memory constraints |
| Batch size | 100 items | API rate limits |
| Concurrent requests | 5 | Prevent overload |
```

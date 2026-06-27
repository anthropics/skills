# HTTP Error Codes Reference

This file documents HTTP error codes returned by the Claude API, their common causes, and how to handle them. For language-specific error handling examples, see the `python/` or `typescript/` folders.

## Error Code Summary

| Code | Error Type              | Retryable | Common Cause                         |
| ---- | ----------------------- | --------- | ------------------------------------ |
| 400  | `invalid_request_error` | No        | Invalid request format or parameters |
| 401  | `authentication_error`  | No        | Invalid or missing API key           |
| 403  | `permission_error`      | No        | API key lacks permission             |
| 404  | `not_found_error`       | No        | Invalid endpoint or model ID         |
| 413  | `request_too_large`     | No        | Request exceeds size limits          |
| 429  | `rate_limit_error`      | Yes       | Too many requests                    |
| 500  | `api_error`             | Yes       | Anthropic service issue              |
| 529  | `overloaded_error`      | Yes       | API is temporarily overloaded        |

## Detailed Error Information

### 400 Bad Request

**Causes:**

- Malformed JSON in request body
- Missing required parameters (`model`, `max_tokens`, `messages`)
- Invalid parameter types (e.g., string where integer expected)
- Empty messages array
- Messages not alternating user/assistant

**Example error:**

```json
{
  "type": "error",
  "error": {
    "type": "invalid_request_error",
    "message": "messages: roles must alternate between \"user\" and \"assistant\""
  },
  "request_id": "req_011CSHoEeqs5C35K2UUqR7Fy"
}
```

**Fix:** Validate request structure before sending. Check that:

- `model` is a valid model ID
- `max_tokens` is a positive integer
- `messages` array is non-empty and alternates correctly

---

### 401 Unauthorized

**Causes:**

- Missing `x-api-key` header or `Authorization` header
- Invalid API key format
- Revoked or deleted API key
- OAuth bearer token sent via `x-api-key` instead of `Authorization: Bearer`
- Both `ANTHROPIC_API_KEY` and `ANTHROPIC_AUTH_TOKEN` set — the SDK sends both headers and the API rejects the request

**Fix:** Set `ANTHROPIC_API_KEY`, or run `ant auth login` and leave the client constructor empty. For raw HTTP with an OAuth token, use `Authorization: Bearer <token>` (not `x-api-key:`).

---

### 403 Forbidden

**Causes:**

- API key doesn't have access to the requested model
- Organization-level restrictions
- Attempting to access beta features without beta access

**Fix:** Check your API key permissions in the Console. You may need a different API key or to request access to specific features.

---

### 404 Not Found

**Causes:**

- Typo in model ID (e.g., `claude-sonnet-4.6` instead of `claude-sonnet-4-6`)
- Using deprecated model ID
- Invalid API endpoint

**Fix:** Use exact model IDs from the models documentation. You can use aliases (e.g., `claude-opus-4-8`).

---

### 413 Request Too Large

**Causes:**

- Request body exceeds maximum size
- Too many tokens in input
- Image data too large

**Fix:** Reduce input size — truncate conversation history, compress/resize images, or split large documents into chunks.

---

### 400 Validation Errors

Some 400 errors are specifically related to parameter validation:

- `max_tokens` exceeds model's limit
- Invalid `temperature` value (must be 0.0-1.0)
- `budget_tokens` >= `max_tokens` in extended thinking
- Invalid tool definition schema

**Model-specific 400s on Fable 5 / Opus 4.8 / 4.7:**

- `temperature`, `top_p`, `top_k` are removed — sending any of them returns 400. Delete the parameter; see `shared/model-migration.md` → Per-SDK Syntax Reference.
- `thinking: {type: "enabled", budget_tokens: N}` is removed — sending it returns 400. Use `thinking: {type: "adaptive"}` instead.
- **Fable 5 only:** an explicit `thinking: {type: "disabled"}` returns 400 (it is accepted on Opus 4.8/4.7). Omit the `thinking` param entirely instead.
- **Fable 5 only:** if the organization is set to zero data retention (ZDR) — or any retention below the required 30 days — then **all** Fable 5 requests return `400 invalid_request_error`, even with a perfectly valid payload. Check the org's retention configuration before debugging the request body.

**Common mistake with extended thinking on older models (Opus 4.6 and earlier):**

```
# Wrong: budget_tokens must be < max_tokens
thinking: budget_tokens=10000, max_tokens=1000  → Error!

# Correct
thinking: budget_tokens=10000, max_tokens=16000
```

---

### 429 Rate Limited

**Causes:**

- Exceeded requests per minute (RPM)
- Exceeded tokens per minute (TPM)
- Exceeded tokens per day (TPD)

**Headers to check:**

- `retry-after`: Seconds to wait before retrying
- `x-ratelimit-limit-*`: Your limits
- `x-ratelimit-remaining-*`: Remaining quota

**Fix:** The Anthropic SDKs automatically retry 429 and 5xx errors with exponential backoff (default: `max_retries=2`). For custom retry behavior, see the language-specific error handling examples.

---

### 500 Internal Server Error

**Causes:**

- Temporary Anthropic service issue
- Bug in API processing

**Fix:** Retry with exponential backoff. If persistent, check [status.anthropic.com](https://status.anthropic.com).

---

### 529 Overloaded

**Causes:**

- High API demand
- Service capacity reached

**Fix:** Retry with exponential backoff. Consider using a different model (Haiku is often less loaded), spreading requests over time, or implementing request queuing.

---

## Common Mistakes and Fixes

| Mistake                         | Error            | Fix                                                     |
| ------------------------------- | ---------------- | ------------------------------------------------------- |
| `temperature`/`top_p`/`top_k` on Fable 5 / Opus 4.8 / 4.7 | 400 | Remove the parameter (see `shared/model-migration.md`)  |
| `budget_tokens` on Fable 5 / Opus 4.8 / 4.7 | 400  | Use `thinking: {type: "adaptive"}`                      |
| `thinking: {type: "disabled"}` on Fable 5 | 400    | Omit the `thinking` param entirely (accepted on Opus 4.8/4.7) |
| Org set to ZDR / retention below 30 days (Fable 5) | 400 on every request | Fix the org's data-retention configuration — the payload isn't the problem |
| `budget_tokens` >= `max_tokens` (older models) | 400 | Ensure `budget_tokens` < `max_tokens`                  |
| Typo in model ID                | 404              | Use valid model ID like `claude-opus-4-8`               |
| First message is `assistant`    | 400              | First message must be `user`                            |
| Consecutive same-role messages  | 400              | Alternate `user` and `assistant`                        |
| API key in code                 | 401 (leaked key) | Use environment variable                                |
| Custom retry needs              | 429/5xx          | SDK retries automatically; customize with `max_retries` |

## Typed Exceptions in SDKs

**Always use the SDK's typed exception classes** instead of checking error messages with string matching. Each HTTP status code maps to a specific exception class per SDK.

### Exception class names by language

| HTTP | Python (`anthropic.*`) / TypeScript (`Anthropic.*`) | Ruby (`Anthropic::Errors::*`) | Java (`com.anthropic.errors.*`) | C# | PHP (`Anthropic\Core\Exceptions\*`) |
|---|---|---|---|---|---|
| 400 | `BadRequestError` | `BadRequestError` | `BadRequestException` | `AnthropicBadRequestException` | `BadRequestException` |
| 401 | `AuthenticationError` | `AuthenticationError` | `UnauthorizedException` | `AnthropicUnauthorizedException` | `AuthenticationException` |
| 403 | `PermissionDeniedError` | `PermissionDeniedError` | `PermissionDeniedException` | `AnthropicForbiddenException` | `PermissionDeniedException` |
| 404 | `NotFoundError` | `NotFoundError` | `NotFoundException` | `AnthropicNotFoundException` | `NotFoundException` |
| 422 | `UnprocessableEntityError` | `UnprocessableEntityError` | `UnprocessableEntityException` | `AnthropicUnprocessableEntityException` | `UnprocessableEntityException` |
| 429 | `RateLimitError` | `RateLimitError` | `RateLimitException` | `AnthropicRateLimitException` | `RateLimitException` |
| ≥500 | `InternalServerError` | `InternalServerError` | `InternalServerException` | `Anthropic5xxException` | `InternalServerException` |
| net | `APIConnectionError` | `APIConnectionError` | `AnthropicIoException` | `AnthropicIOException` | `APIConnectionException` |
| base | `APIError` (both); `APIStatusError` (Python only) | `APIStatusError` / `APIError` | `AnthropicServiceException` | `AnthropicApiException` | `APIStatusException` / `APIException` |

The Ruby and PHP classes live in a dedicated errors namespace — write `Anthropic::Errors::RateLimitError` and `Anthropic\Core\Exceptions\RateLimitException` (not bare `Anthropic::RateLimitError`). All 4xx C# exceptions also inherit from `Anthropic4xxException`.

### Catch most-specific first, in a chain

Order `catch`/`except`/`rescue` clauses from the most specific subclass to the base class, with a separate clause for each category you handle differently — retryable (429, ≥500, network) vs. non-retryable (4xx). The SDK defines a distinct class per status for exactly this reason; a single broad catch-all discards that information.

```python
try:
    msg = client.messages.create(...)
except anthropic.NotFoundError as e:          # 404 — e.g. bad model ID
    ...
except anthropic.RateLimitError as e:         # 429 — back off and retry
    ...
except anthropic.APIStatusError as e:         # any other non-2xx HTTP response
    print(e.status_code, e.message)
except anthropic.APIConnectionError as e:     # network failure before a response
    ...
```

The same chain shape applies in every SDK: TypeScript `instanceof Anthropic.NotFoundError` → `RateLimitError` → `APIConnectionError` → `APIError` (check `APIConnectionError` before `APIError` — in the TypeScript SDK it's a subclass of `APIError`, unlike Python where it's a sibling); Ruby `rescue Anthropic::Errors::NotFoundError` → `…::RateLimitError` → `…::APIStatusError`; Java `catch (NotFoundException) … catch (RateLimitException) … catch (AnthropicServiceException)`; C# `catch (AnthropicNotFoundException) … catch (AnthropicRateLimitException) … catch (AnthropicApiException)`; PHP `catch (NotFoundException) … catch (RateLimitException) … catch (APIStatusException)`.

### Go — `errors.As` then branch on status

The Go SDK returns a single `*anthropic.Error` for all non-2xx responses. Unwrap it with `errors.As`, then branch on `StatusCode`:

```go
_, err := client.Messages.New(ctx, params)
if err != nil {
    var apierr *anthropic.Error
    if errors.As(err, &apierr) {
        switch apierr.StatusCode {
        case 404:
            // bad model ID / resource
        case 429:
            // back off and retry
        default:
            // other API error — apierr.StatusCode, apierr.RequestID
        }
    } else {
        // transport-level error (*url.Error wrapping *net.OpError, etc.)
    }
}
```

### Error `.type` Field

All `APIStatusError` subclasses now expose a `.type` property (Python: `.type`, TypeScript: `.type`, Java: `.errorType()`, Go: `.Type()`, Ruby: `.type`, PHP: `.type`) that returns the API error type string (e.g., `"invalid_request_error"`, `"authentication_error"`, `"rate_limit_error"`, `"overloaded_error"`). Use this for programmatic error classification when you need finer granularity than the HTTP status code — for example, distinguishing `"billing_error"` from `"permission_error"` (both map to 403).

```python
except anthropic.APIStatusError as e:
    if e.type == "rate_limit_error":
        # handle rate limiting
    elif e.type == "overloaded_error":
        # handle overload
```

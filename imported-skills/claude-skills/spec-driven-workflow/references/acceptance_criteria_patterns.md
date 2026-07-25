# Acceptance Criteria Patterns

A pattern library for writing Given/When/Then acceptance criteria across common feature types. Use these as starting points — adapt to your domain.

---

## Pattern Structure

Every acceptance criterion follows this structure:

```
### AC-N: [Descriptive name] (FR-N, NFR-N)
Given [precondition — the system/user is in this state]
When  [trigger — the user or system performs this action]
Then  [outcome — this observable, testable result occurs]
And   [additional outcome — and this also happens]
```

**Rules:**
1. One scenario per AC. Multiple Given/When/Then blocks = multiple ACs.
2. Every AC references at least one FR-* or NFR-*.
3. Outcomes must be observable and testable — no subjective language.
4. Preconditions must be achievable in a test setup.

---

## Authentication Patterns

### Login — Happy Path

```markdown
### AC-1: Successful login with valid credentials (FR-1)
Given a registered user with email "user@example.com" and password "V@lidP4ss!"
When they POST /api/auth/login with email "user@example.com" and password "V@lidP4ss!"
Then the response status is 200
And the response body contains a valid JWT access token
And the response body contains a refresh token
And the access token expires in 24 hours
```

### Login — Invalid Credentials

```markdown
### AC-2: Login rejected with wrong password (FR-1)
Given a registered user with email "user@example.com"
When they POST /api/auth/login with email "user@example.com" and an incorrect password
Then the response status is 401
And the response body contains error code "INVALID_CREDENTIALS"
And no token is issued
And the failed attempt is logged
```

### Login — Account Locked

```markdown
### AC-3: Login rejected for locked account (FR-1, NFR-S2)
Given a user whose account is locked due to 5 consecutive failed login attempts
When they POST /api/auth/login with correct credentials
Then the response status is 403
And the response body contains error code "ACCOUNT_LOCKED"
And the response includes a "retryAfter" field with seconds until unlock
```

### Token Refresh

```markdown
### AC-4: Token refresh with valid refresh token (FR-3)
Given a user with a valid, non-expired refresh token
When they POST /api/auth/refresh with that refresh token
Then the response status is 200
And a new access token is issued
And the old refresh token is invalidated
And a new refresh token is issued (rotation)
```

### Logout

```markdown
### AC-5: Logout invalidates session (FR-4)
Given an authenticated user with a valid access token
When they POST /api/auth/logout with that token
Then the response status is 204
And the access token is no longer accepted for API calls
And the refresh token is invalidated
```

---

## CRUD Patterns

### Create

```markdown
### AC-6: Create resource with valid data (FR-1)
Given an authenticated user with "editor" role
When they POST /api/resources with valid payload {name: "Test", type: "A"}
Then the response status is 201
And the response body contains the created resource with a generated UUID
And the resource's "createdAt" field is set to the current UTC timestamp
And the resource's "createdBy" field matches the authenticated user's ID
```

### Create — Validation Failure

```markdown
### AC-7: Create resource rejected with invalid data (FR-1)
Given an authenticated user
When they POST /api/resources with payload missing required field "name"
Then the response status is 400
And the response body contains error code "VALIDATION_ERROR"
And the response body contains field-level detail: {"name": "Required field"}
And no resource is created in the database
```

### Read — Single Item

```markdown
### AC-8: Read resource by ID (FR-2)
Given an existing resource with ID "abc-123"
When an authenticated user GETs /api/resources/abc-123
Then the response status is 200
And the response body contains the resource with all fields
```

### Read — Not Found

```markdown
### AC-9: Read non-existent resource returns 404 (FR-2)
Given no resource exists with ID "nonexistent-id"
When an authenticated user GETs /api/resources/nonexistent-id
Then the response status is 404
And the response body contains error code "NOT_FOUND"
```

### Update

```markdown
### AC-10: Update resource with valid data (FR-3)
Given an existing resource with ID "abc-123" owned by the authenticated user
When they PATCH /api/resources/abc-123 with {name: "Updated Name"}
Then the response status is 200
And the resource's "name" field is "Updated Name"
And the resource's "updatedAt" field is updated to the current UTC timestamp
And fields not included in the patch are unchanged
```

### Update — Ownership Check

```markdown
### AC-11: Update rejected for non-owner (FR-3, FR-6)
Given an existing resource with ID "abc-123" owned by user "other-user"
When the authenticated user (not "other-user") PATCHes /api/resources/abc-123
Then the response status is 403
And the response body contains error code "FORBIDDEN"
And the resource is unchanged
```

### Delete — Soft Delete

```markdown
### AC-12: Soft delete resource (FR-5)
Given an existing resource with ID "abc-123" owned by the authenticated user
When they DELETE /api/resources/abc-123
Then the response status is 204
And the resource's "deletedAt" field is set to the current UTC timestamp
And the resource no longer appears in GET /api/resources (list endpoint)
And the resource still exists in the database (soft deleted)
```

### List — Pagination

```markdown
### AC-13: List resources with default pagination (FR-4)
Given 50 resources exist for the authenticated user
When they GET /api/resources without pagination parameters
Then the response status is 200
And the response contains the first 20 resources (default page size)
And the response includes "totalCount: 50"
And the response includes "page: 1"
And the response includes "pageSize: 20"
And the response includes "hasNextPage: true"
```

### List — Filtered

```markdown
### AC-14: List resources with type filter (FR-4)
Given 30 resources of type "A" and 20 resources of type "B" exist
When the authenticated user GETs /api/resources?type=A
Then the response status is 200
And all returned resources have type "A"
And the response "totalCount" is 30
```

---

## Search Patterns

### Basic Search

```markdown
### AC-15: Search returns matching results (FR-7)
Given resources with names "Alpha Report", "Beta Analysis", "Alpha Summary" exist
When the user GETs /api/resources?q=Alpha
Then the response contains "Alpha Report" and "Alpha Summary"
And the response does not contain "Beta Analysis"
And results are ordered by relevance score (descending)
```

### Search — Empty Results

```markdown
### AC-16: Search with no matches returns empty list (FR-7)
Given no resources match the query "xyznonexistent"
When the user GETs /api/resources?q=xyznonexistent
Then the response status is 200
And the response contains an empty "items" array
And "totalCount" is 0
```

### Search — Special Characters

```markdown
### AC-17: Search handles special characters safely (FR-7, NFR-S1)
Given resources exist in the database
When the user GETs /api/resources?q="; DROP TABLE resources;--
Then the response status is 200
And no SQL injection occurs
And the search treats the input as a literal string
```

---

## File Upload Patterns

### Upload — Happy Path

```markdown
### AC-18: Upload file within size limit (FR-8)
Given an authenticated user
When they POST /api/files with a 5MB PNG file
Then the response status is 201
And the response contains the file's URL, size, and MIME type
And the file is stored in the configured storage backend
And the file is associated with the authenticated user
```

### Upload — Size Exceeded

```markdown
### AC-19: Upload rejected for oversized file (FR-8)
Given the maximum file size is 10MB
When the user POSTs /api/files with a 15MB file
Then the response status is 413
And the response contains error code "FILE_TOO_LARGE"
And no file is stored
```

### Upload — Invalid Type

```markdown
### AC-20: Upload rejected for disallowed file type (FR-8, NFR-S3)
Given allowed file types are PNG, JPG, PDF
When the user POSTs /api/files with an .exe file
Then the response status is 415
And the response contains error code "UNSUPPORTED_MEDIA_TYPE"
And no file is stored
```

---

## Payment Patterns

### Charge — Happy Path

```markdown
### AC-21: Successful payment charge (FR-10)
Given a user with a valid payment method on file
When they POST /api/payments with amount 49.99 and currency "USD"
Then the payment gateway is charged $49.99
And the response status is 201
And the response contains a transaction ID
And a payment record is created with status "completed"
And a receipt email is sent to the user
```

### Charge — Declined

```markdown
### AC-22: Payment declined by gateway (FR-10)
Given a user with an expired credit card on file
When they POST /api/payments with amount 49.99
Then the payment gateway returns a decline
And the response status is 402
And the response contains error code "PAYMENT_DECLINED"
And no payment record is created with status "completed"
And the user is prompted to update their payment method
```

### Charge — Idempotency

```markdown
### AC-23: Duplicate payment request is idempotent (FR-10, NFR-R1)
Given a payment was successfully processed with idempotency key "key-123"
When the same request is sent again with idempotency key "key-123"
Then the response status is 200
And the response contains the original transaction ID
And the user is NOT charged a second time
```

---

## Notification Patterns

### Email Notification

```markdown
### AC-24: Email notification sent on event (FR-11)
Given a user with notification preferences set to "email"
When their order status changes to "shipped"
Then an email is sent to their registered email address
And the email subject contains the order number
And the email body contains the tracking URL
And a notification record is created with status "sent"
```

### Notification — Delivery Failure

```markdown
### AC-25: Failed notification is retried (FR-11, NFR-R2)
Given the email service returns a 5xx error on first attempt
When a notification is triggered
Then the system retries up to 3 times with exponential backoff (1s, 4s, 16s)
And if all retries fail, the notification status is set to "failed"
And an alert is sent to the ops channel
```

---

## Negative Test Patterns

### Unauthorized Access

```markdown
### AC-26: Unauthenticated request rejected (NFR-S1)
Given no authentication token is provided
When the user GETs /api/resources
Then the response status is 401
And the response contains error code "AUTHENTICATION_REQUIRED"
And no resource data is returned
```

### Invalid Input — Type Mismatch

```markdown
### AC-27: String provided for numeric field (FR-1)
Given the "quantity" field expects an integer
When the user POSTs with quantity: "abc"
Then the response status is 400
And the response body contains field error: {"quantity": "Must be an integer"}
```

### Rate Limiting

```markdown
### AC-28: Rate limit enforced (NFR-S2)
Given the rate limit is 100 requests per minute per API key
When the user sends the 101st request within 60 seconds
Then the response status is 429
And the response includes header "Retry-After" with seconds until reset
And the response contains error code "RATE_LIMITED"
```

### Concurrent Modification

```markdown
### AC-29: Optimistic locking prevents lost updates (NFR-R1)
Given a resource with version 5
When user A PATCHes with version 5 and user B PATCHes with version 5 simultaneously
Then one succeeds with status 200 (version becomes 6)
And the other receives status 409 with error code "CONFLICT"
And the 409 response includes the current version number
```

---

## Performance Criteria Patterns

### Response Time

```markdown
### AC-30: API response time under load (NFR-P1)
Given the system is handling 1,000 concurrent users
When a user GETs /api/dashboard
Then the response is returned in < 500ms (p95)
And the response is returned in < 1000ms (p99)
```

### Throughput

```markdown
### AC-31: System handles target throughput (NFR-P2)
Given normal production traffic patterns
When the system receives 5,000 requests per second
Then all requests are processed without queue overflow
And error rate remains below 0.1%
```

### Resource Usage

```markdown
### AC-32: Memory usage within bounds (NFR-P3)
Given the service is processing normal traffic
When measured over a 24-hour period
Then memory usage does not exceed 512MB RSS
And no memory leaks are detected (RSS growth < 5% over 24h)
```

---

## Accessibility Criteria Patterns

### Keyboard Navigation

```markdown
### AC-33: Form is fully keyboard navigable (NFR-A1)
Given the user is on the login page using only a keyboard
When they press Tab
Then focus moves through: email field -> password field -> submit button
And each focused element has a visible focus indicator
And pressing Enter on the submit button submits the form
```

### Screen Reader

```markdown
### AC-34: Error messages announced to screen readers (NFR-A2)
Given the user submits the form with invalid data
When validation errors appear
Then each error is associated with its form field via aria-describedby
And the error container has role="alert" for immediate announcement
And the first error field receives focus
```

### Color Contrast

```markdown
### AC-35: Text meets contrast requirements (NFR-A3)
Given the default theme is active
When measuring text against background colors
Then all body text meets 4.5:1 contrast ratio (WCAG AA)
And all large text (18px+ or 14px+ bold) meets 3:1 contrast ratio
And all interactive element states (hover, focus, active) meet 3:1
```

### Reduced Motion

```markdown
### AC-36: Animations respect user preference (NFR-A4)
Given the user has enabled "prefers-reduced-motion" in their OS settings
When they load any page with animations
Then all non-essential animations are disabled
And essential animations (e.g., loading spinner) use a reduced version
And no content is hidden behind animation-only interactions
```

---

## Writing Tips

### Do

- Start Given with the system/user state, not the action
- Make When a single, specific trigger
- Make Then observable — status codes, field values, side effects
- Include And for additional assertions on the same outcome
- Reference requirement IDs in the AC title

### Do Not

- Write "Then the system works correctly" (not testable)
- Combine multiple scenarios in one AC
- Use subjective words: "quickly", "properly", "nicely", "user-friendly"
- Skip the precondition — Given is required even if it seems obvious
- Write Given/When/Then as prose paragraphs — use the structured format

### Smell Tests

If your AC has any of these, rewrite it:

| Smell | Example | Fix |
|-------|---------|-----|
| No Given clause | "When user clicks, then page loads" | Add "Given user is on the dashboard" |
| Vague Then | "Then it works" | Specify status code, body, side effects |
| Multiple Whens | "When user clicks A and then clicks B" | Split into two ACs |
| Implementation detail | "Then the Redux store is updated" | Focus on user-observable outcome |
| No requirement reference | "AC-5: Dashboard loads" | "AC-5: Dashboard loads (FR-7)" |

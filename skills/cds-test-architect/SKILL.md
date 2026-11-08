---
name: cds-test-architect
description: Unit and integration testing for the CAP backend using cds.test() from Capire. Use when the user asks for backend tests, writes a *.test.js under test/, mentions cds.test, @cap-js/cds-test, supertest-style HTTP tests for OData/actions, or wants a regression test for a CAP handler, action, or payroll/core/platform service.
---

# Unit Testing the CDS Backend

## When this fires

Triggered for code under `srv/services/**` (pay, core, platform) and `srv/handlers/**`. **Not** for Playwright UI tests under `app-core/e2e/` or `app-pay/e2e/` — those have their own runners. Always co-locate backend tests under `test/<module>/<service>.test.js`, mirroring `srv/services/<module>/<service>.cds`. Tests must never live under `srv/` — that directory ships to deployments.

## Philosophy

Test through public interfaces — OData endpoints or `cds.connect.to(<Service>)` — never by reaching into handler internals or stubbing `cds.db`. Capire's mantra applies: *"The more you mock, the less you test the real thing."* A test that breaks on a rename without behavior change is a bad test.

Real Postgres, real `cds.test()` bootstrap, real handlers. Reset DB state between tests, don't fake it.

## First-run setup (once per repo)

Before adding the first test, run this checklist. Stop and ask the user before editing `package.json`.

- [ ] Install the test helper: `npm i -D @cap-js/cds-test`
- [ ] Add to [package.json](../../../package.json) `scripts`: `"test": "cds test"`
- [ ] Add mocked users under `cds.requires.auth` (test + development profiles):
  ```json
  "auth": {
    "[development]": { "kind": "mocked" },
    "[test]": {
      "kind": "mocked",
      "users": {
        "alice": { "roles": ["admin", "payroll.approver"] },
        "bob":   { "roles": ["viewer"] }
      }
    }
  }
  ```
- [ ] Create `test/` at repo root (sibling of `srv/`, `db/`, `app-core/`).
- [ ] Confirm Postgres test DB is reachable on the active profile — the skill does **not** auto-configure a `pg-test` profile.
- [ ] Add `CDS_TEST_ENV_CHECK=y` to your test environment (`.env.test` or the `test` script in `package.json`). This causes `cds.test` to error if `cds.env` is accessed before `cds.test()` runs, which prevents plugins from loading from the wrong folder.

## Canonical test file

Every backend test file follows this shape:

```js
const cds = require('@sap/cds')
const { GET, POST, expect, data } = cds.test(__dirname + '/../..')

describe('<ServiceName> — <happy path concern>', () => {
  beforeEach(() => data.reset())

  it('lists <Entity> for an authenticated user', async () => {
    const { data: body, status } = await GET('/odata/v4/<service>/<Entity>', {
      auth: { username: 'alice' },
    })
    expect(status).to.equal(200)
    expect(body.value).to.containSubset([{ /* essential fields only */ }])
  })
})
```

`cds.test()` is called **once at file scope** — never inside `describe` or `beforeAll`. The path argument anchors `cds.root` at the repo so the same `db/` and `srv/services/` are picked up.

### Selective service boot

When a test file covers exactly one service, pass the service name to avoid booting unrelated services and reduce startup time:

```js
const { GET, POST, expect, data } = cds.test('serve', 'PayrollLoansService').in(__dirname + '/../..')
```

Use `.in()` fluently after the service name so `cds.root` is still anchored correctly.

## File-wide defaults

Use the `defaults` object to set auth, headers, or `validateStatus` once for the whole file instead of repeating them on every request. Per-request options override `defaults`.

```js
const { GET, POST, expect, data, defaults } = cds.test(__dirname + '/../..')
defaults.auth = { username: 'alice' }  // all requests run as alice unless overridden

// override for the one test that needs a different user
const res = await GET('/odata/v4/payroll-loans/Loans', { auth: { username: 'bob' } })
```

Supported `defaults` keys: `auth`, `headers`, `baseURL`, `validateStatus`.

## Error responses (4xx / 5xx)

`cds.test` throws by default when a response has a 4xx or 5xx status, so a bare `await POST(...)` will throw before you can assert the body. Use `validateStatus: () => true` to receive the error response instead of throwing:

```js
const res = await POST(
  '/odata/v4/payroll-loans/Loans',
  { principal: -1 },
  { auth: { username: 'alice' }, validateStatus: () => true },
)
// assert payload first — it tells you why the error happened
expect(res.data).to.containSubset({ error: { code: 'INVALID_PRINCIPAL' } })
expect(res.status).to.equal(400)
```

Always assert `error.code`, never `error.message` — messages are translated and can change; codes are stable contract.

## Log capture

Use `cds.test.log()` to assert that handlers emit specific warnings or info messages (e.g. `req.warn`, `req.info`, structured audit entries) without writing a separate DB assertion.

```js
describe('PayrollLoansService — ceiling warning', () => {
  let log
  beforeAll(() => { log = cds.test.log() })
  afterAll(() => log.release())
  beforeEach(() => { log.clear(); return data.reset() })

  it('warns when loan exceeds ceiling', async () => {
    await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-001', principal: 999999, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    expect(log.output).to.contain('CEILING_EXCEEDED')
  })
})
```

`log.output` is a plain string of everything written to stdout/stderr since the last `log.clear()`. `log.release()` stops capturing and restores normal output.

## `data.reset()` semantics

`data.reset()` drops and re-deploys the full database schema, then re-seeds from `db/data/` CSV fixtures. Every test therefore starts from a known, identical baseline. Call it in `beforeEach` — not `afterEach` — so failures leave the DB in the broken state for debugging.

If a test creates records it needs to reference by ID (e.g. a seeded approval for an action test), seed those IDs in your CSV fixtures under `db/data/` rather than creating them inside the test — fixture IDs are stable across resets; `POST`-created IDs are not.

## Test patterns

| Pattern | When | Example |
| --- | --- | --- |
| OData CRUD (GET/POST) | Validating a service entity is reachable and obeys auth | See [EXAMPLES.md](EXAMPLES.md#1-odata-crud) |
| OData update/delete (PATCH/DELETE) | Testing write handlers, cascade deletes, optimistic lock | See [EXAMPLES.md](EXAMPLES.md#4-patch-and-delete) |
| Custom action | Testing bound/unbound actions like `approveApproval`, `runPayrollCycle` | See [EXAMPLES.md](EXAMPLES.md#2-custom-action) |
| Error response (4xx) | Asserting validation, auth rejection, or business-rule errors | See [EXAMPLES.md](EXAMPLES.md#5-error-response) |
| Programmatic service | Driving a service without HTTP — best for handler unit logic | See [EXAMPLES.md](EXAMPLES.md#3-programmatic-service) |
| Log capture | Asserting `req.warn` / `req.info` emitted by a handler | See [EXAMPLES.md](EXAMPLES.md#6-log-capture) |

## Anti-patterns

- **Do not** mock `cds.db`, `srv/handlers/**/lib/*`, the SF client, or `bullmq` queues. If you need to skip a side effect, use a feature flag in the handler, not a test mock.
- **Do not** call `cds.test()` more than once per file — it boots a server and leaks state.
- **Do not** use `process.chdir()`; if you need a different root, use `cds.test.in(__dirname)`.
- **Do not** use `deep.equal` on full responses — IDs and `createdAt`/`modifiedAt` will fight you. Use `containSubset` and assert only the fields the test is *about*.
- **Do not** assert HTTP status before payload — when a 500 comes back, the payload tells you why; the status alone hides the bug.
- **Do not** assert `error.message` — assert `error.code`. Messages are translated and unstable; codes are contract.
- **Do not** assert 4xx/5xx responses without `validateStatus: () => true` — `cds.test` throws on error responses by default, so the assertion is never reached.
- **Do not** use `personIdExternal` and `userId` interchangeably — per [CLAUDE.md](../../../CLAUDE.md), `personIdExternal` is the FK; `userId` is audit-only and unstable across rehires.
- **Do not** put tests under `srv/`, `db/`, or `app-*/`.
- **Do not** use `before()` (Mocha-only) — use `beforeAll()` which works across runners.

## Checklist per test

- [ ] File at `test/<module>/<service>.test.js`, mirroring `srv/services/<module>/<service>.cds`
- [ ] `cds.test()` called once at file scope
- [ ] `data.reset()` (or explicit fixture) in `beforeEach`
- [ ] Auth via `auth: { username }` against a user defined in the `[test]` mocked profile
- [ ] `validateStatus: () => true` on any request expected to return 4xx/5xx
- [ ] Asserts observable behavior — OData response, service API return value, or audit-log row — never handler internals
- [ ] Uses `containSubset`, not `deep.equal`, for response bodies
- [ ] Asserts `error.code`, not `error.message`, for error cases
- [ ] No mocks for `cds.db`, SF client, or queues

## Verification

`npm test` invokes `cds test`, which runs Node's built-in `--test`. The boot-time schema-drift warner in [srv/server.js](../../../srv/server.js) is gated on `NODE_ENV !== 'test'`, so test boots stay quiet.

To smoke-test a new test file:

```
npm test -- test/pay/payroll-loans.test.js
```

If the test fails with `ECONNREFUSED` on Postgres, the test DB is not reachable — fix the profile, not the test.

If the test fails with `cds.env loaded before cds.test()`, ensure `cds.test()` is the first `cds` call in the file and that no top-level module import triggers `cds.env` as a side effect.

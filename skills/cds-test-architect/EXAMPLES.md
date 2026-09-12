# Examples — CDS Backend Tests

Six runnable templates. Adapt the entity, service, and field names; keep the structure.

## 1. OData CRUD

Happy-path read + create against `srv/services/pay/payroll-loans.cds`. Asserts the OData layer is wired and audit fields are populated by the service.

```js
// test/pay/payroll-loans.test.js
const cds = require('@sap/cds')
const { GET, POST, expect, data } = cds.test(__dirname + '/../..')

describe('PayrollLoans — OData CRUD', () => {
  beforeEach(() => data.reset())

  it('lists loans for an authenticated user', async () => {
    const { data: body, status } = await GET('/odata/v4/payroll-loans/Loans', {
      auth: { username: 'alice' },
    })
    expect(status).to.equal(200)
    expect(body.value).to.be.an('array') // we don't pin row count — fixtures drift
  })

  it('creates a loan and stamps audit fields', async () => {
    const { data: created, status } = await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-001', principal: 1000, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    expect(status).to.equal(201)
    // assert only what this test is about — the createdBy stamp
    expect(created).to.containSubset({ createdBy: 'alice', principal: 1000 })
  })
})
```

## 2. Custom action

Bound action with auth gating. Two users, one allowed, one denied — asserts the role check, not the action body.

```js
// test/pay/payroll-cycle-approvals.test.js
const cds = require('@sap/cds')
const { POST, expect, data } = cds.test(__dirname + '/../..')

describe('PayrollCycleApprovals — approveApproval action', () => {
  beforeEach(() => data.reset())

  it('admin can approve a pending approval', async () => {
    const { status, data: body } = await POST(
      `/odata/v4/payroll-cycle-approvals/Approvals(<seeded-id>)/PayrollCycleApprovalService.approveApproval`,
      {},
      { auth: { username: 'alice' } },
    )
    expect(body).to.containSubset({ status: 'APPROVED' }) // payload first
    expect(status).to.equal(200)                          // status second
  })

  it('viewer is rejected with 403', async () => {
    const res = await POST(
      `/odata/v4/payroll-cycle-approvals/Approvals(<seeded-id>)/PayrollCycleApprovalService.approveApproval`,
      {},
      { auth: { username: 'bob' }, validateStatus: () => true }, // don't throw on 4xx
    )
    expect(res.status).to.equal(403)
  })
})
```

`validateStatus: () => true` is the escape hatch for asserting error responses — without it `cds.test` throws before the `expect` is reached.

## 3. Programmatic service

No HTTP — talk to the service through `cds.connect.to`. Best for verifying handler logic that has no external surface (e.g. an internal event handler).

```js
// test/core/employee-records-service.test.js
const cds = require('@sap/cds')
const { expect, data } = cds.test(__dirname + '/../..')

describe('EmployeeRecordsService — programmatic', () => {
  let EmployeeRecords
  beforeAll(async () => {   // beforeAll, not before() — works across runners
    EmployeeRecords = await cds.connect.to('EmployeeRecordsService')
  })
  beforeEach(() => data.reset())

  it('returns records keyed by personIdExternal, never userId', async () => {
    const { Employees } = EmployeeRecords.entities
    const rows = await SELECT.from(Employees).limit(1)
    expect(rows[0]).to.have.property('personIdExternal') // SF PK rule from CLAUDE.md
    expect(rows[0]).to.not.have.property('userId')       // userId is audit-only
  })
})
```

Programmatic tests skip the protocol layer, so they're faster and surface handler errors directly. Reach for them when the OData round-trip adds nothing to the assertion.

## 4. PATCH and DELETE

PATCH an entity and assert the `modifiedBy` stamp; DELETE and assert the record is gone.

```js
// test/pay/payroll-loans.test.js  (extend the same file as example 1)
const cds = require('@sap/cds')
const { GET, POST, PATCH, DELETE, expect, data } = cds.test(__dirname + '/../..')

describe('PayrollLoans — updates and deletes', () => {
  beforeEach(() => data.reset())

  it('patches a loan principal and stamps modifiedBy', async () => {
    // create first so we have a stable ID within this test
    const { data: created } = await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-002', principal: 500, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    const id = created.ID

    const { data: patched, status } = await PATCH(
      `/odata/v4/payroll-loans/Loans(${id})`,
      { principal: 750 },
      { auth: { username: 'alice' } },
    )
    expect(patched).to.containSubset({ principal: 750, modifiedBy: 'alice' })
    expect(status).to.equal(200)
  })

  it('deletes a loan and returns 204', async () => {
    const { data: created } = await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-003', principal: 200, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    const id = created.ID

    const { status } = await DELETE(
      `/odata/v4/payroll-loans/Loans(${id})`,
      { auth: { username: 'alice' } },
    )
    expect(status).to.equal(204)

    // confirm the record is gone
    const { data: body } = await GET(
      `/odata/v4/payroll-loans/Loans(${id})`,
      { auth: { username: 'alice' }, validateStatus: () => true },
    )
    expect(body).to.containSubset({ error: { code: '404' } })
  })
})
```

## 5. Error response (4xx)

Assert validation errors, business-rule rejections, and auth failures. Use `validateStatus: () => true` so `cds.test` does not throw. Assert `error.code`, not `error.message` — codes are stable contract; messages are translated.

```js
// test/pay/payroll-loans.test.js
const cds = require('@sap/cds')
const { POST, expect, data } = cds.test(__dirname + '/../..')

describe('PayrollLoans — validation errors', () => {
  beforeEach(() => data.reset())

  it('rejects a negative principal with 400 and a stable error code', async () => {
    const res = await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-001', principal: -1, currency: 'EGP' },
      { auth: { username: 'alice' }, validateStatus: () => true },
    )
    // payload first — tells you *why* on failure
    expect(res.data).to.containSubset({ error: { code: 'INVALID_PRINCIPAL' } })
    expect(res.status).to.equal(400)
  })

  it('rejects unauthenticated requests with 401', async () => {
    const res = await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-001', principal: 100, currency: 'EGP' },
      { validateStatus: () => true }, // no auth
    )
    expect(res.status).to.equal(401)
  })
})
```

## 6. Log capture

Assert that a handler emits specific warnings or info entries (via `req.warn`, `req.info`) without needing a separate DB assertion. Useful for verifying business rules that warn but do not reject.

```js
// test/pay/payroll-loans.test.js
const cds = require('@sap/cds')
const { POST, expect, data } = cds.test(__dirname + '/../..')

describe('PayrollLoans — ceiling warning', () => {
  let log
  beforeAll(() => { log = cds.test.log() })
  afterAll(() => log.release())          // restore normal output after the suite
  beforeEach(() => { log.clear(); return data.reset() })

  it('warns when loan principal exceeds the ceiling', async () => {
    await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-001', principal: 999999, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    // check log output contains the warning code emitted by the handler
    expect(log.output).to.contain('CEILING_EXCEEDED')
  })

  it('does not warn for a normal loan', async () => {
    await POST(
      '/odata/v4/payroll-loans/Loans',
      { personIdExternal: 'EXT-002', principal: 500, currency: 'EGP' },
      { auth: { username: 'alice' } },
    )
    expect(log.output).to.not.contain('CEILING_EXCEEDED')
  })
})
```

`log.output` is a plain string of all stdout/stderr since the last `log.clear()`. Call `log.release()` in `afterAll` to stop capturing and restore normal console output for subsequent test files.

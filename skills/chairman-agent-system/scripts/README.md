# chairman — enforced agent governance

A dependency-free Python package that turns the governance rules in
`../SKILL.md` into code that actually runs. No install step, stdlib only.
Test suite verified against CPython 3.10, 3.11, 3.12 and 3.13; earlier
versions are untested rather than known-broken.

```bash
cd skills/chairman-agent-system/scripts
python3 -m unittest discover -s tests -t .     # 112 tests
python3 -m chairman --db org.db init
```

## What it enforces

**Agents exist only through an approved proposal.** `request_agent()`
refuses any proposal missing purpose, objectives, reporting cadence, or
risks — and records the refusal. The proposal sits in `PENDING` until an
agent with approval authority signs it. Filing a proposal creates nothing.

**Authority narrows going down.** A parent cannot give a child a level at
or above its own, a tool it does not hold, or a clearance above its own.
This is the invariant that stops delegation becoming a privilege-escalation
path: without it, a constrained agent could mint a stronger child and act
through it.

**Conditions are re-checked at approval time.** A proposal filed while the
parent was healthy is re-validated when someone approves it. If the parent
was suspended or filled its report slots in between, approval fails.

**Every decision is logged, including denials.** Each audit record commits
to a SHA-256 hash of the previous one, so altering or deleting any entry
invalidates every hash after it. `verify` reports the first break.

**Termination cascades.** Killing an agent kills its whole subtree — an
orphaned sub-agent would otherwise keep authority its parent granted with
nobody accountable for it.

**Tools cannot be called without authorization.** An agent holds a
`Session`, not callables, and registered functions refuse when invoked
outside an authorized `session.invoke`. See below.

## The enforcement point

A permission check that code can skip by not calling it holds only by
convention. `chairman.enforcement` closes that from both ends: agents get a
`Session` bound to their identity, and `ToolBox.register` wraps the function
so the direct-call path is protected too.

```python
box = ToolBox()

@box.register("ledger.balance", Tool.FINANCE, Classification.CONFIDENTIAL)
def balance(account: str) -> float:
    ...

session = Session(registry, box, "ledger-analyst")
session.invoke("ledger.balance", "ACME")   # authorized, runs
balance("ACME")                            # PermissionDenied
```

The guard is a `contextvars.ContextVar` set only by `invoke` and released in
a `finally`, so it survives handler exceptions and does not leak across
threads or asyncio tasks. It authorizes one name at a time: a tool that
calls another tool must go through `invoke` for the inner one, so crossing a
tool boundary always costs an authorization rather than inheriting the
caller's clearance.

`writes=True` marks a tool as requiring level 3+. Classification may be a
callable instead of a constant when sensitivity depends on the arguments —
`read_file("/public/x")` and `read_file("/payroll/y")` are not the same
request, and pinning the tool to its worst case would either over-refuse or
under-protect.

Two audit entries land per call, because they are different facts: the
permission decision, and the execution outcome. A call can be permitted and
still fail, and `outcome="error"` is not `outcome="denied"`.

`session.available()` lists what the agent may call — useful for building
the tool list you hand a model.

## A real toolkit

`chairman.toolkit` registers filesystem and repository tools that do actual
work, so the refusals are real refusals rather than a demonstration.

```python
box = build_repo_toolkit(Path("/srv/project"))
session = Session(registry, box, "reviewer")
session.invoke("fs.read", "README.md")          # PUBLIC, permitted
session.invoke("fs.read", ".env")               # RESTRICTED, refused
session.invoke("fs.read", "../../etc/passwd")   # refused: outside the root
```

Two controls run before any handler:

**Paths are confined to a root.** `..` traversal, absolute paths outside the
root, and symlinks pointing out of it are refused during classification —
before authorization is reached. This is deliberately not "return
RESTRICTED": an out-of-root path is malformed, not merely sensitive, so even
an agent cleared to RESTRICTED cannot read `/etc/shadow`.

**Sensitivity is derived from the path, not claimed by the caller.**
`.env`, `*.pem`, `*.key`, `id_rsa*`, `*credentials*` and friends are
RESTRICTED whether or not the caller knew. `.git/**` is CONFIDENTIAL —
not secret by nature, but remote URLs carry tokens and rewriting history
corrupts the repo. `README`/`LICENSE`/`*.md` are PUBLIC. Everything else in
the root defaults to INTERNAL.

`examples/governed_repo_session.py` runs the whole thing against this
repository and exits non-zero if the audit chain breaks.

## Levels

| Level | Name | Max clearance | Can write | Direct reports |
|-------|------|---------------|-----------|----------------|
| 1 | `READ_ONLY` | PUBLIC | no | 0 |
| 2 | `INTERNAL` | INTERNAL | no | 5 |
| 3 | `OPERATOR` | CONFIDENTIAL | yes | 10 |
| 4 | `CROSS_AGENT` | CONFIDENTIAL | yes | 25 |
| 5 | `EXECUTIVE` | RESTRICTED | yes | 100 |
| 6 | `CHAIRMAN` | RESTRICTED | yes | 1000 |

An agent's effective clearance is the **stricter** of its level cap and its
charter grant. Creating a level 3+ agent additionally requires an executive
or the Chairman as approver, regardless of who filed the proposal.

## Tool categories

`featured` `productive` `creativity` `developer` `business_ops`
`data_analysis` `communication` `education` `research` `security`
`finance` `healthcare` `entertainment`

These are governance labels, not integrations. Granting `finance` records
that an agent is *authorized* for finance work; wiring that to a real
system is the caller's job. See "What this does not do" below.

## Library use

```python
from chairman import Registry, Store, Level, Tool, Classification

registry = Registry(Store("org.db"))
registry.install_chairman()

request = registry.request_agent(
    requested_by="chairman",
    name="ledger-analyst",
    level=Level.OPERATOR,
    tools=[Tool.FINANCE, Tool.DATA_ANALYSIS],
    max_classification=Classification.CONFIDENTIAL,
    purpose="Daily ledger reconciliation and anomaly detection",
    objectives=["Flag anomalies within 24h"],
    reporting="Daily briefing",
    risks="Touches confidential ledger data",
)
agent = registry.approve_request(request.request_id, approver="chairman")

decision = registry.authorize("ledger-analyst", Tool.FINANCE, Classification.CONFIDENTIAL)
if decision:
    ...  # proceed
else:
    print(decision.reason)
```

Every `ChairmanError` subclass (`PermissionDenied`, `IncompleteRequest`,
`NotFound`, `StateError`) carries a message written to be pasted straight
into an incident note.

## CLI

| Command | Purpose |
|---------|---------|
| `init` | Create the root Chairman |
| `request` | File a creation proposal |
| `approve` / `reject` | Decide a pending proposal |
| `requests` | List proposals by status |
| `chart` | Print the org tree |
| `check` | Test whether an agent may act (exit 1 on deny) |
| `assign` / `tasks` | Delegate and list work |
| `task` | Advance a task's status, escalation, or note |
| `escalations` | Open items at or above a severity (exit 1 if any) |
| `suspend` / `terminate` | Lifecycle control |
| `log` / `verify` | Read and integrity-check the audit chain |

`check`, `escalations`, and `verify` use exit codes, so they drop into CI
or a cron job without parsing output.

## What this does not do

Being precise about this matters more than the feature list.

- **The audit chain is tamper-evident, not tamper-proof.** Anyone who can
  write to the SQLite file can recompute the entire chain and produce a log
  that verifies clean. To get a real guarantee, anchor `head_hash()`
  somewhere the same party cannot rewrite — an external append-only store,
  a countersigned receipt, a commit in another repo. Verified locally, the
  chain catches partial and careless edits, which is the common case.
- **No encryption.** `Classification` is an access-control label the
  registry enforces on its own decisions. It does not encrypt anything, and
  the SQLite file is plaintext on disk. Use filesystem or volume encryption.
- **No authentication.** `authorize("some-agent", ...)` trusts the caller's
  claim about which agent is acting. This is an authorization engine; it
  assumes something upstream established identity.
- **Enforcement is a seatbelt, not a sandbox.** Python offers no true
  isolation. Someone editing the process can reach `ToolBox._specs`, reset
  the context variable, or import the undecorated function from the module
  that defined it. The guard stops the failure that actually happens — code
  paths that forgot to check — not a hostile caller inside your own
  interpreter. Tools registered nowhere are governed by nothing.
- **No budget enforcement.** `budget_usd` is recorded on the proposal and
  never checked against spend.
- **Agents are records, not processes.** Nothing here spawns a worker or
  runs a model. It governs a roster of agents whose execution lives
  elsewhere.

## Layout

```
chairman/
  models.py       dataclasses and enums, no I/O
  permissions.py  pure decision functions — the rules live here
  audit.py        hash chaining and verification
  store.py        SQLite persistence
  registry.py     lifecycle; the only module that mutates state
  enforcement.py  Session, ToolBox, the guard — authorization you can't skip
  toolkit.py      real filesystem/repo tools, path-confined and path-classified
  errors.py       exception hierarchy
  cli.py          argparse front end
examples/         a governed session working on this repo
tests/            112 tests, stdlib unittest
```

The rules in `permissions.py` are pure functions over plain dataclasses, so
`test_permissions.py` exercises every branch without touching a database.

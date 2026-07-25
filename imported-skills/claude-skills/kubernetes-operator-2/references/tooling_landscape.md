# Tooling landscape

Five mainstream operator frameworks. Pick by language, complexity, and target environment.

## At-a-glance

| Framework | Language | Scaffolding | Webhook support | Best for | Project status |
|---|---|---|---|---|---|
| **controller-runtime** | Go | None (library) | Yes | Production-grade, low-level | Active (sig-api-machinery) |
| **kubebuilder** | Go | Yes (CLI) | Yes | Standard Go operator path | Active (Kubernetes SIGs) |
| **operator-sdk** | Go / Helm / Ansible | Yes (CLI) | Yes | OpenShift, mixed paradigms | Active (Red Hat) |
| **metacontroller** | Any (webhook) | None | N/A (uses webhooks) | Polyglot, avoid Go | Less active |
| **KOPF** | Python | None (library) | Yes | Python shops, async-first | Active (community) |
| **java-operator-sdk** | Java | Yes | Yes | JVM shops | Active (Red Hat / Java SIG) |

## Decision tree

```
Primary language?
├── Go ──┬── Need scaffolding + opinionated path → kubebuilder
│        ├── Targeting OpenShift / OLM            → operator-sdk (Go)
│        └── Library-only, full control            → controller-runtime
├── Python ─────────────────────────────────────────→ KOPF
├── Java   ─────────────────────────────────────────→ java-operator-sdk
└── Other (Node, Ruby, Rust)
        └── webhook-based, polyglot                  → metacontroller
```

## controller-runtime (Go library)

**What it is:** The Go library that everyone else builds on. Provides `Manager`, `Reconciler`, cache, client, predicates, leader election.

**Use when:**
- You need fine-grained control over the manager and event sources
- You're building reusable operator components
- Your team has Go experience and prefers libraries to scaffolders

**Skip when:**
- You want bootstrap-by-CLI (use kubebuilder)
- You don't speak Go

**Example:**
```go
mgr, _ := ctrl.NewManager(cfg, ctrl.Options{Scheme: scheme})
ctrl.NewControllerManagedBy(mgr).
    For(&apps.MyApp{}).
    Complete(&MyAppReconciler{Client: mgr.GetClient()})
mgr.Start(ctx)
```

## kubebuilder (Go scaffolder)

**What it is:** The standard scaffolding tool. Wraps controller-runtime with project layout, code generation, and the `kubebuilder` CLI.

**Use when:**
- New Go operator
- You want predictable project structure
- You'll publish the operator publicly

**Workflow:**
```bash
kubebuilder init --domain example.com --repo github.com/org/myapp-operator
kubebuilder create api --group apps --version v1alpha1 --kind MyApp
make manifests
make generate
make run
```

**Strengths:** Excellent docs, mature, used by everyone from cert-manager to Crossplane.

**Weaknesses:** Some teams find the layout opinionated; sometimes hard to escape from.

## operator-sdk (Red Hat / OpenShift)

**What it is:** Wraps kubebuilder for Go and adds Helm-based and Ansible-based operators (no Go required).

**Use when:**
- Targeting OpenShift / OLM (Operator Lifecycle Manager)
- Building a Helm-based operator from an existing chart
- Building an Ansible-based operator from existing playbooks

**Helm-based operator:**
```bash
operator-sdk init --plugins=helm --domain example.com --group apps --version v1 --kind MyApp
operator-sdk create api --group apps --version v1 --kind MyApp --helm-chart=./mychart
```

The operator's reconcile becomes `helm upgrade --install`. Fast on-ramp; less power.

**Ansible-based operator:**
Similar, but reconcile invokes a playbook. Useful for ops teams already deep in Ansible.

**Skip when:**
- Vanilla k8s target (kubebuilder is more direct)
- You want a Go operator without OpenShift coupling

## metacontroller (webhook-based, language-agnostic)

**What it is:** Runs in-cluster, watches your CRDs, and POSTs webhook calls to your endpoints with desired-state computations. You implement the logic in any language behind an HTTP endpoint.

**Use when:**
- Polyglot team (Python, Node, Ruby, etc.)
- Want to avoid Go and Java
- Operator logic is genuinely simple (compute children from parent)

**Example sync hook:**
```python
# Python webhook returns desired children given parent + observed
def sync(request):
    parent = request['parent']
    return {
        'status': {'phase': 'Ready'},
        'children': [{'apiVersion': 'apps/v1', 'kind': 'Deployment', ...}],
    }
```

**Strengths:** No Go required; fast iteration in any language.

**Weaknesses:** Lower ecosystem activity; not great for complex multi-CRD operators; webhook-based latency.

## KOPF (Python)

**What it is:** A Python framework for building operators. Async-first, decorator-based, no scaffolding step.

**Use when:**
- Python shop
- Operator logic is moderate complexity
- Want fast iteration without recompilation

**Example:**
```python
import kopf

@kopf.on.create('apps.example.com', 'v1alpha1', 'myapps')
async def create_fn(spec, name, namespace, logger, **_):
    logger.info(f"creating MyApp {name}")
    # ... create children
    return {'phase': 'Ready'}

@kopf.on.delete('apps.example.com', 'v1alpha1', 'myapps')
async def delete_fn(spec, name, namespace, **_):
    # cleanup external resources
    pass
```

**Strengths:**
- Async/await native (good for many concurrent reconciles)
- No code generation
- Good for ML/data teams already in Python

**Weaknesses:**
- Smaller ecosystem than Go
- Some features lag controller-runtime (e.g., complex caching)
- Python startup cost in the controller pod

## java-operator-sdk

**What it is:** Java framework, Quarkus integration, modeled after controller-runtime.

**Use when:** JVM shop with strong Spring/Quarkus skills.

**Skip when:** You don't already have a JVM ops setup.

## Comparison: complexity vs control

```
control ↑
        │  controller-runtime  (full control, library)
        │       │
        │  kubebuilder         (scaffolded controller-runtime)
        │       │
        │  operator-sdk Go     (kubebuilder + OLM)
        │       │
        │  KOPF                (Python decorators)
        │       │
        │  java-operator-sdk   (JVM)
        │       │
        │  operator-sdk Ansible (playbooks)
        │       │
        │  operator-sdk Helm   (chart-based)
        │       │
        │  metacontroller      (webhook hooks)
        ↓
complexity ↓
```

Higher control = more code, more flexibility. Lower complexity = faster start, less power.

## Cross-cutting concerns

Regardless of framework:

- **Webhooks for validation** — reject bad CRs at admission
- **cert-manager** — rotate webhook certs automatically
- **Prometheus** — `/metrics` endpoint via controller-runtime's built-in metrics
- **OLM** (Operator Lifecycle Manager) — for OperatorHub publishing
- **OperatorHub Capability Levels** — see `operator_capability_audit.py`

## Migration paths

| From | To | Effort |
|---|---|---|
| controller-runtime | kubebuilder | Low (kubebuilder uses controller-runtime) |
| Helm chart | Helm-based operator-sdk | Low |
| Helm chart | Go operator (kubebuilder) | High (rewrite logic in Go) |
| KOPF | Go operator | High (language change) |
| Any | metacontroller | Medium (move logic behind HTTP) |

## Selection checklist

Before committing:
- [ ] Identify primary language constraint
- [ ] Target environment (vanilla k8s vs OpenShift/OLM)
- [ ] Operator complexity: 1 CRD vs many
- [ ] Need webhooks?
- [ ] Need OLM publishing?
- [ ] Build a 1-week proof-of-concept; verify reconcile latency, status update flow, and dev-loop ergonomics

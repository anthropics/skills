# Tooling landscape

Six options. Pick by stack, license preference, and required attack types.

## At-a-glance

| Tool | License | Stack | Attack coverage | Best for |
|---|---|---|---|---|
| **Chaos Toolkit** | OSS (Apache 2) | Any (Python) | Broad via plugins | Lightweight, multi-cloud, JSON experiments |
| **Chaos Mesh** | OSS (Apache 2) | Kubernetes | Very broad (network, pod, IO, time, stress) | k8s-native, rich CRDs |
| **Litmus** | OSS (Apache 2) | Kubernetes | Very broad (300+ experiments) | k8s, Argo-integrated |
| **Gremlin** | Commercial | Any (agents) | Broad, polished | Enterprise, audit, multi-cloud |
| **AWS FIS** | Paid (AWS) | AWS | AWS services + EC2/ECS/EKS | AWS-heavy, IAM-integrated |
| **Custom** | Your code | Any | What you build | Niche, single-cloud, low budget |

## Decision tree

```
Stack constraint?
├── Kubernetes-only ──┬── OSS preferred → Chaos Mesh OR Litmus
│                     │       (Litmus has the bigger experiment library;
│                     │        Chaos Mesh has cleaner CRD model)
│                     └── Enterprise budget → Gremlin
│
├── AWS-heavy ────────┬── Simple needs → AWS FIS
│                     ├── Multi-cloud + AWS → Chaos Toolkit + AWS plugin
│                     └── Enterprise → Gremlin
│
├── Multi-cloud ──────┬── OSS → Chaos Toolkit
│                     └── Enterprise → Gremlin
│
└── No infra constraint
    └── Just need fault injection → Toxiproxy (a single-purpose tool, not full chaos framework)
```

## Chaos Toolkit

**What it is:** Python-based framework. You write experiments as JSON or YAML files; the CLI runs them.

**Strengths:**
- Lightweight; runs anywhere Python runs
- Plugin ecosystem for AWS, Azure, GCP, Kubernetes, etc.
- JSON experiments are version-controllable
- Apache 2 license

**Weaknesses:**
- No built-in scheduling (you bring cron / CI)
- Smaller experiment library than Litmus
- Plugin quality varies

**Example experiment (JSON):**
```json
{
  "title": "Latency on payment-svc",
  "description": "p99 latency stays <500ms when payment is +200ms slow",
  "steady-state-hypothesis": {
    "title": "p99 < 500ms",
    "probes": [{ "type": "probe", "tolerance": [0, 500],
                 "provider": { "type": "http", "url": "https://my.dashboards/p99" } }]
  },
  "method": [{ "type": "action", "name": "add-latency",
               "provider": { "type": "process", "path": "tc", "arguments": [...] } }]
}
```

## Chaos Mesh

**What it is:** Kubernetes operator + CRDs for chaos. Install in-cluster; `kubectl apply` an experiment.

**Strengths:**
- True k8s-native (no external orchestrator)
- Comprehensive coverage: network, pod, IO, stress, time, DNS, HTTP, kernel
- UI dashboard for running experiments
- CNCF Incubating project

**Weaknesses:**
- k8s-only
- CRD layout is opinionated; some types feel similar but aren't
- Setup requires cluster admin

**Example experiment (CRD):**
```yaml
apiVersion: chaos-mesh.org/v1alpha1
kind: NetworkChaos
metadata:
  name: payment-latency
spec:
  action: delay
  mode: one
  selector:
    namespaces: [default]
    labelSelectors:
      app: payment-svc
  delay:
    latency: 200ms
  duration: 5m
```

## Litmus

**What it is:** Kubernetes chaos framework with a large experiment library. Argo-CD integration.

**Strengths:**
- 300+ pre-built experiments
- Strong Argo / GitOps integration
- ChaosHub community library
- Workflow capability for multi-step experiments

**Weaknesses:**
- More moving parts than Chaos Mesh
- Some pre-built experiments are thin wrappers; quality varies
- k8s-only

## Gremlin

**What it is:** Commercial SaaS. Agents on hosts; central control plane.

**Strengths:**
- Polished UX
- Comprehensive attack library
- Audit logs (compliance)
- Multi-cloud, multi-OS
- Customer support

**Weaknesses:**
- Paid (per-host or per-MAU)
- Vendor lock-in
- Less control than OSS

**When to choose:** large enterprise, compliance/audit requirements, dedicated chaos team, budget exists.

## AWS FIS (Fault Injection Simulator)

**What it is:** AWS-managed chaos service. Templates of "actions" (stop instance, throttle API) chained into experiments.

**Strengths:**
- IAM-integrated (proper auth/audit)
- Native to AWS services (RDS failover, ECS/EKS, Network Manager)
- Pay-per-experiment (no agents to maintain)

**Weaknesses:**
- AWS-only
- Smaller attack library than Chaos Mesh / Gremlin
- Multi-account is awkward

**When to choose:** AWS-heavy team that wants chaos without managing the chaos infra.

## Custom (DIY)

**When to choose:**
- Single-cloud, single-stack, low complexity
- Budget = $0
- Have engineering capacity to maintain the tool
- Need a niche attack type that no tool covers

**Implementation patterns:**
- Bash scripts that wrap `tc` / iptables / kill / stress-ng
- Application-level chaos via feature flags + middleware
- Service mesh fault injection (Istio / Linkerd) — covers many cases without a chaos framework

**Trade-offs:**
- You build all the safety rails (abort, timeout, blast-radius)
- You build the scheduler
- You debug your own bugs

For most teams, this is a starter path; once chaos becomes regular, switch to a real tool.

## Pricing rule of thumb

| Tool | Typical cost (annual) |
|---|---|
| Chaos Toolkit | $0 |
| Chaos Mesh | $0 |
| Litmus OSS | $0 |
| Litmus Enterprise | $5-30k |
| Gremlin | $20-100k+ |
| AWS FIS | pay-per-action, ~$100-2000/mo for active use |
| Custom | engineering time only |

## Migration paths

| From | To | Effort |
|---|---|---|
| Custom scripts | Chaos Toolkit | Low (wrap scripts as actions) |
| Chaos Toolkit | Chaos Mesh | Medium (k8s-only; rewrite for CRDs) |
| Chaos Mesh | Litmus | Medium (similar shape, different CRDs) |
| Anything | Gremlin | Easy (Gremlin imports many formats) |

## Selection checklist

Before committing:
- [ ] Stack matches (k8s vs multi-cloud vs AWS-only)
- [ ] Required attack types covered (cross-reference `attack_taxonomy.md`)
- [ ] Audit logging requirement met (Gremlin / AWS FIS only have full audit)
- [ ] Self-hosting requirement met (OSS only)
- [ ] Budget approved
- [ ] Run a 30-day proof-of-concept; verify abort path works

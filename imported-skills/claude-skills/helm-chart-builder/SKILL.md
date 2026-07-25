---
name: "helm-chart-builder"
description: "Helm chart development agent skill and plugin for Claude Code, Codex, Gemini CLI, Cursor, OpenClaw — chart scaffolding, values design, template patterns, dependency management, security hardening, and chart testing. Use when: user wants to create or improve Helm charts, design values.yaml files, implement template helpers, audit chart security (RBAC, network policies, pod security), manage subcharts, or run helm lint/test."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: engineering
  updated: 2026-03-15
---

# Helm Chart Builder

> Production-grade Helm charts. Sensible defaults. Secure by design. No cargo-culting.

Opinionated Helm workflow that turns ad-hoc Kubernetes manifests into maintainable, testable, reusable charts. Covers chart structure, values design, template patterns, dependency management, and security hardening.

Not a Helm tutorial — a set of concrete decisions about how to build charts that operators trust and developers don't fight.

---

## Slash Commands

| Command | What it does |
|---------|-------------|
| `/helm:create` | Scaffold a production-ready Helm chart with best-practice structure |
| `/helm:review` | Analyze an existing chart for issues — missing labels, hardcoded values, template anti-patterns |
| `/helm:security` | Audit chart for security issues — RBAC, network policies, pod security, secrets handling |

---

## When This Skill Activates

Recognize these patterns from the user:

- "Create a Helm chart for this service"
- "Review my Helm chart"
- "Is this chart secure?"
- "Design a values.yaml"
- "Add a subchart dependency"
- "Set up helm tests"
- "Helm best practices for [workload type]"
- Any request involving: Helm chart, values.yaml, Chart.yaml, templates, helpers, _helpers.tpl, subcharts, helm lint, helm test

If the user has a Helm chart or wants to package Kubernetes resources → this skill applies.

---

## Workflow

### `/helm:create` — Chart Scaffolding

1. **Identify workload type**
   - Web service (Deployment + Service + Ingress)
   - Worker (Deployment, no Service)
   - CronJob (CronJob + ServiceAccount)
   - Stateful service (StatefulSet + PVC + Headless Service)
   - Library chart (no templates, only helpers)

2. **Scaffold chart structure**

   ```
   mychart/
   ├── Chart.yaml              # Chart metadata and dependencies
   ├── values.yaml             # Default configuration
   ├── values.schema.json      # Optional: JSON Schema for values validation
   ├── .helmignore             # Files to exclude from packaging
   ├── templates/
   │   ├── _helpers.tpl        # Named templates and helper functions
   │   ├── deployment.yaml     # Workload resource
   │   ├── service.yaml        # Service exposure
   │   ├── ingress.yaml        # Ingress (if applicable)
   │   ├── serviceaccount.yaml # ServiceAccount
   │   ├── hpa.yaml            # HorizontalPodAutoscaler
   │   ├── pdb.yaml            # PodDisruptionBudget
   │   ├── networkpolicy.yaml  # NetworkPolicy
   │   ├── configmap.yaml      # ConfigMap (if needed)
   │   ├── secret.yaml         # Secret (if needed)
   │   ├── NOTES.txt           # Post-install usage instructions
   │   └── tests/
   │       └── test-connection.yaml
   └── charts/                 # Subcharts (dependencies)
   ```

3. **Apply Chart.yaml best practices**

   ```
   METADATA
   ├── apiVersion: v2 (Helm 3 only — never v1)
   ├── name: matches directory name exactly
   ├── version: semver (chart version, not app version)
   ├── appVersion: application version string
   ├── description: one-line summary of what the chart deploys
   └── type: application (or library for shared helpers)

   DEPENDENCIES
   ├── Pin dependency versions with ~X.Y.Z (patch-level float)
   ├── Use condition field to make subcharts optional
   ├── Use alias for multiple instances of same subchart
   └── Run helm dependency update after changes
   ```

4. **Generate values.yaml with documentation**
   - Every value has an inline comment explaining purpose and type
   - Sensible defaults that work for development
   - Override-friendly structure (flat where possible, nested only when logical)
   - No hardcoded cluster-specific values (image registry, domain, storage class)

5. **Validate**
   ```bash
   python3 scripts/chart_analyzer.py mychart/
   helm lint mychart/
   helm template mychart/ --debug
   ```

### `/helm:review` — Chart Analysis

1. **Check chart structure**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | Missing _helpers.tpl | High | Create helpers for common labels and selectors |
   | No NOTES.txt | Medium | Add post-install instructions |
   | No .helmignore | Low | Create one to exclude .git, CI files, tests |
   | Missing Chart.yaml fields | Medium | Add description, appVersion, maintainers |
   | Hardcoded values in templates | High | Extract to values.yaml with defaults |

2. **Check template quality**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | Missing standard labels | High | Use `app.kubernetes.io/*` labels via _helpers.tpl |
   | No resource requests/limits | Critical | Add resources section with defaults in values.yaml |
   | Hardcoded image tag | High | Use `{{ .Values.image.repository }}:{{ .Values.image.tag }}` |
   | No imagePullPolicy | Medium | Default to `IfNotPresent`, overridable |
   | Missing liveness/readiness probes | High | Add probes with configurable paths and ports |
   | No pod anti-affinity | Medium | Add preferred anti-affinity for HA |
   | Duplicate template code | Medium | Extract into named templates in _helpers.tpl |

3. **Check values.yaml quality**
   ```bash
   python3 scripts/values_validator.py mychart/values.yaml
   ```

4. **Generate review report**
   ```
   HELM CHART REVIEW — [chart name]
   Date: [timestamp]

   CRITICAL: [count]
   HIGH:     [count]
   MEDIUM:   [count]
   LOW:      [count]

   [Detailed findings with fix recommendations]
   ```

### `/helm:security` — Security Audit

1. **Pod security audit**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | No securityContext | Critical | Add runAsNonRoot, readOnlyRootFilesystem |
   | Running as root | Critical | Set `runAsNonRoot: true`, `runAsUser: 1000` |
   | Writable root filesystem | High | Set `readOnlyRootFilesystem: true` + emptyDir for tmp |
   | All capabilities retained | High | Drop ALL, add only specific needed caps |
   | Privileged container | Critical | Set `privileged: false`, use specific capabilities |
   | No seccomp profile | Medium | Set `seccompProfile.type: RuntimeDefault` |
   | allowPrivilegeEscalation true | High | Set `allowPrivilegeEscalation: false` |

2. **RBAC audit**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | No ServiceAccount | Medium | Create dedicated SA, don't use default |
   | automountServiceAccountToken true | Medium | Set to false unless pod needs K8s API access |
   | ClusterRole instead of Role | Medium | Use namespace-scoped Role unless cluster-wide needed |
   | Wildcard permissions | Critical | Use specific resource names and verbs |
   | No RBAC at all | Low | Acceptable if pod doesn't need K8s API access |

3. **Network and secrets audit**

   | Check | Severity | Fix |
   |-------|----------|-----|
   | No NetworkPolicy | Medium | Add default-deny ingress + explicit allow rules |
   | Secrets in values.yaml | Critical | Use external secrets operator or sealed-secrets |
   | No PodDisruptionBudget | Medium | Add PDB with minAvailable for HA workloads |
   | hostNetwork: true | High | Remove unless absolutely required (e.g., CNI plugin) |
   | hostPID or hostIPC | Critical | Never use in application charts |

4. **Generate security report**
   ```
   SECURITY AUDIT — [chart name]
   Date: [timestamp]

   CRITICAL: [count]
   HIGH:     [count]
   MEDIUM:   [count]
   LOW:      [count]

   [Detailed findings with remediation steps]
   ```

---

## Tooling

### `scripts/chart_analyzer.py`

CLI utility for static analysis of Helm chart directories.

**Features:**
- Chart structure validation (required files, directory layout)
- Template anti-pattern detection (hardcoded values, missing labels, no resource limits)
- Chart.yaml metadata checks
- Standard labels verification (app.kubernetes.io/*)
- Security baseline checks
- JSON and text output

**Usage:**
```bash
# Analyze a chart directory
python3 scripts/chart_analyzer.py mychart/

# JSON output
python3 scripts/chart_analyzer.py mychart/ --output json

# Security-focused analysis
python3 scripts/chart_analyzer.py mychart/ --security
```

### `scripts/values_validator.py`

CLI utility for validating values.yaml against best practices.

**Features:**
- Documentation coverage (inline comments)
- Type consistency checks
- Hardcoded secrets detection
- Default value quality analysis
- Structure depth analysis
- Naming convention validation
- JSON and text output

**Usage:**
```bash
# Validate values.yaml
python3 scripts/values_validator.py values.yaml

# JSON output
python3 scripts/values_validator.py values.yaml --output json

# Strict mode (fail on warnings)
python3 scripts/values_validator.py values.yaml --strict
```

---

## Template Patterns

### Pattern 1: Standard Labels (_helpers.tpl)

```yaml
{{/*
Common labels for all resources.
*/}}
{{- define "mychart.labels" -}}
helm.sh/chart: {{ include "mychart.chart" . }}
app.kubernetes.io/name: {{ include "mychart.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
app.kubernetes.io/version: {{ .Chart.AppVersion | quote }}
app.kubernetes.io/managed-by: {{ .Release.Service }}
{{- end }}

{{/*
Selector labels (subset of common labels — must be immutable).
*/}}
{{- define "mychart.selectorLabels" -}}
app.kubernetes.io/name: {{ include "mychart.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end }}
```

### Pattern 2: Conditional Resources

```yaml
{{- if .Values.ingress.enabled -}}
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: {{ include "mychart.fullname" . }}
  labels:
    {{- include "mychart.labels" . | nindent 4 }}
  {{- with .Values.ingress.annotations }}
  annotations:
    {{- toYaml . | nindent 4 }}
  {{- end }}
spec:
  {{- if .Values.ingress.tls }}
  tls:
    {{- range .Values.ingress.tls }}
    - hosts:
        {{- range .hosts }}
        - {{ . | quote }}
        {{- end }}
      secretName: {{ .secretName }}
    {{- end }}
  {{- end }}
  rules:
    {{- range .Values.ingress.hosts }}
    - host: {{ .host | quote }}
      http:
        paths:
          {{- range .paths }}
          - path: {{ .path }}
            pathType: {{ .pathType }}
            backend:
              service:
                name: {{ include "mychart.fullname" $ }}
                port:
                  number: {{ $.Values.service.port }}
          {{- end }}
    {{- end }}
{{- end }}
```

### Pattern 3: Security-Hardened Pod Spec

```yaml
spec:
  serviceAccountName: {{ include "mychart.serviceAccountName" . }}
  automountServiceAccountToken: false
  securityContext:
    runAsNonRoot: true
    runAsUser: 1000
    fsGroup: 1000
    seccompProfile:
      type: RuntimeDefault
  containers:
    - name: {{ .Chart.Name }}
      securityContext:
        allowPrivilegeEscalation: false
        readOnlyRootFilesystem: true
        capabilities:
          drop:
            - ALL
      image: "{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"
      imagePullPolicy: {{ .Values.image.pullPolicy }}
      resources:
        {{- toYaml .Values.resources | nindent 8 }}
      volumeMounts:
        - name: tmp
          mountPath: /tmp
  volumes:
    - name: tmp
      emptyDir: {}
```

---

## Values Design Principles

```
STRUCTURE
├── Flat over nested (image.tag > container.spec.image.tag)
├── Group by resource (service.*, ingress.*, resources.*)
├── Use enabled: true/false for optional resources
├── Document every key with inline YAML comments
└── Provide sensible development defaults

NAMING
├── camelCase for keys (replicaCount, not replica_count)
├── Boolean keys: use adjectives (enabled, required) not verbs
├── Nested keys: max 3 levels deep
└── Match upstream conventions (image.repository, image.tag, image.pullPolicy)

ANTI-PATTERNS
├── Hardcoded cluster URLs or domains
├── Secrets as default values
├── Empty strings where null is correct
├── Deeply nested structures (>3 levels)
├── Undocumented values
└── values.yaml that doesn't work without overrides
```

---

## Dependency Management

```
SUBCHARTS
├── Use Chart.yaml dependencies (not requirements.yaml — Helm 3)
├── Pin versions: version: ~15.x.x (patch float)
├── Use condition: to make optional: condition: postgresql.enabled
├── Use alias: for multiple instances of same chart
├── Override subchart values under subchart name key in values.yaml
└── Run helm dependency update before packaging

LIBRARY CHARTS
├── type: library in Chart.yaml — no templates directory
├── Export named templates only — no rendered resources
├── Use for shared labels, annotations, security contexts
└── Version independently from application charts
```

---

## Proactive Triggers

Flag these without being asked:

- **No _helpers.tpl** → Create one. Every chart needs standard labels and fullname helpers.
- **Hardcoded image tag in template** → Extract to values.yaml. Tags must be overridable.
- **No resource requests/limits** → Add them. Pods without limits can starve the node.
- **Running as root** → Add securityContext. No exceptions for production charts.
- **No NOTES.txt** → Create one. Users need post-install instructions.
- **Secrets in values.yaml defaults** → Remove them. Use placeholders with comments explaining how to provide secrets.
- **No liveness/readiness probes** → Add them. Kubernetes needs to know if the pod is healthy.
- **Missing app.kubernetes.io labels** → Add via _helpers.tpl. Required for proper resource tracking.

---

## Installation

### One-liner (any tool)
```bash
git clone https://github.com/alirezarezvani/claude-skills.git
cp -r claude-skills/engineering/helm-chart-builder ~/.claude/skills/
```

### Multi-tool install
```bash
./scripts/convert.sh --skill helm-chart-builder --tool codex|gemini|cursor|windsurf|openclaw
```

### OpenClaw
```bash
clawhub install cs-helm-chart-builder
```

---

## Related Skills

- **senior-devops** — Broader DevOps scope (CI/CD, IaC, monitoring). Complementary — use helm-chart-builder for chart-specific work, senior-devops for pipeline and infrastructure.
- **docker-development** — Container building. Complementary — docker-development builds the images, helm-chart-builder deploys them to Kubernetes.
- **ci-cd-pipeline-builder** — Pipeline construction. Complementary — helm-chart-builder defines the deployment artifact, ci-cd-pipeline-builder automates its delivery.
- **senior-security** — Application security. Complementary — helm-chart-builder covers Kubernetes-level security (RBAC, pod security), senior-security covers application-level threats.

# Values.yaml Design Reference

## Design Principles

### 1. Every Value Is Documented

```yaml
# Bad — what does this mean?
replicaCount: 1
maxSurge: 25%

# Good — clear purpose, type, and constraints
# -- Number of pod replicas. Ignored when autoscaling.enabled is true.
replicaCount: 1
# -- Maximum number of pods above desired count during rolling update (int or percentage).
maxSurge: 25%
```

### 2. Sensible Defaults That Work

A user should be able to `helm install mychart .` with zero overrides and get a working deployment.

```yaml
# Bad — broken without override
image:
  repository: ""           # Fails: no image
  tag: ""                  # Fails: no tag

# Good — works out of the box
image:
  repository: nginx        # Default image for development
  tag: ""                  # Defaults to .Chart.AppVersion in template
  pullPolicy: IfNotPresent
```

### 3. Flat Over Nested

```yaml
# Bad — 5 levels deep, painful to override
container:
  spec:
    security:
      context:
        runAsNonRoot: true

# Good — 2 levels, easy to override with --set
securityContext:
  runAsNonRoot: true
```

**Rule of thumb:** Max 3 levels of nesting. If you need more, redesign.

### 4. Group by Resource

```yaml
# Good — grouped by Kubernetes resource
service:
  type: ClusterIP
  port: 80

ingress:
  enabled: false
  className: ""
  hosts: []

autoscaling:
  enabled: false
  minReplicas: 1
  maxReplicas: 10
```

---

## Standard Values Structure

### Recommended Layout Order

```yaml
# -- Number of pod replicas
replicaCount: 1

# -- Override chart name
nameOverride: ""
# -- Override fully qualified app name
fullnameOverride: ""

image:
  # -- Container image repository
  repository: myapp
  # -- Image pull policy
  pullPolicy: IfNotPresent
  # -- Image tag (defaults to .Chart.AppVersion)
  tag: ""

# -- Image pull secrets for private registries
imagePullSecrets: []

serviceAccount:
  # -- Create a ServiceAccount
  create: true
  # -- Annotations for the ServiceAccount
  annotations: {}
  # -- ServiceAccount name (generated from fullname if not set)
  name: ""
  # -- Automount the service account token
  automount: false

# -- Pod annotations
podAnnotations: {}
# -- Additional pod labels
podLabels: {}

# -- Pod security context
podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1000
  fsGroup: 1000
  seccompProfile:
    type: RuntimeDefault

# -- Container security context
securityContext:
  allowPrivilegeEscalation: false
  readOnlyRootFilesystem: true
  capabilities:
    drop:
      - ALL

service:
  # -- Service type
  type: ClusterIP
  # -- Service port
  port: 80

ingress:
  # -- Enable ingress
  enabled: false
  # -- Ingress class name
  className: ""
  # -- Ingress annotations
  annotations: {}
  # -- Ingress hosts
  hosts:
    - host: chart-example.local
      paths:
        - path: /
          pathType: ImplementationSpecific
  # -- Ingress TLS configuration
  tls: []

# -- Container resource requests and limits
resources:
  requests:
    cpu: 100m
    memory: 128Mi
  limits:
    cpu: 500m
    memory: 256Mi

# -- Liveness probe configuration
livenessProbe:
  httpGet:
    path: /healthz
    port: http
  initialDelaySeconds: 15
  periodSeconds: 20

# -- Readiness probe configuration
readinessProbe:
  httpGet:
    path: /readyz
    port: http
  initialDelaySeconds: 5
  periodSeconds: 10

autoscaling:
  # -- Enable horizontal pod autoscaler
  enabled: false
  # -- Minimum replicas
  minReplicas: 1
  # -- Maximum replicas
  maxReplicas: 10
  # -- Target CPU utilization percentage
  targetCPUUtilizationPercentage: 80
  # -- Target memory utilization percentage (optional)
  # targetMemoryUtilizationPercentage: 80

pdb:
  # -- Enable PodDisruptionBudget
  enabled: false
  # -- Minimum available pods
  minAvailable: 1
  # -- Maximum unavailable pods (alternative to minAvailable)
  # maxUnavailable: 1

# -- Node selector constraints
nodeSelector: {}
# -- Tolerations for pod scheduling
tolerations: []
# -- Affinity rules for pod scheduling
affinity: {}

# -- Additional volumes
volumes: []
# -- Additional volume mounts
volumeMounts: []
```

---

## Anti-Patterns

### 1. Secrets in Default Values

```yaml
# BAD — secret visible in chart package, git history, Helm release
database:
  password: "mysecretpassword"
  apiKey: "sk-abc123"

# GOOD — empty defaults with documentation
database:
  # -- Database password (required). Provide via --set or external secret.
  password: ""
  # -- API key. Use external-secrets or sealed-secrets in production.
  apiKey: ""
```

### 2. Cluster-Specific Defaults

```yaml
# BAD — won't work on any other cluster
ingress:
  host: app.my-company.internal
storageClass: gp3
registry: 123456789.dkr.ecr.us-east-1.amazonaws.com

# GOOD — generic defaults
ingress:
  host: chart-example.local
storageClass: ""              # Uses cluster default
image:
  repository: myapp           # Override for private registry
```

### 3. Boolean Naming

```yaml
# BAD — unclear, verb-based
createServiceAccount: true
doAutoScale: false
skipTLS: true

# GOOD — adjective-based, consistent
serviceAccount:
  create: true               # "Is it created?" reads naturally
autoscaling:
  enabled: false             # "Is it enabled?" reads naturally
tls:
  insecureSkipVerify: false  # Matches Go/K8s convention
```

### 4. Undocumented Values

```yaml
# BAD — what are these? What types? What are valid options?
foo: bar
maxRetries: 3
mode: advanced
workers: 4

# GOOD — purpose, type, and constraints are clear
# -- Operation mode. Options: "simple", "advanced", "debug"
mode: advanced
# -- Number of background worker threads (1-16)
workers: 4
# -- Maximum retry attempts for failed API calls
maxRetries: 3
```

### 5. Empty String vs Null

```yaml
# BAD — ambiguous: is empty string intentional?
annotations: ""
nodeSelector: ""

# GOOD — null/empty map means "not set"
annotations: {}
nodeSelector: {}
# Or simply omit optional values
```

---

## Override Patterns

### Hierarchy (lowest to highest priority)

1. `values.yaml` in chart
2. Parent chart's `values.yaml` (for subcharts)
3. `-f custom-values.yaml` (left to right, last wins)
4. `--set key=value` (highest priority)

### Common Override Scenarios

```bash
# Production override file
helm install myapp . -f values-production.yaml

# Quick override with --set
helm install myapp . --set replicaCount=3 --set image.tag=v2.1.0

# Multiple value files (last wins)
helm install myapp . -f values-base.yaml -f values-production.yaml -f values-secrets.yaml
```

### values-production.yaml Pattern

```yaml
# Production overrides only — don't repeat defaults
replicaCount: 3

image:
  tag: "v2.1.0"
  pullPolicy: IfNotPresent

resources:
  requests:
    cpu: 500m
    memory: 512Mi
  limits:
    cpu: "2"
    memory: 1Gi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 20

ingress:
  enabled: true
  className: nginx
  hosts:
    - host: app.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: app-tls
      hosts:
        - app.example.com
```

---

## Type Safety with values.schema.json

### Basic Schema

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "type": "object",
  "required": ["replicaCount", "image"],
  "properties": {
    "replicaCount": {
      "type": "integer",
      "minimum": 1,
      "description": "Number of pod replicas"
    },
    "image": {
      "type": "object",
      "required": ["repository"],
      "properties": {
        "repository": {
          "type": "string",
          "minLength": 1,
          "description": "Container image repository"
        },
        "tag": {
          "type": "string",
          "description": "Image tag"
        },
        "pullPolicy": {
          "type": "string",
          "enum": ["Always", "IfNotPresent", "Never"],
          "description": "Image pull policy"
        }
      }
    },
    "service": {
      "type": "object",
      "properties": {
        "type": {
          "type": "string",
          "enum": ["ClusterIP", "NodePort", "LoadBalancer"],
          "description": "Kubernetes service type"
        },
        "port": {
          "type": "integer",
          "minimum": 1,
          "maximum": 65535,
          "description": "Service port number"
        }
      }
    }
  }
}
```

### Why Use Schema

- **Fails fast** — `helm install` rejects invalid values before rendering templates
- **Documents types** — self-documenting valid options (enums, ranges)
- **IDE support** — editors can autocomplete and validate values files
- **CI safety** — catches typos in value overrides early

---

## Testing Values

### helm lint

```bash
# Basic lint
helm lint mychart/

# Lint with override values
helm lint mychart/ -f values-production.yaml

# Lint with --set
helm lint mychart/ --set replicaCount=0  # Should fail schema
```

### helm template

```bash
# Render templates locally
helm template myrelease mychart/

# Render with overrides to verify
helm template myrelease mychart/ -f values-production.yaml

# Debug mode (shows computed values)
helm template myrelease mychart/ --debug

# Render specific template
helm template myrelease mychart/ -s templates/deployment.yaml
```

### Checklist for New Values

| Check | Question |
|-------|----------|
| Documented? | Does the key have an inline comment? |
| Default works? | Can you helm install without overriding? |
| Type clear? | Is it obvious if this is string, int, bool, list, map? |
| Overridable? | Can it be set with `--set`? (avoid deeply nested) |
| No secrets? | Are default values free of passwords/tokens? |
| camelCase? | Does it follow Helm naming convention? |
| Flat enough? | Is nesting 3 levels or less? |

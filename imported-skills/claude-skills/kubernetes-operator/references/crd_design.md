# CRD design

Custom Resource Definitions (CRDs) define the API surface of your operator. A bad CRD design locks you into hard-to-evolve schemas, forces wrapper APIs, and creates user-facing UX problems via `kubectl`.

## Anatomy of a production CRD

```yaml
apiVersion: apiextensions.k8s.io/v1
kind: CustomResourceDefinition
metadata:
  name: myapps.apps.example.com         # plural.group
spec:
  group: apps.example.com
  names:
    kind: MyApp                         # PascalCase
    plural: myapps                      # lowercase
    singular: myapp                     # lowercase
    listKind: MyAppList                 # KindList
    shortNames: [ma]                    # optional
  scope: Namespaced                     # or Cluster (justify)
  versions:
    - name: v1alpha1
      served: true
      storage: true
      schema:
        openAPIV3Schema:
          type: object
          properties:
            spec:
              type: object
              required: [version]
              properties:
                version:
                  type: string
                  pattern: '^[0-9]+\.[0-9]+\.[0-9]+$'
                replicas:
                  type: integer
                  minimum: 1
                  maximum: 100
                  default: 3
            status:
              type: object
              properties:
                phase:
                  type: string
                  enum: [Pending, Running, Failed]
                conditions:
                  type: array
                  items:
                    type: object
                    required: [type, status, lastTransitionTime]
                    properties:
                      type:    { type: string }
                      status:  { type: string, enum: ["True", "False", "Unknown"] }
                      reason:  { type: string }
                      message: { type: string }
                      lastTransitionTime: { type: string, format: date-time }
                observedGeneration: { type: integer }
      subresources:
        status: {}                      # CRITICAL — see below
        scale:                          # if scaling is meaningful
          specReplicasPath: .spec.replicas
          statusReplicasPath: .status.readyReplicas
      additionalPrinterColumns:
        - name: Phase
          type: string
          jsonPath: .status.phase
        - name: Ready
          type: string
          jsonPath: .status.conditions[?(@.type=="Ready")].status
        - name: Age
          type: date
          jsonPath: .metadata.creationTimestamp
```

## Required structural elements

### 1. Status subresource — `subresources.status: {}`

Without it:
- `r.Status().Update(ctx, obj)` doesn't work — falls back to `r.Update`
- Status updates re-trigger spec reconcile → loop
- RBAC can't be split between spec writers and status writers

**Always declare it.**

### 2. Conditions array

Use the standard `metav1.Condition` shape. Required fields: `type`, `status`, `lastTransitionTime`. Recommended: `reason`, `message`, `observedGeneration`.

Conventional condition types:
- `Ready` — overall readiness
- `Reconciling` — controller is actively working
- `Degraded` — operating but with reduced capability
- `Progressing` — change in progress (mostly for Deployments-style flows)

Use `meta.SetStatusCondition()` from `k8s.io/apimachinery/pkg/api/meta` — don't write to the slice directly.

### 3. observedGeneration

Track which spec generation the controller has acted on:

```go
status.ObservedGeneration = obj.Generation
```

Lets users tell whether status reflects the latest spec or a previous one.

### 4. Printer columns

`kubectl get myapp` UX is determined by `additionalPrinterColumns`. Always include:
- `Phase` or `Ready` (status)
- `Age` (so users know when it was created)

Optionally: replicas, version, key spec field.

### 5. Validation in the schema, not the controller

Express constraints declaratively:

| Constraint | OpenAPI |
|---|---|
| Range | `minimum`/`maximum` |
| String pattern | `pattern: '^...$'` |
| Enum | `enum: [Pending, Running]` |
| Required field | `required: [...]` |
| Default value | `default: 3` |
| Min/max length | `minLength`/`maxLength` |

Reserve controller validation for cross-field rules and external dependencies (e.g., "this name is taken in our DB").

### 6. Avoid `x-kubernetes-preserve-unknown-fields: true`

It disables structural validation. Sometimes needed (e.g., raw `kubectl apply` patches), but never at the spec root. Use it sparingly on a single sub-tree.

## Versioning strategy

CRDs evolve. Plan from day 1:

| Stage | Version | Stability | Allowed changes |
|---|---|---|---|
| Internal preview | `v1alpha1` | None | Anything; document breaking changes |
| Beta | `v1beta1` | Some | Additive only; deprecate fields |
| GA | `v1` | Strong | Additive only; never remove fields |

Conversion webhook required when:
- Multiple versions are served simultaneously
- A field's shape changed between versions

For simple field renames, `x-kubernetes-conversion-strategy: None` works.

## Scope: Namespaced vs Cluster

Default to **Namespaced**. Cluster-scoped CRDs:
- Can't be RBAC-restricted by namespace
- Can't have `OwnerReferences` from namespaced parents
- Are appropriate only for cluster-wide resources (`StorageClass`-like things)

If your operator manages namespace-bound things (apps, databases, queues), use Namespaced.

## Naming

- **Group**: `<domain>.<reverse-domain>` — e.g., `apps.example.com`. Don't use generic groups (`com`, `io`).
- **Kind**: PascalCase, singular, descriptive — `MyApp`, `Database`, `Cache`. Avoid `MyAppResource` (the `Resource` suffix is implicit).
- **Plural**: lowercase, plural — `myapps`, `databases`, `caches`.
- **Short name**: 2-3 letters; check for conflicts with built-in resources.

## Validation tooling

- `kubectl apply --dry-run=server` — validates against your CRD
- `kubectl explain <kind>.<field>` — shows what your schema documents
- `crd_validator.py` — this skill's tool, structural rules

## Documentation in the schema

Use the `description` field on every property. `kubectl explain` reads it:

```yaml
properties:
  replicas:
    type: integer
    minimum: 1
    description: |
      Number of replicas to run. Production deployments should use ≥3.
      Increases above 100 require quota approval.
```

## Anti-patterns

- **Top-level `x-kubernetes-preserve-unknown-fields: true`** — defeats validation
- **No `scope:` declared** — defaults to namespaced but make intent explicit
- **No printer columns** — `kubectl get` shows only `NAME AGE`
- **Conditions written by hand** (not via `SetStatusCondition`) — easy to lose `lastTransitionTime`
- **Status fields that duplicate spec** — keep them separate
- **Using `metadata.annotations` to encode operator state** — use status fields
- **Single huge CRD with 50+ fields** — split into multiple CRDs (e.g., MyApp + MyAppBackup + MyAppRestore)

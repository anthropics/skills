---
name: k8s-nextjs-deploy
description: Kubernetes deployment patterns for Next.js applications — Deployment/Service/Ingress manifests, Harbor image pull secrets, Traefik ingress with cert-manager TLS, Linkerd service mesh, multi-app namespaces, and K8s secret rotation. Use this skill whenever the user mentions deploying a Next.js app to Kubernetes, ImagePullBackOff, CrashLoopBackOff, Harbor pull secret, Traefik ingress, cert-manager, a missing secretKeyRef, or namespace recovery — even if they just say "the pod won't start" or "deploy this to k8s" without further detail.
---

# k8s-nextjs-deploy

Kubernetes deployment patterns for containerized Next.js apps: Harbor registry auth, Traefik ingress with automatic TLS, Linkerd sidecar injection, and multi-app namespace management.

## When to use

- Deploying a new Next.js app (Deployment + Service + Ingress rule)
- Diagnosing `ImagePullBackOff`, `ErrImagePull`, `CreateContainerConfigError`
- Rotating Harbor pull secret credentials
- Adding a subdomain to an existing Traefik ingress with cert-manager
- Applying K8s manifests after a namespace was deleted
- Troubleshooting pods stuck because of missing `secretKeyRef` secrets

Do NOT use for:
- Non-Kubernetes deployments (Docker Compose, bare-metal, Vercel)
- Database deployments (stateful sets require separate skill)

## Deployment manifest

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: cloudreviewer-web
  namespace: cloudreviewer
spec:
  replicas: 1
  selector:
    matchLabels:
      app: cloudreviewer-web
  template:
    metadata:
      labels:
        app: cloudreviewer-web
    spec:
      imagePullSecrets:
        - name: harbor-pull-secret
      containers:
        - name: web
          image: harbor.example.com/project/app:latest
          imagePullPolicy: Always
          securityContext:
            allowPrivilegeEscalation: false
          ports:
            - containerPort: 3000
          resources:
            requests:
              cpu: "100m"
              memory: "128Mi"
            limits:
              cpu: "500m"
              memory: "512Mi"
          env:
            - name: HOSTNAME
              value: "0.0.0.0"
            - name: NODE_ENV
              value: "production"
            - name: NEXT_TELEMETRY_DISABLED
              value: "1"
            - name: OTEL_SERVICE_NAME
              value: "my-app"
            - name: OTEL_EXPORTER_OTLP_ENDPOINT
              value: "http://tempo.tempo.svc.cluster.local:4318"
          readinessProbe:
            httpGet:
              path: /
              port: 3000
          livenessProbe:
            httpGet:
              path: /
              port: 3000
```

## Service

```yaml
apiVersion: v1
kind: Service
metadata:
  name: cloudreviewer-web
  namespace: cloudreviewer
spec:
  selector:
    app: cloudreviewer-web
  ports:
    - name: http
      port: 80
      targetPort: 3000
```

## Ingress (Traefik + cert-manager)

```yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: cloudreviewer
  namespace: cloudreviewer
  annotations:
    cert-manager.io/cluster-issuer: letsencrypt-prod
spec:
  ingressClassName: traefik
  tls:
    - hosts:
        - www.example.com
        - buy.example.com
        - kb.example.com
      secretName: cloudreviewer-tls
  rules:
    - host: www.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: cloudreviewer-web
                port:
                  number: 80
```

Add new subdomains to both `tls.hosts` and `rules`.

## Harbor pull secret

```bash
kubectl -n <namespace> create secret docker-registry harbor-pull-secret \
  --docker-server=harbor.example.com \
  --docker-username='robot$project+robot' \
  --docker-password='TOKEN'
```

**Single quotes are mandatory** — robot account usernames contain `$` which the shell would expand. Never use double quotes.

### Rotating credentials

```bash
kubectl -n <namespace> delete secret harbor-pull-secret
kubectl -n <namespace> create secret docker-registry harbor-pull-secret \
  --docker-server=harbor.example.com \
  --docker-username='robot$project+robot' \
  --docker-password='NEW_TOKEN'
kubectl -n <namespace> rollout restart deployment/<name>
```

Pods scheduled before the secret existed cache the auth failure. Always `rollout restart` after recreating the secret.

## Common failure diagnosis

### ImagePullBackOff / ErrImagePull

```bash
kubectl -n <ns> describe pod <pod> | grep -A 10 "Events:"
```

| Error message | Cause | Fix |
|---------------|-------|-----|
| `401 Unauthorized` | Stale or missing pull secret | Rotate pull secret → rollout restart |
| `repository does not exist` | Wrong image name or project | Check Harbor project name matches image path |
| `no basic auth credentials` | Pod scheduled before secret created | `rollout restart` after creating secret |

### CreateContainerConfigError

Pod image pulled successfully but container won't start — usually a missing `secretKeyRef`:

```bash
kubectl -n <ns> describe pod <pod> | grep -i "secret\|error" | head -20
```

The referenced secret (e.g., `cloudreviewer-buy-secrets`) was lost when the namespace was deleted. Recreate it:

```bash
kubectl -n <ns> create secret generic my-app-secrets \
  --from-literal=key1=value1 \
  --from-literal=key2=value2
```

### Namespace deleted — full apply order

```bash
kubectl apply -f k8s/namespace.yaml
kubectl apply -f k8s/web-deployment.yaml -f k8s/web-service.yaml
kubectl apply -f k8s/buy-deployment.yaml -f k8s/buy-service.yaml
kubectl apply -f k8s/kb-deployment.yaml  -f k8s/kb-service.yaml
kubectl apply -f k8s/ingress.yaml
# Then recreate pull secret and app secrets
```

## Environment variables for Next.js

Required env vars for a standalone Next.js container:

| Variable | Value | Purpose |
|----------|-------|---------|
| `HOSTNAME` | `0.0.0.0` | Bind to all interfaces |
| `NODE_ENV` | `production` | Enables prod optimisations |
| `NEXT_TELEMETRY_DISABLED` | `1` | Disable Next.js telemetry |
| `OTEL_SERVICE_NAME` | app name | OTel trace attribution |
| `OTEL_EXPORTER_OTLP_ENDPOINT` | Tempo/Grafana URL | Trace export |
| `NEXT_PUBLIC_SITE_URL` | `https://www.example.com` | Metadata base URL |

## Multiple kubectl contexts

When managing multiple clusters:

```bash
kubectl config get-contexts          # list
kubectl config use-context sr-k8s   # switch
kubectl config current-context      # verify
```

Always verify context before applying manifests or rotating secrets.

## Example prompts

- *"Our pods are stuck in `ImagePullBackOff`. How do I diagnose and fix this?"*
- *"I rotated the Harbor robot account token. How do I update the pull secret without downtime?"*
- *"Add subdomain `kb.example.com` to the existing Traefik ingress."*
- *"The namespace got accidentally deleted. Walk me through restoring everything in order."*
- *"A pod is in `CreateContainerConfigError`. What does that mean and how do I fix it?"*
- *"Show me a production-ready Next.js Deployment manifest with resource limits and probes."*

## Related skills

- [`nextjs-monorepo-ci`](./nextjs-monorepo-ci/SKILL.md) — CI pipeline that builds and pushes the images this skill deploys
- [`arcgis-enterprise-k8s`](./arcgis-enterprise-k8s/SKILL.md) — deploying a more complex stateful app on Kubernetes

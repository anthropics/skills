# Architecture Diagram Layout

## Flow Direction

Choose one primary direction:
- **Left-to-Right (LTR):** Best for data pipelines, request flows. Users/clients on left, data stores on right.
- **Top-to-Bottom (TTB):** Best for layered architectures. Clients at top, infrastructure at bottom.

## Layout Algorithm

1. **Identify layers:** Group components by role (clients, gateways, services, data, infrastructure)
2. **Assign columns (LTR) or rows (TTB):** One layer per column/row
3. **Within each layer:** Stack components vertically (LTR) or horizontally (TTB), 40px gap minimum
4. **Region boundaries:** Draw around groups that share infrastructure (e.g., "AWS us-east-1", "Kubernetes Cluster")
5. **Connectors:** Route arrows between layers. For buses/queues between layers, place a thin connector bar in the gap.

## Typical Layer Structure (LTR)

```
Col 1 (x=40)     Col 2 (x=250)     Col 3 (x=460)     Col 4 (x=670)
┌──────────┐     ┌──────────┐      ┌──────────┐      ┌──────────┐
│  Client   │────▶│ Gateway  │─────▶│ Services │─────▶│ Database │
│  Layer    │     │  Layer   │      │  Layer   │      │  Layer   │
└──────────┘     └──────────┘      └──────────┘      └──────────┘
```

Column spacing: 200-220px between column starts. Adjust if components are wider.

## Typical Layer Structure (TTB)

```
Row 1 (y=60):   [ Browser ]  [ Mobile App ]  [ API Client ]
Row 2 (y=160):  [         Load Balancer / API Gateway       ]
Row 3 (y=280):  [ Auth Svc ]  [ User Svc ]  [ Order Svc ]
Row 4 (y=400):  [  Redis  ]   [ PostgreSQL ]  [ S3 Bucket ]
```

Row spacing: 120-140px between row starts.

## Connection Routing

- Prefer straight horizontal or vertical lines
- For connections that would cross components, use two-segment (L-shaped) paths:
  ```svg
  <path d="M x1,y1 L midX,y1 L midX,y2" fill="none" stroke="#64748b" marker-end="url(#arrow)"/>
  ```
- For busy diagrams, use `stroke-opacity="0.6"` on less important connections
- Label important connections with a text element near the midpoint

## Message Bus / Event Bus Pattern

When services communicate through a shared bus, draw it as a horizontal bar between the service layer:

```
Services:  [ Svc A ]    [ Svc B ]    [ Svc C ]
              │              │            │
Bus:     ════╪══════════════╪════════════╪═══════
              │              │            │
Data:    [ DB A ]        [ DB B ]     [ Cache ]
```

Use the Connector color (orange) for the bus bar.

## Multi-Region / Multi-Cloud

Nest region boundaries:
- Outer boundary: Cloud provider (AWS, GCP)
- Inner boundary: Region or VPC
- Innermost: Availability zones or subnets

Use different dash patterns to distinguish nesting levels:
- Outer: `stroke-dasharray="12,4"`
- Middle: `stroke-dasharray="8,4"`
- Inner: `stroke-dasharray="4,4"`

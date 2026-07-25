#!/usr/bin/env python3
"""Generate an operational runbook skeleton for a service."""

from __future__ import annotations

import argparse
from datetime import date
from pathlib import Path


def build_runbook(service: str, owner: str, environment: str) -> str:
    today = date.today().isoformat()
    return f"""# Runbook - {service}

- Service: {service}
- Owner: {owner}
- Environment: {environment}
- Last verified: {today}

## Overview

Describe the service purpose, dependencies, and critical user impact.

## Preconditions

- Access to deployment platform
- Access to logs/metrics
- Access to secret/config manager

## Start Procedure

1. Pull latest config/secrets.
2. Start service process.
3. Confirm process is healthy.

```bash
# Example
# systemctl start {service}
```

## Stop Procedure

1. Drain traffic if applicable.
2. Stop service process.
3. Confirm no active workers remain.

```bash
# Example
# systemctl stop {service}
```

## Health Checks

- HTTP health endpoint
- Dependency connectivity checks
- Error-rate and latency checks

```bash
# Example
# curl -sf https://{service}.example.com/health
```

## Deployment Checklist

1. Verify CI status and artifact integrity.
2. Apply migrations (if required) in safe order.
3. Deploy service revision.
4. Run smoke checks.
5. Observe metrics for 10-15 minutes.

## Rollback

1. Identify last known good release.
2. Re-deploy previous version.
3. Re-run health checks.
4. Communicate rollback status to stakeholders.

```bash
# Example
# deployctl rollback --service {service}
```

## Incident Response

1. Classify severity.
2. Contain user impact.
3. Triage likely failing component.
4. Escalate if SLA risk is high.

## Escalation

- L1: On-call engineer
- L2: Service owner ({owner})
- L3: Platform/Engineering leadership

## Post-Incident

1. Write timeline and root cause.
2. Define corrective actions with owners.
3. Update this runbook with missing steps.
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate a markdown runbook skeleton.")
    parser.add_argument("service", help="Service name")
    parser.add_argument("--owner", default="platform-team", help="Service owner label")
    parser.add_argument("--environment", default="production", help="Primary environment")
    parser.add_argument("--output", help="Optional output path (prints to stdout if omitted)")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    markdown = build_runbook(args.service, owner=args.owner, environment=args.environment)

    if args.output:
        path = Path(args.output)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(markdown, encoding="utf-8")
        print(f"Wrote runbook skeleton to {path}")
    else:
        print(markdown)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

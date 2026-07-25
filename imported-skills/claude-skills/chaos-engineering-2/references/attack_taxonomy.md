# Attack taxonomy

7 categories of fault injection. Each tests a different system property. Pick the one whose failure mode matches your hypothesis.

## 1. Latency

**What it tests:** timeouts, retries, circuit breakers, fallback paths.

**Inject:** add N ms of delay to network responses to a target.

**When to use:**
- "What if dependency X is slow?"
- "Are timeouts configured correctly upstream?"
- "Does the retry budget kick in?"

**Tools:**
- Linux `tc` (traffic control) — direct kernel-level shaping
- Chaos Mesh `NetworkChaos` (delay)
- Toxiproxy — proxy-based, language-agnostic
- AWS FIS — `aws:network:traffic-control` action

**Example magnitude:** +200ms (90% of typical timeouts), +2000ms (test backoff), +30s (test giving-up logic).

## 2. Error injection

**What it tests:** error handling paths, fallback behavior, retry policies.

**Inject:** return errors (5xx, exceptions) for a fraction of requests.

**When to use:**
- "What happens when X starts failing?"
- "Does the fallback path actually work in prod?"
- "Are we logging errors correctly?"

**Tools:**
- Chaos Mesh `HTTPChaos`
- Service mesh (Istio, Linkerd) fault injection
- Toxiproxy with error toxic
- Application-level feature flag for synthetic errors

**Example magnitude:** 1% errors (test handler), 50% errors (test retry), 100% errors (test fallback path).

## 3. Resource exhaustion

**What it tests:** saturation handling, autoscaling, OOM behavior, disk-full handling.

**Inject:** consume CPU, memory, or disk on the target.

**When to use:**
- "What if memory leaks?"
- "Does the autoscaler kick in?"
- "What happens when disk fills?"

**Sub-types:**
- **CPU pressure** — peg cores at N% usage
- **Memory pressure** — allocate large blocks
- **Disk fill** — write large files until partition fills
- **I/O saturation** — high random read/write

**Tools:**
- `stress-ng` — CPU/memory/IO/disk
- Chaos Mesh `StressChaos` and `IOChaos`
- AWS FIS `aws:ssm:send-command` with stress-ng

**Example magnitude:** 80% CPU sustained, 90% memory, fill /var to 95%.

## 4. Network partition

**What it tests:** consensus protocols, leader election, split-brain prevention, region failover.

**Inject:** drop all packets between a set of hosts.

**When to use:**
- "What if AZ-A loses connectivity to AZ-B?"
- "Does the database elect a new primary?"
- "Does the cluster avoid split-brain?"

**Tools:**
- Chaos Mesh `NetworkChaos` (partition mode)
- `tc` with iptables drop rules
- AWS FIS `aws:network:disrupt-connectivity`

**Example magnitude:** drop 100% to peer X (full partition), drop 50% (degraded link).

## 5. Dependency failure

**What it tests:** graceful degradation, fallback to cache, fallback to default values.

**Inject:** make a downstream dependency unavailable (timeout, refuse connections).

**When to use:**
- "What if the rec engine goes down?"
- "Does Search degrade gracefully when ML models are unreachable?"
- "Is cache the fallback for the user-pref service?"

**Tools:**
- Service mesh fault injection (most flexible)
- Toxiproxy
- iptables rules to refuse connections
- Chaos Mesh `NetworkChaos` with `corrupt` or `drop`

**Example magnitude:** 100% requests to dep X timeout (full outage), 25% timeout (intermittent), 0% available for 5 min (sustained outage).

## 6. Time skew

**What it tests:** time-sensitive logic — token expiry, cron schedules, TTLs, retry backoff.

**Inject:** alter the wall clock seen by a process.

**When to use:**
- "What if NTP fails?"
- "What if a process clock drifts +5 minutes?"
- "Do tokens correctly fail validation when expired?"
- "Does cron skip or double-fire?"

**Tools:**
- `libfaketime` — preload library
- Chaos Mesh `TimeChaos`
- Custom: change container's `/etc/localtime`

**Example magnitude:** +1 minute (subtle), +5 minutes (TLS / token failures), +1 day (catastrophic for some logic).

**Caution:** time skew can cause cluster-wide consensus failures. Test in isolation first.

## 7. Infrastructure (kill instance / pod / container)

**What it tests:** auto-recovery, failover, replica count maintenance.

**Inject:** terminate an instance, pod, or container.

**When to use:**
- "Does Kubernetes restart the pod?"
- "Does the load balancer remove the instance from rotation?"
- "Is the replication factor maintained?"

**Tools:**
- Chaos Monkey (the original)
- Chaos Mesh `PodChaos` (kill, fail)
- AWS FIS `aws:ec2:terminate-instances`
- `kubectl delete pod` (manual, simplest)

**Example magnitude:** kill 1 of N pods (Chaos Monkey level), kill all pods of a deployment (test recreation), kill 1 of 3 replica DB nodes (test failover).

## Choosing an attack

| Hypothesis pattern | Attack type |
|---|---|
| "What if X is slow?" | Latency |
| "What if X is failing?" | Error |
| "What if we run hot?" | Resource |
| "What if regions partition?" | Network partition |
| "What if dep X is down?" | Dependency failure |
| "What if clocks drift?" | Time skew |
| "What if a node dies?" | Infrastructure |

## Combining attacks

Real outages often combine attacks (e.g., latency + saturation). Once basic experiments are stable, run combinations:

- Latency on dependency + CPU pressure on app → tests timeout + retry budget interaction
- Pod kill + network partition → tests recovery during a partition
- Disk fill + dependency failure → tests fallback path while disk is constrained

Combinations have higher risk; reduce blast radius accordingly.

## Severity ladder

```
S1 — Latency (small)              ← start here
S2 — Error injection (low %)
S3 — Resource pressure (CPU/mem)
S4 — Latency (large) / errors (high %)
S5 — Single instance kill
S6 — Network partition (single peer)
S7 — Multiple instance kill
S8 — Region partition / time skew
S9 — Combinations of S5-S8        ← here be dragons
```

Don't skip levels. Earn confidence at S1-S3 before attempting S5+.

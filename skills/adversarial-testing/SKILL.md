---
name: adversarial-testing
description: Adversarial testing, stress testing, and simulation for any implementation — services, configs, pipelines, scripts, infrastructure. Use when deploying anything non-trivial, stress-testing a service, simulating failure scenarios, red-teaming a design, validating resilience across reboots/crashes/network loss, or when the user asks to "adversarially test", "stress test", "simulate failures", "red team", "what will break", "failure modes", "will this survive a reboot", "chaos test", or wants pre-implementation review. Also trigger when setting up systemd services, cron jobs, Docker containers, or anything that needs to survive real-world conditions. Trigger on "done"/"ship"/"deploy"/"merge" when implementation work is being finalized for production.
---

# Adversarial Testing & Simulation

Structured adversarial review protocol for all non-trivial implementations. Catches wrong IDs, missing edge cases, credential exposure, and failure modes before they bite at 3am.

## When to Use

- Before implementing any non-trivial spec (pre-implementation review)
- After implementing anything that runs unattended (services, crons, pipelines)
- When deploying to a new device or environment
- When the user asks "will this survive X?" or "what will break?"
- Before shipping configs, scripts, or infrastructure changes
- When the user says "done", "ship", "deploy", or "merge" for production work

## Phase 1: Pre-Implementation Review (3 Parallel Passes)

Before writing any code, dispatch 3 adversarial reviewers as parallel subagents. Each has a distinct focus and produces a structured report.

### Pass 1: Correctness & Completeness
- Are all IDs, codes, URLs, paths, ports correct? Cross-reference against known facts.
- Missing sections? Undefined behavior? Ambiguous requirements?
- Do the numbers add up? (e.g., API endpoints, config values, port numbers)
- Are all dependencies accounted for? Version compatibility?

### Pass 2: Security & Attack Surface
- Credential exposure: hardcoded secrets, env vars in logs, world-readable configs?
- Injection vectors: prompt injection, command injection, path traversal?
- Privilege escalation: running as root when unnecessary? Overly broad permissions?
- Data leaks: PII in logs, sensitive data to untrusted providers, unencrypted storage?
- Network exposure: unnecessary open ports, missing firewall rules, unauthenticated endpoints?

### Pass 3: Reliability & Failure Modes
- What breaks under: bad network, DNS failure, API changes, rate limits?
- Empty/null data handling? Oversized inputs? Malformed responses?
- Resource exhaustion: memory leaks, disk fill, file descriptor leaks?
- Recovery: does it resume after crash? Does state survive reboot?
- Concurrency: race conditions, duplicate runs, lock contention?

### Report Format
Each pass produces:
```
## [Pass Name] Review

| # | Issue | Severity | Details |
|---|-------|----------|---------|
| 1 | ... | CRITICAL | ... |
| 2 | ... | HIGH | ... |
| 3 | ... | MEDIUM | ... |

**Verdict:** PASS / FAIL
```

**Gate:** Fix ALL CRITICAL and HIGH issues before proceeding to implementation.

## Phase 2: Post-Implementation Testing (5 Rounds)

After implementation, run 5 test rounds on the actual target device/environment. Each round builds on the previous — don't skip ahead.

### Round 1: Unit Tests
Test each component in isolation. Mock nothing that can be tested live. Verify:
- Each function/service does what it claims
- Config is parsed correctly
- Dependencies are reachable
- Permissions are correct

### Round 2: Integration Test
Full pipeline dry run with no side effects. Verify:
- Data flows end-to-end correctly
- Services communicate as expected
- Startup order is correct (dependencies before dependents)
- Logs capture useful information

### Round 3: Adversarial / Attack Test
Actively try to break it:
- Send malformed input, empty input, oversized input
- Test network interruption (see Simulation Scenarios below — **requires user confirmation**)
- Run two instances simultaneously (race condition check)
- Inject unexpected characters, unicode, null bytes
- If it has a web interface: XSS, CSRF, auth bypass attempts

### Round 4: Edge Case Test
Push the boundaries:
- Empty results from upstream APIs
- Oversized responses (10x normal)
- Non-English/non-ASCII content
- Clock skew, timezone edge cases (midnight, DST transition)
- Disk nearly full, low memory conditions
- Paywalled or rate-limited upstream sources

### Round 5: Endurance Test
Let it run for real over an extended period (not just a few invocations) and verify it holds up:
- Check for: memory growth, log rotation, token/budget exhaustion
- Verify cron/timer/systemd reliability across reboot
- Check that state files don't grow unbounded
- Monitor for resource leaks (file descriptors, connections, temp files)

### Round Report Format
```
## Round N: [Name]

**Tests run:** X
**Passed:** Y / X
**Failed:** Z / X

| Test | Result | Details |
|------|--------|---------|
| ... | PASS/FAIL | ... |

**Verdict:** PASS / NEEDS_FIX
**Blockers:** [list if any]
```

**Gate:** Fix all failures before next round. After Round 5 PASS, the implementation is cleared.

## Simulation Scenarios

For infrastructure (systemd services, cron jobs, Docker containers), always simulate these.

**STOP: Every scenario below is destructive. Get explicit user confirmation before executing any of them.** These are reference patterns, not commands to run autonomously.

### Reboot Survival
```bash
# REQUIRES USER CONFIRMATION — will restart the device
sudo systemctl reboot
# After reboot: check service status, logs, data integrity
```

### Process Crash Recovery
```bash
# REQUIRES USER CONFIRMATION — use exact PID, never broad pgrep -f patterns
# First identify the exact PID:
systemctl show <service> --property=MainPID
# Then kill specifically:
kill -9 <exact_pid>
# Verify: does it restart? Is state consistent? Any data loss?
```

### Dependency Failure
```bash
# REQUIRES USER CONFIRMATION — will stop a running service
sudo systemctl stop <dependency>
# Check: does the service hang? crash? retry? log the issue?
sudo systemctl start <dependency>
# Check: does it recover automatically?
```

### Resource Pressure
```bash
# REQUIRES USER CONFIRMATION
# Memory pressure
stress-ng --vm 2 --vm-bytes 80% -t 30s &
# Check: does the service survive? OOM-killed?

# Disk pressure — use a fixed size, NOT a percentage
fallocate -l 4G /tmp/disk-pressure-test.tmp
# Check: does it handle disk-full gracefully?
rm /tmp/disk-pressure-test.tmp
```

### Network Partition
```bash
# REQUIRES USER CONFIRMATION — will sever ALL outbound connections
# WARNING: On remote devices via SSH, this will lock you out until timeout
sudo iptables -A OUTPUT -j DROP
sleep 30
sudo iptables -D OUTPUT -j DROP
# Check: does it reconnect? Retry? Queue work?
```

## Environment-Specific Considerations

When testing on different platforms, verify platform-specific concerns:

- **Linux (systemd):** Check CPU temp after endurance, check for throttling, verify RAM with `free -h`, check journal for errors
- **Immutable Linux (ostree/Bazzite):** Everything in `/home`, containers not native packages, systemd user services with linger
- **macOS:** Check if Docker uses Colima or Docker Desktop (affects paths), Homebrew services vs LaunchAgents
- **Windows:** Use `cmd.exe /c "..."` for native commands, check if inbound TCP is blocked, PowerShell vs cmd syntax differences
- **Containers (Docker/Podman):** Check volume mounts survive container recreation, verify health checks, test restart policies

## Remote Testing via SSH

When running post-implementation tests on remote devices:
- If SSH to target fails (device rebooting, IP changed, network issue), **document the failure** in the test report
- Simulate locally with the same commands where possible
- Flag the test result as `SIMULATED — not verified on target hardware`
- Retry SSH after a reasonable interval (60s for reboot)

## Integration with Parallel Subagents

When running pre-implementation reviews, dispatch the 3 passes as parallel subagents. Each reviewer should be a focused agent with a single mandate — don't bundle concerns.

For post-implementation testing, prefer running tests on the actual target environment rather than simulating locally.

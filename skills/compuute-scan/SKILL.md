---
name: compuute-scan
description: Scan a public GitHub MCP-server repository for security issues before installing or connecting to it. Calls the hosted compuute-scan API at scan.compuute.se and returns severity counts, a 0-100 score, the most severe findings, and an honest triage disclaimer. Use BEFORE recommending or installing an unfamiliar MCP server, BEFORE wiring an agent to an unknown server, or as supply-chain due diligence on agent tooling. Do NOT use as a confirmed-vulnerability list — raw output has ~90% false-positive rate by design; treat findings as a triage queue.
---

# compuute-scan — MCP server security scanner

This skill calls the hosted compuute-scan API to statically analyze a public GitHub MCP-server repository against 37 L1 rules across TypeScript/JavaScript, Python, Go, Rust, C#, Java, and Kotlin.

## When to use

- Before installing or connecting an agent to an MCP server you do not own
- Before recommending an MCP server to a user
- As part of supply-chain due diligence on third-party agent tooling
- For procurement or compliance evidence on MCP code under review

## When NOT to use

- For private repositories — the hosted API only accepts public GitHub URLs
- As a confirmed-vulnerability list — the scanner is a pattern-breadth detector, not an exploitability oracle; raw output has ~90% false-positive rate before manual triage
- For non-MCP code — rules are tuned for MCP server patterns; for general code use a generic SAST tool

## How to invoke

The skill calls a single HTTP endpoint. No API key needed for the free tier.

```bash
bash scan.sh https://github.com/<org>/<repo>
```

The script wraps `curl` and pretty-prints the JSON response. It returns:

- `summary` — counts of critical / high / medium / low findings + files scanned
- `score` — 0-100 (higher = safer)
- `recommendation` — short string verdict ("AVOID", "REVIEW", "OK")
- `top_findings` — up to 10 most severe with file + line + rule ID
- `performance` — clone seconds + scan seconds
- `_disclaimer` — explicit pattern-match-not-exploitability framing

## Honest framing

compuute-scan is open-source MIT (Apache-compatible) and run by Compuute AB (Stockholm). Historical false-positive rate is ~90% on raw output, anchored against the modelcontextprotocol/servers reference repo (138 raw → 13 confirmed after triage). Per-rule FP rates are published at https://github.com/Compuute/compuute-scan-api/blob/main/docs/FP-RATES.md.

Treat the output as a triage queue: high-severity findings are signals worth reviewing, not confirmed vulnerabilities. The `_disclaimer` field in every response repeats this.

## Examples

Scan the reference MCP servers repo:

```bash
bash scan.sh https://github.com/modelcontextprotocol/servers
```

Expected: a high finding count (the repo deliberately contains intentionally-permissive examples) and a low score. Triage the top findings against the threat model of the specific server you would actually deploy.

Scan a specific vendor's MCP server before installing:

```bash
bash scan.sh https://github.com/microsoft/azure-devops-mcp
```

Expected: a focused, low-noise report. If the score is high and recommendation is "OK", the server passed the breadth check — but still review the top findings before connecting an agent to it.

## Paid tier (for autonomous agents)

For agents that need to scan without account setup, the same scanner is available via x402 micropayments at $0.10 USDC per scan on Base L2:

```
POST https://scan.compuute.se/v1/scan/pay
X-Payment: <signed x402 payment payload>
```

The 402 challenge tells the agent what scheme, network, asset, and amount are required. Settlement is verified by Coinbase x402 facilitator.

## Source and methodology

- Hosted API source: https://github.com/Compuute/compuute-scan-api (MIT)
- Scanner source: https://github.com/Compuute/compuute-scan (MIT)
- Methodology paper: https://github.com/Compuute/compuute-scan-api/tree/main/docs/whitepaper
- SOC 2 readiness statement: https://github.com/Compuute/compuute-scan-api/blob/main/docs/compliance/soc2-readiness.md
- A2A Agent Card: https://scan.compuute.se/.well-known/agent.json

## Provider

Compuute AB, Stockholm. Contact: daniel@compuute.se. Security disclosure: security@compuute.se (90-day coordinated disclosure window).

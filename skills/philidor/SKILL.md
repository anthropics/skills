---
name: philidor
description: >
  DeFi vault intelligence: risk scores, yield comparison, portfolio analysis,
  and oracle monitoring across Morpho, Yearn, Aave, Beefy, and Spark.
  Use when the user wants to find safe DeFi vaults, compare yields,
  check vault risk scores, analyze a wallet's DeFi positions, search for
  yield opportunities, monitor oracle freshness, or get DeFi market overview stats.
  Covers Ethereum, Base, Arbitrum, Polygon, Optimism, and Avalanche.
---

# Philidor — DeFi Vault Intelligence

Philidor is a CLI and API for institutional-grade DeFi risk analysis. It provides risk scores, yield data, portfolio analysis, and oracle monitoring across major DeFi protocols (Morpho, Yearn, Aave, Beefy, Spark) and chains (Ethereum, Base, Arbitrum, Polygon, Optimism, Avalanche).

## Quick Start

**Install:**

```bash
npm install -g @philidorlabs/cli
```

No API key is required. The CLI uses the public API at `api.philidor.io`.

**Try these commands:**

```bash
# Market overview — total TVL, vault count, risk distribution
philidor stats

# Search for USDC vaults
philidor search "USDC"

# Analyze a wallet's DeFi positions
philidor portfolio 0xYourAddress

# Find the safest vaults
philidor safest

# Get full detail on a specific vault
philidor vault morpho-ethereum-0x...
```

---

## Core Concepts

### Risk Tiers

Every vault receives a risk score from 0 to 10. The score maps to a tier:

| Tier   | Score Range | Meaning                                                   |
|--------|-------------|-----------------------------------------------------------|
| Prime  | 8.0 -- 10.0 | Highest confidence. Battle-tested protocols, blue-chip assets, strong governance. |
| Core   | 5.0 -- 7.9  | Solid fundamentals with moderate risk factors.             |
| Edge   | 0.0 -- 4.9  | Higher risk. Newer protocols, exotic assets, or weaker controls. |

### Risk Vectors

The total score is a weighted composite of three vectors:

| Vector              | Weight | What It Measures                                          |
|---------------------|--------|-----------------------------------------------------------|
| Asset Composition   | 40%    | Underlying asset quality, liquidity depth, oracle reliability. |
| Platform & Strategy | 40%    | Protocol maturity, audit coverage, code quality, strategy complexity. |
| Control             | 20%    | Governance structure, admin key risk, timelock presence, upgradeability. |

### APR Convention

All APR values are stored and returned as **decimals**:

- `0.05` = 5%
- `0.12` = 12%
- `apr_net` = total APR (base yield + incentive rewards)
- `base_apr` = native protocol yield only (lending rate, share price accrual)
- Invariant: `apr_net = base_apr + SUM(reward APRs)`

---

## Commands

### Safest Vaults

Find the highest-scored, audited vaults with optional filters.

```bash
philidor safest
philidor safest --asset USDC
philidor safest --chain Ethereum
philidor safest --min-tvl 10000000
philidor safest --asset WETH --chain Base --min-tvl 1000000
```

### Vault Screening

Use preset screens for common allocation strategies.

```bash
philidor screen conservative       # Prime tier, high TVL, audited
philidor screen balanced            # Core+ tier, diversified
philidor screen aggressive          # Higher APR, accepts Edge tier
philidor screen stablecoin-yield    # Stablecoin vaults sorted by APR
philidor screen blue-chip           # WETH/WBTC vaults, Prime/Core only
```

### Discovery

Browse and search across all indexed vaults.

```bash
philidor vaults
philidor vaults --chain Ethereum --asset USDC
philidor vaults --protocol morpho --min-tvl 5000000
philidor vaults --sort apr_net --order desc --limit 20

philidor search "steakhouse USDC"
philidor search "Gauntlet"
philidor search "yearn WETH"
```

### Vault Detail

Get full information on a single vault by ID or by network + address.

```bash
# By vault ID
philidor vault morpho-ethereum-0xABC123

# By network and address
philidor vault ethereum 0xABC123

# With extra sections
philidor vault ethereum 0xABC123 --events      # Recent vault events
philidor vault ethereum 0xABC123 --markets      # Market allocations (Morpho)
philidor vault ethereum 0xABC123 --strategies   # Sub-strategies (Yearn)
philidor vault ethereum 0xABC123 --rewards      # Reward token breakdown
```

### Portfolio

Analyze a wallet address's DeFi vault positions.

```bash
philidor portfolio 0xYourAddress
philidor portfolio 0xYourAddress --chain Ethereum
philidor portfolio 0xYourAddress --json
```

Returns each position with vault name, deposited value, current APR, risk tier, and risk score.

### Compare and Risk

Compare vaults side by side and drill into risk details.

```bash
# Compare two vaults
philidor compare morpho-ethereum-0xAAA morpho-ethereum-0xBBB

# Full risk vector breakdown
philidor risk breakdown morpho-ethereum-0xAAA

# Explain what a specific score means
philidor risk explain
philidor risk explain --score 7.5

# List vaults with recent critical incidents
philidor risk incidents
```

### Reference Data

Query protocols, curators, chains, assets, and system health.

```bash
philidor protocols                   # List all indexed protocols
philidor protocol morpho             # Detail for a specific protocol
philidor protocol aave-v3            # Includes TVL, audit history, incidents

philidor curators                    # List vault curators
philidor curator steakhouse          # Curator detail with managed vaults

philidor stats                       # Market overview (TVL, counts, distribution)
philidor chains                      # Supported chains
philidor assets                      # Indexed assets

philidor oracles freshness           # Oracle feed staleness across chains
```

### Output Formatting

Control how results are displayed.

```bash
philidor vaults --json               # Raw JSON output
philidor vaults --table              # Tabular format (default)
philidor vaults --csv                # CSV for spreadsheets
philidor vaults --select name,apr_net,total_score   # Pick specific fields
philidor vaults --results-only       # Omit metadata, return data array only
```

---

## Agent Workflows

These multi-step workflows show how to chain commands for common analysis tasks.

### Workflow 1: Find the Best Vault for a Given Asset

1. **Search** for candidate vaults:
   ```bash
   philidor search "USDC" --sort apr_net --order desc --limit 10
   ```
2. **Compare** the top candidates:
   ```bash
   philidor compare <vault-id-1> <vault-id-2>
   ```
3. **Drill into risk** for the leading candidate:
   ```bash
   philidor risk breakdown <vault-id>
   ```
4. **Check recent events** for any red flags:
   ```bash
   philidor vault <vault-id> --events
   ```

### Workflow 2: Compare Protocols

1. **List protocols** and pick two to compare:
   ```bash
   philidor protocols
   ```
2. **Get vaults per protocol**:
   ```bash
   philidor vaults --protocol morpho --sort tvl_usd --order desc --limit 5
   philidor vaults --protocol aave-v3 --sort tvl_usd --order desc --limit 5
   ```
3. **Compare top vaults** across protocols:
   ```bash
   philidor compare <morpho-vault-id> <aave-vault-id>
   ```
4. **Review protocol detail** (audit history, incidents):
   ```bash
   philidor protocol morpho
   philidor protocol aave-v3
   ```

### Workflow 3: Portfolio Risk Analysis

1. **Load portfolio** positions:
   ```bash
   philidor portfolio 0xAddress
   ```
2. **Identify Edge-tier positions** (risk score < 5.0) from the output.
3. **Get risk breakdown** for each risky position:
   ```bash
   philidor risk breakdown <edge-vault-id>
   ```
4. **Find safer alternatives** for the same asset:
   ```bash
   philidor safest --asset <asset-symbol>
   ```

### Workflow 4: Monitor Safety

1. **Check for recent incidents** across all indexed vaults:
   ```bash
   philidor risk incidents
   ```
2. **Verify oracle freshness** — stale oracles are a leading indicator of risk:
   ```bash
   philidor oracles freshness
   ```
3. **Review events** on vaults you hold or are monitoring:
   ```bash
   philidor vault <vault-id> --events
   ```

---

## Output Interpretation

Key fields returned by vault queries:

| Field            | Type    | Description                                                        |
|------------------|---------|--------------------------------------------------------------------|
| `apr_net`        | decimal | Total APR including base yield and incentive rewards. `0.05` = 5%. |
| `base_apr`       | decimal | Native protocol yield only, before rewards.                        |
| `tvl_usd`        | number  | Total value locked in USD.                                         |
| `total_score`    | number  | Composite risk score, 0--10. Higher is safer.                      |
| `risk_tier`      | string  | `Prime`, `Core`, or `Edge`.                                        |
| `risk_vectors`   | object  | Breakdown: `asset_composition`, `platform_strategy`, `control`.    |
| `is_audited`     | boolean | Whether the vault's protocol has been audited.                     |
| `last_synced_at` | ISO8601 | When Philidor last refreshed this vault's data.                    |
| `rewards`        | array   | Incentive reward tokens with individual APRs and types.            |

**Reward types:**

- `token_incentive` — protocol token rewards (MORPHO, ARB, SPK)
- `points` — points-based incentive programs
- `trading_fee` — LP trading fee revenue
- `strategy` — yield from sub-strategies (Yearn)

---

## Error Handling

The CLI uses standard exit codes:

| Exit Code | Meaning                                            |
|-----------|-----------------------------------------------------|
| 0         | Success.                                           |
| 1         | General error (invalid arguments, unknown command).|
| 2         | Network error (API unreachable, timeout).           |
| 3         | Vault not found.                                   |
| 4         | Invalid address format.                            |
| 5         | Rate limited — wait and retry.                     |

**Common errors and fixes:**

| Error Message                     | Fix                                                        |
|-----------------------------------|-------------------------------------------------------------|
| `Vault not found`                 | Verify the vault ID or address. Use `philidor search` to find it. |
| `Invalid address`                 | Ensure the address is a valid 0x-prefixed hex string (42 chars). |
| `Network error`                   | Check connectivity. The API is at `api.philidor.io` (HTTPS). |
| `Rate limited`                    | Wait 60 seconds and retry. Avoid tight loops.              |
| `No results`                      | Broaden filters. Remove `--chain` or `--min-tvl` constraints. |

---

## Best Practices

1. **Use `--json` for programmatic consumption.** Tabular output is for human review; JSON is stable and machine-parseable.

2. **Always check risk before recommending a vault.** Never suggest a vault based on APR alone. Run `philidor risk breakdown <id>` and review all three vectors.

3. **Note sync timestamps.** The `last_synced_at` field tells you how fresh the data is. Data older than 24 hours may be stale — flag this to the user.

4. **Cross-reference incidents.** Before recommending any vault, run `philidor risk incidents` to check whether its protocol has had recent critical events.

5. **Combine safest + compare for allocation decisions.** Use `philidor safest --asset X` to get candidates, then `philidor compare` to evaluate tradeoffs between APR and risk.

6. **Filter by TVL for institutional use.** Use `--min-tvl 1000000` (or higher) to exclude low-liquidity vaults that may have exit risk.

7. **Prefer Prime and Core tiers for conservative recommendations.** Only suggest Edge-tier vaults when the user explicitly accepts higher risk.

8. **Explain APR decomposition.** When presenting yields, break down `apr_net` into `base_apr` + individual reward APRs so users understand what is sustainable yield versus temporary incentives.

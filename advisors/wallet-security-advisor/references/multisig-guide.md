# Multisig Security Guide

## What is Multisig?

A multisignature (multisig) wallet requires multiple private keys to authorize transactions. Common configurations:
- **2-of-3**: 2 signatures needed from 3 possible signers
- **3-of-5**: 3 signatures needed from 5 possible signers
- **4-of-7**: 4 signatures needed from 7 possible signers

## When to Use Multisig

- Protocol treasuries and DAOs
- Business accounts with shared control
- High-value personal holdings (>$100K)
- Any situation requiring checks and balances

## Threshold Selection

| Team Size | Recommended | Rationale |
|-----------|-------------|-----------|
| 2-3 people | 2-of-3 | Balance security and availability |
| 4-6 people | 3-of-5 | Prevents single point of failure |
| 7+ people | 4-of-7 or 5-of-9 | Higher security, plan for unavailability |

**Key principle**: Threshold should be >50% of signers to prevent minority takeover.

## Signer Requirements

Each signer should:
- Use a dedicated hardware wallet (Ledger, Trezor)
- Store seed phrase securely and separately
- Never share signing devices
- Verify transactions independently before signing
- Use secure communication channels for coordination

## Transaction Verification Checklist

Before signing any multisig transaction:
1. Verify the request came through official channels
2. Confirm the recipient address matches expected
3. Check the amount and token are correct
4. For contract calls, understand the function being called
5. Verify on hardware wallet screen, not just web UI
6. If anything seems off, STOP and verify with other signers

## Common Multisig Platforms

### Safe (formerly Gnosis Safe)
- Most widely used on EVM chains
- Web interface at app.safe.global
- Supports hardware wallet signing
- Transaction simulation before execution

### Squads
- Native Solana multisig
- Similar security model to Safe
- Integrates with Solana ecosystem

## Emergency Procedures

If a signer's keys are compromised:
1. Do NOT alert the compromised party
2. Coordinate remaining signers immediately
3. Remove compromised signer address
4. Add replacement signer
5. Consider rotating all signers if breach scope unclear

## Backup and Recovery

- Document all signer addresses and thresholds
- Store documentation separately from seeds
- Have a succession plan if signers become unavailable
- Test recovery procedures periodically

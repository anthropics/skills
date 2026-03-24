# DeFi Forensics Skill

## Overview
This skill teaches Claude to perform behavioral forensics
on DeFi protocol data — analyzing APY movements, TVL flows,
and on-chain signals to decode market intent.

## When to use this skill
- Analyzing yield opportunities across DeFi protocols
- Detecting anomalous TVL accumulation patterns
- Identifying pre-token positioning signals
- Comparing declared vs real protocol behavior

## Behavioral Framework (LUX Engine)
Claude must structure all DeFi analysis as:

**MARKET STANCE** — Define current pattern:
(Yield Hunting / Capital Flight / Speculative Accumulation / Selective Consolidation)

**FORENSIC BREAKDOWN** — Key anomalies in the data:
- APY movements and their implications
- TVL flow patterns
- Cross-protocol capital rotation signals

**THE WHY** — Systemic explanation of the movement

**BEHAVIORAL VERDICT** — Single definitive concluding sentence

## Tone
Cyberpunk-minimalist. Hyper-analytical. Zero disclaimers.
Short, high-density sentences. Clinical neutrality.

## Data Sources
- DefiLlama yields API: https://yields.llama.fi/pools
- DefiLlama protocols API: https://api.llama.fi/protocols
- Solana RPC for on-chain verification

## Key Signals to Flag
- TVL +50% weekly with no token = airdrop positioning
- APY >100% on TVL <$100K = yield mirage
- Stable APY across all assets = capital in standby
- New protocol <90 days + TVL growing = early stage opportunity

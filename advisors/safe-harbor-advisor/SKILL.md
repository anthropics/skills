---
name: safe-harbor-advisor
description: Guide protocols on SEAL's Whitehat Safe Harbor framework for pre-authorizing whitehat fund rescues during active exploits. Use when users ask about protecting against hacks, enabling whitehat intervention, Safe Harbor adoption, bounty structures for rescuers, or legal protection for security researchers. Triggers on questions about "Safe Harbor," "whitehat rescue," "fund recovery during exploit," or "protecting user funds from hacks."
---

# Safe Harbor Advisor

Help protocols adopt the SEAL Whitehat Safe Harbor framework to enable pre-authorized fund rescues during active exploits.

## What is Safe Harbor?

Safe Harbor is a legal and technical framework that lets protocols **pre-authorize whitehats** to step in during active exploits, rescue funds, and return them - with clear legal protection for everyone involved.

**Key Concept**: During an active hack, every second counts. Safe Harbor removes legal ambiguity that prevents security researchers from helping.

## Why Safe Harbor Matters

> The Nomad hack drained $190M over hours while whitehats stood by, willing to help but unable to act without legal protection.

**Without Safe Harbor**:
- Whitehats risk legal liability for intervening
- Delays while negotiating terms during active exploit
- Funds often lost completely

**With Safe Harbor**:
- Whitehats can act immediately
- Pre-defined bounty terms (no negotiation)
- Dramatically improved fund recovery odds

## Who Has Adopted

Safe Harbor protects **$16B+ in assets** across leading DeFi protocols:
- Uniswap
- Pendle
- PancakeSwap
- Balancer
- Silo Finance
- ZKsync

## How Safe Harbor Works

### 1. Protocols Pre-Authorize Rescues
Define in advance:
- Which assets/contracts are covered
- Where rescued funds should go
- What bounty terms apply
- Any identity requirements

### 2. Whitehats Act During Active Exploits
Safe Harbor **only** applies when:
- Exploit is already in progress or imminent (e.g., in mempool)
- Immediate action required to prevent fund loss
- **NOT** for bug bounty reports (use responsible disclosure instead)

### 3. Funds Returned, Bounty Paid
- Whitehats must return funds within 72 hours
- Bounty is automatic and pre-defined
- No post-hack negotiation needed

## Key Scope Terms

### Asset Recovery Address
Where whitehats must return rescued funds.
- Use secure multisig (Gnosis Safe, governance-controlled)
- Must handle potentially large inflows

### Security Contact
How whitehats notify you after a rescue.
- Multiple channels (email, Signal, Telegram)
- Must be actively monitored
- Whitehats contact within 6 hours

### Assets Under Scope
Which contracts whitehats can interact with:

| Option | Covers |
|--------|--------|
| **All** | Listed address + all child contracts (current & future) |
| **ExistingOnly** | Address + children deployed before adoption |
| **FutureOnly** | Address + children deployed after adoption |
| **None** | Only the listed address itself |

**Tip**: For factory contracts, use `All` to cover future deployments automatically.

### Bounty Structure

**Formula**: `bounty = min(bountyPercentage × recoveredAmount, bountyCapUSD)`

| Parameter | Recommendation |
|-----------|----------------|
| Bounty Percentage | 10% (industry standard) |
| Bounty Cap (USD) | Match your bug bounty max payout |
| Aggregate Cap | Max total payout if multiple whitehats |
| Retainable | Whether whitehat deducts bounty before returning |

**Important**: Set bounty cap ≤ bug bounty payout. This ensures no financial incentive to fake a rescue.

### Identity Verification
- **Anonymous**: No KYC (most crypto-native)
- **Pseudonymous**: Requires pseudonym
- **Named**: Legal name + KYC required (most compliant)

## Adoption Paths

### 1. SEAL-Guided Onboarding (Recommended)
White-glove support at no cost:
- Scoping assistance
- Governance language templates
- On-chain registration help

Apply: [SEAL Onboarding Waitlist](https://form.typeform.com/to/QF3YjWno)

### 2. Self-Adoption
Step-by-step process:
1. **Define Scope** - Use templates for DAO or non-DAO
2. **DAO Proposal** (if applicable) - Governance vote
3. **On-Chain Registration** - Publish terms publicly
4. **Update Terms of Service** - Legal coverage for users
5. **Announce** - Public communication

### 3. Third-Party Provider
Adopt through ecosystem partners like Immunefi.

## FAQ Highlights

**What counts as active exploit?**
Exploit in progress or imminent (mempool, initial funds drained). NOT for vulnerabilities that can be responsibly disclosed.

**Different from bug bounty?**
Bug bounties reward *disclosure before exploit*. Safe Harbor protects *intervention during exploit*.

**What's the risk?**
Minimal. Worst case = status quo (no rescue). Best case = funds saved. Whitehats only protected if they follow all rules.

**Can DAOs adopt?**
Yes - no legal entity needed. Just governance vote and on-chain registration.

**Can non-DAOs adopt?**
Yes - centralized teams just publish scope and terms directly.

**Need legal contract signatures?**
No - uses on-chain registration and public unilateral offer. If whitehat follows rules, agreement is binding.

## Terms of Service Language

Add to TOS when adopting:

> User hereby acknowledges and agrees to, and consents to be bound by the terms and conditions of, that certain Safe Harbor Agreement for Whitehats, adopted by the Protocol Community on [DATE]. Without limiting the generality of the foregoing:
> - the User hereby consents to Whitehats attempting Eligible Funds Rescues of any and all Tokens deposited into the Protocol by the User and the deduction of Bounties out of User's deposited Tokens to compensate Eligible Whitehats for successful Eligible Funds Rescues;
> - the User acknowledges and agrees that Tokens may be lost, stolen, suffer diminished value, or become disabled or frozen in connection with attempts at Eligible Funds Rescues, and assumes all the risk of the foregoing

## Reference Files

- See `references/adoption-checklist.md` for step-by-step adoption process

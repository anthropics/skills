          } from "../../../components";

# Guide: Large Cryptocurrency Transfers

## Core Principles

Large cryptocurrency transfers require rigorous verification because transactions are irreversible. This guide covers both receiving and sending significant amounts, with security measures scaling to transfer size.

## Part 1: Receiving Large Transfers

### Pre-Transfer Setup (48 Hours Before)

#### Choose Appropriate Deposit Address

The address strategy depends on your custody model:

**For Institutional Custody** (Coinbase, Anchorage, BitGo):

- **Always generate a fresh deposit address** for large incoming transfers
- **Verify you're on the correct website** - check URL carefully, bookmark the official site, watch for phishing lookalikes
- Use the platform's "offline deposit address" or "new address" function
- **Why fresh addresses?** Prevents counterparties from viewing your entire treasury balance/history and isolates each major transfer for clean audit trails

**For Self-Custody Multisigs**:

- **Use your established, proven multisig address** that has been successfully tested in prior transactions
- **Never generate a fresh multisig for large transfers** - multisig setup is complex and a new deployment risks misconfiguration
- The battle-tested multisig you've been using is safer than a newly created one
- Document the multisig configuration: threshold (e.g., 3-of-5), signer addresses, and deployment transaction
- Verify multisig configuration on block explorer before providing address to sender

#### Address Verification Protocol

Have 2-3 team members independently verify the address:

```
1. Retrieve address from custody platform or multisig interface
2. Person A: Verify via custody UI or block explorer (multisig configuration)
3. Person B: Independently verify via separate block explorer or multisig interface
4. Perform checksum validation:
   - Ethereum: EIP-55 checksum
   - Bitcoin: Bech32 checksum
5. For multisigs: Verify threshold and signer configuration match expected setup
```

**For transfers >$1M**: Require all verifiers to sign a document confirming they verified the address character-by-character.

#### Bidirectional Test Transaction

This should occur **24-48 hours before the main transfer**.

**Phase 1: Sender → You (Incoming Test)**

```
1. Sender sends small amount (0.001 ETH or 0.0001 BTC) to your new address
2. Verify receipt through multiple sources:
   - Custody platform interface
   - Primary block explorer (Etherscan, Blockchain.com)
   - Secondary block explorer (redundancy check)
3. Document transaction hash and confirmation time
```

**Phase 2: You → Sender (Outgoing Test)**

```
4. Send test amount BACK to another address you control
5. You confirm you received the return transaction
```

**Why bidirectional?** Proves address can both receive AND withdraw funds before large transfer arrives, and confirms both parties control their stated addresses.

#### Coordinate with Sender

Provide via encrypted channel (PGP email or Signal):

- Deposit address
- Network specification (Ethereum mainnet chain ID 1, Bitcoin mainnet)
- Test transaction hash (incoming only)
- Video call scheduled time for live transfer

Request from sender:

- Source wallet addresses they'll send from
- Approximate transfer timing: specific date and time window
  - Example: "Tuesday, March 15th, 2:00-6:00 PM EST"
  - This allows you to have all required personnel available and monitoring
- Whether they'll use single or multiple transactions

**Best practices for transaction splitting:**

- **\<$10M**: Single transaction preferred (simpler, one confirmation cycle, cleaner records)
- **\>$10M**: Consider 2-3 separate transactions (reduces single-transaction risk, allows staged confirmation, provides pause points to verify each step)
- **\>$50M**: Multiple transactions strongly recommended with 30-minute intervals between each
**Anti-Duress Protocols:**

Since kidnapping and other forms of duress have been employed by criminals to steal cryptocurrency, organizations should prepare for this. Establish a duress word that indicates a transfer is not being made of your own free will. Once the duress word is mentioned during an exchange involving the transfer, law enforcement will be contacted and the transaction not processed. Procedures should be put in place with concrete run books for these situations. Safe words should not appear in run books or any digital format.
**Anti-Social-Engineering Protocols:**

Establish code phrase during initial verified meeting. Use this phrase to authenticate any address changes or unusual requests. Example: "What was the name of the restaurant where we finalized the agreement?" Exchange secondary contact numbers for key personnel - if primary contact requests changes, call secondary to confirm. Maintain out-of-band verification: if request comes via email, confirm via phone.

**Red flags that should trigger immediate verification:**

- Urgent requests to bypass procedures or claims of "emergency"
- Requests to send to "temporary" or "new" address without proper verification
- Pressure to skip test transactions or any rushed requests

If anything feels wrong, STOP and verify through multiple channels. Urgency is an attacker's favorite tool - legitimate counterparties will understand security delays.

### Day of Transfer

#### Pre-Transfer Video Verification (30 minutes prior to transfer)

Require video call with minimum 2 _internal_ people present.

**Liveness and identity verification** (prevents AI deepfakes):

```
1. Ask participant to hold up specific number of fingers (change unpredictably)
2. Ask them to wave their hand in front of their face
3. Request they state current date and time
4. Reference specific details from previous conversations only real participant would know
5. If anything seems off, halt the transfer and investigate
```

**Critical confirmations during call:**

1. **Address Reconfirmation**

   - Read deposit address character-by-character from your screen
   - Sender confirms they see identical address on their screen
   - **Critical: "Read ONLY from your custody platform or multisig interface (Safe, Zodiac, etc.)"**
   - **Do NOT copy from email, Etherscan, any block explorer, or any intermediary source**
   - **Only trust the address shown directly in your custody interface or multisig platform**
   - For multisigs: State the configuration (e.g., "3-of-5 multisig at address 0x...")
   - This prevents compromised email, address poisoning, and man-in-the-middle attacks from causing misdirection

2. **Test Transaction Review**

   - Display test transaction on block explorer during call
   - Confirm sender sees same transaction hash
   - Review the bidirectional test from 24-48 hours ago

3. **Amount and Network**
   - State total amount in native units and USD equivalent
   - Confirm network explicitly: "Ethereum mainnet, chain ID 1" (not testnet, not L2)
   - If ERC-20 tokens: State token name AND read out full contract address
     - Example: "Sending 100,000 USDC, contract address 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"
     - Verify contract address against official source (token website, CoinGecko) on call
   - Confirm no mistakes in decimal places or token contract

#### Live Monitoring

**Understanding Blockchain Finality:**

Wait for enough confirmations that a chain reorganization becomes economically infeasible or cryptographically impossible.

**Monitoring phases:**

```
1. Transaction Broadcast: Appears in mempool, verify correct parameters
2. First Confirmation: Included in a block
3. Progressive Confirmations: Each block makes reversal exponentially harder
4. Finality: Sufficient confirmations reached, transaction irreversible
```

**Confirmation requirements by chain:**

- **Ethereum**: 2 epochs (~12.8 minutes)
- **Bitcoin**: 6 confirmations (~60 minutes)
- **Polygon**: 128 confirmations (~5 minutes)
- **Solana**: ~12.8 seconds

**On-call updates from Technical Operator:**

- "Transaction in mempool, parameters correct"
- "Block 1 confirmed, no anomalies"
- "Block 12 confirmed, [X.XXX] ETH received and final"

#### Dual Confirmation Requirement

Before ending call, verify through TWO sources:

1. Custody platform showing updated balance
2. Block explorer showing confirmed transaction

#### Post-Receipt Actions

**Immediate (within 15 min):**

- Document transaction hash, block number, timestamp
- Record amount in native units and USD equivalent
- Note all personnel involved

**Within 30 minutes:**

- Email confirmation to sender with transaction details

## Part 2: Sending Large Cryptocurrency Transfers

### Pre-Transfer Planning (72 Hours Before)

#### Authorization

Document and obtain approvals:

- Purpose of transfer
- Recipient verification
- Amount and timeline
- Required signatures based on amount:
  - \<$100K: Treasury Manager
  - $100K-$1M: CFO + Security Officer
  - \>$1M: CFO + CEO

#### Recipient Address Verification

Multi-source verification is critical:

```
STEP 1: Receive address through official channel
├─> Request via verified email/signed contract

STEP 2: Independent verification through multiple sources (e.g., email, phone call)
├─> At least two team members independently confirm the recipient address using different communication channels (such as verified email and a direct phone call with the recipient)

STEP 3: Mandatory test transaction
├─> Send $10-100 equivalent first
├─> Wait for recipient confirmation
├─> Recipient provides test transaction hash
├─> Verify hash matches your outbound transaction
└─> Proves recipient controls address and communications secure
```

**Never skip the test transaction.**

#### Whitelist Addition (If Using Custody Platform)

Most custody platforms support whitelisting:

```
1. Submit whitelist request with justification
2. Wait mandatory cooling-off period:
   - Standard: 24-48 hours
   - High security: 72 hours
3. Different team member approves whitelist addition
4. Test transaction AFTER whitelist approval
```

**Why cooling-off periods?** Prevents attackers who gain account access from immediately adding malicious addresses and draining funds. Gives time for legitimate personnel to notice unauthorized changes.

### Day of Transfer

#### Final Verification Checklist (15 min before)

Minimum 2 _internal_ people present, verify:

```
□ Authorization documentation signed
□ Recipient address verified by 2 independent sources
□ Test transaction confirmed successful by recipient
□ Whitelist cooling-off period complete (if applicable)
□ Exact amount confirmed (recipient expects this amount)
□ Network confirmed (mainnet, not testnet)
□ Sufficient balance in source wallet (amount + fees + buffer)
□ All required approvers available next 60 minutes
```

**For transfers \>$1M**: Conduct formal video call with all approvers present.

#### Execution Protocol

**Video Call Requirements**:

```
1. Screen share custody interface or wallet
2. Primary operator reads transaction parameters aloud:
   - "Sending [X.XXXXX] ETH"
   - "To address: 0x[read full address character-by-character]"
   - "On network: Ethereum mainnet, chain ID 1"

3. Each approver independently verifies on their device:
   - Destination matches authorized recipient
   - Amount matches approved transfer
   - Network is correct

4. Approvers use MFA to approve:
   - Hardware security key, biometric, or authenticator app
   - For multisigs: Each signer verifies transaction details on their signing device
   - Verbally confirm: "I approve this transaction"

5. Final approval triggers broadcast to blockchain
```

#### Post-Submission Monitoring

Monitor transaction through finality:

```
1. Copy transaction hash from custody platform
2. Enter into block explorer immediately
3. Verify parameters match intended transaction
4. Monitor confirmation progress:
   - Ethereum: Wait for 12 confirmations (~3 minutes)
   - Bitcoin: Wait for 6 confirmations (~60 minutes)
5. Watch for recipient confirmation of receipt
```

#### Confirmation and Documentation

After transaction reaches finality:

```
1. Internal record (within 15 min):
   - Transaction hash and block number
   - Timestamp and confirmation count
   - Source wallet balance updated in records

2. Request receipt from recipient (within 30 min):
   - Formal acknowledgment they received funds

3. Permanent documentation:
   - Full transaction details (hash, block, timestamp, amount)
   - Authorization chain (who approved, when)
   - Personnel involved
```

---

## Multi-Signature Best Practices

See the Multisigs for Protocols guide.

# TODO: Add link to Multisigs for Protocols guide. AFTER IT IS MERGED

## Critical Risk Mitigations

### Address Verification

**Multisig and custody interface verification:**

- Always verify addresses directly from your custody platform or multisig interface (Safe, Zodiac, etc.)
- For multisigs: Cross-check configuration (threshold, signers) on block explorer
- Never trust copy-pasted addresses from email or chat
- Verify entire address character-by-character

**Address poisoning defense:**

- Never copy from transaction history
- Always copy from authoritative source
- Use custody platform address books when available

### Communication Security

**Email compromise prevention:**

- Address confirmation during video call prevents MITM
- Live verbal verification catches discrepancies
- Code phrases for authentication

**Social engineering defense:**

- Never accept urgent bypass requests
- Callback on known numbers to verify
- Any request to skip verification triggers security review

### Multi-Party Controls

**Prevents single-actor fraud:**

- Multiple personnel
- Video recording of approvals
- Separation of duties: requester ≠ approver ≠ technical executor

### Transaction Parameter Security

**Custody platform policy engines:**

- Enforce withdrawal limits automatically
- Block transactions to non-whitelisted addresses
- Require elevated approvals above thresholds
- Create circuit breakers if account compromised

---

## Key Principles Summary

1. **Test everything**: Small test transactions can catch human errors
2. **Verify independently**: Multiple people through different channels
3. **Never rush**: Urgency benefits attackers, not you
4. **Use multisig for self-custody**: Multiple signers prevent single points of failure
5. **Verify addresses live**: Always verify addresses during video calls from authoritative sources

**In cryptocurrency, there are no chargebacks.** Every transaction is final. The procedures in this guide may seem extensive, but preventing a single mistake justifies significant operational overhead.

The cost of verification is measured in minutes. The cost of a mistake is measured in millions.

---


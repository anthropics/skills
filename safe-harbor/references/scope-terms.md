# Safe Harbor Scope Terms

When adopting Safe Harbor, you'll define specific parameters that control what's covered and how whitehat rescues work.
Below is an explanation of each term with tips and best practices.

## 1. Asset Recovery Address

The address where whitehats must return rescued funds after an exploit.

**Tips:**

- Use a highly secure smart contract wallet (e.g., Gnosis Safe or governance-controlled address).
- Ensure it can handle large inflows, potentially a significant portion of your TVL.
- Please refer to [this framework on Wallet Multisig Security](/wallet-security/secure-multisig-best-practices)

## 2. Security Contact

The person or team whitehats must notify after completing a rescue.

**Tips:**

- Provide multiple points of contact (email, Signal, Telegram) for redundancy.
- Make sure these methods of notification are checked in case of an active exploit. Whitehats should reach out within 6
hours of a rescue

## 3. Assets Under Scope

The on-chain contracts or accounts that whitehats can legally interact with under Safe Harbor.

**Scope Options:**

- **All:** Covers the listed address and all child contracts, both existing and future.
- **ExistingOnly:** Covers the address and child contracts deployed before adoption.
- **FutureOnly:** Covers the address and child contracts deployed after adoption.
- **None:** Covers only the listed address.

**Examples:**

- All: Use for factories or deployer addresses that create vaults, pools, or markets. Covers all current and future
instances.
- None: Use for single vault contracts where funds are concentrated and no child contracts exist.
- ExistingOnly / FutureOnly: Very rarely used; typically for protocols with legal or operational constraints on future
contracts.

**Tips:**

- If your protocol deploys many contracts, include your deployer address EOA/Multisig/Governance Addresses with All.
This avoids the need for updates.
- Keep this list current - if you launch new deployments and they aren't covered, whitehats can't legally intervene.

## 4. Bounty Terms

Defines how whitehats are rewarded for successful intervention.

### 4.1 Bounty Calculation

As a FYI, the formula to determine the bounty payout to the whitehats is:

`bounty = min(bountyPercentage × recoveredAmount, bountyCapUSD)`

Predefining this ensures no post-hack negotiation and prevents delays.

### 4.2 Bounty Percentage

The percentage of recovered funds that a whitehat receives.

**Recommendation:**

- 10% is standard in the industry.
- Set equal to your bug bounty program's critical exploit payout percentage

### 4.3 Bounty Cap (USD)

The maximum bounty amount for a single whitehat, in USD.

**Recommendation:**

- Match or set equal to your bug bounty program’s max payout to avoid incentives for malicious behavior.

### 4.4 Aggregate Bounty Cap (USD)

The maximum total bounty payout across all whitehats for a single incident. Bounties will be distributed pro-rata.

**Rule:**

- If you set an Aggregate Bounty Cap, you must set retainable to false so all funds return to the protocol first, then
bounties are distributed.

### 4.5 Retainable

Whether whitehats keep their bounty directly or return everything first.

- **True**: Whitehat deducts bounty before returning funds.
- **False**: Whitehat returns all funds; protocol pays bounty afterward.

**Rule:**

- Cannot set retainable to true if Aggregate Bounty Cap is enabled.

## 5. Identity Verification

Determines whether whitehats must verify their identity.

**Options:**

- **Anonymous**: No KYC (most crypto-native option).
- **Pseudonymous**: Requires a pseudonym.
- **Named**: Legal name verification (KYC required).

**Tips:**

- Most protocols choose Named (KYC) for compliance.
- Some opt for crypto-native option of protecting the whitehat's anonymity.

## 6. Diligence Requirements

Additional compliance checks for whitehats before bounty payout (applies only if identity = Named).

Generic Template:

` requires all eligible whitehats to undergo Know Your Customer (KYC) verification and be screened
against global sanctions lists, including US, UK, and EU regulations. This process ensures that all bounty recipients
are compliant with legal and regulatory standards before qualifying for payment.`

---

If you ever need help or have any questions, don’t hesitate to reach out!

📬 Contact us at: [safe-harbor@securityalliance.org](mailto:safe-harbor@securityalliance.org)

---


# Data Integrity & Verification

## Use On-chain Resolution for Financial Transactions

- Always resolve fresh data directly from Ethereum mainnet whenever conducting financial transactions
- Do not rely on indexer or API data when moving or managing funds
- Preferably run an Ethereum node for high-value transactions, or if not feasible, use reputable L1 RPC providers while
  still verifying the integrity and audit status of all software involved in the resolution process

**Rationale**: Indexers and third-party APIs may have delayed updates or inconsistencies that could lead to payments
being sent to outdated or incorrect addresses. By querying L1 directly, applications work with the most current and
authoritative ENS data, dramatically reducing the risk of misdirected funds. This is particularly crucial for high-value
transactions where the consequences of using stale data could be severe.

## Verify Forward Resolution on [Reverse Records](https://docs.ens.domains/ensip/3)

- Always perform forward resolution on reverse records to verify address matches
- Check that name → address → name completes a valid loop
- Clearly indicate to users when there's a mismatch

**Rationale**: ENS supports both forward resolution (name → address) and reverse resolution (address → name). However,
reverse records can be set independently, creating the possibility for spoofing or impersonation if not properly
verified. By performing forward resolution on the result of a reverse lookup and comparing it to the original address,
applications can ensure the bidirectional integrity of the ENS data, preventing potential phishing or impersonation
attacks.

---


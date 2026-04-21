# Web3 Scam Patterns

## Social Engineering Scams

### The Fake Job Interview
**Pattern**: Attacker poses as recruiter for legitimate company, sends "coding challenge" or "interview task" that requires running malicious code.

**Red Flags**:
- Unsolicited job offer via DM
- Requires downloading/running code before real interview
- "Urgent" timeline pressure
- Interview process feels unusual

**Defense**:
- Verify recruiter through company's official channels
- Never run code from unknown sources
- Use VM/sandbox if you must run code
- Legitimate companies don't require running code for initial screening

### The Compromised Friend
**Pattern**: Attacker gains access to trusted person's account, uses that trust to scam their contacts.

**Red Flags**:
- Unusual requests from known contacts
- Urgency or secrecy requirements
- Request to send crypto or click links
- Communication style seems off

**Defense**:
- Verify through separate channel (call them, different platform)
- Don't send money based on messages alone
- If account seems compromised, alert the real person

### Customer Support Impersonation
**Pattern**: Attacker poses as support staff, claims to need seed phrase or remote access to "fix" an issue.

**Red Flags**:
- Unsolicited contact about "issues"
- Requests for seed phrase or private keys
- Asks for remote access to your device
- Creates urgency ("your funds are at risk")

**Defense**:
- Real support NEVER asks for seed phrases
- Only contact support through official channels
- Ignore DMs claiming to be support

---

## Phishing Scams

### Fake Airdrop Claim
**Pattern**: Announce fake airdrop, link leads to malicious site that requests wallet signature draining funds.

**Red Flags**:
- Too-good-to-be-true free tokens
- Requires connecting wallet to claim
- Requests unusual permissions/signatures
- Site URL slightly misspelled

**Defense**:
- Verify airdrops on official project channels
- Never sign transactions you don't understand
- Use a burner wallet for claims
- Check approved transactions before signing

### Clone Site Attack
**Pattern**: Pixel-perfect copy of legitimate site at similar domain (uniswop.com vs uniswap.org).

**Red Flags**:
- Reached via link rather than bookmark
- URL doesn't match exactly
- SSL certificate warnings
- Site behavior slightly different

**Defense**:
- Bookmark trusted sites
- Always verify URL carefully
- Check certificate details
- If something feels off, stop

### Malicious NFT / Token
**Pattern**: Unsolicited NFT/token in wallet contains link to scam site or triggers malicious contract on interaction.

**Red Flags**:
- Token you didn't buy appearing in wallet
- NFT with enticing "claim" message
- Interaction required to "remove" it

**Defense**:
- Ignore unknown tokens/NFTs
- Don't interact (hide in wallet UI)
- Never visit links in unsolicited tokens
- Some are designed to steal on any interaction

---

## Technical Scams

### Unlimited Approval Exploit
**Pattern**: dApp requests unlimited token approval, later drains all approved tokens.

**Red Flags**:
- Request for "unlimited" or very high approval
- Approval for tokens you're not using
- Site not well-known or verified

**Defense**:
- Only approve exact amounts needed
- Regularly review approvals (revoke.cash)
- Revoke approvals for sites you no longer use
- Use hardware wallet (shows approval amounts)

### Address Poisoning
**Pattern**: Attacker sends tiny transactions from address similar to yours, hoping you copy their address from history.

**Red Flags**:
- Unexpected small incoming transactions
- Address in history looks almost like yours
- Only first/last characters match

**Defense**:
- Always copy address from source, not history
- Verify full address, not just start/end
- Be suspicious of unexpected small transactions
- Use address book features

### Clipboard Hijacking
**Pattern**: Malware monitors clipboard, replaces copied crypto addresses with attacker's address.

**Red Flags**:
- Address changes after pasting
- Unexpected software installed
- Computer behaving unusually

**Defense**:
- Always verify pasted address matches copied
- Keep system clean of malware
- Use hardware wallet (shows destination address)
- Verify on multiple devices if sending large amounts

---

## Investment Scams

### Rug Pull
**Pattern**: Project launches, gains investment, team disappears with funds.

**Red Flags**:
- Anonymous team
- Unrealistic returns promised
- Liquidity can be removed by team
- No security audit
- Heavy marketing, light substance

**Defense**:
- Research team backgrounds
- Check if liquidity is locked
- Read audit reports (if any)
- Start small, watch behavior
- If returns seem too good, they are

### Pump and Dump
**Pattern**: Coordinated group pumps price, sells to latecomers who lose when price crashes.

**Red Flags**:
- Sudden social media hype
- "Alpha" shared in paid groups
- Extreme short-term price movement
- Low liquidity tokens

**Defense**:
- Be skeptical of "insider info"
- Don't FOMO into pumped tokens
- Check trading volume and liquidity
- Remember: if you heard about it, you're probably late

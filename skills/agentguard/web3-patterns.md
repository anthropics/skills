# Web3 Vulnerability Patterns Reference

Detailed vulnerability patterns for the `web3` subcommand. Use this when performing Web3/smart contract security audits.

## Solidity Vulnerability Categories

### 1. Reentrancy (HIGH)

**Pattern**: External call before state update in the same function.

```solidity
// VULNERABLE: state updated after external call
function withdraw(uint amount) public {
    require(balances[msg.sender] >= amount);
    (bool success, ) = msg.sender.call{value: amount}("");  // external call
    balances[msg.sender] -= amount;  // state change AFTER call
}
```

**Detection**: Look for `.call{`, `.transfer(`, `.send(` followed by storage variable assignment (`var =`, `var +=`, `var -=`) within the same function body.

**Fix**: Use Checks-Effects-Interactions pattern or ReentrancyGuard.

### 2. Wallet Draining (CRITICAL)

**Patterns**:
- `approve()` with max uint256 value followed by `transferFrom()`
- `permit()` with far-future deadline enabling gasless approvals
- Approval granted to attacker-controlled address

**Detection**:
- `approve(address, type(uint256).max)` or `MaxUint256` or `2**256-1`
- `transferFrom` in same contract/flow as `approve`
- `permit(` with `deadline` parameter

### 3. Unlimited Approval (HIGH)

**Pattern**: Token approval for maximum amount, giving spender unlimited access.

```solidity
token.approve(spender, type(uint256).max);
token.setApprovalForAll(operator, true);
```

**Risk**: If the spender contract is compromised, all approved tokens can be drained.

### 4. Self-Destruct (HIGH)

**Pattern**: `selfdestruct(address)` or deprecated `suicide(address)`.

**Risk**: Permanently destroys the contract, sending remaining ETH to the specified address. Can be exploited if access control is weak.

### 5. Signature Replay (HIGH)

**Pattern**: Using `ecrecover()` without nonce or chain ID protection.

```solidity
// VULNERABLE: no nonce, signature can be replayed
function execute(bytes memory signature, uint amount) public {
    bytes32 hash = keccak256(abi.encodePacked(msg.sender, amount));
    address signer = ecrecover(hash, v, r, s);
    // Missing: nonce check, chain ID, contract address in hash
}
```

**Fix**: Include nonce, chainId, and contract address in signed message. Use EIP-712 typed data.

### 6. Flash Loan Attacks (MEDIUM)

**Patterns**:
- `flashLoan()`, `IFlashLoan`, `executeOperation()`
- AAVE/dYdX/Uniswap flash loan interfaces

**Risk**: Attacker borrows large amounts without collateral within a single transaction to manipulate prices, governance, or vulnerable protocols.

**Check**: Ensure price oracles use TWAP, governance has timelock, and lending markets have proper collateral checks.

### 7. Proxy Upgrade Risks (MEDIUM)

**Patterns**:
- `upgradeTo(address)`, `upgradeToAndCall(address, bytes)`
- `_setImplementation()`, `IMPLEMENTATION_SLOT`
- Transparent proxy / UUPS patterns

**Check**:
- Is upgrade function access-controlled?
- Is there a timelock on upgrades?
- Can the proxy be upgraded to a malicious implementation?

### 8. Hidden Transfers (MEDIUM)

**Pattern**: ETH or token transfers hidden in functions not named transfer/send.

```solidity
// Transfer hidden in an innocuous-looking function
function updateConfig(address _new) public {
    payable(_new).transfer(address(this).balance);  // hidden drain
}
```

**Detection**: `.transfer(`, `.call{value:}` in functions not named `transfer`, `_transfer`, `send`, `withdraw`.

### 9. Price Oracle Manipulation

**Patterns**:
- Single-block spot price from DEX (e.g., `getReserves()` used directly for pricing)
- No TWAP (Time-Weighted Average Price) implementation
- Price feed without staleness check

**Check**: Look for Uniswap `getReserves()`, Chainlink `latestRoundData()` without `updatedAt` staleness check.

### 10. Access Control Issues

**Patterns**:
- Public/external functions that modify critical state without access modifiers
- Missing `onlyOwner`, `onlyRole`, or similar guards
- `tx.origin` used for authentication (vulnerable to phishing)

**Check**:
- All state-changing functions should have appropriate access control
- `tx.origin` should never be used for authorization (use `msg.sender`)
- Owner/admin functions should be behind multisig or timelock

## JavaScript/TypeScript Web3 Patterns

### Private Key Exposure

- Hardcoded private keys: `0x` followed by 64 hex characters in quotes
- `PRIVATE_KEY` in environment variable assignments
- Private key in config files, .env files committed to repo

### Mnemonic Exposure

- BIP-39 seed phrases (12-24 words) in source code
- `seed_phrase`, `mnemonic`, `recovery_phrase` variable assignments

### Unsafe RPC Usage

- Sending signed transactions without user confirmation
- Using `eth_sendTransaction` with hardcoded parameters
- Missing gas limit estimation (risk of out-of-gas)

### Front-End Risks

- Phishing patterns: UI mimicking wallet approval screens
- Hidden iframe/overlay for approval harvesting
- Approval transactions disguised as other operations

## GoPlus Security Checks (Optional)

If GoPlus API is available, these additional checks can be performed:

| Check | API | Description |
|-------|-----|-------------|
| Token Security | `tokenSecurity(chainId, address)` | Honeypot, tax, owner control |
| Address Security | `addressSecurity(chainId, address)` | Blacklisted, phishing, mixer |
| Approval Risk | `approvalSecurity(chainId, address)` | Risky approvals |
| Phishing Site | `phishingSite(url)` | Known phishing URL |
| Transaction Simulation | `simulateTransaction(...)` | Pre-execution risk analysis |

Requires `GOPLUS_API_KEY` and `GOPLUS_API_SECRET` environment variables.

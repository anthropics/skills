# Testing Tools Setup Guide

## Foundry

### Installation
```bash
# Install foundryup
curl -L https://foundry.paradigm.xyz | bash

# Install/update Foundry
foundryup

# Verify installation
forge --version
```

### Project Setup
```bash
# New project
forge init my-project
cd my-project

# Install dependencies
forge install OpenZeppelin/openzeppelin-contracts
forge install foundry-rs/forge-std
```

### foundry.toml Configuration
```toml
[profile.default]
src = "src"
out = "out"
libs = ["lib"]
optimizer = true
optimizer_runs = 200

# Fuzzing configuration
[fuzz]
runs = 10000
max_test_rejects = 65536

# Invariant testing
[invariant]
runs = 256
depth = 15
fail_on_revert = false

# Fork testing
[rpc_endpoints]
mainnet = "${ETH_RPC_URL}"
```

### Common Commands
```bash
# Run all tests
forge test

# Run with verbosity
forge test -vvvv

# Run specific test
forge test --match-test test_Transfer

# Run with gas report
forge test --gas-report

# Coverage report
forge coverage --report lcov

# Fork testing
forge test --fork-url $ETH_RPC_URL
```

---

## Slither (Static Analysis)

### Installation
```bash
# Via pip
pip3 install slither-analyzer

# Or via pipx (isolated)
pipx install slither-analyzer

# Verify
slither --version
```

### Basic Usage
```bash
# Analyze project
slither .

# Analyze specific file
slither src/MyContract.sol

# JSON output
slither . --json output.json

# Only show high/medium
slither . --filter-paths "test|lib" --exclude-low
```

### Configuration (.slither.config.json)
```json
{
  "filter_paths": ["lib", "test", "node_modules"],
  "exclude_informational": true,
  "exclude_low": false,
  "exclude_medium": false,
  "exclude_high": false,
  "exclude_optimization": true,
  "detectors_to_exclude": ["naming-convention"],
  "solc_remaps": [
    "@openzeppelin/=lib/openzeppelin-contracts/"
  ]
}
```

### Key Detectors to Enable
```bash
# High severity
slither . --detect reentrancy-eth,arbitrary-send-eth,controlled-delegatecall

# Access control
slither . --detect suicidal,unprotected-upgrade,tx-origin

# All detectors
slither . --list-detectors
```

---

## Aderyn (Static Analysis)

### Installation
```bash
# Via cargo
cargo install aderyn

# Verify
aderyn --version
```

### Usage
```bash
# Analyze project
aderyn .

# Output formats
aderyn . --output report.md
aderyn . --output report.json

# Specific scope
aderyn src/
```

---

## Echidna (Fuzzing)

### Installation
```bash
# Via prebuilt binary
wget https://github.com/crytic/echidna/releases/latest/download/echidna-linux
chmod +x echidna-linux
sudo mv echidna-linux /usr/local/bin/echidna

# Via Docker
docker pull ghcr.io/crytic/echidna/echidna
```

### Configuration (echidna.yaml)
```yaml
testMode: assertion
testLimit: 50000
shrinkLimit: 5000
seqLen: 100
contractAddr: "0x00a329c0648769a73afac7f9381e08fb43dbea72"
deployer: "0x30000"
sender: ["0x10000", "0x20000", "0x30000"]
coverage: true
corpusDir: "corpus"
```

### Test Contract Pattern
```solidity
contract EchidnaTest is MyContract {
    function echidna_total_supply_constant() public view returns (bool) {
        return totalSupply() == INITIAL_SUPPLY;
    }

    function echidna_balance_under_supply() public view returns (bool) {
        return balanceOf(msg.sender) <= totalSupply();
    }
}
```

---

## Certora (Formal Verification)

### Installation
```bash
# Install Java 11+
sudo apt install openjdk-11-jdk

# Install Certora
pip3 install certora-cli

# Set API key
export CERTORAKEY="your-api-key"
```

### Spec File (.spec)
```cvl
methods {
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function transfer(address, uint256) external returns (bool);
}

// Invariant: balance <= totalSupply
invariant balanceUnderSupply(address user)
    balanceOf(user) <= totalSupply()

// Rule: transfer preserves total supply
rule transferPreservesTotalSupply(address to, uint256 amount) {
    uint256 supplyBefore = totalSupply();

    env e;
    transfer(e, to, amount);

    uint256 supplyAfter = totalSupply();
    assert supplyBefore == supplyAfter;
}
```

### Running Verification
```bash
certoraRun src/Token.sol:Token \
    --verify Token:specs/Token.spec \
    --solc solc8.19
```

---

## CI/CD Integration

### GitHub Actions
```yaml
name: Security Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
        with:
          submodules: recursive

      - name: Install Foundry
        uses: foundry-rs/foundry-toolchain@v1

      - name: Run tests
        run: forge test -vvv

      - name: Run coverage
        run: forge coverage

      - name: Install Slither
        run: pip3 install slither-analyzer

      - name: Run Slither
        run: slither . --filter-paths "test|lib"
```

---

## Recommended Workflow

1. **During Development**
   - Run `forge test` after each change
   - Run `slither .` before commits

2. **Before PR**
   - Full test suite: `forge test -vvv`
   - Coverage check: `forge coverage`
   - Static analysis: `slither .` and `aderyn .`

3. **Before Audit**
   - Mutation testing
   - Invariant tests passing
   - Zero high/medium static analysis findings
   - Fork tests against mainnet

4. **Before Mainnet**
   - All of the above
   - Formal verification on critical paths
   - External audit complete

# Integration Testing

While unit tests verify individual functions work in isolation (often with mocked dependencies), integration tests
verify that your smart contracts work correctly with real external systems. In Web3, this primarily means testing with
**fork tests** - running your contracts against real blockchain state. With out unit tests, we `mocked` working with
external systems, integration tests however will actually work with those systems, by running as:

- Fork tests
- Testnet Tests
- Inexpensive Mainnet Tests (Be careful here!)

In smart contract development, this means testing your contracts against real protocols, oracles, and blockchain state
rather than mocked versions.

## What are Fork Tests?

Fork tests involve creating a local copy of the blockchain state at a specific block height, allowing you to run your
smart contracts against real data and interactions. This is crucial for testing how your contracts will behave in
production conditions, especially when they rely on external systems like oracles or other protocols.

In foundry, you can run a fork test just by passing in a URL to fork:

```bash
forge test --fork-url 
```

## Why Fork Testing Matters

Most smart contract security issues arise from unexpected interactions with external systems. Fork testing helps you
catch these issues before deployment by testing against real-world conditions.

## How to Implement Fork Tests

Running a fork test can be as straightforward as pointing to contract addresses on a forked network. You can see a full
example from the
[Cyfrin Updraft foundry-fund-me curriculum.](https://github.com/Cyfrin/foundry-fund-me-cu/blob/main/test/integration/InteractionsTest.t.sol)

## References

This document incorporates knowledge from:

- [Cyfrin Updraft Security Testing Curriculum](https://updraft.cyfrin.io)

---


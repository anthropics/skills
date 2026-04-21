# Unit Testing

Unit testing is the foundation of smart contract security testing. While fuzz tests can find edge cases and integration
tests verify system interactions, unit tests ensure that individual functions behave correctly under expected
conditions. Every smart contract should have comprehensive unit test coverage before moving to more advanced testing
methodologies.

## Overview

Unit testing involves testing individual components or functions of your codebase in isolation. In smart contract
development, this means testing each function with known inputs to verify expected outputs and state changes.

**Why Unit Tests Matter for Security:**

- Catch basic logic errors before they become vulnerabilities
- Ensure access controls work as expected
- Verify arithmetic operations don't have overflow/underflow issues
- Document expected behavior for auditors and future developers
- Provide a safety net when refactoring code

## The Foundation of Security Testing

As mentioned in your security testing strategy, unit testing should **always** be implemented with high code coverage.
Think of unit tests as your first line of defense against bugs that could become security vulnerabilities.

```solidity
// Example: Simple token contract
contract SimpleToken {
    mapping(address => uint256) public balances;
    uint256 public totalSupply;

    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount, "Insufficient balance");
        require(to != address(0), "Cannot transfer to zero address");

        balances[msg.sender] -= amount;
        balances[to] += amount;
    }
}
```

## Writing Effective Unit Tests

### Basic Unit Test Structure

Here's how you'd test the transfer function above using Foundry:

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SimpleTokenTest is Test {
    SimpleToken token;
    address alice = address(0x1);
    address bob = address(0x2);

    function setUp() public {
        token = new SimpleToken();
        // Give Alice some initial balance
        vm.store(
            address(token), 
            keccak256(abi.encode(alice, 0)), // balances[alice] slot
            bytes32(uint256(1000))
        );
        token.setTotalSupply(1000);
    }

    function testTransferSuccess() public {
        vm.prank(alice);
        token.transfer(bob, 100);

        assertEq(token.balances(alice), 900);
        assertEq(token.balances(bob), 100);
    }

    function testTransferFailsInsufficientBalance() public {
        vm.prank(alice);
        vm.expectRevert("Insufficient balance");
        token.transfer(bob, 2000); // More than Alice has
    }

    function testTransferFailsZeroAddress() public {
        vm.prank(alice);
        vm.expectRevert("Cannot transfer to zero address");
        token.transfer(address(0), 100);
    }
}
```

### Security-Focused Test Cases

For each function, you should test:

1. **Happy Path**: Normal expected usage
2. **Edge Cases**: Boundary conditions (zero values, maximum values)
3. **Access Control**: Who can and cannot call the function
4. **Failure Cases**: Invalid inputs that should revert
5. **State Changes**: Verify all expected state modifications occur

### From Unit Test to Fuzz Test

You can easily convert a unit test to a fuzz test:

```solidity
// Unit test
function testTransferAmount() public {
    uint256 amount = 100;
    vm.prank(alice);
    token.transfer(bob, amount);
    assertEq(token.balances(bob), amount);
}

// Fuzz test version
function testTransferAmountFuzz(uint256 amount) public {
    amount = bound(amount, 0, 1000); // Bound to valid range
    vm.prank(alice);
    token.transfer(bob, amount);
    assertEq(token.balances(bob), amount);
}
```

## Mocking External Dependencies

Unit tests should test your contract logic in isolation. When your contracts depend on external systems like oracles,
other protocols, or complex state, you should mock these dependencies to create predictable, fast, and controlled test
conditions.

### Why Mock in Unit Tests?

**Problems with real external dependencies in unit tests:**

- **Slow**: Network calls and complex state slow down tests
- **Unpredictable**: External state changes make tests non-deterministic
- **Expensive**: RPC calls cost money and hit rate limits
- **Complex**: Hard to test edge cases with real systems

**Benefits of mocking:**

- **Fast**: No network calls or complex state
- **Predictable**: You control exactly what the mock returns
- **Comprehensive**: Easy to test all edge cases and failure scenarios
- **Isolated**: Test only YOUR contract logic, not external systems

### Example Mock

For example, if you are interacting with an ERC20 that has very odd functionality, an easier way to test working with it
would be to make a mock of that contract.

```solidity
// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract MockERC20 is ERC20 {
    constructor(string memory name, string memory symbol)
    ERC20(name, symbol) {}

    function mint(address account, uint amount) external {
        _mint(account, amount);
    }
}
```

Then, use that mock in your tests:

```solidity
contract MyContractTest is Test {
    MockERC20 mockToken;

    function setUp() public {
        mockToken = new MockERC20("Mock Token", "MTK");
        mockToken.mint(address(this), 1000); // Mint some tokens for testing
    }
}
```

### When NOT to Mock

**Don't mock when:**

- Testing the integration between YOUR contracts
- The external dependency is simple and deterministic
- You're specifically testing the interaction with the external system

## Best Practices

### 1. Achieve High Code Coverage

Aim for 90%+ line coverage and 100% branch coverage on critical functions:

```bash
# Run coverage with Foundry
forge coverage
```

### 2. Test All Access Controls

```solidity
function testOnlyOwnerCanMint() public {
    vm.prank(alice); // Alice is not owner
    vm.expectRevert("Ownable: caller is not the owner");
    token.mint(alice, 100);

    vm.prank(owner);
    token.mint(alice, 100); // Should succeed
    assertEq(token.balances(alice), 100);
}
```

### 3. Test Arithmetic Operations

```solidity
function testNoOverflowOnMint() public {
    // Set total supply to near max uint256
    uint256 nearMaxSupply = type(uint256).max - 100;
    token.setTotalSupply(nearMaxSupply);

    vm.prank(owner);
    vm.expectRevert(); // Should revert on overflow
    token.mint(alice, 200);
}
```

### 4. Use Descriptive Test Names

```solidity
function testTransferFailsWhenRecipientIsZeroAddress() public {
    // Clear what this test does
}

function testMintIncreasesTotalSupplyAndRecipientBalance() public {
    // Tests multiple related behaviors
}
```

### 5. Arrange, Act, Assert Pattern

```solidity
function testTransfer() public {
    // Arrange
    uint256 initialBalance = 1000;
    uint256 transferAmount = 100;

    // Act
    vm.prank(alice);
    token.transfer(bob, transferAmount);

    // Assert
    assertEq(token.balances(alice), initialBalance - transferAmount);
    assertEq(token.balances(bob), transferAmount);
}
```

## Common Smart Contract Tools and Frameworks

- [Foundry (Solidity)](https://github.com/foundry-rs/foundry):
- [Hardhat (Solidity)](https://hardhat.org/)
- [Moccasin (Vyper)](https://github.com/Cyfrin/moccasin)
- [Anchor (Rust)](https://www.anchor-lang.com/docs)

## References

This document incorporates knowledge from:

- [Cyfrin Updraft Security Testing Curriculum](https://updraft.cyfrin.io)

---


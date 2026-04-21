# Smart Contract Testing Patterns

## Unit Test Patterns

### Basic Structure (Foundry)
```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "forge-std/Test.sol";
import "../src/MyContract.sol";

contract MyContractTest is Test {
    MyContract public target;
    address public alice = makeAddr("alice");
    address public bob = makeAddr("bob");

    function setUp() public {
        target = new MyContract();
        deal(alice, 100 ether);
    }

    function test_BasicTransfer() public {
        vm.prank(alice);
        target.transfer(bob, 1 ether);
        assertEq(target.balanceOf(bob), 1 ether);
    }

    function test_RevertWhen_InsufficientBalance() public {
        vm.prank(alice);
        vm.expectRevert("Insufficient balance");
        target.transfer(bob, 1000 ether);
    }
}
```

### Testing Access Control
```solidity
function test_OnlyOwnerCanPause() public {
    // Non-owner should fail
    vm.prank(alice);
    vm.expectRevert("Ownable: caller is not the owner");
    target.pause();

    // Owner should succeed
    vm.prank(target.owner());
    target.pause();
    assertTrue(target.paused());
}
```

### Testing Events
```solidity
function test_EmitsTransferEvent() public {
    vm.expectEmit(true, true, false, true);
    emit Transfer(alice, bob, 100);

    vm.prank(alice);
    target.transfer(bob, 100);
}
```

---

## Fuzz Testing Patterns

### Basic Fuzzing
```solidity
function testFuzz_Transfer(uint256 amount) public {
    // Bound to reasonable values
    amount = bound(amount, 0, alice.balance);

    uint256 balanceBefore = target.balanceOf(bob);

    vm.prank(alice);
    target.transfer(bob, amount);

    assertEq(target.balanceOf(bob), balanceBefore + amount);
}
```

### Fuzzing with Assumptions
```solidity
function testFuzz_Deposit(uint256 amount) public {
    // Skip invalid inputs
    vm.assume(amount > 0);
    vm.assume(amount <= type(uint128).max);

    deal(alice, amount);
    vm.prank(alice);
    target.deposit{value: amount}();

    assertEq(target.balanceOf(alice), amount);
}
```

### Stateful Fuzzing (Invariant Testing)
```solidity
// Test that total supply always equals sum of balances
function invariant_TotalSupplyEqualsBalances() public {
    uint256 sum = 0;
    for (uint i = 0; i < actors.length; i++) {
        sum += target.balanceOf(actors[i]);
    }
    assertEq(target.totalSupply(), sum);
}
```

---

## Fork Testing Patterns

### Mainnet Fork Setup
```solidity
function setUp() public {
    // Fork mainnet at specific block
    vm.createSelectFork(vm.envString("ETH_RPC_URL"), 18_000_000);

    // Now can interact with real contracts
    usdc = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
}

function test_SwapOnUniswap() public {
    // Test against real Uniswap deployment
    deal(address(usdc), alice, 1000e6);

    vm.prank(alice);
    usdc.approve(address(router), type(uint256).max);

    vm.prank(alice);
    router.swapExactTokensForTokens(...);
}
```

### Testing Protocol Integrations
```solidity
function test_AaveDeposit() public {
    // Fork and test real Aave integration
    deal(address(weth), alice, 10 ether);

    vm.startPrank(alice);
    weth.approve(address(aavePool), type(uint256).max);
    aavePool.deposit(address(weth), 10 ether, alice, 0);
    vm.stopPrank();

    assertGt(aWeth.balanceOf(alice), 0);
}
```

---

## Security-Specific Tests

### Reentrancy Protection
```solidity
contract ReentrancyAttacker {
    Target target;
    uint256 public attackCount;

    function attack() external payable {
        target.withdraw(msg.value);
    }

    receive() external payable {
        if (attackCount < 5) {
            attackCount++;
            target.withdraw(msg.value);
        }
    }
}

function test_ReentrancyProtected() public {
    ReentrancyAttacker attacker = new ReentrancyAttacker(target);
    deal(address(attacker), 1 ether);

    vm.expectRevert(); // Should revert due to reentrancy guard
    attacker.attack();
}
```

### Oracle Manipulation
```solidity
function test_OracleManipulation() public {
    // Simulate oracle price manipulation
    MockOracle(oracle).setPrice(1e18); // Normal price

    uint256 normalBorrow = target.maxBorrow(alice);

    MockOracle(oracle).setPrice(10e18); // 10x price
    uint256 manipulatedBorrow = target.maxBorrow(alice);

    // Borrow limit should have safety bounds
    assertLt(manipulatedBorrow, normalBorrow * 2);
}
```

### Flash Loan Attack Simulation
```solidity
function test_FlashLoanResistance() public {
    // Simulate attacker with flash loaned funds
    deal(address(token), attacker, 1_000_000e18);

    vm.startPrank(attacker);
    // Attempt manipulation
    target.deposit(1_000_000e18);
    target.manipulatePrice(); // Should fail or have no effect
    target.withdraw(1_000_000e18);
    vm.stopPrank();

    // Price should not have changed significantly
    assertApproxEqRel(target.price(), originalPrice, 0.01e18);
}
```

---

## Test Organization

### File Structure
```
test/
├── unit/
│   ├── Token.t.sol
│   ├── Vault.t.sol
│   └── Oracle.t.sol
├── integration/
│   ├── VaultOracle.t.sol
│   └── TokenVault.t.sol
├── fuzz/
│   ├── Token.fuzz.t.sol
│   └── Vault.fuzz.t.sol
├── invariant/
│   └── Protocol.invariant.t.sol
└── fork/
    └── MainnetIntegration.t.sol
```

### Naming Conventions
```solidity
// Unit tests
function test_FunctionName_WhenCondition() public { }
function test_RevertWhen_InvalidInput() public { }
function test_RevertIf_Unauthorized() public { }

// Fuzz tests
function testFuzz_FunctionName(uint256 input) public { }

// Invariants
function invariant_PropertyName() public { }
```

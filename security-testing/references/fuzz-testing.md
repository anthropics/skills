# Fuzz Testing

Fuzz testing (or fuzzing) is when you supply random data to your system in an attempt to break it. Most of the time,
hacks come from scenarios you didn't think about and write a test for. What if I told you that you could write one test
that would check for almost every possible scenario?

## What is Fuzz Testing?

For example, if a balloon was our system/code, it would involve doing random stuff to the balloon to break it.

- Punch it
- Squeeze it
- Throw it
- etc

Why would we want to do all that? Let's look at an example.

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MyContract {
    uint256 public shouldAlwaysBeZero = 0;
    uint256 private hiddenValue = 0;

    function doStuff(uint256 data) public {
        if (data == 2) {
            shouldAlwaysBeZero = 1;
        }
        if (hiddenValue == 7) {
            shouldAlwaysBeZero = 1;
        }
        hiddenValue = data;
    }
}
```

Let's say we have this function named `doStuff`, which takes an integer as input. We additionally have a variable named
`shouldAlwaysBeZero` that we want always to be zero.

The fact that this variable should always be zero is known as our **invariant**, or "property of the system that should
always hold."

**Invariant**: The property of the system that should always hold.

Our invariant in this contract is that:
**Invariant: `shouldAlwaysBeZero` MUST always be 0**

## Why Normal Unit Tests Aren't Enough

Let's look at a normal unit test:

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MyContractTest is Test {
    MyContract exampleContract;

    function setUp() public {
        exampleContract = new MyContract();
    }

    function testIsAlwaysZeroUnit() public {
        uint256 data = 0;
        exampleContract.doStuff(data);
        assert(exampleContract.shouldAlwaysBeZero() == 0);
    }
}
```

With this single unit test `testIsAlwaysZeroUnit`, we might think our code has enough coverage, but if we look at the
`doStuff` function again, we can see that if our input is `2`, our variable will not be zero.

```solidity
function doStuff(uint256 data) public {
    // WHAT IS THIS IF STATEMENT???
    // 👇👇👇👇👇👇
    if (data == 2) {
        shouldAlwaysBeZero = 1;
    }
    // 👆👆👆👆👆👆

    // Ignore this one for now
    if (hiddenValue == 7) {
        shouldAlwaysBeZero = 1;
    }
    hiddenValue = data;
}
```

This seems obvious with our example function, but more often than not, you'll have a function that's much more complex
with numerous edge cases that are impossible to manually test.

## Stateless Fuzz Tests

In Foundry, you'd write a fuzz test like so:

```solidity
function testIsAlwaysZeroFuzz(uint256 randomData) public {
    exampleContract.doStuff(randomData);
    assert(exampleContract.shouldAlwaysBeZero() == 0);
}
```

Foundry will automatically input semi-random values to `randomData` and over many runs, input them to the `doStuff`
function and check that the assertion holds.

This would be equivalent to writing many tests where `randomData` had different values, all in one test!

Now I say "semi-random" because the way your fuzzer (in our case, Foundry) picks the random data isn't truly random, and
should be somewhat intelligent with the random numbers it picks. Foundry is smart enough to see the `if data == 2`
conditional, and pick `2` as an input.

If we run our fuzz test, it tells us exactly what input fails our test:

```bash
$ forge test -m testIsAlwaysZeroFuzz

Failing tests:
Encountered 1 failing test in test/MyContractTest.t.sol:MyContractTest
[FAIL. Reason: Assertion violated Counterexample:
calldata=0x47fb53d00000000000000000000000000000000000000000000000000000000000000002, args=[2]]
testIsAlwaysZeroFuzz(uint256) (runs: 6, μ: 27070, ~: 30387)
```

We can see that it found out if it passed `args=[2]` to the test, it was able to break our
`assert(exampleContract.shouldAlwaysBeZero() == 0)`. So now, we can go back into our code, and realize we need to fix
the edge case where `data == 2`, and now we are safe from the exploit!

## Stateful vs Stateless Fuzzing

### The Hidden Bug

Now you may notice that there is another scenario where our code could have an issue, and that's when `hiddenValue ==
7`. In order for this revert to happen, you have to:

1. First call `doStuff` with the value `7` (which sets `hiddenValue` to `7`)
2. Then call this function again with any other number

It takes **2 calls** for our invariant to be broken:

1. Call `doStuff` with `7`
2. Call `doStuff` with any other number

Our fuzz test written above will never be able to find this example because as it's currently written, our test is
what's known as a **"stateless fuzz test."**

**Stateless Fuzzing**: Fuzzing where the state of a previous run is discarded for the next run.

### Stateful Fuzz Tests (Invariant Tests)

So, in smart contract testing, we can do **"stateful fuzzing"** instead.

**Stateful Fuzzing**: The state of our previous fuzz run is the starting state of our next fuzz run.

To write a stateful fuzz test in Foundry, you'd use the `invariant` keyword, and it requires a little more setup:

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MyContractTest is StdInvariant, Test {
    MyContract exampleContract;

    function setUp() public {
        exampleContract = new MyContract();
        targetContract(address(exampleContract));
    }

    function invariant_testAlwaysReturnsZero() public {
        assert(exampleContract.shouldAlwaysBeZero() == 0);
    }
}
```

Instead of just passing random data to function calls, a stateful fuzz test (invariant test) will automatically call
random functions with random data.

We use the `targetContract` function to tell Foundry that it can use any of the functions in `exampleContract`. There is
just one function for this example, so it will just call `doStuff` with different values across multiple calls.

If we run this test, we can see it finds out that if you call `doStuff` twice (once with the value `7`), it will break
our invariant!

```bash
$ forge test -m invariant_testAlwaysReturnsZero

Failing tests:
Encountered 1 failing test in test/MyContractTest.t.sol:MyContractTest
[FAIL. Reason: Assertion violated]
        [Sequence]
                sender=0x000000000000000000000000000000000000018f addr=[src/MyContract.sol:MyContract]0x5615deb798bb3e4dfa0139dfa1b3d433cc23b72f calldata=doStuff(uint256), args=[7]
                sender=0x0000000008ba49893f3f5ba10c99ef3a4209b646 addr=[src/MyContract.sol:MyContract]0x5615deb798bb3e4dfa0139dfa1b3d433cc23b72f calldata=doStuff(uint256), args=[2390]
```

Perfect! It shows us the exact sequence of calls that broke our invariant.

## Real-World Smart Contract Invariants

In an actual smart contract, your invariants won't be that a balloon shouldn't pop or some function should always be
zero; they'll be something like:

- New tokens minted < inflation rate
- There should only be 1 winner of a random lottery
- Someone shouldn't be able to take more money out of the protocol than they put in
- The protocol must always be over-collateralized
- Total supply should equal sum of all balances

## Fuzz Testing Tools

- [Foundry](https://github.com/foundry-rs/foundry/)
- [Echidna](https://github.com/crytic/echidna)
- [Medusa](https://github.com/crytic/medusa)

## Best Practices

1. **Start with Unit Tests**: Build your foundation with comprehensive unit tests first
2. **Identify Invariants**: Clearly define what properties must always hold
3. **Use Stateful Fuzzing**: Most real bugs require multiple function calls to trigger
4. **Bound Your Inputs**: Use realistic parameter ranges in handlers
5. **Document Invariants**: Make your invariants clear in comments and documentation

## References

Much of this document was inspired by the
[Cyfrin Updraft fuzzing](https://patrickalphac.medium.com/fuzz-invariant-tests-the-new-bare-minimum-for-smart-contract-security-87ebe150e88c)
curriculum.

---


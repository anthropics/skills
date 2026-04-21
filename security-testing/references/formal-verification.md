# Formal Verification

Formal verification is the act of proving or disproving a given property of a system using a mathematical model. While
fuzz testing tries to break properties by throwing random data at your system, formal verification tries to break
properties using mathematical proofs.

This is the highest level of assurance you can achieve in smart contract testing - mathematical certainty that your code
behaves correctly under all possible conditions. The downside, is that it is often the most time-consuming to get
correct.

## What is Formal Verification?

Think of formal verification as translating your code into a mathematical model and using formal reasoning to prove
whether certain properties hold. Unlike fuzzing, which tests the program with many random inputs, formal verification
explores the program’s behavior through modeling rather than relying on specific test cases.

For example, if you want to prove that a function should never revert, formal verification will create mathematical
representations of all possible code paths and determine if any input could cause a revert.

## Symbolic Execution

The most popular technique for formal verification in smart contracts is **symbolic execution**. In a nutshell, symbolic
execution explores **every possible execution path** mathematically.

Here's how it works:

### 1. Explore All Possible Paths

Consider this simple function:

```solidity
function f(uint256 a) public pure returns (uint256) {
    return a + 1;
}
```

If our property is "this function should never revert", symbolic execution will find two possible paths:

- **Path 1**: `a < type(uint256).max` → returns `a + 1`
- **Path 2**: `a == type(uint256).max` → overflows and reverts

### 2. Convert Paths to Mathematical Expressions

These paths become boolean expressions:

**Path 1**: `a < type(uint256).max`
**Path 2**: `a == type(uint256).max AND a + 1 < a`

### 3. Feed to SMT/SAT Solver

These expressions are converted to SMT-LIB format and sent to solvers like Z3:

```lisp
; Declare a symbolic integer variable 'a'
(declare-const a (_ BitVec 256))

; Path 2: Check if overflow is possible
(assert (= a #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
(assert (bvult (bvadd a (_ bv1 256)) a))
(check-sat)
```

If the solver returns `sat` (satisfiable), it found an input that breaks your property!

## Real-World Example: Complex Math Functions

Here's where formal verification really shines - catching bugs in complex mathematical code that would be nearly
impossible to find manually or through testing.

Consider this
[intentionally confusing contract with custom operators](https://github.com/Cyfrin/sc-exploits-minimized/blob/main/src/invariant-break/FormalVerificationCatches.sol):

*It has been truncated for space here:*

```solidity
// Custom type with confusing operator overloads
type Int is uint256;

using {add as -} for Int global;  // - actually does division!
using {div as +} for Int global;  // + actually does multiplication!
using {mul as / } for Int global; // / actually does subtraction!
using {sub as *} for Int global;  // * actually does addition!

function add(Int a, Int b) pure returns (Int) {
    return Int.wrap(Int.unwrap(a) / Int.unwrap(b)); // Division
}

contract FormalVerificationCatches {
    function hellFunc(uint128 numberr) public view returns (uint256) {
        // Extremely complex math with many nested conditions
        // and confusing operator overloads...
        // (hundreds of lines of complex mathematical operations)
    }
}
```

### Formal Verification Test with Halmos

We can use [Halmos](https://github.com/a16z/halmos) (a symbolic execution tool) to verify this function never reverts:

```solidity

contract HalmosTest is Test {
    FormalVerificationCatches fvc;

    function setUp() public {
        fvc = new FormalVerificationCatches();
    }

    // Symbolic execution test with Halmos
    // Run with: halmos --function check_hellFunc_doesnt_revert_halmos
    function check_hellFunc_doesnt_revert_halmos(uint128 num) public view {
        (bool success,) = address(fvc).staticcall(
            abi.encodeWithSelector(fvc.hellFunc.selector, num)
        );
        assert(success);
    }
}
```

### The Power of Formal Verification

When you run this test, Halmos will output:

```bash
[FAIL] check_hellFunc_doesnt_revert_halmos(uint128) (paths: 10/18, time: 3.05s)
Counterexample:
    p_num_uint128 = 0x0000000000000000000000000000000000000063 (99)
```

**Formal verification found that input `99` causes the function to revert!**

This bug would be difficult to find through:

- Manual review (very complex to trace)
- Unit testing (would need to test that exact input)
- Fuzz testing (might miss this specific edge case)

But formal verification explored all mathematical paths and proved the bug exists.

## Limitations

Formal verification is not a silver bullet:

### Path Explosion Problem

Complex contracts can have too many execution paths for tools to explore in reasonable time.

### Significant Effort Required

Often, to get this right, this technique requires significant effort to be used. You need to understand how they work,
their limitations, and how to help them.

### Specification Challenge

You must clearly define what properties you want to prove. If your specification is wrong, verification is useless.

### Solver Limitations

Sometimes solvers cannot find solutions to complex mathematical problems within reasonable timeouts.

## Tools and Frameworks

**Symbolic Execution Tools:**

- [Halmos](https://github.com/a16z/halmos) - Symbolic testing for Foundry
- [HEVM](https://github.com/ethereum/hevm) - Haskell EVM with symbolic execution
- [certora prover](https://github.com/Certora/CertoraProver)

**SMT/SAT Solvers:**

- [Z3](https://github.com/Z3Prover/z3) - Microsoft's theorem prover
- [CVC4](https://cvc4.github.io/) - Automatic theorem prover

**Built-in Options:**

- Solidity SMT Checker - Built into the compiler

## References

This document was inspired by
[this article](https://patrickalphac.medium.com/formal-verification-symbolic-execution-the-security-silver-bullet-38e0ac9072eb)
and the [Cyfrin Updraft formal verification curriculum](https://updraft.cyfrin.io/courses/formal-verification).

---


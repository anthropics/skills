## What is Mutation Testing?

Mutation testing is a technique used to evaluate the quality of a test suite by introducing small changes (mutations) to
the code and checking if the tests catch these changes. Each change, called a "mutant," simulates a potential bug. If
your tests fail when a mutant is introduced, the mutant is "killed," indicating your tests are effective. If the tests
pass, the mutant "survives," revealing a potential gap in your test coverage.

## How does it work?

The exact behavior varies depending on the tool used, but the general flow looks like this:

1. **Mutant Generation**: The mutation testing tool automatically modifies your source code in small ways (e.g.,
changing a `+` to a `-`, or replacing a `<` with a `=<`).
2. **Test Execution**: The full test suite is run against each mutant version of the code.
3. **Result Analysis**: If the tests fail for a mutant, it is considered "killed." If the tests pass, the mutant
"survives," indicating that the test suite did not detect the change.
4. **Mutation Score**: The effectiveness of your tests is measured by the mutation score, calculated as the percentage
of mutants killed by the test suite.

## Types of Mutants

There is a wide range of mutations that you can have, ranging from common software engineering ones to solidity-specific
ones, for example:

**Common Types:**

- **Arithmetic Operator Replacement**: Changes `+` to `-`.
- **Relational Operator Replacement**: Alters `==` to `!=`.
- **Logical Operator Replacement**: Modifies `&&` to `||`.
- **Conditional Boundary Changes**: Adjusts `>=` to `>`.
- **Constant Replacement**: Replaces `0` constants with `1`.
- **Statement Removal**: Removes or skips statements to simulate missing logic.

**Solidity specific:**

- **Data Location Keyword Replacement:** Changing `memory` to `storage` and vice versa.
- **Call Type Replacement:** Changing `delegatecall()` to `call()`.
- **Modifier Deletion or Insertion:** Removing or inserting for example `onlyOwner()` modifier.
- **Exception Handling Deletion:** Remove `require()` statements.

## Selecting mutations

Depending on the framework you use and the protocol you are building, you will have to pick appropriate mutators. The
balance is the following:

- More mutations -> Longer execution time -> Potentially more coverage
- Less mutations -> Quicker execution time -> Potentially less coverage

Here are some examples of types of issues that mutation testing is particularly effective at spotting and types of
operators you should consider using:

- **Logic Errors:** [Off-by-one errors](https://en.wikipedia.org/wiki/Off-by-one_error), incorrect comparison operators,
wrong arithmetic operations, and logical operator mistakes.
- **Edge Case Failures:** Boundary condition bugs, empty value handling, Overflow/underflow issues.
- **Validation:** Missing access controls, Insufficient validation.

What it's NOT good at:

- Design-level architectural flaws
- Complex integration bugs requiring multiple components
- Performance issues not related to logic
- Documentation or specification mismatches

## Modifier Mutation Example

Let's say you have this simple Token Vault that allows users to withdraw funds:

```solidity
contract TokenVault {
 mapping(address => uint256) public balances;
 address public owner;

 modifier onlyOwner() {
 require(msg.sender == owner, "Not authorized");
 _;
 }

 // assume there is a deposit function as well here

 function withdraw(uint256 amount) external onlyOwner {
 require(balances[msg.sender] >= amount, "Insufficient balance");
 balances[msg.sender] -= amount;
 payable(msg.sender).transfer(amount);
 }
}
```

Let's now use [SuMo](https://github.com/MorenaBarboni/SuMo-SOlidity-MUtator), as they have their modifier list easily
available.

We could apply the following mutation to this code:

- Remove `onlyOwner` modifier, using `MOD` operator.  → Tests should fail when non-owner calls withdraw.
- Change `>=` to `>`, using the `BOR` operator. To be mindful, this will produce a lot of mutations with other operators
as well. → Tests should fail for exact balance withdrawals.
- Change `-=` to `+=`, using `AOR` operator. Similarly to `BOR` will produce a lot of mutations. → Tests should fail
(balance increases instead of decreases).
- Remove the `require` statement, using the `EHD` operator. → Tests should fail when withdrawing more than the balance.

The tool will produce a report, where survived and killed mutations will be highlighted. The next step would be to
investigate whether any mutations have survived and, if so, whether testing for that case makes sense, or if there is a
bug in the code.

## Best Practices and things to keep in mind

### 1. Make sure your Line and Branch coverage is already very high, close to 100%

Mutation testing is essentially a "meta-test" of your test suite. If your tests don't even execute certain lines of code
(low line coverage), then mutations in those lines will always survive because the tests never run that code path. This
makes mutation testing ineffective and misleading; hence, improving line and branch coverage first is the priority
before attempting mutation testing.

### 2. Achieving a 100% mutation score might not be feasible

A 100% mutation score indicates that no mutants have survived the test. Fundamentally, it is the end goal, but can be
sometimes infesable and unnecessary, especially as the codebase grows in size. Instead 100% should be strived for, and
every survived mutant carefully examined to see if that mutation makes sense and if the test should cover it.

### 3. Consider using only a subset of the mutators available

Not all mutation operators are equally useful for every project. Some may generate mutants that are irrelevant or
impossible to kill due to language constraints or business logic. A larger subset of mutators will also take
significantly longer to run, especially if there are many replacements per mutation.

### 4. Consider using cloud infrastructure if your codebase is reasonably large

Due to how mutation testing works, the larger the codebase size, naturally, the more mutants there will be, which
increases the runtime of the test suite. Let's say you have 2k LoC, and you want to mutate `>` operator, you might have
100 occurrences of that operator, where each will be mutated 4 times, leaving you already with 400 variations of the
codebase, where you have to run the whole test suite on. So it is not unusual for mutation testing to take multiple
hours to run. Hence, having a remote cloud setup for such testing is advisable.

## Limitations

- Mutation testing is a time-consuming process and is only as good as the mutations it generates. Therefore, selecting
the key mutations is a crucial step.
- Mutation testing is only as good as your existing test suite. If your tests are fundamentally flawed, mutation testing
won't help identify the real issues.
- Focuses primarily on unit-level testing and may miss integration-level or system-level bugs that require broader
context.

In summary, mutation testing is a great tool if used correctly, but it is not a silver bullet for ensuring code quality.
While it can significantly improve test quality by identifying gaps in your test suite, it requires careful
configuration and interpretation of results.

## Tools and Frameworks

- [SuMo](https://github.com/MorenaBarboni/SuMo-SOlidity-MUtator) by MorenaBarboni
- [vertigo-rs](https://github.com/RareSkills/vertigo-rs) by RareSkills
- [Gambit](https://github.com/Certora/gambit) by Certora
- [UniversalMutator](https://github.com/sambacha/universalmutator/tree/new-solidity-rules) by sambacha. However, it is a
generalized mutation testing framework, which may lack the Solidity-specific mutators that the others contain.

## References

This guide was heavily inspired by the following:

1. [RareSkills Solidity Mutation Testing](https://rareskills.io/post/solidity-mutation-testing#gdvnie-100-line-and-branch-coverage-is-important-for-mutation-testing)
2. [Metana Solidity Mutation Testing](https://metana.io/blog/solidity-mutation-testing/)

---


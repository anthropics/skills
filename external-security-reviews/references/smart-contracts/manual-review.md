# Manual Review

Manual review of a smart contract is the process of carefully examining the source code to identify potential
vulnerabilities, logic errors, and design flaws.
The approach to manual review can vary from person to person or team to team. This document outlines some of the
possible things the process can comprise.

## Gather resources

1. **Scope:**
This can be a link to the code repository. e.g. Github, Gitlab link which consist of all the smart contracts required to
be reviewed.

2. **Commit hash:**
Agree on a specific commit hash from the repository and freeze the previously defined scope. Avoid continuous
modifications to the codebase. Any changes should be communicated, and the commit hash should be updated for the code
under review.

3. **Documentation and specification:**
    - Documentation describes how the code works, how to use it, and its expected functionality.
    - Specification defines the exact requirements, constraints, and behaviors the system must meet, including
    invariants that must always hold true.
        - Invariants are the properties of the system that should always hold. Invariants can be useful for checking the
        expected behavior of the system when the certain actions or a transaction flow is executed. Invariants are
        useful in many testing approaches, including manual reviews, where a reviewer checks whether a specific
        property can be violated for a function under any sequence of function calls.
        - Get simplified math formulas if the protocol has any custom/fancy formulas implemented.

4. **Tests:**
Tests are important for understanding the expected behavior and ensuring that the system works as intended. The
following types of tests can be useful for understanding and verifying the code:
    - [unit tests](/security-testing/unit-testing): Unit tests ensure that individual functions behave correctly under
    expected conditions.
    - [Integration Tests](/security-testing/integration-testing): Integration tests verify that your smart contracts
    work correctly with real external systems.

## Smart contract higher overview

1. **Documentation and whitepaper walkthrough:**
Go through the whitepaper and documentation to gain a better understanding of the project and to see how the proposed
business logic is structured. What are the involved components.

2. **High level idea:**
Get a high level idea behind the project: Through diagrams, developer walkthrough.

3. **Structural overview:**
Get a structural overview of the project: Check how integration of contracts and functions is happening throughout the
protocol.

4. **Create a diagram:**
Based on the structural and functional understanding the high level diagram can be created if required.
    - The diagram can be modified over a time as you get more understanding.
    - The diagram can grow more complex and detailed depending on the time.
    - There are many tools that can be used like Excalidraw, Miro, Lucidchart, Mermaid etc.
    - High level structural example of staking diagram:

<MermaidRenderer
id="manual-review-diagram"
code={`classDiagram
direction LR
class Token {
  +mint()
  +burn()
  +transfer()
  +transferFrom()
}
class Staking {
  +constructor()
  +stake()
  +unstake()
  +getStakedAmount()
  +getTotalStaked()
}
class Rewards {
  +calculateRewards()
  +claimRewards()
  +initialize()
}
class Bridge {
  +transferToChain()
  +transferFromChain()
}
Token --> Staking: used in
Staking --> Token
Staking --> Rewards
Staking --> Bridge : bridges token`} />

## Manual review

1. **Understand the flow:**
Understand the flow from [unit](/security-testing/unit-testing) and [Integration](/security-testing/integration-testing)
tests. Test cases are important. They give you an understanding of how the setup works and what state needs to be in
place for users to start using the system’s entry points. They also give you time to test more offensive or edge-case
scenarios (after verifying unit tests) instead of spending most of your time testing general scenarios.

    - When math formulas or complex interconnected calls are involved, debugging the values of variables helps sometime
    to see how the state changes are happening e.g. what is the value of variable `x/totalStakedEth` before the specific
    internal/external call. or what it becomes after that call.
    - Debugging can be done in many ways, depending on which framework you are using. Some examples are.
        - Foundry - native debugger, console logs in the contracts, Tenderly debugger, simbolik.
        - Hardhat - console logs in the contracts, debuggers like Hardhat-tracer, Tenderly debugger.

2. **Choose least dependent contract to review one by one:**
This can be done by looking into a diagram and current understanding of the smart contract functionality. For example
in this case it's a Token contract that is least dependent (in fact the functionality from that contract is getting used
in other contracts so other smart contracts are dependent on it).

3. **Checklist reviews:**
    - Known smart contract vulnerabilities checklist.
    - Project specific checklists (e.g. When dealing with bridges it's also important to check bridge specific
    checklists).
    - Checklists may vary over time and can become outdated. Below are some examples for reference:
        - [Smart Contract Security Field Guide](https://scsfg.io/hackers/)
        - [Smart Contract Security Verification
        Standard](https://github.com/ComposableSecurity/SCSVS?tab=readme-ov-file#table-of-contents)

4. **Maintain a list of invariants:**
Maintain a list of invariants for every functions (Can be useful later for other tests/fuzzing/format verification).

5. **Offensively analyze the code:**
Offensively analyze the code to identify logical issues, edge cases, and any conditions that could break invariants.

6. **Visit all paths:**
Visiting all paths in a smart contract is crucial from a security perspective. For example, in the below
`withdraw()` function, every path has its own potential security implications and behavior that needs to be verified.
Sometimes these unexpected paths lead us to potential bugs. Generally frameworks provide tools to check test coverage,
like the [forge coverage](https://getfoundry.sh/forge/reference/coverage/) command which can be used to generate code
coverage reports for tests.

    > While this section focuses more on manual approach, automated testing approaches like fuzzing and formal
    > verification can be useful here for checking possible invariant violations across multiple paths.

    As can be seen below, everything boils down to each path. Even the ternary expression is ultimately a path.

    ```solidity
    function withdraw(uint256 amount, bool emergency) public {
            require(amount > 0, "Withdraw amount must be greater than 0");
            uint256 balance = balances[msg.sender];
            bool success;

            if (emergency) {
                success = (address(this).balance >= amount) ? payable(msg.sender).send(amount) : false;
            } else {
                if (balance >= amount) {
                    balances[msg.sender] -= amount;
                    totalBalance -= amount;
                    success = payable(msg.sender).send(amount);
                } else {
                    success = false;
                }
            }

            if (!success) {
                // call other contract to handle failed withdrawal
            }
            emit Withdrawn(msg.sender, amount, success);
    }
    ```

    In next example, because every value (`_amount`, `minRequired`) can go increase or decrease, the results can vary.
    If the result is used for some operations like decreasing the `drivingScore` in `burnFuelAndReduce()` for example.

    E.g. depending on the amounts are same (as they were while filling the fuel) or increased or decreased, the value of
    `fuelReduction` will change and while subtracting it from the `drivingScore[msg.sender]` it needs to be handled
    accordingly. which also creates different paths.

    ```solidity
    function fillFuelAndCalculate(uint256 _amount) public {
            require(_amount > minRequired, "ERR");
            fuelTank[msg.sender] += _amount;
            drivingScore[msg.sender] += (_amount * multiplier) / minRequired;
    }

    function burnFuelAndReduce(uint256 _amount) public {
            fuelTank[msg.sender] -= _amount;
            uint256 fuelReduction = (_amount * multiplier) / minRequired;
            drivingScore[msg.sender] = drivingScore[msg.sender] > fuelReduction ? drivingScore[msg.sender] - fuelReduction : 0;
    }
    ```

7. **Write down notes, doubts and edge cases:**
One reason for writing down questions, ideas, possible issues is, when you start going through these issues as you
encounter new path you can see more doubts, possible issues in your mind. So sometimes it becomes a loop where you will
keep thinking about new ideas while exploring previous/current one.
    - Take notes to check your understanding.
    - Write down any questions to ask developers when you need clarification.
    - Note down edge cases for later testing. E.g: [test] Possible reentrancy in unstake() function.
    - Try to break down the business logic while going through every code block. (again note down the thing that needs
    to be tested)
    - Write down things to revisit after the code is fixed. E.g: In the review you noticed that if specific
    functionality would be added based on doubts asked or based on the suggested fixes etc, there are chances of something
    to go wrong for example. Note it down and check in the **Fixed code review**.
    - The minimal markdown file for taking notes might look like this:

    ```markdown
    # Project Name
    ## Scope:  
    GH link:  
    Commit hash:  

    ## Flow:
    1. Manual review
    2. Functional testing:
        - Unit testing
        - Edge case testing
    3. Automated testing:
        - ...
    4. ...

    ## Resources:
    1. Specification doc:
    2. Whitepaper:
    3. Any other documentation and links.

    ## ToDo:
    *Things to do/ remaining things.*   
    1. High level things about audit 
    2. Developer project walk-through.
    3. ...

    ## Common/Doubts/Research:
    1. Relearn about specific cross chain service/protocol that's getting used.

    ## ContractName.sol
    *This contains doubts/points/research/potential bugs regarding the ContractName.sol*
    1. Confirmed issue 1.
    2. Confirmed issue 2.
        ### Doubts/Research:
        1. Checking specific formulas.
        2. Checking specific doubt.
        3. Check the subtraction on L453 can be a problem.
        4. [revisit] Revisit something based on the suggestion given.
        * Testcases:  
            1. [test] User should be able to stake.
            2. [test] Multiple users should be able to stake.
            3. [test] ...

    ## ContractName2.sol
    *This contains doubts/points/research/potential bugs regarding the ContractName2.sol*
    ...

    ---
    ## Questions for developers:
    1. Explanation for formulas.
    2. Questions about intended logic.
    3. ...
    ```

## Functional testing

1. Check any missing test cases that should be covered.

2. Write and test edge cases from notes taken while manually reviewing contracts.

## Automated review

While automated review can be classified as a different approach from manual review, it is useful to use techniques such
as [static analysis](/security-testing/static-analysis) to identify low-hanging bugs by triaging warnings from tools
like [Slither](https://github.com/crytic/slither), [Wake](https://github.com/Ackee-Blockchain/wake),
[Aderyn](https://github.com/Cyfrin/aderyn) etc.

> There are other types of automated testing approaches, such as [Fuzz Testing](/security-testing/fuzz-testing) and
> [formal verification](/security-testing/formal-verification), can also be helpful at different stages of the audit
> life-cycle, though they are less directly related to manual review.

## Report writing

1. **Questions and issue discussion with internal team:**
Discuss any questions and identified issues with the internal team or, if applicable, with the team of reviewers working
in parallel on the project. This will help you reach a conclusion.

2. **Questions and issue discussion with the developers or project team:**
Discuss and convey issues to the developers or project teams, as applicable. The goal is the technical dev. members of
team should get issues so they can try to fix them. It can save time in large projects once the report is delivered.

3. **Report writing:**
While the structure of a report and the issues/bugs it documents may vary, the following elements are helpful to
include:
    - Public link to the code repository.
    - The commit hash pointing to the recently reviewed commit.
    - Issues can include a detailed description, recommendations, severity, status, the commit where the issue was
    fixed, and acknowledgments from developers.
    - References to correct functions and line numbers while writing issues.
    - Example and POC, helpful for critical bugs.
    - Checking the grammar/style for better readability.

## Updated code review

For checking fixed code, it may be necessary to repeat previously performed actions, depending on what has changed. To
avoid repeating work, you can:

1. **Code comparison:**
This helps in identifying updates and detecting deviations from expected changes. For example, a git diff may reveal
changes in functions that should not have been changed.

2. **Reviewing updated code:**
Review the updated code to check expected and unexpected changes.

3. **Run all the tests:**
Run all available tests on the updated code to ensure the newly updated code does not break any invariant.

4. **Write new tests for the updated code:**
If the updated code creates any new control flow paths it's necessary to write tests to visit those paths and to ensure
it yields the expected output.

5. **Go through checklists again:**
For the updated functionality (depending on what has been changed), review the checklists to ensure that no
vulnerabilities remain or have been introduced.

6. **Check things/notes that needs to be revisited:**
Check items or notes that need to be revisited from the manual review. Sometimes you may have observations noted, e.g.,
Adding this fix to the code can create this problem.

7. **Update the report:**
Update the report and issue status based on the updated code.
    - Change the status.
    - Add/update most recently reviewed commit link/hash.
    - Add comments from the audit team (when required).
        - These may include, for example, the reason why an issue remains open, any unresolved security concerns, or
        even new issues created by the fixes, but are not limited to these.
    - Add comments from the project team (when required).
        - These may include the reasons why an issue is acknowledged, or mitigations that will not be implemented at the
        smart contract level, but are not limited to these.

## Final thoughts

Having multiple teams/members review each contract individually leads to better results, as it ensures more sets of eyes
are examining the code.

## References

- [Auditing mental model by Caliber](https://www.calibersec.com/smart-contract-auditing-mental-model/)

---


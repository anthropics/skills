---
name: logic-lens
description: AI code analyzer that catches logic errors, runtime bugs, and correctness issues that compilers and type systems miss. Use when reviewing code for null/undefined dereference, race conditions, integer overflow, off-by-one errors, SQL injection, authentication bypass, memory leaks, infinite loops, state machine violations, and other runtime failure patterns. Covers 9 risk categories across 49 scenario types. Pairs with brooks-lint for full-stack code review coverage.
license: Apache-2.0
---

# logic-lens

AI code analyzer that catches logic errors and runtime bugs that compilers, type checkers, and linters miss. Where brooks-lint reviews architectural structure, logic-lens reviews runtime correctness.

## When to Use This Skill

Use logic-lens when you want to verify that code will actually work correctly at runtime. Ideal for:

- Security-sensitive code (auth, payments, data access)
- Concurrent/async code (race conditions, deadlocks)
- Data processing with edge cases (overflow, empty inputs, nulls)
- Code that has been failing in production in unexpected ways
- Pre-release review of critical paths

## How It Works

logic-lens analyzes code across 9 risk categories covering 49 scenario types:

| Category | What It Catches |
|----------|-----------------|
| C1 - Null/Undefined | Null dereference, optional chaining gaps, uninitialized variables |
| C2 - Race Conditions | TOCTOU, check-then-act, unsynchronized shared state |
| C3 - Integer/Numeric | Overflow, underflow, division by zero, float comparison |
| C4 - Collection/Array | Off-by-one, empty collection, index out of bounds |
| C5 - Control Flow | Infinite loops, unreachable code, missing break/return |
| C6 - State Machine | Invalid state transitions, missing states, state corruption |
| C7 - Resource Management | Memory leaks, unclosed handles, connection pool exhaustion |
| C8 - Security Logic | SQL injection, auth bypass, insecure deserialization, path traversal |
| C9 - Silent Failure | Swallowed exceptions, ignored return values, lost error context |

## Commands

When this skill is active, respond to these slash commands:

- /logic-lens <file>         Full analysis across all 9 categories
- /logic-quick <file>        Fast scan for critical issues only (C1, C2, C8)
- /logic-security <file>     Security-focused review (C8 deep dive)
- /logic-concurrency <file>  Concurrency and race condition focused (C2)
- /logic-trace <file> <path> Trace execution along a specific code path

## Review Process

For each file analyzed:

1. Read the complete file
2. For each of the 9 categories (C1-C9), scan for known patterns
3. For each finding, report:
   - Category and severity (CRITICAL / HIGH / MEDIUM / LOW)
      - Exact line number
         - What will go wrong at runtime (the failure mode)
            - A concrete fix
            4. Prioritize findings: CRITICAL first (data loss, security breach, crash)
            5. Provide summary with counts by severity

            Severity guide:
            - CRITICAL: Can cause data loss, security breach, or system crash
            - HIGH: Will cause incorrect behavior or failures under expected load
            - MEDIUM: Will fail under specific but realistic conditions
            - LOW: Edge case or defensive programming gap

            ## Example Output

            ```
            /logic-lens src/order/OrderProcessor.ts

            Analyzing 312 lines across 9 logic categories...

            C1 - NULL DEREFERENCE (CRITICAL) - Line 47
            user.address.city accessed without null check.
            Guest checkout users have no address object.
            Failure: NullPointerException at checkout for guest users.
            Fix: user.address?.city ?? 'Unknown'

            C2 - RACE CONDITION (CRITICAL) - Line 103
            inventory.count checked (line 103) then decremented (line 118) in separate operations.
            Under concurrent load, two threads both pass the check before either decrements.
            Failure: Overselling inventory under concurrent requests.
            Fix: Use atomic compare-and-decrement with minimum-value guard.

            C4 - OFF-BY-ONE (HIGH) - Line 156
            Loop condition: i <= items.length (should be i < items.length)
            Failure: ArrayIndexOutOfBoundsException on last iteration for any non-empty order.
            Fix: Change <= to <

            C9 - SILENT FAILURE (HIGH) - Line 203
            Empty catch block swallows payment gateway exception.
            Failure: Payment failures silently ignored, orders marked complete with no payment.
            Fix: Log exception, set order status to PAYMENT_FAILED, return error response.

            C8 - SECURITY: No critical findings in this file.

            Summary: 2 CRITICAL, 2 HIGH, 0 MEDIUM, 0 LOW
            Fix order: C2 (data integrity) > C1 (crash) > C4 (crash) > C9 (silent data loss)
            ```

            ## The 49 Scenario Types

            Full list of patterns logic-lens checks:

            **C1 - Null/Undefined (6 scenarios)**
            Null dereference, undefined property access, uninitialized variable use,
            optional chain bypass, null return not handled, nullable parameter ignored

            **C2 - Race Conditions (5 scenarios)**
            TOCTOU (check-then-act), unsynchronized shared state, double-checked locking,
            lost update, phantom read

            **C3 - Integer/Numeric (6 scenarios)**
            Signed integer overflow, unsigned wraparound, division by zero,
            float equality comparison, precision loss in conversion, accumulation error

            **C4 - Collection/Array (5 scenarios)**
            Off-by-one in loop bounds, empty collection not handled,
            index out of bounds, iterator invalidation, concurrent modification

            **C5 - Control Flow (6 scenarios)**
            Infinite loop, unreachable code after return, missing break in switch,
            fall-through side effect, early return skips cleanup, dead branch

            **C6 - State Machine (5 scenarios)**
            Invalid state transition, missing state in handler, state corruption on error,
            concurrent state mutation, terminal state re-entered

            **C7 - Resource Management (5 scenarios)**
            Memory leak (object held in collection), unclosed file handle,
            database connection not returned to pool, goroutine/thread leak, event listener accumulation

            **C8 - Security Logic (6 scenarios)**
            SQL injection via string concatenation, authentication bypass via logic error,
            insecure direct object reference, path traversal, mass assignment, insecure deserialization

            **C9 - Silent Failure (5 scenarios)**
            Empty catch block, ignored return value from error-returning function,
            exception logged but execution continues incorrectly, error swallowed in async callback,
            partial failure treated as success

            ## Design Philosophy

            Compilers catch syntax errors. Type systems catch type errors. Linters catch style issues.
            logic-lens catches the remaining class of bugs: logical errors that are syntactically valid,
            type-correct, and style-compliant — but will fail at runtime under specific conditions.

            These are often the most expensive bugs because they reach production.

            ## Installation

            ```bash
            claude skills add https://github.com/hyhmrright/logic-lens
            ```

            ## Pairing with brooks-lint

            logic-lens covers **runtime correctness** (will it work?).
            brooks-lint covers **architecture and design** (is the structure sound?).

            Use both for complete code review coverage:
            - brooks-lint: structural problems, technical debt, release risks
            - logic-lens: logic errors, runtime failures, security vulnerabilities

            brooks-lint: https://github.com/hyhmrright/brooks-lint

            ## Source

            GitHub: https://github.com/hyhmrright/logic-lens

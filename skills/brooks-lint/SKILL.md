---
name: brooks-lint
description: AI code reviewer grounded in 12 classic software engineering books (Clean Code, Clean Architecture, The Mythical Man-Month, A Philosophy of Software Design, Refactoring, The Pragmatic Programmer, Designing Data-Intensive Applications, Release It!, Site Reliability Engineering, Accelerate, Software Engineering at Google, The Art of Software Security). Use when you want architectural and design feedback on code files. Identifies god classes, tight coupling, missing abstractions, release risks, and security concerns mapped to 6 risk categories (R1-R6). Pairs with logic-lens for full-stack code review coverage.
license: Apache-2.0
---

# brooks-lint

AI code reviewer grounded in 12 classic software engineering books. Provides architectural and design feedback beyond style checks, identifying structural problems before they compound into technical debt.

## When to Use This Skill

Use brooks-lint when you want to know **why** code is problematic, not just **that** it is. Ideal for:

- Pre-merge architectural review of new features
- Refactoring decisions: what to tackle first?
- Identifying release risks before shipping to production
- Security-focused review of sensitive modules
- Before/after comparison when rewriting code

## How It Works

brooks-lint maps every finding to one of 6 risk categories (R1-R6), each grounded in specific books:

| Category | Source | What It Catches |
|----------|--------|-----------------|
| R1 - Accidental Complexity | A Philosophy of Software Design (Ousterhout) | Deep modules, leaky abstractions, unnecessary complexity |
| R2 - Rotting Design | Refactoring (Fowler) + Clean Code (Martin) | God classes, long methods, feature envy, duplication |
| R3 - Mythical Man-Month Risk | The Mythical Man-Month (Brooks) | Hidden coordination costs, unclear interfaces, team coupling |
| R4 - Pragmatic Debt | The Pragmatic Programmer (Hunt & Thomas) | Quick fixes that compound, broken windows, DRY violations |
| R5 - Release Risk | Release It! (Nygard) + SRE (Beyer et al.) | Missing circuit breakers, no timeouts, cascade failure paths |
| R6 - Security Concern | The Art of Software Security (Viega & McGraw) | Input validation gaps, auth bypass patterns, injection risks |

## Commands

When this skill is active, respond to these slash commands:

- /brooks-review <file>     Full architectural review, all 6 risk categories
- /brooks-quick <file>      Fast scan, critical issues only (R1, R5, R6)
- /brooks-refactor <file>   Refactoring-focused review (R2, R4 emphasis)
- /brooks-security <file>   Security-focused deep dive (R6)
- /brooks-compare <v1> <v2> Before/after comparison of two file versions

## Review Process

For each file reviewed:

1. Read the full file
2. Identify issues in each of R1-R6 categories
3. For each finding, cite the specific book principle violated
4. Rate severity: HIGH (fix before release), MEDIUM (fix this sprint), LOW (track as debt)
5. Provide concrete, actionable recommendations
6. Summarize: count of high/medium/low findings, recommended fix order

## Example Output

```
/brooks-review src/payment/PaymentService.ts

Reviewing 847 lines against 12 engineering classics...

R1 - ACCIDENTAL COMPLEXITY (HIGH)
PaymentService handles: payment processing, retry logic, notifications,
audit logging, and fraud detection - 5 responsibilities in one class.
Source: A Philosophy of Software Design ch.4 (Deep Modules),
        Clean Architecture (Single Responsibility Principle)
        Recommendation: Extract PaymentProcessor, AuditLogger, FraudDetector.

        R2 - ROTTING DESIGN (MEDIUM)
        processPayment() is 340 lines with 6 nesting levels.
        Feature envy: reaches into Order internals 12 times.
        Duplication: retry logic copied in 3 places.
        Source: Refactoring (Fowler) - Extract Method, Move Method
        Recommendation: Extract PaymentValidator, centralize retry with backoff.

        R5 - RELEASE RISK (HIGH)
        No circuit breaker on payment gateway calls.
        Retry loop can cascade during gateway outages.
        Source: Release It! (Nygard) - Stability Patterns ch.5
        Recommendation: Wrap gateway calls in circuit breaker pattern.

        R6 - SECURITY: No critical findings.
        Input validation present. Parameterized queries used correctly.

        Summary: 2 HIGH, 1 MEDIUM, 0 LOW
        Fix order: R5 (production risk) > R1 (architecture) > R2 (maintainability)
        ```

        ## The 12 Books

        This skill synthesizes principles from:

        1. Clean Code - Robert C. Martin
        2. Clean Architecture - Robert C. Martin
        3. The Mythical Man-Month - Fred Brooks
        4. A Philosophy of Software Design - John Ousterhout
        5. Refactoring - Martin Fowler
        6. The Pragmatic Programmer - Hunt & Thomas
        7. Designing Data-Intensive Applications - Martin Kleppmann
        8. Release It! - Michael Nygard
        9. Site Reliability Engineering - Beyer, Jones, Petoff, Murphy (Google)
        10. Accelerate - Forsgren, Humble, Kim
        11. Software Engineering at Google - Winters, Manshreck, Wright
        12. The Art of Software Security - Viega & McGraw

        ## Pairing with logic-lens

        brooks-lint covers **architecture and design** (structural problems that cause maintenance and reliability failures).
        logic-lens covers **runtime correctness** (null dereference, race conditions, off-by-ones, type errors).

        Use both for complete code review coverage:
        - brooks-lint: Is the structure sound?
        - logic-lens: Will it work correctly at runtime?

        logic-lens: https://github.com/hyhmrright/logic-lens

        ## Source

        GitHub: https://github.com/hyhmrright/brooks-lint

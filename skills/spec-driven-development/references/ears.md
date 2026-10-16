# EARS Notation Reference

All functional requirements are written using Easy Approach to Requirements Syntax
(EARS). The table below lists the five EARS patterns.

| Pattern        | Template                                                        | Use When                                         |
|----------------|-----------------------------------------------------------------|--------------------------------------------------|
| **Ubiquitous** | The \<system\> shall \<action\>.                               | The behavior applies at all times.               |
| **Event-driven** | When \<trigger\>, the \<system\> shall \<action\>.            | The behavior is triggered by a specific event.   |
| **State-driven** | While \<state\>, the \<system\> shall \<action\>.             | The behavior applies during a specific state.    |
| **Optional**   | Where \<feature\>, the \<system\> shall \<action\>.           | The behavior applies only when a feature is active. |
| **Unwanted**   | The \<system\> shall not \<action\>.                           | The behavior describes something that must never happen. |

## Hard Rules

1. **Stable IDs.** Every requirement receives a stable identifier: `R1`, `R2`, `R3`,
   and so on. IDs never change once assigned. If a requirement is removed, its ID is
   retired (not reused).

2. **Each requirement is verifiable by test.** For every R\<n\>, there must exist at
   least one test that can objectively confirm the requirement is satisfied. If you
   cannot write a test for it, it is not a valid requirement.

3. **One SHALL per requirement.** Each R\<n\> contains exactly one `shall` or
   `shall not`. Do not combine multiple obligations into a single requirement. Split
   them into separate R\<n\> entries.

4. **Only SHALL and SHALL NOT.** Use `shall` for mandatory behavior and `shall not`
   for prohibited behavior. Do not use `should`, `may`, `will`, `must`, or `can` in
   requirement text.

## Examples

```markdown
## R1
The system shall reject login attempts after 5 consecutive failures.

## R2
When the user submits a valid credentials pair, the system shall issue an
authentication token.

## R3
The system shall not reveal whether the username or the password was wrong.
```

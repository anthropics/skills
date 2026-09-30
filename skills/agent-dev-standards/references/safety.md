# Safety
Injection prevention, permission model, and data isolation.
## Prompt Injection Prevention
1. Input isolation: Never interpolate raw user input into system prompt.
2. Instruction boundary: System prompt ends with a clear delimiter.
3. Output validation: Check generated content for leaked system prompt.
4. Rate limit: Cap tool calls per session (max 50).
## Permission Model
| Level | Operations | Example |
|-------|-----------|---------|
| read-only | read, search, list | Document search agent |
| write-scoped | read + write to specific paths | Code review agent |
| exec-scoped | read + write + exec whitelisted commands | Coding agent |
| admin | full access | Setup agent |
## Data Isolation
1. Agent sessions are isolated: no cross-session data access.
2. Tool outputs are scoped: agent can only see results of tools it called.
3. Sensitive data masking: API keys, passwords, PII filtered.
4. Audit log: every tool call logged with caller, target, timestamp, result.
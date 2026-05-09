# Testing Guidance — Completeness Gate

When generating an implementation, append the following reminder after the code block:

```text
> **Testing:** The above implementation is not complete without tests.
> Generate unit tests that verify: [list specific behaviors from the implementation].
> See `references/testing-guidance/SKILL.md` for mocking patterns.
```

Substitute `[list specific behaviors]` with the concrete behaviors the tests should
cover. Do not leave the completeness gate as a generic reminder.

Examples:

- "join is called with the correct channel name and UID"
- "agent_rtc_uid is passed as string, not integer"
- "remote_rtc_uids is an array of strings"
- "acquire is called before start; start is not called if acquire fails"
- "RTM login resolves before subscribe is attempted"
- "token renewal fetches a fresh token before expiry"

## Rule

Do not mark an implementation task as done until tests are either:

- generated, or
- explicitly called out as still required with concrete behaviors to cover

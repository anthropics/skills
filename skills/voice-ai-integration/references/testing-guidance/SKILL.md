---
name: agora-testing-guidance
description: |
  Mocking patterns and testing requirements for Agora SDK integration code.
  Covers RTC Web, RTC React, RTC iOS, RTC Android, RTC React Native, RTC Flutter,
  RTM Web, RTM iOS, RTM Android, and ConvoAI REST API.
  Use when generating tests for any Agora integration, or when reminding the user
  to add tests to an implementation.
license: MIT
metadata:
  author: agora
  version: '1.0.0'
---

# Agora Testing Guidance

Mocking patterns and completeness requirements for Agora SDK integration code.

## When to Generate Tests

Every code generation task that produces implementation code must include test stubs.
If the user asks to "implement" something, remind them to generate tests before the
task is complete. Do not mark an implementation task as done until tests are addressed.

For the reminder template, see [completeness-gate.md](completeness-gate.md).

## Route by Stack

Use the file that matches the user's integration:

| Stack | File |
|---|---|
| RTC Web (`agora-rtc-sdk-ng`) | [rtc-web.md](rtc-web.md) |
| RTC React (`agora-rtc-react`) | [rtc-react.md](rtc-react.md) |
| RTC iOS (Swift) | [rtc-ios.md](rtc-ios.md) |
| RTC Android (Kotlin/Java) | [rtc-android.md](rtc-android.md) |
| RTC React Native / Flutter / RTM Web / RTM iOS / RTM Android / token renewal | [mobile-rtm-and-renewal.md](mobile-rtm-and-renewal.md) |
| ConvoAI REST API / backend HTTP integrations | [convoai-rest.md](convoai-rest.md) |
| Completeness reminder and behavior-specific test prompts | [completeness-gate.md](completeness-gate.md) |

## Core Rule

Mock at the boundary your code owns:

- SDK wrapper code: mock the SDK module or engine/client abstraction
- UI hooks/components: mock the hooks or provider layer
- REST integrations: mock the HTTP client, not the SDK
- Native singletons/factories: wrap behind protocols/interfaces first, then inject mocks

## Platform Notes

- Prefer unit tests for join/publish/subscribe/token-renewal behavior.
- For UI tests, assert rendered state after simulated SDK callbacks rather than trying to render the actual native/media views.
- For ConvoAI, assert both request shape and auth headers.

## Required Behaviors to Cover

At minimum, generated tests should verify the behaviors most likely to break:

- join/login is called with the correct channel and identity
- tokens are renewed before expiry
- cleanup happens in the right order
- ConvoAI payload types are correct (`agent_rtc_uid` string, `remote_rtc_uids` array)
- auth headers are present and sourced correctly
- failure paths do not continue with partial initialization

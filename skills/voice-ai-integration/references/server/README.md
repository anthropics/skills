# Agora Server-Side: Token Generation

Server-side token generation for Agora authentication.

## When Tokens Are Needed

- **Production**: Always. Tokens authenticate users before they join channels.
- **Testing/Development**: Technically optional — token auth can be disabled in [Agora Console](https://console.agora.io), allowing `null` to be passed as the token. **Warn the user if they attempt this**: any channel can be joined by anyone without authentication. This is never acceptable for production and should be avoided even in development unless strictly necessary.
- **No App Certificate provided**: If the user has no App Certificate, they cannot generate tokens. Warn them explicitly that their project has no token security enabled, advise them to enable it in [Agora Console](https://console.agora.io) → Project Management → Edit → App Certificate, and do not proceed to generate code that omits token auth without this warning.
- **Never expose App Certificate on client**. Token generation must happen server-side.

## Token Types

- **RTC Token**: Grants access to join a specific RTC channel with a specific UID. Required for Video/Voice SDK.
- **RTM Token**: Grants access to RTM services for a specific user ID.
- **AccessToken2**: Current token format. Supports privilege expiration per service and can bundle RTC + RTM privileges in a single token.

## Reference Files

- **[tokens.md](tokens.md)** — Token generation for Node.js, Python, and Go. Express server example, security best practices.
- **Full token auth guide** — <https://docs-md.agora.io/en/video-calling/token-authentication/deploy-token-server.md>

## Mid-Conversation System Messages (Quick Reference)

**Claude Opus 5, Claude Opus 4.8, Claude Fable 5, and Claude Mythos 5; not Claude Sonnet 5; no beta header.** Append `{"role": "system", "content": "…"}` to the `messages` array (not the top-level `system` field) to add an operator instruction mid-conversation without invalidating the cached prefix. Use the regular `client.messages.create` — there is no beta. A mid-conversation system message must follow a `user` message (or an `assistant` message ending in server-tool use), and must be either the last entry in `messages` or be followed by an `assistant` turn — it cannot be `messages[0]`. Availability: `shared/platform-availability.md`. See `shared/prompt-caching.md` § Mid-conversation system messages.

---

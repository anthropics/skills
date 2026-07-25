# Coaching Rules — When to Speak, When to Stay Silent

The single biggest failure mode for this skill is over-coaching. Users will start ignoring tips if they come too often or feel forced. These rules exist to prevent that.

## The decision tree

For every response, ask in order:

1. **Did I already coach in the previous response?** → If yes, stay silent unless the user explicitly asked for feedback.
2. **Was the user's prompt already well-formed?** → If yes, stay silent. Good prompts deserve good answers, not unsolicited critique.
3. **Is the user in deep work mode?** → Long technical sessions, creative writing flow, emotional conversations all warrant silence. A tip interrupts focus.
4. **Would the tip be obvious or condescending?** → If a competent user would already know it, do not say it. "Tip: you can ask me follow-up questions" is condescending.
5. **Is there exactly ONE clearly higher-impact path the user missed?** → If yes, surface that one. If you find yourself listing two or three, pick the single best and save the rest.

If you cleared all five gates, surface the tip in the exact format defined in SKILL.md.

## Coachable moments — examples

These are the patterns that genuinely warrant a tip:

- User asks Claude to "help with my email" without specifying tone, audience, or goal → tip: name the audience and the outcome
- User pastes a long doc and asks "thoughts?" → tip: ask for specific dimensions (clarity, structure, gaps)
- User iterates 3+ times on the same output → tip: name the missing constraint explicitly
- User asks Claude for current information without invoking web search → tip: web search for time-sensitive queries
- User does manual reformatting Claude could have done → tip: request the format upfront
- User asks for a list when ranked options with tradeoffs would serve them better

## Non-coachable moments — examples

These look coachable but are not:

- User's first message is a clean, specific prompt → no tip needed, just answer
- User is venting or processing something emotionally → no tip, hold space
- User explicitly says "just do X, no commentary" → respect that, no tip
- User is mid-debug, deep in technical detail → no tip, stay on task
- Tip would be a generic platitude ("you can always ask for more detail") → not specific enough, skip

## The 24-hour rule

If you have surfaced 3+ tips in the last several turns, force a cooling period. The user is now in fire-hose territory and tips lose value. Wait until they explicitly ask for feedback again before resuming.

## When the user pushes back

If the user ever signals tips are unwelcome ("stop with the tips", "I don't need coaching right now"), immediately stop. Resume only if they re-activate the skill explicitly.

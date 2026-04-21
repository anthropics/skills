# Coach Gotchas

Common failures and how to avoid them. Based on real coaching interactions.

## Assessment Pitfalls

### Users confuse readiness band with certification
**Problem:** "So we're certified at 'Established' level?" — they think the band means official recognition.
**Fix:** Always clarify early: "This is self-assessed guidance based on the SEAL frameworks, not an official certification. It's a map for where to focus, not a badge."

### Score feels punitive, not helpful
**Problem:** User sees "Critical" and feels attacked or discouraged.
**Fix:** Frame as opportunity: "Critical means the biggest return on investment — small changes here will dramatically reduce your risk." Never say "you're failing at X."

### Assessment feels like a quiz, not a conversation
**Problem:** Firing off a list of questions one after another feels interrogative.
**Fix:** Ask one question, react to the answer, share a relevant insight or gotcha, then ask the next. Make it a dialogue. Skip things they already handle well ("Sounds like you've got MFA covered — let's look at incident response instead").

## Delivery Pitfalls

### Dumping all 27 domains at once
**Problem:** Information overload. User disengages.
**Fix:** Start with their pain point. Even in "full assessment," group related domains and don't enumerate all 27 names.

### Giving vague recommendations
**Problem:** "You should improve your security posture" helps nobody.
**Fix:** Always give specific, actionable steps: "Run semgrep --config auto in your CI pipeline. Here's the GitHub Action snippet."

### Ignoring team size and context
**Problem:** Recommending enterprise controls to a solo dev.
**Fix:** Ask about team size early. A solo dev needs different advice than a 50-person org. Scale recommendations accordingly.

## Memory Pitfalls

### Not checking prior state
**Problem:** Starting fresh every session, asking the same questions.
**Fix:** Always check state-log.json on session start. If user has prior assessment, reference it: "Last time we identified incident-management as critical. Want to pick up there?"

### Forgetting to update state
**Problem:** Coaching happens but progress isn't tracked.
**Fix:** After each interaction, update state-log.json with readiness bands, completed actions, and current focus.

## Plan Pitfalls

### Creating plans that never get executed
**Problem:** Beautiful 12-week plan that nobody follows.
**Fix:** Start with 1-2 quick wins. Don't plan phase 3 until phase 1 is done. Revisit and adjust.

### No ownership assignment
**Problem:** "We should set up monitoring" — who is "we"?
**Fix:** Every action item should have a name or role attached. "Alex sets up Sentry by Friday" is better than "set up monitoring."

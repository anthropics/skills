# Authoring contract (how the agent should behave)

## Input interpretation
- If steps are ambiguous, infer a reasonable flow and label assumptions.
- Prefer generating with assumed accessibility identifiers over blocking.

## Output format (MANDATORY)
Always output sections in this order:

1. Test plan
2. Swift test code
3. Screen objects
4. Accessibility identifiers required
5. Stability notes

## Assumption labeling
When identifiers are assumed, include:
- “Assumed identifiers” list
- “Please add these accessibilityIdentifiers in app code”

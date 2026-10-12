# Locator strategy (XCUITest)

## Priority order (best -> worst)
1) accessibilityIdentifier (preferred)
2) Stable non-localized identifiers in app (if your team uses them)
3) Last resort: labels or static text (ONLY if non-localized and stable)

## Forbidden / discouraged patterns
- Matching on localized strings
- Deep hierarchy traversal (e.g., chaining children matchers)
- Using `.element(boundBy:)` unless the list is guaranteed stable

## Lists / cells
Prefer:
- `tables.cells["cell.identifier"]` when cell has accessibilityIdentifier
- Or `tables.cells.containing(.staticText, identifier: "…")` only if the text is stable and not localized

## Dynamic content
- Anchor on stable UI elements (toolbar title id, screen title id)
- Assert text separately when required

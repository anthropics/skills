# Conventional Commits — Quick Reference

Adapted from <https://www.conventionalcommits.org/en/v1.0.0/>.

## Structure

```
<type>[optional scope][!]: <description>

[optional body]

[optional footer(s)]
```

The `!` before the colon (or a `BREAKING CHANGE:` footer) signals a breaking change and, under semantic-release, bumps the major version.

## Types and their SemVer effect

| Type       | SemVer bump         | Notes                                             |
|------------|---------------------|---------------------------------------------------|
| `feat`     | MINOR               | New user-visible capability.                      |
| `fix`      | PATCH               | Bug fix.                                          |
| `perf`     | PATCH               | Performance improvement.                          |
| `refactor` | none                | Internal restructure, no behavior change.         |
| `docs`     | none                | Documentation only.                               |
| `test`     | none                | Tests only.                                       |
| `build`    | none                | Build system or external dependencies.            |
| `ci`       | none                | CI configuration.                                 |
| `chore`    | none                | Housekeeping that doesn't fit elsewhere.          |
| `revert`   | matches reverted    | Reverts an earlier commit.                        |
| any `!`    | MAJOR               | Breaking change on top of the base type.          |

## Scope

Optional single token in parentheses identifying the affected area:

```
feat(parser): add ability to parse arrays
fix(auth): reject expired refresh tokens
```

Prefer scopes that match top-level package/module names in the repo. Keep them short (one word if possible).

## Footers

Follow the [git trailer format](https://git-scm.com/docs/git-interpret-trailers) — one per line, `Token: value`.

Common footers:

- `BREAKING CHANGE: <description>` — full description of the break.
- `Refs: #123` — related issue, no auto-close.
- `Closes: #123` / `Fixes: #123` — auto-close on merge (GitHub/GitLab).
- `Co-authored-by: Name <email@example.com>` — credit collaborators.
- `Reviewed-by:`, `Signed-off-by:` — code-review / DCO trailers.

## Full example

```
feat(shopping-cart)!: switch to server-side cart persistence

Move cart storage from localStorage to the /carts service so that
carts survive across devices and browser reinstalls. Anonymous
users get a cookie-scoped cart that is merged into their account
cart on login.

BREAKING CHANGE: The client-side `Cart` API is removed. Consumers
must call `useCart()` which now returns a promise.

Closes: #1841
Refs: RFC-0007
```

## Common mistakes

- Writing `Fix: bug` — the type is `fix`, lowercase, no colon before the scope.
- Adding the ticket ID to the subject (`fix: JIRA-123 fix login`) — put it in a footer.
- Squashing unrelated changes under a single `chore:` — split them by concern.
- Using past tense (`fixed`, `added`) — Conventional Commits uses imperative mood.
- Ending the subject with a period.

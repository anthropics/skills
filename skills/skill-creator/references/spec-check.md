# Spec-drift check — verify against the live Agent Skills documentation

This reference describes when, why, and how to verify that a skill being authored complies with the **current** Agent Skills documentation at <https://agentskills.io/>.

The Agent Skills documentation evolves across nine canonical pages (specification, best practices, optimizing descriptions, using scripts, evaluating skills, quickstart, home, client implementation, llms.txt index). Fields get added, character limits change, deprecations happen, design guidance gets refined.

The constraints encoded in `SKILL.md` and the supporting references were correct at the time of writing — this check catches drift between then and now.

**Scoped fetches, not full traversal.** Don't fetch all nine pages on every check. Use the topic→URL routing table in `references/spec-source-map.md` to identify the single page that covers your specific concern, then fetch only that page. The map handles the routing so you don't have to memorize which page covers what.

---

## When to run this check

Run on these triggers, not on every skill-creator invocation:

| Trigger | Why |
|---|---|
| **Before final packaging** | Last-mile guarantee that the skill being shipped is valid against today's spec. One fetch per skill creation. |
| **On unexpected install / validation failure** | If `package_skill.py`, `quick_validate.py`, or the installer rejects with an error this guide doesn't predict, the spec may have changed. Fetch and look. |
| **On explicit user request** | "Is my skill still spec-compliant?" or "Has the spec changed since I last looked?" → run this check. |
| **Once per session, then cache** | If you've already fetched the spec in this conversation, reuse the cached content. The spec doesn't change inside a 30-minute session. |

## When NOT to run this check

- **On every invocation of the skill.** Network latency on every "help me make a skill" interaction is bad UX and provides no value when the local guide is current.
- **Before drafting the SKILL.md.** Start with the local guide — it's right 99% of the time. Verify before packaging, not before writing.
- **In offline environments.** The check is best-effort. If the fetch fails, log a warning and proceed with the local guide unchanged. Never block packaging on inability to reach the spec.

---

## The procedure

### 1. Identify exactly what you need to verify

Name the specific concern. Examples:

- "Did the `description` 1024-char limit change?"
- "Are there any new frontmatter fields this skill doesn't know about?"
- "Did the inline-script-vs-bundled-script guidance change?"
- "Has the recommended SKILL.md token budget shifted?"
- "Have new `--help` / structured-output rules been added for agentic scripts?"

The narrower the concern, the smaller the fetch.

### 2. Look up the right URL in `references/spec-source-map.md`

That map routes topics → URLs. Match your concern to a forward-map row and read the URL listed. **Fetch ONLY that URL.** Don't fetch all the docs pages; don't even fetch `/specification` if your concern is about scripts (that lives on `/using-scripts`).

If your concern doesn't match any row, start with `/specification`, then fall back to `/skill-creation/best-practices`. As a last resort, fetch the `https://agentskills.io/llms.txt` index to find the right page.

### 3. Fetch the page (once per session, then cache)

```
WebFetch: <URL from the source map>
```

Or via `curl` / `wget` in environments without WebFetch. Cache the response in memory (or `/tmp/agentskills-cache/<page-name>.html`) for the session. Don't refetch the same URL within one conversation. A different concern that maps to a different URL → fetch that new URL; same concern revisited → use the cached version.

### 4. Compare against the constraints in this guide

For frontmatter concerns, the fields and constraints this guide currently encodes:

| Field | Current encoding in this guide |
|---|---|
| `name` | 1–64 chars, lowercase ASCII + hyphens, no leading/trailing hyphens, no consecutive hyphens, must match parent directory name |
| `description` | 1–1024 chars, required, non-empty |
| `license` | Optional, no length limit |
| `compatibility` | Optional, 1–500 chars |
| `metadata` | Optional, arbitrary key-value mapping |
| `allowed-tools` | Optional, experimental, space-separated tool list |

For each field, ask:

- Did the character limit change?
- Did the allowed-character set change?
- Are there new required fields?
- Are existing fields now deprecated?
- Are there new optional fields worth surfacing?

Also check the **progressive disclosure** guidance — the recommended SKILL.md token budget (currently <5000 tokens) and file-reference depth (one level).

For non-frontmatter concerns (script bundling, trigger optimization, eval design), the constraints aren't encoded as a table — they're embedded as prose in the relevant references. Compare the fetched page section by section against the corresponding reference file in this skill:

| Concern | Fetched from | Compare against |
|---|---|---|
| Script bundling rules | `/skill-creation/using-scripts` | the script-bundling guidance in `SKILL.md` and `references/description-optimization.md` |
| Trigger optimization | `/skill-creation/optimizing-descriptions` | `references/description-optimization.md` |
| Eval methodology | `/skill-creation/evaluating-skills` | `references/running-evals.md` |
| Best practices | `/skill-creation/best-practices` | the writing-style and progressive-disclosure sections of `SKILL.md` |

### 3. Surface deltas to the user

If anything changed, tell the user plainly:

> The Agent Skills spec changed since this guide was written. Found:
> - `description` field max length increased from 1024 → 2048 characters.
> - New optional field `tags` (max 10 strings) for marketplace organization.
> Recommend updating the local SKILL.md guidance to
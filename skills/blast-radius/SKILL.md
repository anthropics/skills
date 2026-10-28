---
name: blast-radius
description: Before any bulk or destructive operation on real data — archiving users, revoking access, deleting rows, sending a batch of emails — measure what it would actually touch and prove the query means what you think it means. Use when a request implies writing to many rows at once, or when a filter is about to decide something about real people.
license: Apache-2.0
---

# Blast radius

A query is a claim about rows. A bulk operation is a claim about the world. They come
apart more often than they look like they will, and the gap is where the damage happens.

## The six ways a signal lies

Learn these as names. Most bad bulk writes are one of them, and naming the failure is
usually enough to stop it.

| # | Name | The shape | Real cost |
|---|---|---|---|
| 1 | **Absence ≠ departure** | "Not in the system" merges *never arrived* with *left* | Archiving on "no account on the chat platform" caught the **research director**. Of 505 members, exactly **one** had ever left; 80 had never joined. |
| 2 | **Ghost activity** | Rows a cron created look like rows a human caused | **3,037 of 3,392** weekly reports were auto-generated drafts. Counting them made 411 idle people look active. |
| 3 | **The field changed meaning** | A column was write-once, or unpopulated, until some commit | Timestamps before the fix answer a different question than timestamps after it. Find the commit before trusting the range. |
| 4 | **Status lags the artifact** | A row says `pending` while the thing already happened | Someone sat at `shortlisted` while holding a live offer. Re-sending would have rotated their token and **killed the accept link already in their inbox**. |
| 5 | **Clustered timestamps** | Everything is "stale" at suspiciously similar ages | A tight age band is one bulk edit, not independent decay. `updatedAt` records the last touch, not the last event. |
| 6 | **Loose matching invents members** | Surname, prefix or fuzzy matching pulls in strangers | "Hossain" matched one person to another and credited them with two papers they did not write. Match on identity, never a fragment. |

Write down the sentence your filter implies, then try to falsify it with the table above.
If the sentence survives, continue. If it does not, the query was fine and the plan was wrong.

## Classify every row before touching any

**Never act on a count.** Resolve each row to something you can name, then sort it:

- **act** — you can say who it is and why it qualifies
- **exclude** — it qualifies, but something outranks the rule: work in flight, a paid
  contract, ownership of something live, a role the rule never meant to reach
- **unknown** — you cannot resolve it. **Unknown is never act.**

Ninety-eight permission grants once looked stale. Classified: **74** matched no user at
all (service accounts, unlinked staff, people long gone), **6** were senior staff holding
deliberate oversight, **18** were genuinely stale. "Revoke the 98" would have cut off the
bot and the team leads.

Then read the **act** bucket back. If it contains the most senior person in the
organisation, a service account, or anything mid-flight, the rule is wrong — not them.
Narrow the rule rather than hand-listing exceptions, so it stays true next time.

## Ask what each row takes with it

A row is not only itself. Before removing a person, account or record, check what points
at it: work in progress, things it owns, things owed to it, anything that breaks when it
disappears. Exclusions found this way are the output, not friction.

Eight of twenty-three accounts archived on a "never logged in" rule turned out to be
published authors with live submissions — including one paper awaiting revisions and one
already accepted.

## Make the write refuse to be wrong

Put the guard in the script, not in how careful you feel at the time:

- **Dry run prints every affected row**; applying is a separate flag.
- **Refuse the ambiguous** — error on a row you cannot classify rather than skipping it.
- **Refuse the already-done** — check for the artifact, not the status field.
- **Write the record after the side effect.** A failed send must not leave a row marked sent.
- **Fail closed on environment.** If a link would point at localhost, refuse the batch.

## Verify the outcome, not the call

A function returning success means accepted, not done. Re-read the state and check the
number you expected actually moved. Then report what changed, what you skipped, and why —
**the skips are the useful half.**

## When the honest answer is "not safely"

Sometimes the data cannot support the decision. Say so, say what evidence would support
it, and stop. A bulk write on an unverified signal is worse than none, because afterwards
it looks authoritative.

## Installing the guard as a hook (optional)

`scripts/blast-radius.sh` is a `PreToolUse` hook that runs the checklist above against the
command itself. It exists because of the trigger problem: a skill about not trusting a
query only helps if it loads, and the agent that would blindly run the query is the one
that will not think to load it.

Hooks are wired through settings, not by living in this folder, so nothing happens until
you add it to `~/.claude/settings.json` (or a project `.claude/settings.json`):

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "~/.claude/skills/blast-radius/scripts/blast-radius.sh"
          }
        ]
      }
    ]
  }
}
```

An unfiltered write (`deleteMany({})`, `DELETE FROM users;`) returns
`permissionDecision: "ask"`. A filtered bulk write returns the checklist as
`additionalContext`. Read-only commands, and anything already flagged `--dry-run`, stay
silent — a dry run is the behaviour this skill exists to encourage.

It fails open: no `jq`, unrecognised input, or any error exits `0` silently. A safety hook
that breaks someone's workflow gets deleted, and then it protects nobody.

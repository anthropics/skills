# Resistance patterns

Use this file as a menu, not a checklist. Most challenges need zero or one pattern.

The selection rule is:

> Choose the largest reduction in cheap pattern matching for the smallest increase in human effort.

## Pattern break

Use when names, messages, or layout practically announce a textbook exploit.

**Good:** a generic `receipt` identifier instead of a parameter literally named `admin_id`.

**Bad:** renaming every variable to random strings.

**Typical human cost:** zero or one extra inspection step.

## Runtime discovery

Move one small solve-relevant fact into normal runtime behavior.

**Good:** an activity endpoint reveals a valid object reference that a vulnerable receipt endpoint fails to authorize.

**Good:** an object ID is generated at startup but is visible through ordinary application behavior.

**Bad:** generating a secret value that the player has no normal way to discover.

Randomization is useful only when it removes a static shortcut, not when it adds luck.

**Typical human cost:** one extra request or observation.

## Context split

Place two simple clues in different but nearby application surfaces so the player has to connect them.

**Good:** an order ID appears in recent activity and is accepted by an insecure receipt endpoint.

**Bad:** requiring clues from unrelated protocols, files, and services for an otherwise easy challenge.

**Typical human cost:** one or two extra observations.

## State dependency

Let a small amount of ordinary state affect the solve.

**Good:** a session-created resource must exist before an authorization bug can be exercised.

**Bad:** a five-step state machine that turns an easy challenge into an exploitation chain.

**Typical human cost:** one normal setup action.

## Semantic decoy

Add a plausible attack surface that can be disproved quickly.

**Good:** a download endpoint looks traversal-prone but rejects traversal cleanly; one test is enough to move on.

**Bad:** multiple rabbit holes, fake flags, destructive traps, rate-limit punishment, or misleading evidence that costs substantial time.

Use at most one semantic decoy.

**Typical human cost:** one failed hypothesis.

## Do not stack by default

If one pattern already removes the identified shortcut, stop. A second pattern needs a clear reason and must still pass the Human Cost Gate.

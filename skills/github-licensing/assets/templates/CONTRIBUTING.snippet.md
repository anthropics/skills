<!-- Drop this section into your CONTRIBUTING.md. Pick the DCO or CLA block. -->

## Contributor sign-off

### Option A — Developer Certificate of Origin (DCO) — lightweight

We use the [Developer Certificate of Origin](DCO.txt) (DCO). Every commit must be
signed off, certifying you have the right to submit it under this project's
license. Add the sign-off with `-s`:

```bash
git commit -s -m "Your message"
# adds: Signed-off-by: Your Name <you@example.com>
```

Forgot to sign off?

```bash
git commit --amend -s --no-edit          # last commit
git rebase --signoff HEAD~<N>            # last N commits
```

A DCO check on each PR blocks merge until all commits are signed off.

> Use the DCO when you do **not** need to relicense/dual-license. It certifies
> the contribution is properly licensed under the *current* license — it does
> **not** grant us rights to relicense.

### Option B — Contributor License Agreement (CLA) — required for dual-licensing

Because this project is offered under both an open-source and a commercial
license, contributors must sign our CLA (a one-time agreement granting
[Holder] a broad license to your contributions) before we can merge. Our bot
([CLA Assistant](https://cla-assistant.io/)) will comment on your first PR with a
link to sign. This is what lets us keep offering the commercial edition.

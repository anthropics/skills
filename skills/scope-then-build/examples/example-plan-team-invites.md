# Example plan: team invites

A worked example of the `scope-then-build` output for a typical product feature ask.

**User asked:** "Can you add team invites to the dashboard?"

---

## 1. What we're actually building

Email-based invite flow for an Account owner to invite teammates, with role-on-invite (Admin / Member), accepted via a one-time link that lands them in the same Account on signup.

## 2. Files we'll touch

- `prisma/schema.prisma` — add `Invite` model (id, email, role, account_id, expires_at, accepted_at)
- `src/lib/invites.ts` (new) — create / accept / expire helpers
- `src/api/invites/route.ts` (new) — `POST /api/invites` (create), `GET /api/invites/[token]` (accept)
- `src/components/InviteTeammateForm.tsx` (new) — form UI
- `src/email/templates/invite.tsx` (new) — invite email body
- `tests/lib/invites.test.ts` (new)

## 3. The order of work

1. **Step 1** — Schema + migration for `Invite` model. No code paths use it yet. This lands cleanly with no behavioral changes.
2. **Step 2** — Lib helpers + tests. Pure functions, no HTTP. Includes `createInvite`, `acceptInvite`, `expireInvite`.
3. **Step 3** — POST `/api/invites` endpoint + email send via the existing mail client. Unit + integration test.
4. **Step 4** — Accept endpoint + signup flow integration (gate the redirect on accept). E2E test.
5. **Step 5** — Form UI + the page that lists pending invites for an Account.

## 4. What we're explicitly NOT doing

- Not adding SCIM / SSO provisioning (separate effort, blocked on enterprise plan).
- Not implementing invite revoke (v1 escape hatch is delete from DB; explicit revoke is a follow-up).
- Not enforcing invite-count limits per plan (left for billing PR).
- Not migrating existing teammates added by other means (manual cleanup).

## 5. First thing to build

Step 1: the `Invite` model + migration. Lands cleanly with no behavioral changes, unblocks every other step.

Ready to proceed with step (5) or want to adjust scope?

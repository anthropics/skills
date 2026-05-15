# Store Rejection Recipes

When user pastes a rejection email, parse the Guideline number / category and apply the recipe below. Always verify the fix via API after applying, before telling user to resubmit.

## Apple App Store

### Guideline 2.1 — China book/magazine license

> *"app includes or accesses book or magazine content and is intended for distribution on the App Store in China mainland. However, you have not provided a permit demonstrating authorization to distribute an app with this content."*

**Root cause**: China mainland requires an Internet Publishing License (网络出版服务许可证) for book/magazine apps. Acquiring one takes months.

**Fix** (UI-only, the API for `appAvailabilities` v2 is undocumented and brittle):
1. App Store Connect → app → **Pricing and Availability**
2. Click **Edit Countries or Regions**
3. Uncheck **China mainland**
4. Save
5. Resubmit

Don't waste time on the API — we attempted 5 payload shapes against `v2/appAvailabilities` POST during a real fix and got 409s every time.

---

### Guideline 2.3.8 — Inaccurate Metadata (kids implication)

> *"the app subtitle to be displayed on the App Store includes the term kids, which implies that this app is made specifically for children. However, this app was not submitted as a Kids category app."*

**Root cause**: Subtitle/keywords claim the app is *exclusively* for children, but the app isn't in the Kids Category (which has strict requirements: no third-party analytics, parental gate on purchases, no behavioral ads, etc.).

**Fix**:
1. Scrub `kids` and `children` from:
   - `ios/fastlane/metadata/<locale>/subtitle.txt` (the highest-priority one — this is what got flagged)
   - `ios/fastlane/metadata/<locale>/keywords.txt`
   - `ios/fastlane/metadata/<locale>/promotional_text.txt`
   - First sentence of `description.txt` (the strongest signal)
2. **Keep allowed**: age-range mentions in description body (`ages 10+`, `Perfect for families`), the SAFE/AGE-APPROPRIATE section. Apple's rule is "implies exclusively-for-children", not "mentions children at all".
3. Push: `bun run ios:metadata` (or `cd ios && fastlane metadata` with UTF-8 locale)
4. Verify via API: check `subtitle` on `appInfoLocalizations` (NOT `appStoreVersionLocalizations` — subtitle moved)
5. Reply to reviewer in App Store Connect noting the change
6. Resubmit

**Example rewrites** (from a real production fix):
- Subtitle: `AI storybooks for kids` → `Write & illustrate with AI`
- Keywords: drop `kids,children`; add `imagination,books`
- Promo: `with your kids tonight` → `with your family tonight`

---

### Guideline 2.3.10 — Inaccurate Metadata (screenshots/copy don't match app)

> *"app's screenshots/description reference functionality not present in the app"*

**Fix**:
1. Open each screenshot and compare to live app
2. Re-read description.txt vs actual feature list
3. Remove any "coming soon" / aspirational language
4. Update screenshots with `bun run ios:screenshots`

---

### Guideline 4.0 — Sign-in failed

> *"We could not sign in to your app with the demo credentials you provided"*

**Fix**:
1. Re-run reviewer-user script: `bun scripts/create-app-review-user.ts` (rotates password idempotently)
2. Verify creds work — try signing in manually in your local app
3. Update `ios/.env.review` with new password
4. Push: `bun run ios:metadata` (Fastfile picks up new env vars and patches App Review Information)
5. Reply to reviewer
6. Resubmit

**Common gotcha**: account exists but email not confirmed. Check Supabase `auth.users` — `email_confirmed_at` must be non-null. The bootstrap script always sets `email_confirm: true`.

---

### Guideline 4.3 — Spam / duplicate

Usually means you've shipped similar AI-generated apps before. No automated fix — reply explaining differentiation.

---

### Guideline 5.1.1 — Privacy

> *"app collects user data but App Privacy says it doesn't"* or vice versa

**Fix**: Open App Store Connect → app → **App Privacy** → edit data types. Match what the app actually collects. Common omissions: email, IP address (for analytics), user content (stories users create).

---

### Common Apple gotchas (not full rejections, but precheck warnings)

| Symptom | Cause | Fix |
|---|---|---|
| `Incorrect, or missing copyright date` | Missing `metadata/copyright.txt` | Create with `2026 <CompanyName>` (top-level, not per-locale) |
| `Phone number must be in valid format` | Reviewer phone missing country code | `+91XXXXXXXXXX` format, no spaces |
| `invalid byte sequence in US-ASCII` | Ruby locale not UTF-8 | Set `LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8` in npm script |
| `Couldn't find API key JSON file at path '../app-store-connect-key.json'` | Fastfile uses relative path | Use `File.expand_path("../app-store-connect-key.json", __dir__)` |
| iPad screenshots uploaded but don't show in "iPad 13" Display" tab | Wrong display-type slot | Rename to `iPad Pro (12.9-inch) (3rd generation)-N.png` |

## Google Play Store

### Data Safety mismatch

> *"Your declarations in the Data safety form do not match how your app collects, shares, and handles user data"*

**Fix**: Open Play Console → app → **App content** → **Data safety**. Make declarations match real behavior:
- If app uses any analytics SDK (Firebase, Mixpanel, Meta Pixel) → declare `Device or other IDs` collected + shared
- If app uses Supabase Auth → declare `Email address` collected (not shared if RLS-protected)
- If users create stories → declare `Photos and videos` (if illustrations) + `Personal info` (story text) collected, NOT shared
- For payments → declare `Financial info` (purchase history) collected, shared with Google Play Billing

---

### Account deletion URL missing

> *"You must provide a way for users to request account deletion"*

**Required since 2024**. Two-step fix:
1. **Build a public `/delete-account` page** at your marketing domain with:
   - Instructions to delete (in-app button OR mailto link)
   - What data gets deleted
   - What data is retained (legal requirements only) and for how long
   - Refer to the app/developer name (Google requires this verbatim)
2. **Add URL** in Play Console → **App content** → **Data safety** → Account deletion section

Page template:
```jsx
<DeleteAccount>
  <h1>Delete your <AppName> account</h1>
  <h2>How to request deletion</h2>
  <ol>
    <li>From inside the app — Profile → Danger zone → Delete account</li>
    <li>By email — privacy@<domain> with subject "delete"</li>
  </ol>
  <h2>What gets deleted</h2>
  <ul>(account record, content, transactions, sessions...)</ul>
  <h2>What we keep</h2>
  <ul>(payment records 7yr for tax; T&S records 2yr; backups 35-day rolling)</ul>
</DeleteAccount>
```

---

### Target audience violation

> *"Your app is targeting children but is not enrolled in Designed for Families"*

**Fix**: Play Console → **App content** → **Target audience and content**. Either:
- Set min age to 13+ if you don't really target children, OR
- Opt into **Designed for Families** program (has stricter ad/SDK requirements)

---

### App access — reviewer can't sign in

> *"We were unable to access all parts of your app"*

**Fix**: Play Console → **App content** → **App access** → **Add new instructions**:
- Username: `appstore-reviewer@<your-domain>` (or whatever reviewer email)
- Password: from `ios/.env.review`
- Other instructions: paste reviewer-notes content (testing steps)

This form has **no API**. Use `bun run reviewer:print` to get the exact strings to paste.

---

### Closed testing requirement

> *"Your app must be tested by at least 12 testers in closed testing for 14 continuous days"*

**Personal developer accounts only**. Fix:
1. Recruit 12 real testers (must accept invitation, install app, keep installed)
2. Roll release to closed testing track instead of internal
3. Wait 14 days minimum
4. Then promote to production

Not bypassable. Business accounts skip this. If user is on personal account and time-sensitive, recommend they upgrade to business account (~$25 one-time).

## Verification commands after any fix

Always run before telling user to resubmit:

```bash
# iOS: confirm metadata is live as expected
bun scripts/check-ios-state.ts

# Android: confirm listing publishing succeeded
cd android && ./gradlew publishListing --info 2>&1 | grep -E 'UP-TO-DATE|SUCCESS|FAIL'
```

If verification fails, do not tell user to resubmit. Re-investigate first.

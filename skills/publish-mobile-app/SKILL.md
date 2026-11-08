---
name: publish-mobile-app
description: Automate iOS App Store + Google Play Store publishing for Capacitor, Expo, or Flutter apps — listing copy, screenshots, IPA/AAB upload, reviewer credentials, and fixing common rejection emails (Guideline 2.3.8 metadata, 2.1 China license, 4.0 sign-in, etc). Use when user mentions `/publish-mobile-app`, Play Store, App Store Connect, fastlane, gradle-play-publisher, TestFlight, or pastes an Apple/Google store rejection email.
---

# Publish Mobile App

Automates the boring parts of shipping a mobile app to both stores. Forged from real production ship cycles: one-command listing sync, signed IPA upload to TestFlight, reviewer-user provisioning, and recipes for the most common rejection emails.

## Sub-commands

When invoked via `/publish-mobile-app`, route based on the user's argument:

| Argument | What it does |
|---|---|
| `setup` | One-time wiring: fastlane + gradle-play-publisher + reviewer user + key bootstrap |
| `push` | Upload current listing + screenshots to both stores (or one, ask user) |
| `ipa` | Build signed iOS IPA and push to TestFlight |
| `aab` | Build signed Android AAB and push to Play internal track |
| `release` | Full bump + build + upload + listing push for both stores |
| `fix-rejection` | User pastes rejection email; map issue → fix → apply |
| `status` | Read live state from both stores via API; report what's present and what's missing |
| `checklist` | Generate/refresh `RELEASE_CHECKLIST.md` at repo root |

If no argument given, ask the user which sub-command they want, defaulting to `status` to orient first.

## Framework detection

Detect which mobile framework the project uses before doing anything else:

```bash
test -f capacitor.config.ts -o -f capacitor.config.json && echo capacitor
test -f app.json && grep -q '"expo"' app.json 2>/dev/null && echo expo
test -f pubspec.yaml && echo flutter
```

Behaviors differ per stack — see [REFERENCE.md](REFERENCE.md#framework-differences).

## Setup checklist

When user runs `setup`, work through this checklist in order. Mark each with TodoWrite and tick off as you go.

1. **Detect framework** (capacitor / expo / flutter) and confirm with user
2. **Verify prerequisites**: `fastlane --version`, gradle (Android), Xcode (iOS), `bun` or `node`
3. **iOS — App Store Connect API key**
   - User generates `.p8` key in App Store Connect → Users and Access → Integrations → App Store Connect API
   - Run [scripts/bootstrap-app-store-key.ts](scripts/bootstrap-app-store-key.ts) with `ASC_KEY_ID`, `ASC_ISSUER_ID`, `ASC_KEY_PATH` to assemble `ios/app-store-connect-key.json`
   - Move `.p8` from `~/Downloads/` to `~/.appstoreconnect/private_keys/` (standard location)
4. **iOS — fastlane scaffolding**
   - Create `ios/fastlane/Appfile` with `app_identifier`, `team_id`
   - Create `ios/fastlane/Fastfile` with lanes: `metadata`, `screenshots`, `beta` (build+TestFlight upload). Template: [REFERENCE.md#fastfile-template](REFERENCE.md#fastfile-template)
   - **Critical**: `API_KEY_PATH = File.expand_path("../app-store-connect-key.json", __dir__)` so it works from any CWD
   - **Critical**: every npm script invoking fastlane must set `LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8` or Ruby crashes on em-dashes/bullets in description.txt
5. **iOS — metadata + screenshots**
   - Create `ios/fastlane/metadata/en-US/` with `name.txt`, `subtitle.txt`, `description.txt`, `keywords.txt`, `promotional_text.txt`, `release_notes.txt`, `support_url.txt`, `privacy_url.txt`, `marketing_url.txt`
   - Create `ios/fastlane/metadata/copyright.txt` (non-localized, top-level)
   - Screenshots in `ios/fastlane/screenshots/en-US/` — naming conventions matter for iPad routing, see [REFERENCE.md#ipad-screenshot-filename-magic](REFERENCE.md#ipad-screenshot-filename-magic)
6. **Android — Play Console service account**
   - User creates service account in Google Play Console → Setup → API access
   - Save JSON to `android/play-config.json` (gitignored)
7. **Android — gradle-play-publisher**
   - Add plugin to `android/app/build.gradle`: see [REFERENCE.md#android-build-gradle](REFERENCE.md#android-build-gradle)
   - Initial `track` should be `internal`; `defaultToAppBundles.set(true)`; `releaseStatus.set(ReleaseStatus.DRAFT)` until first prod release
8. **Android — listings**
   - Listing files at `android/app/src/main/play/listings/<locale>/` — locale must match Play Console default (often `en-GB`, not `en-US`!)
   - Subfolders: `graphics/icon/icon.png` (512×512), `graphics/feature-graphic/feature-graphic.png` (1024×500), `graphics/phone-screenshots/`, `graphics/tablet-7-inch-screenshots/`, `graphics/tablet-10-inch-screenshots/`
   - `release-notes/<locale>/default.txt`
9. **Gitignore credentials**
   - `ios/app-store-connect-key.json`, `*.p8`, `android/play-config.json`, `ios/.env.review`, `ios/build/`, `ios/*.ipa`, `ios/fastlane/README.md`
10. **Reviewer user**
    - Run [scripts/create-app-review-user.ts](scripts/create-app-review-user.ts) — provisions reviewer auth user in Supabase if detected. Stores creds in `ios/.env.review`. Falls back to printing instructions if not Supabase.
11. **App Review Information**
    - Phone with country code is required (`+91XXXXXXXXXX` format, no spaces)
    - Wire env vars into Fastfile `app_review_information:` block

## Push workflow

When user runs `push`:

1. Validate metadata char limits — see [REFERENCE.md#character-limits](REFERENCE.md#character-limits)
2. Validate asset dimensions
3. Verify no `kids`/`children` in subtitle if not in Kids Category (Apple flags this — Guideline 2.3.8)
4. Push iOS: `cd ios && LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8 fastlane metadata`
5. Push Android: `cd android && ./gradlew publishListing`
6. **Verify outcome via API**, not just fastlane log — see [scripts/check-ios-state.ts](scripts/check-ios-state.ts). Fastlane sometimes routes uploads to wrong slot (the iPad-3rd-gen bug); only the API tells the truth.

## Rejection fix mapping

When user pastes a rejection email, parse the **Guideline number** and route to the appropriate recipe. Full recipes in [REJECTIONS.md](REJECTIONS.md).

| Apple Guideline | Common cause | Quick fix |
|---|---|---|
| 2.1 | China book/magazine license missing | Remove China mainland in App Store Connect → Pricing & Availability |
| 2.3.8 | Subtitle/keywords imply "for kids" without Kids Category | Scrub `kids`/`children` from subtitle + keywords + promo; keep age messaging in description (it's allowed) |
| 2.3.10 | Inaccurate marketing copy | Re-read description vs actual app behavior |
| 4.0 | Reviewer sign-in failed | Re-run reviewer-user script to rotate password; update App Review Information |
| 5.1.1 | Privacy / data collection | Check App Privacy questionnaire — must match what app actually collects |

| Google Play | Common cause | Quick fix |
|---|---|---|
| Data Safety mismatch | Declared data types don't match runtime | Update Data Safety form in Play Console |
| Account deletion URL missing | Required since Play Console 2024 | Add `/delete-account` page + URL in Data Safety form |
| Target audience violation | App targeting children without Designed for Families opt-in | Either change target age range or join Designed for Families |

## What's permanently manual

These have no public API and must be done in the store consoles:

- **Apple**: App Privacy questionnaire, Age Rating, App Review Information (programmable via fastlane `deliver`), Export Compliance (one-time `ITSAppUsesNonExemptEncryption` plist flag handles this for most apps)
- **Google**: Data Safety form, Content Rating, Target Audience, App Access (test-account credentials), Government/News/COVID declarations
- **Both**: Pricing & territories (Apple has an undocumented API; Google has none reliable)

See [MANUAL_FORMS.md](MANUAL_FORMS.md) for guided answers — what to pick for each question for a typical content-creation app.

## Reference files

- [REFERENCE.md](REFERENCE.md) — Framework-specific behaviors, fastlane templates, API gotchas, character limits, the iPad-3rd-gen filename magic
- [REJECTIONS.md](REJECTIONS.md) — Detailed recipes per rejection guideline with copy-paste code
- [MANUAL_FORMS.md](MANUAL_FORMS.md) — Walkthroughs for App Privacy, Age Rating, Data Safety questionnaires

## Scripts (deterministic, reusable)

- [scripts/bootstrap-app-store-key.ts](scripts/bootstrap-app-store-key.ts) — assemble ASC key JSON from `.p8` + IDs
- [scripts/create-app-review-user.ts](scripts/create-app-review-user.ts) — idempotently provision reviewer user (Supabase auto, others manual)
- [scripts/check-ios-state.ts](scripts/check-ios-state.ts) — query App Store Connect API to verify what's actually live (counter to fastlane's optimistic logs)
- [scripts/print-reviewer-creds.ts](scripts/print-reviewer-creds.ts) — print creds in copy-friendly format for Play Console (which has no API for App Access)
- [scripts/validate-metadata.ts](scripts/validate-metadata.ts) — check char limits + asset dimensions + ASCII-trap words before push

## Key principle

**Fastlane's "Successfully uploaded" log ≠ "appears correctly in App Store Connect UI"**. Always verify via the App Store Connect API after any push. The `check-ios-state.ts` script is the source of truth — fastlane sometimes routes 2048×2732 iPad screenshots to the wrong display-type slot.

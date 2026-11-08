# Manual Store Forms — Answer Guide

These store-side questionnaires have **no API**. Apple and Google require they be filled in the consoles. This file documents the right answers for a typical content-creation / AI app (classic shape: AI-generated user content, optional account, no in-app messaging, no ads, family-friendly).

When user is filling these forms, ask the routing question first:

> *"Is this a content-creation/AI app? Or a different category — game, social, finance, health?"*

The defaults below assume content-creation/AI. Adjust for other categories.

## Apple — Age Rating questionnaire

### Step 1: Features
| Question | Default | Why |
|---|---|---|
| Parental Controls | **No** | Unless you ship a dedicated parental-controls UI dashboard |
| Age Assurance | **No** | Unless you verify birthdate / ID |
| Unrestricted Web Access | **No** | If using Capacitor Browser or in-app browser to specific URLs only |
| User-Generated Content | **No** | If content is private by default & sharing is account-controlled. Apple defines this as "broad distribution" — public feeds count, private sharing doesn't |
| Messaging and Chat | **No** | No user-to-user messaging |
| Advertising | **No** | No paid promotion inside the app |

### Steps 2–5: Mature content categories
Default to **None** for all of these unless app actually contains:
- Cartoon/Fantasy Violence
- Realistic Violence
- Profanity / Crude Humor
- Sexual Content / Nudity
- Alcohol / Tobacco / Drug Use
- Mature/Suggestive Themes
- Horror/Fear Themes (consider **Infrequent/Mild** if AI could generate scary content — but content filtering makes **None** defensible)
- Medical / Treatment Info
- Gambling / Contests

### Step 6: Generative AI (Apple added this recently — be honest)
| Question | Answer |
|---|---|
| Does your app use generative AI? | **Yes** |
| Will generated content be sensitive/inappropriate for under-17? | **No** (if you have content filtering) |
| Do you have safeguards? | **Yes** — mention them in App Review notes too |

### Step 7: Result
Apple computes the rating. Typical landing: **4+** or **9+** for filtered AI content apps.

**Important nuance — Kids Category opt-in**:
Even if app targets 10+ in description, **do NOT opt into Kids Category** unless you accept these strict requirements:
- No third-party analytics linked to user identifiers (kills Firebase Analytics, Meta Pixel, etc.)
- No behavioral advertising
- No external links to other apps
- Parental gate before purchases
- Restricted data sharing

Standard 4+/9+ rating without the Kids Category badge is the right shape for most family-friendly apps.

## Apple — App Privacy questionnaire

For each data type, declare:
1. Is it **collected**? Yes/No
2. Is it **linked to user identity**?
3. Is it **used for tracking** across apps?
4. **Purpose**: App Functionality / Analytics / Product Personalization / Developer Communications

Typical answers for a content-creation/AI app:

| Data type | Collected? | Linked? | Tracking? | Purpose |
|---|---|---|---|---|
| Email address | Yes | Linked | No | App Functionality |
| Name | Yes (if you ask) | Linked | No | App Functionality |
| User Content (stories) | Yes | Linked | No | App Functionality |
| Photos / Videos | Only if user uploads | Linked | No | App Functionality |
| Audio Data (narration) | Yes (output) | Linked | No | App Functionality |
| Purchase History | Yes | Linked | No | App Functionality |
| Device ID | If using Firebase / analytics SDK | Not Linked | No | Analytics |
| Crash Data | Yes (Sentry/Crashlytics) | Not Linked | No | App Functionality |
| Performance Data | Yes | Not Linked | No | Analytics |
| Coarse Location | No | — | — | — |
| Precise Location | No | — | — | — |
| Contacts | No | — | — | — |
| Search History | No | — | — | — |

Mark "Used to Track You" = **No** for everything unless you genuinely share data with third parties for advertising.

## Google — Data Safety form

Mirrors App Privacy but with different terminology. Key differences:
- "Collected" + "Shared" are separate questions per data type
- "Processed ephemerally" option exists for things touched in-memory but not stored
- Required: **encryption in transit** declaration (always "Yes" for any HTTPS app)
- Required: **users can request deletion** declaration

Typical declarations for content-creation/AI:

**Personal info**:
- Name, Email: collected (encrypted in transit, optional, used for account management)
- NOT shared

**User-generated content**:
- Photos/Videos: collected if user uploads, encrypted in transit
- Audio: collected (narration), encrypted in transit
- Other (story text): collected, encrypted in transit
- NOT shared (RLS-protected in Supabase)

**App activity**:
- App interactions: collected for Analytics if using Firebase/Mixpanel
- In-app search history: collected only if there's an actual search feature

**Device or other IDs**:
- Collected for Analytics/Crash purposes if using Firebase, Sentry, Meta Pixel, etc.
- Shared with those third parties

**Financial info**:
- Purchase history: collected, NOT shared (Google Play Billing handles this separately)

## Google — Content Rating

Questionnaire is straightforward. Most "Does your app contain X?" questions get **No** for a content-creation/AI app.

Key calls:
- **Cartoon violence**: No (AI doesn't generate violent content by default)
- **Sexual content**: No
- **Profanity**: No (content filtering)
- **User-generated content**: **Yes** (this triggers a follow-up requiring you to have a content moderation policy — which you should already document in `/safety` page)
- **Social features**: No (if no in-app messaging)
- **Personal info shared with users**: No
- **Allows users to interact**: No (no chat)

Typical resulting rating: **PEGI 3 / Everyone**.

## Google — Target Audience and Content

This is **where you choose whether to opt into Designed for Families**.

Typical answers for a content-creation/AI app:
- Target age groups: **13+** (avoid the under-13 box unless app is designed exclusively for kids)
- Does the app appeal to children? **No** (if 13+) or **Yes, mixed audience** (if 13+ but also family-friendly)

If you check the under-13 box, you're auto-enrolled in **Designed for Families** with strict requirements (no behavioral ads, restricted SDKs, etc.).

## Google — App Access

Required when app has sign-in. Reviewer credentials go here:
- Instruction name: `App reviewer login` (or similar)
- Username: from `ios/.env.review`
- Password: from `ios/.env.review`
- Other instructions: paste reviewer notes verbatim

Run `bun scripts/print-reviewer-creds.ts` to get copy-paste strings.

## Apple App Review Information (programmable via fastlane)

Unlike the forms above, this **does have an API** — handled by the `metadata` lane:
- First name, Last name, Phone (with country code), Email
- Demo user / password
- Notes (testing instructions for reviewer)

Source: `ios/.env.review` env vars → Fastfile's `app_review_information:` block. See [SKILL.md](SKILL.md) setup step 11.

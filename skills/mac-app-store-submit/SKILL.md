---
name: mac-app-store-submit
description: "Guide for submitting Mac apps to the App Store via App Store Connect. Use when the user wants to publish a macOS app, submit to the Mac App Store, or fill out App Store Connect metadata. Triggers on: submit to app store, publish mac app, app store connect, mac app store submission."
allowed-tools: Bash, Read, Write, WebFetch, mcp__chrome-devtools__*
---

# Mac App Store Submission Guide

Step-by-step process for submitting a macOS app to the Mac App Store via App Store Connect.

## Automation Level

**~95% automatable** via Chrome DevTools MCP. The entire App Store Connect UI flow (metadata, screenshots, submission) can be handled automatically.

**Only manual step:** Certificate and provisioning profile setup in Xcode (one-time per app/team).

## Prerequisites

Before submitting, ensure you have:
- Apple Developer account ($99/year)
- **[MANUAL]** Distribution certificate created in Xcode (Signing & Capabilities → Team → Manage Certificates)
- **[MANUAL]** Provisioning profile for App Store distribution (auto-created by Xcode when you archive)
- Build archived and uploaded (can be automated - see Build Upload section)

## Required Metadata (Must Complete Before Submission)

### 1. App Privacy (`/distribution/privacy`)

**Two parts:**
1. **Privacy Policy URL** - Required. Can use GitHub README section (e.g., `https://github.com/user/repo#privacy`)
2. **Data Collection Questionnaire** - Click "Get Started", answer questions about data collection
   - For simple local-only apps: Select "No, we do not collect data from this app"
   - Click "Publish" after completing

### 2. Age Ratings (`/distribution/info` → scroll to Age Ratings)

Click "Set Up Age Ratings" and complete 7 steps:
- **Step 1: Features** - Parental Controls, Age Assurance, Web Access, User Content, Messaging, Advertising (select NO for simple apps)
- **Step 2: Mature Themes** - Profanity, Horror, Alcohol/Drugs (select NONE)
- **Step 3: Medical/Wellness** - Medical content, Health topics (select NONE/NO)
- **Step 4: Sexuality** - Suggestive themes, Nudity (select NONE)
- **Step 5: Violence** - Cartoon, Realistic, Graphic, Weapons (select NONE)
- **Step 6: Gambling** - Simulated gambling, Contests, Gambling, Loot boxes (select NONE/NO)
- **Step 7: Confirmation** - Review calculated rating (usually 4+ for utility apps)

### 3. Primary Category (`/distribution/info`)

Select from dropdown (common choices):
- **Productivity** - Document editors, task managers, utilities
- **Developer Tools** - IDEs, debugging tools
- **Utilities** - System tools, file managers
- **Graphics & Design** - Image editors, design tools

**Note:** The category dropdown may appear empty visually but have a value set. Use JavaScript if needed:
```javascript
document.querySelector('select[name*="primary"]').value = 'PRODUCTIVITY';
document.querySelector('select[name*="primary"]').dispatchEvent(new Event('change', { bubbles: true }));
```

### 4. Pricing (`/distribution/pricing`)

1. Click "Add Pricing"
2. Select Base Country (default: United States USD)
3. Choose Price tier ($0.00 for free apps)
4. Click Next → Next → Confirm

### 5. Content Rights (`/distribution/info`)

Click "Set Up Content Rights Information":
- **For original content apps:** Select "No, it does not contain, show, or access third-party content"
- **For apps with licensed content:** Select "Yes" and confirm you have rights

## Version Page Metadata (`/distribution/macos/version/inflight`)

### Required Fields:
- **Screenshot** - At least 1 screenshot (1280x800 or 1440x900 for Mac)
- **Promotional Text** - Short marketing text (optional but recommended)
- **Description** - Full app description
- **Keywords** - Comma-separated search terms
- **Support URL** - Link to support page or GitHub issues
- **Copyright** - Format: "2024 Your Name" or "2024 Company Name"

### Build Selection:
- Click "Add Build" or the build section
- Select your uploaded build from the list
- Click "Done"

## Submission Process

1. Complete all required sections above
2. Navigate to version page (`/distribution/macos/version/inflight`)
3. Click "Add for Review" button
4. If errors appear, click the links to fix missing items
5. Once ready, "Draft Submission" dialog appears
6. Click "Submit for Review"
7. Status changes to "Waiting for Review"

## Common Errors & Fixes

| Error | Solution |
|-------|----------|
| "Privacy Policy URL required" | Go to App Privacy, click Edit, add URL |
| "Age Rating frequency required" | Complete all 7 steps of Age Rating setup |
| "Primary category required" | Select category in App Information |
| "Price tier required" | Set up pricing (even for free apps) |
| "Content Rights required" | Click "Set Up Content Rights Information" |
| Phone number validation fails | Use format `+14155551234` (no hyphens) |

## App Store Connect URLs

Base URL: `https://appstoreconnect.apple.com/apps/{APP_ID}/distribution/`

| Section | Path |
|---------|------|
| Version Page | `macos/version/inflight` |
| App Information | `info` |
| App Privacy | `privacy` |
| Pricing | `pricing` |
| App Review | `reviewsubmissions` |

## Timeline

- **Review time:** Typically 24-48 hours
- **Email notification:** Sent when review complete
- **If rejected:** You'll receive specific feedback to address

## Build Upload (Automatable)

After archiving in Xcode, upload via command line:
```bash
xcrun altool --upload-app -f /path/to/App.pkg -t macos -u "apple-id@example.com" -p "@keychain:AC_PASSWORD"
```

Or use `xcrun notarytool` for newer workflows:
```bash
xcrun notarytool submit App.zip --apple-id "apple-id@example.com" --team-id TEAMID --password "@keychain:AC_PASSWORD" --wait
```

**Note:** Store App Store Connect password in keychain: `xcrun altool --store-password-in-keychain-item AC_PASSWORD -u "apple-id@example.com" -p "app-specific-password"`

## Chrome DevTools MCP Automation

The entire App Store Connect UI can be automated using Chrome DevTools MCP:

1. **Navigate directly** to sections using URL patterns (see App Store Connect URLs table)
2. **Click buttons** using `mcp__chrome-devtools__click` with element refs from snapshots
3. **Fill forms** using `mcp__chrome-devtools__fill` or `mcp__chrome-devtools__form_input`
4. **Upload screenshots** by clicking the upload area and using file input
5. **Handle stubborn dropdowns** with JavaScript execution (see Category dropdown workaround)

**Workflow:**
1. Take snapshot with `mcp__chrome-devtools__take_snapshot`
2. Find element refs for buttons/inputs
3. Click/fill as needed
4. Repeat until submission complete

## Tips

1. **Save frequently** - App Store Connect can lose unsaved changes
2. **Check for yellow warning banners** - They indicate missing required items
3. **Export Compliance** - Usually just needs one checkbox for standard encryption
4. **Test before submitting** - Use TestFlight to verify the build works
5. **Use direct URLs** - Navigate directly to sections rather than clicking through menus

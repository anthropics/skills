# Reference

## Framework differences

### Capacitor
- iOS project: `ios/App/App.xcodeproj`, scheme `App`
- Android project: `android/app/build.gradle`
- Web build pipeline: `vite build --mode production && cap sync <platform>` before any binary build
- npm scripts wrap fastlane: `bun run ios:metadata`, `bun run android:metadata`

### Expo
- iOS project: built via `eas build --platform ios` OR `npx expo prebuild --platform ios` to generate `ios/` then use fastlane
- Recommended path: use EAS Build + `eas submit` (Expo's own toolchain); fastlane works only after `expo prebuild`
- Submission metadata lives in `store.config.json` (Expo) or fastlane folders if prebuilt
- `app.json` → `expo.ios.bundleIdentifier` is the bundle ID

### Flutter
- iOS project: `ios/Runner.xcodeproj`, scheme `Runner`
- Android project: `android/app/build.gradle`
- Build pipeline: `flutter build ios --release --no-codesign` then `gym`/`fastlane` for signing
- Android: `flutter build appbundle` produces the AAB; can also use `gradle-play-publisher` from the `android/` dir
- Version source of truth: `pubspec.yaml` → `version: 1.0.0+1` (the `+1` is build number)

## Fastfile template

```ruby
# ios/fastlane/Fastfile
API_KEY_PATH = File.expand_path("../app-store-connect-key.json", __dir__)

default_platform(:ios)

platform :ios do
  before_all do
    ENV["FASTLANE_HIDE_CHANGELOG"] = "1"
  end

  desc "Upload metadata + screenshots only (no binary)."
  lane :metadata do
    review_info = {
      first_name: ENV["ASC_REVIEW_FIRST_NAME"],
      last_name: ENV["ASC_REVIEW_LAST_NAME"],
      phone_number: ENV["ASC_REVIEW_PHONE"],
      email_address: ENV["ASC_REVIEW_EMAIL"],
      demo_user: ENV["ASC_REVIEW_DEMO_USER"],
      demo_password: ENV["ASC_REVIEW_DEMO_PASSWORD"],
      notes: ENV["ASC_REVIEW_NOTES"],
    }.compact

    deliver(
      api_key_path: API_KEY_PATH,
      skip_binary_upload: true,
      skip_screenshots: false,
      skip_metadata: false,
      force: true,
      overwrite_screenshots: true,
      precheck_include_in_app_purchases: false,
      app_review_information: review_info,
    )
  end

  desc "Build signed IPA and push to TestFlight."
  lane :beta do
    api_key = app_store_connect_api_key(key_filepath: API_KEY_PATH, in_house: false)

    next_build = latest_testflight_build_number(
      api_key: api_key,
      app_identifier: ENV["BUNDLE_ID"] || "com.example.app",
      initial_build_number: 0,
    ) + 1
    increment_build_number(
      xcodeproj: "App/App.xcodeproj",  # or "Runner/Runner.xcodeproj" for Flutter
      build_number: next_build.to_s,
    )

    build_app(
      project: "App/App.xcodeproj",
      scheme: "App",
      configuration: "Release",
      export_method: "app-store",
      clean: true,
      output_directory: "build",
      output_name: "App.ipa",
      export_options: { signingStyle: "automatic", teamID: ENV["TEAM_ID"] },
    )

    upload_to_testflight(
      api_key: api_key,
      skip_waiting_for_build_processing: true,
      skip_submission: true,
    )
  end
end
```

## Android build.gradle

```gradle
// android/app/build.gradle
def playConfigFile = rootProject.file('play-config.json')
if (playConfigFile.exists()) {
    apply plugin: 'com.github.triplet.play'

    play {
        serviceAccountCredentials.set(playConfigFile)
        track.set("internal")
        defaultToAppBundles.set(true)
        // Switch to ReleaseStatus.COMPLETED after first prod release
        releaseStatus.set(com.github.triplet.gradle.androidpublisher.ReleaseStatus.DRAFT)
    }
}
```

Plugin in `android/build.gradle`:
```gradle
classpath 'com.github.triplet.gradle:play-publisher:3.12.1'
```

## Character limits

### App Store Connect (per locale)
| Field | Max |
|---|---|
| `name.txt` | 30 |
| `subtitle.txt` | 30 |
| `promotional_text.txt` | 170 |
| `keywords.txt` | 100 (comma-separated, no spaces) |
| `description.txt` | 4000 |
| `release_notes.txt` | 4000 |

### Play Console (per locale)
| Field | Max |
|---|---|
| `title.txt` | 30 |
| `short-description.txt` | 80 |
| `full-description.txt` | 4000 |

## Asset dimensions

### iOS screenshots
| Display type | Pixel size |
|---|---|
| iPhone 6.5" (`APP_IPHONE_65`) | 1242×2688 or 1284×2778 |
| iPhone 6.7" (`APP_IPHONE_67`) | 1290×2796 |
| iPad 12.9" Display (`APP_IPAD_PRO_3GEN_129`, the "iPad 13"" tab) | 2064×2752 or 2048×2732 |

### Android assets
| Asset | Pixel size |
|---|---|
| App icon | 512×512 |
| Feature graphic | 1024×500 (no transparency, no text near edges) |
| Phone screenshot | min 320, max 3840, aspect 16:9 or 9:16 ≤ 2:1 |

## iPad screenshot filename magic

**This bit us.** `2048×2732` is ambiguous in fastlane 2.226 — it maps to either:
- `APP_IPAD_PRO_129` (legacy iPad Pro 12.9", hidden in current ASC UI)
- `APP_IPAD_PRO_3GEN_129` (the "iPad 13" Display" tab users see)

Fastlane's heuristic: **filename must contain one of these substrings** to route to the 3rd-gen+ slot:

```
iPad Pro (12.9-inch) (3rd generation)
iPad Pro (12.9-inch) (4th generation)
iPad Pro (12.9-inch) (5th generation)
iPad Pro (12.9-inch) (6th generation)
IPAD_PRO_3GEN_129
ipadPro129
```

Recommended naming pattern:
```
ios/fastlane/screenshots/en-US/iPad Pro (12.9-inch) (3rd generation)-1.png
ios/fastlane/screenshots/en-US/iPad Pro (12.9-inch) (3rd generation)-2.png
...
```

Source: `/opt/homebrew/Cellar/fastlane/.../deliver/lib/deliver/app_screenshot.rb#resolve_ipadpro_conflict_if_needed`

## Locale gotcha (Play Console)

Google Play's default territory is often **en-GB**, not **en-US**. If you create listings under `en-US/` and they don't appear in Play Console, it's because the default locale doesn't match. Two options:
1. Move listing to `android/app/src/main/play/listings/en-GB/`
2. Add both `en-GB` and `en-US`

The `publishListing` task silently skips folders whose locale isn't enabled in Play Console.

## API gotchas

### Fastlane log lies sometimes
`Successfully uploaded all screenshots` does NOT mean they're visible in the correct slot. Always verify with the API after any upload:

```bash
bun scripts/check-ios-state.ts
```

The API returns the actual `screenshotDisplayType` each shot was filed under. The `count=N states=[COMPLETE×N]` output is the only source of truth.

### Ruby UTF-8 crash
Without `LANG=en_US.UTF-8 LC_ALL=en_US.UTF-8`, Ruby 3.x reads `description.txt` as US-ASCII and crashes on em-dashes `—`, bullets `•`, smart quotes. Symptom: `invalid byte sequence in US-ASCII (Encoding::CompatibilityError)`. Always set the locale in every fastlane-invoking script.

### Phone format
App Store Connect rejects phone numbers without `+<country code>`. Always store as `+919994619490` (no spaces, no dashes).

### Copyright placement
The `copyright` field is **non-localized** (top-level) — file goes at `ios/fastlane/metadata/copyright.txt`, NOT `ios/fastlane/metadata/en-US/copyright.txt`. Forgetting this triggers a precheck warning.

### Territory removal via API
`v2/appAvailabilities` POST endpoint exists but the payload shape is **undocumented** and brittle. After 5 attempts during a real production fix, we used the UI instead. Don't waste time on this — instruct user to toggle in App Store Connect → Pricing & Availability.

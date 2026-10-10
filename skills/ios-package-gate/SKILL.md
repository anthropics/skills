---
name: ios-package-gate
description: Inspect a signed iOS .ipa or .app before you ship it — the artifact itself, not the build log. Use when about to upload to App Store Connect or TestFlight, when `xcodebuild archive` printed ARCHIVE SUCCEEDED but you have not proven the bundle is signed, when a delivery report needs package evidence, or when debugging "Apple rejected my binary" / "this build will not install". Checks signature authority, get-task-allow, beta-reports-active, embedded profile, architecture, version fields, privacy manifest, icon, declared-vs-actual permissions, and whether the export-compliance flag agrees with the source.
---

# iOS Package Gate

## Why this exists

`** ARCHIVE SUCCEEDED **` does not prove your app is signed.

Measured: a build printed `** ARCHIVE SUCCEEDED **` and the resulting bundle was
`code object is not signed at all`. Any pipeline that trusts build output will happily try
to upload that. So this gate ignores the log and opens the package.

## When to use it

- Immediately before uploading an `.ipa` anywhere.
- When writing package evidence into a delivery/handoff record.
- When an upload or install failed and you need to know whether the artifact is the problem.

## When NOT to use it

- To review source code — this reads the built artifact only.
- On simulator builds — those are unsigned by design and the gate will correctly go red.
- To decide whether you are ready for App Review — this checks the binary, not store
  metadata, age rating or the privacy questionnaire.

## Usage

```bash
scripts/package-gate.sh <path.ipa|path.app> [options]
  --expect-bundle <id>        bundle identifier must match
  --expect-name <name>        CFBundleDisplayName must match
  --expect-version <x.y.z>    CFBundleShortVersionString must match
  --permissions <NS...,NS...> DECLARED permission keys; an undeclared one is red
  --test-vectors <glob>       files matching this must NOT be in the bundle
```

Exit code carries the verdict: `0` all gates pass, `1` at least one failed. Use it in CI.
Nothing is project-specific; there are no constants baked in.

## What it measures

| # | Gate | Why it matters |
|---|---|---|
| 1 | signature present | catches `code object is not signed at all` |
| 2 | distribution signature | a bundle signed `Apple Development` cannot be uploaded |
| 3 | signature integrity | `codesign --verify --deep --strict` |
| 4 | `get-task-allow` disabled | App Store rejects a bundle where it is enabled |
| 5 | `beta-reports-active` | required for TestFlight |
| 6 | profile has no device list | `ProvisionedDevices` present ⇒ development profile |
| 7 | architecture arm64 | |
| 8 | version fields | an empty `CFBundleVersion` fails the upload |
| 9 | display name | parameterized |
| 10 | bundle identifier | parameterized |
| 11 | privacy manifest | `PrivacyInfo.xcprivacy` must be in the bundle |
| 12 | app icon | `Assets.car` / `AppIcon*.png` |
| 13 | permissions match declaration | an undeclared permission is one added silently |
| 14 | export declaration vs source | `ITSAppUsesNonExemptEncryption` is compared against whether the source actually uses an encryption API |

Gate 14 is the valuable one: the declaration and the artifact cannot drift apart silently.
If one changes and the other does not, the gate goes red.

## Before you blame the product

A red result can be your own parameter. Measured: running this against a second app with
`--expect-name` set to the wrong capitalisation produced a failure that was **the flag's**
fault, not the app's.

The permission gate has the same shape. Its first version came from an app whose flow asks
for nothing, so it asserted "there must be no permission strings at all". Run against a
different app it went red on a **legitimate** microphone and photo-library permission. A gate
that encodes one product's assumptions will write that assumption onto the next product as a
defect. The rule became "permissions must match what you declared" — an undeclared one is
still red, which is the real risk.

## Verification record

| Arm | Package | Result |
|---|---|---|
| known-good | app A, signed `.ipa` | 14 PASS / 0 FAIL |
| different app | app B, signed `.ipa` | 14 PASS / 0 FAIL once permissions declared |
| **known-bad** | same package, permission **not** declared | **RED**, named the exact missing key |
| third app | app C, signed `.ipa` | 14 PASS / 0 FAIL |
| **known-bad** | signature + profile stripped from a real bundle | **RED**, 2 failures: integrity and missing profile |
| **known-bad** | unsigned archive output | **RED**, 7 failures including every signature gate |

Run against three different apps; rejected known-bad in three distinct ways.

## Neighbours

Store metadata, age rating, App Privacy and review submission are out of scope.
Getting a native Xcode build *to* App Store Connect is `ios-appstore-native-delivery`.

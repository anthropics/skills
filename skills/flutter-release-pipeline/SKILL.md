---
name: flutter-release-pipeline
description: Automates the entire Flutter release process in one command. Use this skill when the user asks to run a Flutter release, publish a Flutter app, bump the version, build an APK or AAB, generate release notes, or do a Flutter release pipeline. Handles OS detection, flutter test gating, version bumping in pubspec.yaml, git log extraction, markdown release notes generation, CSV release logging, Android AAB/APK builds, optional iOS archive prep, and git commit/tag/push.
---

# Flutter Release Pipeline Skill

A production-grade, cross-agent automation skill that handles the entire Flutter release process in a single command. Works on macOS, Linux, and Windows.

## Prerequisites

Before running, verify:
- You are in a Flutter project root (pubspec.yaml must exist)
- DOCs/ and DOCs/releases/ directories exist (create if missing, with user permission)
- Git is initialized and remote is configured

## Safety Rules

- NEVER delete any files
- ALWAYS append to CSVs, never overwrite
- ALWAYS respect case sensitivity: DOCs/ (capital D, capital C, lowercase s)
- STOP the pipeline on test failure — do not proceed to build

## Step 0: Project Verification

1. Confirm pubspec.yaml exists in current directory
2. Confirm DOCs/ directory exists — if not, ask user: "DOCs/ directory not found. Create it? (yes/no)"
3. Confirm DOCs/releases/ exists — create if DOCs/ exists and user approved
4. Check for flutter_release_config.json — if exists, load saved preferences (build type, branch)
5. If no config, ask user:
   - Build type: AAB / APK / both / skip Android
   - Git branch to push to (default: main)
   - Save preferences to flutter_release_config.json for next time

## Step 1: Run Tests (GATE)

Detect OS and run tests:
- macOS/Linux: `flutter test --machine 2>&1 | tee /tmp/flutter_test_output.json`
- Windows: `flutter test --machine 2>&1 | Tee-Object -FilePath $env:TEMP\flutter_test_output.json`

Parse output:
- Count passed, failed, skipped, errors
- Extract failed test names and error messages
- Calculate duration

Log to DOCs/test_log.csv (append):
```
date,time,total,passed,failed,skipped,duration_seconds,status,failed_tests
```

**GATE: If any tests fail → print error summary, stop pipeline. Do NOT proceed.**

## Step 2: Version Bumping

Read current version from pubspec.yaml (format: `version: X.Y.Z+BUILD`):
- Increment patch: Z → Z+1
- Increment build number: BUILD → BUILD+1
- Write back to pubspec.yaml
- Confirm new version to user

## Step 3: Git Log Extraction

Get commits since last tag:
```bash
git log $(git describe --tags --abbrev=0 2>/dev/null || git rev-list --max-parents=0 HEAD)..HEAD --pretty=format:"%h|%s|%an|%ad" --date=short
```

Categorize commits:
- Features: feat, add, new, implement
- Bug Fixes: fix, bug, patch, resolve
- Improvements: improve, update, refactor, enhance, perf
- Other: everything else

## Step 4: Generate Release Notes

Create DOCs/releases/release_notes_vX.Y.Z.md:
```markdown
# Release Notes - vX.Y.Z
**Date:** YYYY-MM-DD  
**Build:** BUILD_NUMBER  
**Branch:** BRANCH_NAME

## What's New
### Features
- commit message (hash)

### Bug Fixes
- commit message (hash)

### Improvements
- commit message (hash)

### Other Changes
- commit message (hash)

## Build Information
- Flutter Version: (from `flutter --version`)
- Dart Version: (from flutter --version output)
- Total Commits: N
```

Present to user and offer: [1] Accept [2] Edit [3] Regenerate [4] Cancel
Wait for user choice before proceeding.

## Step 5: Log Release to CSV

Append to DOCs/releases/releases.csv:
```
version,build_number,date,time,branch,total_commits,features,fixes,improvements,other,release_notes_file,status
```
Status: "in-progress" at this point.

## Step 6: Android Build

Based on user preference from Step 0:

**AAB:**
- macOS/Linux: `flutter build appbundle --release 2>&1 | tee /tmp/flutter_build_output.txt`
- Windows: `flutter build appbundle --release`
- Output: build/app/outputs/bundle/release/app-release.aab

**APK:**
- `flutter build apk --release`
- Output: build/app/outputs/flutter-apk/app-release.apk

On build failure: show error, update CSV status to "build-failed", stop.

## Step 7: iOS Archive Prep (Optional)

After Android build succeeds, ask: "Prepare iOS archive? (flutter clean + flutter pub get) [yes/no]"

If yes:
```bash
flutter clean
flutter pub get
```
Then instruct user to open Xcode and run Product > Archive.

## Step 8: Git Operations

```bash
git add pubspec.yaml DOCs/
git commit -m "chore: release vX.Y.Z (build BUILD_NUMBER)"
git tag vX.Y.Z
git push origin BRANCH_NAME
git push origin vX.Y.Z
```

Update releases.csv status from "in-progress" to "complete".

## Step 9: Summary

Print a formatted summary box:
```
╔══════════════════════════════════════════╗
║         FLUTTER RELEASE COMPLETE         ║
╠══════════════════════════════════════════╣
║ Version:      X.Y.Z+BUILD               ║
║ Branch:       main                      ║
║ Tests:        N passed                  ║
║ Build:        AAB / APK                 ║
║ Release Notes: DOCs/releases/release_notes_vX.Y.Z.md ║
║ Tag:          vX.Y.Z pushed             ║
╚══════════════════════════════════════════╝
```

## Examples

- "Run the Flutter release pipeline"
- "Do a Flutter release"
- "Release my Flutter app"
- "Build and publish Flutter AAB"
- "Bump version and build Flutter"

## Guidelines

- Always verify project structure before starting
- Never skip the test gate
- Always append to CSV logs, never overwrite
- Respect case sensitivity of DOCs/ directory
- Present release notes for review before building
- Confirm git operations before pushing
- Source: https://github.com/Jaywalker-not-a-whitewalker/flutter-release-pipeline

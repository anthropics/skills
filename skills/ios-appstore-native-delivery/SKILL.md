---
name: ios-appstore-native-delivery
description: Ship a NATIVE Xcode iOS app (not Expo/EAS) to App Store Connect headlessly — archive, exportArchive, altool upload, bounded processing poll, internal TestFlight group, tester. Use when uploading a native build to TestFlight or App Store Connect, or when hitting "conflicting provisioning settings", "Cannot determine the Apple ID from Bundle ID", "Cloud signing permission error", a 403 on POST /v1/apps, or a mysterious KeyError after an App Store Connect API call. Covers four measured traps and keeps "uploaded", "VALID" and "installable" as separate claims.
---

# Native iOS → App Store Connect delivery

For projects built with `xcodebuild` against an `.xcodeproj`. If you are on **Expo/EAS**,
this is the wrong skill — that path has its own credentials model and its own traps.

## Prerequisites

```text
ASC API key : Key ID + Issuer ID + .p8        (from the environment, never in a file)
                export ASC_KEY_ID=<Key ID>
                export ASC_P8=<full path to AuthKey_<KeyID>.p8>   # chmod 600
                export ASC_ISSUER=<Issuer ID>   # or ASC_ISSUER_KEYCHAIN=<keychain service>
distribution certificate in the keychain
bundle identifier ALREADY REGISTERED in the developer portal (see trap 3)
```

No built-in defaults. A default would leak an account identifier into a shared file *and*
make the script silently look for the wrong key on someone else's machine — the second
failure is the nastier one.

## FOUR MEASURED TRAPS

### 1. Under automatic signing the identity STAYS `Apple Development`

```text
setting CODE_SIGN_IDENTITY="Apple Distribution" ->
  error: ... has conflicting provisioning settings. ... is automatically signed for
  development, but a conflicting code signing identity Apple Distribution has been
  manually specified.
```

Leave `CODE_SIGN_STYLE=Automatic` with `CODE_SIGN_IDENTITY=Apple Development`. The
distribution identity is swapped in by **`xcodebuild -exportArchive`**
(`method=app-store-connect`), not by `archive`. The `archive` step produces a
development-signed bundle with a wildcard profile, and **that bundle cannot be uploaded**.

Measured: five attempts were needed to find this. Attempts 1–3 all failed or produced an
unusable package; attempt 4 archived with a development identity; only attempt 5
(`archive` + `exportArchive`) produced a distribution-signed `.ipa`.

### 2. `ARCHIVE SUCCEEDED` does not prove the bundle is signed

With `CODE_SIGN_IDENTITY=""` the archive reports success and the bundle is
`code object is not signed at all`. Judge from `codesign -dvv` and the embedded profile,
never from the build log. Use `ios-package-gate`.

### 3. The API cannot create the app record

```text
POST /v1/apps -> 403
"The resource 'apps' does not allow 'CREATE'.
 Allowed operations are: GET_COLLECTION, GET_INSTANCE, UPDATE"
```

Creating the record is a **web-UI step**. Until it exists, `altool` says:

```text
ERROR: Cannot determine the Apple ID from Bundle ID '<id>' and platform 'IOS'. (19)
```

That message reads like a signing failure and is routinely misdiagnosed as one. It is not —
the record is simply missing.

Separately: if your key cannot create **identifiers**, `xcodebuild -allowProvisioningUpdates`
reports `Cloud signing permission error` plus `No profiles for '<id>' were found`. Register
the bundle id in the portal first, or use a key with the privileges to do it.

### 4. JWT `exp` must be ≤ 20 minutes

Exceed it and the API returns 401, which surfaces downstream as an unrelated error — often a
bare `KeyError: 'data'` — and gets debugged as a payload problem. Use `now + 1000`.

## Workflow

1. **Check the record first:** `asc-request.py GET "/v1/apps?filter[bundleId]=<id>"`.
   Empty ⇒ human step; do not attempt a blind upload.
2. Build in distribution mode — bundle id, team and version as **parameters**, never
   hard-coded into the project source.
3. `xcodebuild … archive` → `xcodebuild -exportArchive … method=app-store-connect`.
4. **Run `ios-package-gate`.** Red ⇒ stop.
5. Record the `.ipa` sha256, byte size and source commit.
6. `asc-upload.sh <ipa> <bundle-id>`.
7. Regenerate the project file *without* the distribution flags and verify it returns to its
   committed hash — otherwise your repo now carries signing config it should not.

## Acceptance — three separate states

```text
"No errors uploading"       = Apple ACCEPTED the bytes
processingState: VALID      = Apple FINISHED processing      <- different state
/betaGroups/<gid>/builds    = reachable by that group        <- different state
installed from TestFlight   = a FOURTH thing this never does
```

Report each one separately. "Uploaded" is not "installable".

## Failure handling

| Symptom | What to do |
|---|---|
| `apps does not allow CREATE` 403 | human step; the script exits `3` |
| `Cannot determine the Apple ID` | the record is missing — **not** a signing fault |
| `Cloud signing permission error` | bundle id not registered / key lacks the privilege |
| `processingState: INVALID` | classify and fix. **No blind retry, never re-upload the same build** |
| no VALID within the poll window | write `NOT_VERIFIED`; do not upload again |
| `KeyError: 'data'` | JWT lifetime; `exp ≤ 20 min` |

Re-uploading an identical binary burns a build number and hides the original error.

## Safety boundaries

- Tester identity is **read, not guessed**: `GET /v1/users`, take the `ACCOUNT_HOLDER`,
  add them, then **read the group back** to confirm. No other user is added.
- The `.p8` is **symlinked**, never copied. Key id and issuer are never printed in full.
- External test groups, public join links and App Review submission are **out of scope** —
  those are separate, human-authorized decisions.

## Verification record

| Arm | Result |
|---|---|
| `asc-request.py` against the live API | **HTTP 200** |
| `asc-upload.sh` with no bundle id | exits `1`, "no project constant is embedded" |
| `asc-upload.sh` with no credentials | exits `1`, names the missing variable |
| `asc-upload.sh`, record absent | exits `3`, prints the human step, attempts no upload |
| package bundle ≠ expected bundle | caught before any network call |
| traps 1–3 | measured first-hand |

> **Honest limit:** stages 0–2 are measured. The chain **after** `altool --upload-app` —
> processing poll, internal group creation, build assignment, tester — is written and
> reviewed but has **never run against a real upload**, because the app record did not
> exist. Treat those stages as unverified until you run them.

## Neighbours

Inspecting the package itself: `ios-package-gate`.
Everything *after* the first ship — release cadence, phased rollout, rejections: a release
operations skill, not this one.

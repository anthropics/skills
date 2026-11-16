# Firebase and Android checks

Apply these on top of the general review passes in SKILL.md when the code uses Firebase (Firestore, Realtime Database, Storage, Cloud Functions) on web or Android, or is an Android app. Ask for `firestore.rules`, `storage.rules`, and Realtime Database rules if they aren't in the code under review; in this stack, the rules are the backend.

## Contents

- Security rules
- Application logic
- Cloud Functions and the Admin SDK
- Android security
- Performance

## Security rules

- `allow read, write: if true;`, or `if request.auth != null` on collections holding per-user data, lets any visitor or any logged-in user read or write everyone's data.
- Rules should check ownership (`request.auth.uid == resource.data.ownerId`) and, on create and update, `request.resource.data`, so users can't set `ownerId`, `role`, `isAdmin`, `balance`, or `price` themselves.
- Field validation in rules: types, allowed keys (`request.resource.data.keys().hasOnly([...])`), and size limits.
- Expired test-mode rules (`request.time < timestamp.date(...)`).
- Rules for subcollections and `collectionGroup` queries.

## Application logic

Firestore isn't injectable the way SQL is, but logic still leaks:

- Client-side-only filtering (fetching everything and filtering in the app).
- Trusting totals or prices computed on the client.
- Roles stored in a document the user can write.
- Counters updated without `increment()` or a transaction (lost updates).

## Cloud Functions and the Admin SDK

- The Admin SDK bypasses security rules. Every callable or HTTP function must check `context.auth`/`request.auth`, validate its input, and authorize the action.
- Turn on App Check for callable functions where it makes sense.

## Android security

- **Treat the APK as public.** No API secrets, service-account JSON, or third-party secret keys in code, `strings.xml`, `BuildConfig`, or assets. (The API key in `google-services.json` is fine; it's an identifier, and rules plus App Check do the protecting.)
- Local SQLite/Room: `rawQuery`/`execSQL` with string concatenation is SQL injection. Use `?` placeholders with `selectionArgs`, or Room `@Query` parameters.
- Exported components (`android:exported="true"` activities, services, receivers, content providers) without permissions; deep links or intent extras trusted without validation; WebViews with `setJavaScriptEnabled(true)` plus `addJavascriptInterface`, or loading untrusted URLs.
- Sensitive data in `SharedPreferences` without encryption; tokens or PII in `Log.d`; `android:allowBackup` exposing app data; cleartext HTTP allowed in the network security config.
- Coroutines launched in `GlobalScope`; Firebase listeners not tied to a lifecycle-aware scope.

## Performance

- N+1: `getDoc()`/`get()` per item in a loop. Batch with `where(documentId(), 'in', chunk)` (chunks of up to 30), denormalize the fields you need, or restructure the data.
- Reading whole collections; listeners on large queries; missing composite indexes; documents that grow without limit (arrays that keep growing); patterns that multiply read/write costs. Suggest checking the Firebase usage dashboard.
- Android: network, database, or file work on the main thread; large bitmaps not downscaled; `RecyclerView` without `DiffUtil`/`ListAdapter`; work in `onBindViewHolder` that should be done once; listeners not tied to the lifecycle. Suggest the Android Studio Profiler to confirm.

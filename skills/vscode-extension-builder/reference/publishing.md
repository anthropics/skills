# Publishing to the VS Code Marketplace

Only follow this when the user explicitly asks to publish. Never fabricate,
store, or ask to persist a Personal Access Token (PAT) or Entra ID
credential — the user provides/pastes it themselves when prompted.

## 1. Ensure package.json is publish-ready

Required fields: `name`, `version` (semver), `publisher`, `engines.vscode`.

Recommended — set these yourself based on what the user described, don't
leave them for the user to add later:
- `repository` — enables vsce to auto-adjust relative links in README/CHANGELOG
- `icon` — 128x128+ PNG only, **SVG is rejected**
- `keywords` — up to 30 tags; more than that fails publishing outright
- `galleryBanner.color` — hex color for the Marketplace banner background
- `pricing` — `"Free"` or `"Trial"` (case-sensitive; defaults to `"Free"` if omitted, requires vsce ≥2.10.0)
- `sponsor` — `{ "url": "https://..." }` to show a sponsorship link (requires vsce ≥2.9.1)

## 2. Publisher + credential (user does this)

The user must do this part personally — it requires their own authenticated
browser session and cannot be done on their behalf.

1. User creates a publisher at https://marketplace.visualstudio.com/manage
   (unique publisher `id` + `name`).
2. User obtains a credential — two options:
   - **Personal Access Token (PAT)** — works today, but Azure DevOps is
     sunsetting global PATs on **December 1, 2026**. Generate at
     https://go.microsoft.com/fwlink/?LinkId=307137 (Azure DevOps → User
     settings → Personal access tokens → New Token → Organization: "All
     accessible organizations", Scope: Marketplace → Manage).
   - **Microsoft Entra ID with workload identity federation** (recommended
     going forward, especially for CI/CD) — a managed identity is added as a
     Marketplace publisher member (Contributor role), then credentials are
     exchanged via Azure CLI/pipeline rather than a long-lived token. This is
     org/pipeline setup the user (or their Azure admin) configures; walk them
     to https://code.visualstudio.com/api/working-with-extensions/publishing-extension#continuous-integration
     if they want it, don't attempt to configure Azure resources yourself.
3. Make sure `package.json`'s `"publisher"` field matches their publisher id.

## 3. Login (interactive — let the user paste their credential)

```bash
npx --yes @vscode/vsce login <publisher-id>
```

With Entra ID / managed identity already configured in the environment, skip
login and pass `--azure-credential` directly to `publish` instead (see below).

## 4. Publish

```bash
npx --yes @vscode/vsce publish
```

Or bump version while publishing:

```bash
npx --yes @vscode/vsce publish minor
npx --yes @vscode/vsce publish patch
npx --yes @vscode/vsce publish major
npx --yes @vscode/vsce publish 1.1.0
```

With Entra ID / managed identity:

```bash
npx --yes @vscode/vsce publish --azure-credential
```

### Pre-release versions

Only if the user explicitly asks for a pre-release channel:

```bash
npx --yes @vscode/vsce publish --pre-release
```

VS Code doesn't support semver pre-release tags (`1.0.0-beta`) — only plain
`major.minor.patch`. Convention: use **even** minor versions for regular
releases (`0.2.x`) and **odd** minor versions for pre-releases (`0.3.x`) so
the two channels never collide on a version number. Requires
`engines.vscode` >= `1.63.0`, or the pre-release won't show as installable.

### Platform-specific packaging

Only if the extension bundles native/platform-specific code — most
extensions this skill generates don't need this:

```bash
npx --yes @vscode/vsce package --target win32-x64
npx --yes @vscode/vsce publish --target win32-x64 win32-arm64
```

Supported targets: `win32-x64`, `win32-arm64`, `linux-x64`, `linux-arm64`,
`linux-armhf`, `alpine-x64`, `alpine-arm64`, `darwin-x64`, `darwin-arm64`,
`web`. If you want the extension to also run in the browser, `web` must be
included as one of the targets.

## Unpublishing / removing a version

```bash
npx --yes @vscode/vsce unpublish <publisher-id>.<extension-name>
```

This sets the extension's status to "Unpublished" — it's hidden from VS Code
and the Marketplace, but statistics are preserved and it remains reachable
via the API. **This is destructive and irreversible for that identifier** —
confirm explicitly with the user before running it; never run it
speculatively or as part of a troubleshooting attempt.

Deleting a single version, or removing an extension entirely (freeing
nothing — the name is permanently reserved and can never be reused by any
publisher), can only be done by the user via the
https://marketplace.visualstudio.com/manage web UI ("More Actions" menu) —
there's no CLI for those two operations.

## Alternative: manual upload (no credential needed in the terminal)

```bash
npx --yes @vscode/vsce package
```

Then the user uploads the generated `.vsix` manually at
https://marketplace.visualstudio.com/manage.

## Gotchas

- **SVG images are rejected.** Anywhere an image is resolvable in the
  extension (icon, README, CHANGELOG) — use PNG for the icon and
  HTTPS-hosted images (PNG/SVG-from-a-trusted-badge-provider only) elsewhere.
- **Publishing from Windows can lose POSIX file attributes** in the packaged
  `.vsix` (executable bits on bundled scripts, etc.). If the extension ships
  any file that needs an executable bit, publish from Linux or macOS (e.g. a
  CI runner) instead of a Windows dev machine.
- **`engines.vscode` semver matters.** No caret (`"1.8.0"`) pins to exactly
  that version; `"^1.8.0"` (the generator's default) allows that version and
  all later ones — almost always what you want.

## Troubleshooting

- **"You exceeded the number of allowed tags of 30"** — trim the `keywords`
  array in `package.json` to 30 or fewer.
- **403 Forbidden / 401 Unauthorized on login or publish** — the PAT's scope
  or organization is wrong. It must be scoped to "All accessible
  organizations" with "Marketplace (Manage)" access.
- **"Extension 'name' already exists"** — the `name` (or `displayName`) isn't
  unique on the Marketplace; pick a different one. Marketplace name
  uniqueness is separate from local scaffold naming, so this can surface
  only at publish time even though scaffolding succeeded.
- **`vsce unpublish` doesn't work** — this happens if the extension or
  publisher ID was changed after a prior publish. Fall back to the
  marketplace.visualstudio.com/manage web UI.
- **Pre-release not showing as installable** — `engines.vscode` is below
  `1.63.0`; bump it.

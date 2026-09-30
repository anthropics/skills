# Agora CLI Install and Auth

Verified against Agora CLI `0.1.3`.

## Install

```bash
npm install -g agoraio-cli
```

The installed command is:

```bash
agora --help
```

If the user still has the deprecated preview package:

```bash
npm uninstall -g agora-cli-preview
npm install -g agoraio-cli
```

## Login Flow

Primary commands:

```bash
agora login
agora whoami
agora logout
```

Equivalent auth-group commands:

```bash
agora auth login
agora auth status
agora auth logout
```

`agora login` starts an OAuth browser flow and stores a local session.

If browser auto-open fails, the CLI prints a URL and the user can open it manually.

## OAuth Loopback Rule

The verified `0.1.3` loopback login flow advertises a redirect URI shaped like:

```text
http://localhost:<port>/oauth/callback
```

Important rule:

- the `redirect_uri` sent to authorize and token exchange must match exactly
- treat `localhost` and `127.0.0.1` as different strings for OAuth validation

If the user reports a `redirect_uri mismatch` or a browser login that gets a `400` during token exchange, tell them to check for any local tooling or overrides that switch one step to `127.0.0.1` while the other still uses `localhost`.

## Config and Session Location

The CLI stores config, session, logs, and current-project context under the Agora CLI config directory.

- macOS default: `~/.agora-cli`
- Linux default: `$XDG_CONFIG_HOME/agora-cli` or `~/.config/agora-cli`
- local override for testing or isolation: `AGORA_HOME=/custom/path`

## What to Tell the User

- If they are not logged in, tell them to run `agora login` first.
- If they ask "am I logged in?", use `agora whoami` or `agora auth status`.
- If they want a noninteractive or isolated local setup, route to [automation.md](automation.md).

## Things Not to Overstate

- Do not promise headless service-account auth; the verified flow in `0.1.3` is browser-based OAuth.
- Do not claim the preview package is still the recommended install target.

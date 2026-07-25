# Setup & troubleshooting — wx-cli environment

Load this file when: (a) starting a run in a fresh environment where wx-cli hasn't been verified yet, or (b) any `wx` command fails.

## Prerequisites

Before invoking the workflow, verify the environment. Run these checks in order; stop at the first failure and surface the exact next command the user needs.

1. **wx-cli installed** — run `wx --version`. If missing, tell the user to install it themselves (`npm install -g @jackwener/wx-cli` or use one of the alternatives at https://github.com/jackwener/wx-cli). **Do NOT auto-install** — this repo forbids piped/silent installs.
2. **`~/.wx-cli` directory owned by the current user** — `sudo wx init` historically chowned this directory to root, which breaks every subsequent non-sudo `wx` call. Check:
   ```bash
   ls -la ~/.wx-cli/ 2>/dev/null | head -5
   ```
   If the directory exists but the owner is `root` (or anything other than `$(whoami)`), tell the user to repair it themselves:
   ```bash
   sudo chown -R $(whoami) ~/.wx-cli
   sudo rm -f ~/.wx-cli/daemon.pid ~/.wx-cli/daemon.sock
   wx daemon start
   ```
   The skill should NOT run `sudo` on the user's behalf.
3. **wx-cli initialized** — `wx sessions` should return data. If it fails with "no keys" / "init required", instruct the user to run `wx init` while WeChat is running (on macOS, `codesign --force --deep --sign - /Applications/WeChat.app` first). Prefer non-sudo init; only fall back to `sudo wx init` if the user's wx-cli version requires it — and warn them that they'll need step 2's chown after.
4. **WeChat 4.x running and logged in** — required for the daemon to find data files.

## wx-cli quick reference

| Command | Purpose |
|---------|---------|
| `wx --version` | Sanity-check that wx-cli is installed |
| `wx sessions --json` | List recent sessions; useful for verifying init and finding the user's own wxid |
| `wx contacts --query "<name>" --json` | Fuzzy-match contacts/groups by display name, remark, or wxid |
| `wx history "<group>" --since DATE --until DATE -n N --json` | Pull a group's messages within a date range as JSON |
| `wx members "<group>" --json` | List a group's members (rarely needed; mostly for completeness) |
| `wx stats "<group>" --since DATE` | wx-cli's built-in stats; we compute our own from `wx history` JSON so the format matches our digest |
| `wx daemon status` / `wx daemon stop` / `wx daemon logs --follow` | Daemon lifecycle (troubleshooting) |

All `wx` commands accept `--json` for machine-readable output. Default output is YAML — only use it for human eyeballing during debugging.

## Troubleshooting

When a `wx` command fails, diagnose by the symptom, not by retrying blindly. Common patterns:

| Symptom | Cause | Fix (tell the user to run these — do NOT run `sudo` for them) |
|---------|-------|----------------------------------------------------------------|
| `Operation not permitted` / `Access denied to ~/.wx-cli` | Sandbox is on | Re-run the command with `dangerouslyDisableSandbox: true`. Persistent fix: `/sandbox` to allow `~/.wx-cli` and the WeChat data dir. |
| `无法写入 /Users/<u>/.wx-cli` / `Permission denied` | `~/.wx-cli` is owned by root (legacy `sudo wx init`) | `sudo chown -R $(whoami) ~/.wx-cli && sudo rm -f ~/.wx-cli/daemon.{pid,sock} && wx daemon start` |
| `wx history` hangs / times out / returns nothing | Daemon is stuck | `wx daemon stop && rm -f ~/.wx-cli/daemon.{pid,sock} && wx daemon start`, then retry |
| `no keys` / `init required` after the daemon was working | Keys went stale (WeChat restart, version upgrade) | Make sure WeChat is running, then `wx init --force` (non-sudo first; only `sudo` if your wx-cli version requires it) |
| `wx contacts` returns zero rows for a group you know exists | Group is folded into 折叠群 or the daemon hasn't indexed it yet | `wx sessions --json` and search there; if missing, run `wx daemon stop && wx daemon start` and retry |
| Messages returned but `--since` / `--until` window looks wrong | Date string not in `YYYY-MM-DD` format, or off-by-one timezone | Confirm the dates are local-time `YYYY-MM-DD`. Re-filter the JSON by `timestamp` locally as a belt-and-suspenders step. |
| Empty result for a chat that should have activity | `-n` cap too low for a noisy group | Raise `-n` (e.g. to 20000) and re-fetch |

**Recovery order when nothing makes sense:**

1. Is WeChat running?
2. Is `~/.wx-cli` owned by `$(whoami)`?
3. Is the daemon healthy? (`wx daemon status`)
4. Restart the daemon (`wx daemon stop && wx daemon start`)
5. Last resort: `wx init --force` (while WeChat is running)

Never auto-retry inside the skill — every failure should produce a clear diagnostic plus the exact command the user needs to run.

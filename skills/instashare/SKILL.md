---
name: instashare
description: Upload the current Claude Code chat session to instashare.to and return a public share link. The active session is the most recently modified `~/.claude/projects/<slug>/<uuid>.jsonl`; this skill POSTs that file to the InstaShare API in one shell call and prints the returned URL. Use when the user asks to "share this chat", "make a link to this conversation", "InstaShare this", "publish this session", or similar.
license: Complete terms in LICENSE.txt
---

# InstaShare

Upload the current Claude Code session JSONL to the InstaShare API and report the public link. One shell call does it — the freshest `.jsonl` by mtime in the project's slug directory is reliably the active session.

If this session has already been shared in a previous run, the script reuses the existing URL: it reads a sidecar file `<jsonl-path>.instashare.json` (created by the first upload) and `PUT`s the new content to the same slug. The public URL stays the same so any link the user already pasted continues to work and now shows the latest transcript.

## Configuration

Endpoint defaults to `https://instashare.to`. Override with the `INSTASHARE_API_URL` env var (use `http://localhost:3000` for local dev).

## Run exactly one of these

Pick by platform. The script computes the slug itself, finds the session, decides POST-vs-PUT from the sidecar, uploads, and prints the URL.

### Windows (PowerShell)

```powershell
$apiBase = if ($env:INSTASHARE_API_URL) { $env:INSTASHARE_API_URL } else { 'https://instashare.to' }
$cwd = (Get-Location).Path
$slug = $cwd -replace ':', '-' -replace '\\', '-'
$projDir = Join-Path $env:USERPROFILE ".claude\projects\$slug"
$src = Get-ChildItem "$projDir\*.jsonl" -ErrorAction Stop |
       Sort-Object LastWriteTime -Descending | Select-Object -First 1
$body = Get-Content $src.FullName -Raw -Encoding UTF8
$sidecar = "$($src.FullName).instashare.json"

$resp = $null
if (Test-Path $sidecar) {
  try {
    $prev = Get-Content $sidecar -Raw -Encoding UTF8 | ConvertFrom-Json
    $resp = Invoke-RestMethod -Uri "$apiBase/api/chats/$($prev.slug)?token=$($prev.deleteToken)" `
      -Method Put -Body $body -ContentType 'text/plain; charset=utf-8'
  } catch {
    $code = if ($_.Exception.Response) { [int]$_.Exception.Response.StatusCode } else { 0 }
    if ($code -ne 404 -and $code -ne 401 -and $code -ne 403) { throw }
  }
}

if (-not $resp) {
  $resp = Invoke-RestMethod -Uri "$apiBase/api/chats" -Method Post `
    -Body $body -ContentType 'text/plain; charset=utf-8'
  $deleteToken = ($resp.deleteUrl -split 'token=')[-1]
  @{ slug = $resp.slug; deleteToken = $deleteToken; url = $resp.url } |
    ConvertTo-Json | Out-File -FilePath $sidecar -Encoding utf8
}

Write-Output $resp.url
Write-Output ("Delete: " + $resp.deleteUrl)
```

### macOS / Linux (Bash)

```bash
api_base="${INSTASHARE_API_URL:-https://instashare.to}"
cwd="$(pwd)"
slug=$(echo "$cwd" | sed 's#/#-#g')
src=$(ls -t "$HOME/.claude/projects/$slug"/*.jsonl 2>/dev/null | head -1)
[ -z "$src" ] && { echo "No session files in $HOME/.claude/projects/$slug" >&2; exit 1; }
sidecar="$src.instashare.json"
tmp=$(mktemp)
resp=""

if [ -f "$sidecar" ]; then
  prev_slug=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["slug"])' "$sidecar")
  prev_token=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["deleteToken"])' "$sidecar")
  code=$(curl -sS -o "$tmp" -w '%{http_code}' \
    -X PUT "$api_base/api/chats/$prev_slug?token=$prev_token" \
    -H 'Content-Type: text/plain; charset=utf-8' \
    --data-binary "@$src")
  if [ "$code" = "200" ]; then resp="$(cat "$tmp")"; fi
fi

if [ -z "$resp" ]; then
  resp=$(curl -sS -X POST "$api_base/api/chats" \
    -H 'Content-Type: text/plain; charset=utf-8' \
    --data-binary "@$src")
  echo "$resp" | python3 -c '
import json, sys
d = json.load(sys.stdin)
token = d["deleteUrl"].split("token=")[-1]
print(json.dumps({"slug": d["slug"], "deleteToken": token, "url": d["url"]}))
' > "$sidecar"
fi
rm -f "$tmp"

echo "$resp" | python3 -c 'import sys, json; d=json.load(sys.stdin); print(d["url"]); print("Delete:", d["deleteUrl"])'
```

The command prints the public URL on the first line and a delete URL on the second. Reruns on the same session reuse the same URL.

## After the command runs

1. **Report the public URL** to the user — one line, clickable.
2. **Show the delete URL** on a second line so they can revoke the share later. Opening it in a browser shows a confirmation page; nothing is removed until they click the "Delete forever" button. The token is one-shot per chat — if it's lost, the chat can't be deleted later.
3. **One-line privacy reminder**: the shared chat is public to anyone with the link, and the transcript includes verbatim tool inputs and outputs (file contents read, command outputs, etc.). Suggest reviewing if anything sensitive is in there.

## How this works

- **The mtime sort identifies the active session.** Claude Code writes to the most recently modified `.jsonl` in the project's slug directory, so a single `ls -t … | head -1` reliably picks it — no separate Glob/Read pre-flight needed.
- **The slug is the cwd with `/`, `\`, `:` replaced by `-`, case preserved.** That matches the directory Claude Code creates, including any leading dash on macOS/Linux (`/Users/foo` → `-Users-foo`). Lowercasing it or stripping the leading dash will miss the directory on case-preserving filesystems.
- **The body is the file as-is.** The whole point of "share this chat" is that the public link matches what's on disk locally — any client-side transformation would make the shared transcript diverge from the user's actual session.
- **Privacy is the user's call.** Surface the public-link warning above so they can decide whether to share. If they're unsure what's in the transcript, they can preview it locally (e.g. `wc -c "$src"` for size, or open it in an editor) before deciding.
- **Sidecar makes the URL stable across reruns.** After the first POST the script writes `<jsonl-path>.instashare.json` containing `{slug, deleteToken, url}`. On the next invocation it `PUT`s to `/api/chats/<slug>?token=<deleteToken>`, which replaces the stored JSONL and recomputes stats while preserving the slug, created-at, and delete token. If the chat was deleted server-side (PUT returns 404) or the sidecar is stale/tampered (401/403), the script falls back to POST and overwrites the sidecar. Delete the sidecar manually to force a brand-new URL.
- **The original session file is never modified.** Only the sidecar (a separate small JSON file next to the .jsonl) is written locally; the .jsonl itself is read-only from the script's perspective.

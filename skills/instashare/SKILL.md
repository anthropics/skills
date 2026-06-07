---
name: instashare
description: InstaShare — upload the current Claude Code chat session to instashare.to and return a public share link. The active session is the most recently modified `~/.claude/projects/<slug>/<uuid>.jsonl`; this skill POSTs that file to the InstaShare API in one shell call and prints the returned URL. Use when the user asks to "share this chat", "make a link to this conversation", "InstaShare this", "publish this session", or similar.
tools: Bash
---

# InstaShare

Upload the current Claude Code session JSONL to the InstaShare API and report the public link. One shell call does it — the freshest `.jsonl` by mtime in the project's slug directory is reliably the active session.

If this session has already been shared in a previous run, the script reuses the existing URL: it reads a sidecar file `<jsonl-path>.instashare.json` (created by the first upload) and `PUT`s the new content to the same slug. The public URL stays the same so any link the user already pasted continues to work and now shows the latest transcript.

## Configuration

**Requires an account.** Sign in at <https://instashare.to>, generate an upload token at `/account`, and set it as `INSTASHARE_TOKEN` in your shell. The skill sends it as `Authorization: Bearer …` with every upload so the share lands on `/mine`.

Endpoint defaults to `https://instashare.to`. Override with the `INSTASHARE_API_URL` env var (use `http://localhost:3000` for local dev).

## Run exactly one of these

Pick by platform. The script computes the slug itself, finds the session, scrubs known secret patterns from the body in memory, decides POST-vs-PUT from the sidecar, uploads the scrubbed body, and prints the URL.

### Windows (PowerShell)

```powershell
$apiBase = if ($env:INSTASHARE_API_URL) { $env:INSTASHARE_API_URL } else { 'https://instashare.to' }
$token = $env:INSTASHARE_TOKEN
if (-not $token) {
  Write-Output "INSTASHARE_TOKEN is not set. Generate one at $apiBase/account and add it to your shell (setx INSTASHARE_TOKEN '...' then reopen the shell), then retry."
  exit 1
}
$authHeaders = @{ Authorization = "Bearer $token" }
$cwd = (Get-Location).Path
$slug = $cwd -replace ':', '-' -replace '\\', '-'
$projDir = Join-Path $env:USERPROFILE ".claude\projects\$slug"
$src = Get-ChildItem "$projDir\*.jsonl" -ErrorAction Stop |
       Sort-Object LastWriteTime -Descending | Select-Object -First 1
$body = Get-Content $src.FullName -Raw -Encoding UTF8
$sidecar = "$($src.FullName).instashare.json"

# Redact common secrets before upload. Curated patterns only — provider-specific
# first so e.g. OPENAI_API_KEY=sk-... is labelled openai-key rather than env-secret.
# Each rule has its own replacement string so cookie/auth-header rules can preserve
# the surrounding header name and quoting.
$patterns = @(
  @{ name = 'anthropic-key';     regex = 'sk-ant-[A-Za-z0-9_\-]{20,}';                                              replacement = '[REDACTED:anthropic-key]' },
  @{ name = 'openai-key';        regex = 'sk-(?!ant-)[A-Za-z0-9_\-]{20,}';                                          replacement = '[REDACTED:openai-key]' },
  @{ name = 'aws-access-key-id'; regex = '\b(?:AKIA|ASIA)[A-Z0-9]{16}\b';                                           replacement = '[REDACTED:aws-access-key-id]' },
  @{ name = 'github-token';      regex = '\b(?:gh[posru]_|github_pat_)[A-Za-z0-9_]{20,}\b';                         replacement = '[REDACTED:github-token]' },
  @{ name = 'slack-token';       regex = 'xox[abprs]-[A-Za-z0-9\-]{10,}';                                           replacement = '[REDACTED:slack-token]' },
  @{ name = 'stripe-key';        regex = '\b(?:sk|pk|rk)_live_[A-Za-z0-9]{20,}\b';                                  replacement = '[REDACTED:stripe-key]' },
  @{ name = 'google-api-key';    regex = '\bAIza[A-Za-z0-9_\-]{35}\b';                                              replacement = '[REDACTED:google-api-key]' },
  @{ name = 'jwt';               regex = '\beyJ[A-Za-z0-9_\-]{10,}\.eyJ[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{10,}\b'; replacement = '[REDACTED:jwt]' },
  @{ name = 'http-auth';         regex = '(?i)Authorization:\s*(?:Basic|Bearer|Digest|Token|OAuth)\s+[A-Za-z0-9+/=._\-]{8,}'; replacement = 'Authorization: [REDACTED:http-auth]' },
  @{ name = 'cookie-header';     regex = '(?i)(?:Cookie|Set-Cookie):\s*[A-Za-z_][A-Za-z0-9_\-]*=[^"''\\\r\n]{10,}'; replacement = '[REDACTED:cookie-header]' },
  @{ name = 'curl-cookie-arg';   regex = '(?<=\s)(?:-b|--cookie)\s+''[A-Za-z_][A-Za-z0-9_\-]*=[^''\\\r\n]{10,}''';  replacement = "-b '[REDACTED:cookie-header]'" },
  # Bare cookie chains (no `Cookie:` header in front) — 3+ name=value pairs separated by `; `.
  # Catches pasted DevTools output, COOKIE=… shell vars, heredoc cookie files, etc.
  # `(?<!\\)` avoids starting a match right after a JSON-escape backslash
  # (e.g. inside `"…cookie\nname=val…"`), which would otherwise corrupt the
  # JSON by leaving an orphan `\`.
  @{ name = 'cookie-chain';      regex = '(?<!\\)(?:[A-Za-z_][A-Za-z0-9_\-]{2,}=[^;"''\\\r\n]{8,};\s+){2,}[A-Za-z_][A-Za-z0-9_\-]{2,}=[^;"''\\\r\n]{8,}'; replacement = '[REDACTED:cookie-chain]' },
  @{ name = 'pem-private-key';   regex = '-----BEGIN [A-Z ]*PRIVATE KEY-----[\s\S]*?-----END [A-Z ]*PRIVATE KEY-----'; replacement = '[REDACTED:pem-private-key]' }
)
$redactionSummary = [ordered]@{}
foreach ($p in $patterns) {
  $matchCount = ([regex]::Matches($body, $p.regex)).Count
  if ($matchCount -gt 0) {
    $body = [regex]::Replace($body, $p.regex, $p.replacement)
    $redactionSummary[$p.name] = $matchCount
  }
}
$envRx = '\b([A-Z][A-Z0-9_]{0,40}(?:KEY|TOKEN|SECRET|PASSWORD|PASSWD))\s*=\s*([A-Za-z0-9_\-+/=]{16,})'
$envCount = ([regex]::Matches($body, $envRx)).Count
if ($envCount -gt 0) {
  $body = [regex]::Replace($body, $envRx, '$1=[REDACTED:env-secret]')
  $redactionSummary['env-secret'] = $envCount
}

$resp = $null
if (Test-Path $sidecar) {
  try {
    $prev = Get-Content $sidecar -Raw -Encoding UTF8 | ConvertFrom-Json
    $putUri = "$apiBase/api/chats/$($prev.slug)"
    if ($prev.deleteToken) { $putUri = "$putUri`?token=$($prev.deleteToken)" }
    $resp = Invoke-RestMethod -Uri $putUri -Method Put -Body $body `
      -ContentType 'text/plain; charset=utf-8' -Headers $authHeaders
  } catch {
    $code = if ($_.Exception.Response) { [int]$_.Exception.Response.StatusCode } else { 0 }
    if ($code -ne 404 -and $code -ne 401 -and $code -ne 403) { throw }
  }
}

if (-not $resp) {
  try {
    $resp = Invoke-RestMethod -Uri "$apiBase/api/chats" -Method Post `
      -Body $body -ContentType 'text/plain; charset=utf-8' -Headers $authHeaders
  } catch {
    $code = if ($_.Exception.Response) { [int]$_.Exception.Response.StatusCode } else { 0 }
    if ($code -eq 401) {
      Write-Output "Upload rejected (401). Your INSTASHARE_TOKEN is missing or revoked — generate a new one at $apiBase/account."
      exit 1
    }
    throw
  }
  $deleteToken = if ($resp.deleteUrl -and $resp.deleteUrl -match 'token=') { ($resp.deleteUrl -split 'token=')[-1] } else { '' }
  @{ slug = $resp.slug; deleteToken = $deleteToken; url = $resp.url } |
    ConvertTo-Json | Out-File -FilePath $sidecar -Encoding utf8
}

Write-Output $resp.url
Write-Output ("Delete: " + $resp.deleteUrl)
if ($redactionSummary.Count -gt 0) {
  $summary = ($redactionSummary.GetEnumerator() | ForEach-Object { "$($_.Value) $($_.Key)" }) -join ', '
  Write-Output "Redacted before upload: $summary"
}
```

### macOS / Linux (Bash)

```bash
api_base="${INSTASHARE_API_URL:-https://instashare.to}"
if [ -z "$INSTASHARE_TOKEN" ]; then
  echo "INSTASHARE_TOKEN is not set. Generate one at $api_base/account and add it to your shell (e.g. export INSTASHARE_TOKEN=...), then retry." >&2
  exit 1
fi
cwd="$(pwd)"
slug=$(echo "$cwd" | sed 's#/#-#g')
src=$(ls -t "$HOME/.claude/projects/$slug"/*.jsonl 2>/dev/null | head -1)
[ -z "$src" ] && { echo "No session files in $HOME/.claude/projects/$slug" >&2; exit 1; }
sidecar="$src.instashare.json"
tmp=$(mktemp)
redacted=$(mktemp)
resp=""

# Redact common secrets before upload. Curated patterns only — provider-specific
# first so e.g. OPENAI_API_KEY=sk-... is labelled openai-key rather than env-secret.
summary=$(python3 - "$src" "$redacted" <<'PY'
import re, sys
# (regex, replacement). Provider-specific rules first so e.g. OPENAI_API_KEY=sk-...
# is labelled openai-key rather than env-secret. Cookie/auth-header rules keep
# their surrounding header name or curl flag intact.
PATTERNS = [
    ('anthropic-key',     r'sk-ant-[A-Za-z0-9_\-]{20,}',                                              '[REDACTED:anthropic-key]'),
    ('openai-key',        r'sk-(?!ant-)[A-Za-z0-9_\-]{20,}',                                          '[REDACTED:openai-key]'),
    ('aws-access-key-id', r'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b',                                           '[REDACTED:aws-access-key-id]'),
    ('github-token',      r'\b(?:gh[posru]_|github_pat_)[A-Za-z0-9_]{20,}\b',                         '[REDACTED:github-token]'),
    ('slack-token',       r'xox[abprs]-[A-Za-z0-9\-]{10,}',                                           '[REDACTED:slack-token]'),
    ('stripe-key',        r'\b(?:sk|pk|rk)_live_[A-Za-z0-9]{20,}\b',                                  '[REDACTED:stripe-key]'),
    ('google-api-key',    r'\bAIza[A-Za-z0-9_\-]{35}\b',                                              '[REDACTED:google-api-key]'),
    ('jwt',               r'\beyJ[A-Za-z0-9_\-]{10,}\.eyJ[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{10,}\b', '[REDACTED:jwt]'),
    ('http-auth',         r'(?i)Authorization:\s*(?:Basic|Bearer|Digest|Token|OAuth)\s+[A-Za-z0-9+/=._\-]{8,}', 'Authorization: [REDACTED:http-auth]'),
    ('cookie-header',     r'''(?i)(?:Cookie|Set-Cookie):\s*[A-Za-z_][A-Za-z0-9_\-]*=[^"'\\\r\n]{10,}''', '[REDACTED:cookie-header]'),
    ('curl-cookie-arg',   r"""(?<=\s)(?:-b|--cookie)\s+'[A-Za-z_][A-Za-z0-9_\-]*=[^'\\\r\n]{10,}'""", "-b '[REDACTED:cookie-header]'"),
    # Bare cookie chains (no `Cookie:` header in front) — 3+ name=value pairs
    # separated by `; `. Catches pasted DevTools output, COOKIE=… shell vars,
    # heredoc cookie files, etc. `(?<!\\)` avoids starting a match right after
    # a JSON-escape backslash (e.g. inside `"…cookie\nname=val…"`), which
    # would otherwise corrupt the JSON by leaving an orphan `\`.
    ('cookie-chain',      r'''(?<!\\)(?:[A-Za-z_][A-Za-z0-9_\-]{2,}=[^;"'\\\r\n]{8,};\s+){2,}[A-Za-z_][A-Za-z0-9_\-]{2,}=[^;"'\\\r\n]{8,}''', '[REDACTED:cookie-chain]'),
    ('pem-private-key',   r'-----BEGIN [A-Z ]*PRIVATE KEY-----[\s\S]*?-----END [A-Z ]*PRIVATE KEY-----', '[REDACTED:pem-private-key]'),
]
text = open(sys.argv[1], 'r', encoding='utf-8').read()
counts = {}
for name, rx, repl in PATTERNS:
    n = len(re.findall(rx, text))
    if n:
        counts[name] = n
        text = re.sub(rx, repl, text)
text, n = re.subn(
    r'\b([A-Z][A-Z0-9_]{0,40}(?:KEY|TOKEN|SECRET|PASSWORD|PASSWD))\s*=\s*([A-Za-z0-9_\-+/=]{16,})',
    r'\1=[REDACTED:env-secret]', text)
if n:
    counts['env-secret'] = n
open(sys.argv[2], 'w', encoding='utf-8').write(text)
print(', '.join(f'{v} {k}' for k, v in counts.items()))
PY
)

if [ -f "$sidecar" ]; then
  prev_slug=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["slug"])' "$sidecar")
  prev_token=$(python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d.get("deleteToken","") or "")' "$sidecar")
  put_uri="$api_base/api/chats/$prev_slug"
  [ -n "$prev_token" ] && put_uri="$put_uri?token=$prev_token"
  code=$(curl -sS -o "$tmp" -w '%{http_code}' \
    -X PUT "$put_uri" \
    -H "Authorization: Bearer $INSTASHARE_TOKEN" \
    -H 'Content-Type: text/plain; charset=utf-8' \
    --data-binary "@$redacted")
  if [ "$code" = "200" ]; then resp="$(cat "$tmp")"; fi
fi

if [ -z "$resp" ]; then
  code=$(curl -sS -o "$tmp" -w '%{http_code}' \
    -X POST "$api_base/api/chats" \
    -H "Authorization: Bearer $INSTASHARE_TOKEN" \
    -H 'Content-Type: text/plain; charset=utf-8' \
    --data-binary "@$redacted")
  if [ "$code" = "401" ]; then
    rm -f "$tmp" "$redacted"
    echo "Upload rejected (401). Your INSTASHARE_TOKEN is missing or revoked — generate a new one at $api_base/account." >&2
    exit 1
  fi
  if [ "$code" != "200" ] && [ "$code" != "201" ]; then
    cat "$tmp" >&2
    rm -f "$tmp" "$redacted"
    echo "" >&2
    echo "Upload failed (HTTP $code)." >&2
    exit 1
  fi
  resp="$(cat "$tmp")"
  echo "$resp" | python3 -c '
import json, sys
d = json.load(sys.stdin)
url = d.get("deleteUrl", "")
token = url.split("token=")[-1] if "token=" in url else ""
print(json.dumps({"slug": d["slug"], "deleteToken": token, "url": d["url"]}))
' > "$sidecar"
fi
rm -f "$tmp" "$redacted"

echo "$resp" | python3 -c 'import sys, json; d=json.load(sys.stdin); print(d["url"]); print("Delete:", d["deleteUrl"])'
[ -n "$summary" ] && echo "Redacted before upload: $summary"
```

The command prints the public URL on the first line, a delete URL on the second, and — if anything was scrubbed — a `Redacted before upload: …` summary on a third. Reruns on the same session reuse the same URL. The share also shows up immediately at `<api_base>/mine` for the signed-in account that owns the token.

## After the command runs

1. **Report the public URL** to the user — one line, clickable.
2. **Show the delete URL** on a second line as a one-click revoke link. Also mention that the share is listed at `/mine` for the account that owns the upload token — that's the primary place to manage shares.
3. **Note what was redacted, if anything**: when a `Redacted before upload: …` line appears, the skill replaced matches of a curated pattern set (AWS / GitHub / Slack / Stripe / OpenAI / Anthropic / Google keys, JWTs, PEM private-key blocks, HTTP `Authorization: Basic|Bearer|…` headers, `Cookie:` / `Set-Cookie:` header values, curl `-b 'cookie=val; …'` flags, and `*_KEY=` / `*_TOKEN=` / `*_SECRET=` / `*_PASSWORD=` assignments) with `[REDACTED:<kind>]` markers before upload. The scan is best-effort — custom or proprietary token formats won't match — so still suggest reviewing the public link if the chat may contain anything else sensitive.

## How this works

- **The mtime sort identifies the active session.** Claude Code writes to the most recently modified `.jsonl` in the project's slug directory, so a single `ls -t … | head -1` reliably picks it — no separate Glob/Read pre-flight needed.
- **The slug is the cwd with `/`, `\`, `:` replaced by `-`, case preserved.** That matches the directory Claude Code creates, including any leading dash on macOS/Linux (`/Users/foo` → `-Users-foo`). Lowercasing it or stripping the leading dash will miss the directory on case-preserving filesystems.
- **The body is the file with common secrets scrubbed in place.** Before POST/PUT the snippet scans `$body` against a curated pattern set (provider API keys, JWTs, PEM private-key blocks, HTTP `Authorization` / `Cookie` / `Set-Cookie` header values, curl `-b 'cookies'` flags, and `*_KEY=` / `*_TOKEN=` / `*_SECRET=` / `*_PASSWORD=` style env assignments) and replaces matches with `[REDACTED:<kind>]`. Everything else is uploaded verbatim. Secrets matching one of the patterns therefore never leave the machine — they're scrubbed before the HTTPS body is even constructed. The original `.jsonl` on disk is never modified.
- **The scan is best-effort.** It targets the well-known token formats listed above. Custom or proprietary tokens, free-form passwords in prose, and high-entropy strings without a recognizable prefix won't match. Still surface the public-link warning so the user can decide whether to share, and recommend reviewing the link if the chat may contain anything else sensitive. If they're unsure what's in the transcript, they can preview it locally (e.g. `wc -c "$src"` for size, or open it in an editor) before deciding.
- **Sidecar makes the URL stable across reruns.** After the first POST the script writes `<jsonl-path>.instashare.json` containing `{slug, deleteToken, url}`. On the next invocation it `PUT`s to `/api/chats/<slug>?token=<deleteToken>`, which replaces the stored JSONL and recomputes stats while preserving the slug, created-at, and delete token. If the chat was deleted server-side (PUT returns 404) or the sidecar is stale/tampered (401/403), the script falls back to POST and overwrites the sidecar. Delete the sidecar manually to force a brand-new URL.
- **The original session file is never modified.** Only the sidecar (a separate small JSON file next to the .jsonl) is written locally; the .jsonl itself is read-only from the script's perspective.

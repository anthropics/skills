# Anthropic CLI (`ant`)

The `ant` CLI exposes every Claude API resource as a shell subcommand. Compared to `curl`: request bodies are built from typed flags or piped YAML instead of hand-written JSON, `@path` inlines file contents into any string field, `--transform` extracts fields with a GJSON path (no `jq`), list endpoints auto-paginate (cap total results with `--max-items N`; `--limit` only sets the server page size), and the `beta:` prefix auto-sets the right `anthropic-beta` header.

## When to use the CLI vs the SDK

**CLI for the control plane, SDK for the data plane.** Agents and environments are relatively static resources you define, configure, and debug with `ant` — check the YAML into your repo, apply from CI, inspect from a terminal. Sessions are dynamic and driven by your application through the SDK — create per task, stream events, react to tool calls, integrate into your product. Both hit the same API; the split is about where the call lives, not what's possible.

| | Control plane → `ant` | Data plane → SDK |
|---|---|---|
| Resources | agents, environments, skills, vaults, files | sessions, events |
| Cadence | Once per deploy / ad-hoc | Every task / every turn |
| Lives in | `*.yaml` in your repo + CI + terminal | Application code |
| Typical calls | `create < agent.yaml`, `update --version N`, `list`, `retrieve`, `archive`, `--debug` | `sessions.create()`, `events.stream()`, `events.send()` |

## Install and auth

```sh
# macOS
brew install anthropics/tap/ant
xattr -d com.apple.quarantine "$(brew --prefix)/bin/ant"

# Linux / WSL — pick the release from github.com/anthropics/anthropic-cli/releases
curl -fsSL "https://github.com/anthropics/anthropic-cli/releases/download/v${VERSION}/ant_${VERSION}_$(uname -s | tr A-Z a-z)_$(uname -m | sed -e s/x86_64/amd64/ -e s/aarch64/arm64/).tar.gz" \
  | sudo tar -xz -C /usr/local/bin ant

# Or from source (Go 1.22+)
go install github.com/anthropics/anthropic-cli/cmd/ant@latest
```

**Auth** — the CLI resolves credentials the same way the SDKs do (first match wins): explicit flags, then `ANTHROPIC_API_KEY`, then `ANTHROPIC_AUTH_TOKEN`, then the `ANTHROPIC_PROFILE`-selected or active profile, then Workload Identity Federation env vars, then the default profile on disk. Override the host with `ANTHROPIC_BASE_URL` or `--base-url`.

- **API key**: set `ANTHROPIC_API_KEY` in the environment.
- **OAuth profile** (no static key to manage): `ant auth login` opens a browser, exchanges for a short-lived token, and stores a profile under `$ANTHROPIC_CONFIG_DIR` (default `~/.config/anthropic/` on Linux/macOS, `%APPDATA%\Anthropic` on Windows — `configs/<profile>.json` for settings, `credentials/<profile>.json` for tokens). Subsequent `ant` (and SDK) calls pick it up automatically — a bare `Anthropic()` client works after login, but scripts that read `ANTHROPIC_API_KEY` directly do not. Claude Code and the Claude Agent SDK honor the same profile resolution. `ant auth status` shows which credential source and profile won (it reports status only — don't script against its exit code as a health check); `ant auth logout` clears the active profile (`--all` for every profile). On a remote host without a browser, `ant auth login --no-browser` prints the authorize URL and accepts the code back in the terminal.
- **Non-interactive workloads** (CI, servers, containers): interactive login is for development on your own machine — use Workload Identity Federation instead (see the authentication docs via `shared/live-sources.md`).

> **The #1 auth trap:** profiles are only consulted when no API key is set. A stale exported `ANTHROPIC_API_KEY` silently overrides every profile — requests hit whatever org/workspace that key is scoped to. `ant auth status` shows which source won; unset the key (or per-command: `env -u ANTHROPIC_API_KEY ant …`) before relying on a profile. Truly **unset** it — an empty `ANTHROPIC_API_KEY=""` still wins its precedence slot and authenticates with an empty key. The same shadowing applies in reverse to Claude Code: after `ant auth login`, Claude Code may warn about an auth conflict between the profile and its own `/login` credential — keep one (use the profile and `/logout` in Claude Code, or `ant auth logout` to keep Claude Code's own login).

**Named profiles** — an interactive-login token is bound to a single org+workspace, and the API only shows resources belonging to that workspace. If an agent, session, or file you created "disappears", the usual cause is a token scoped to a different workspace than the one that created it (`ant auth status` shows the active workspace). Multi-workspace work means one profile per workspace:

```sh
ant auth login --profile <name>                  # creates the profile if it doesn't exist; org/workspace picker in browser
ant auth login --profile <name> --workspace-id wrkspc_01...   # bind directly, skip the picker
ant profile activate <name>                      # switch the default profile
ant --profile <name> models list                 # one-off; equivalent: ANTHROPIC_PROFILE=<name> ant models list
ant profile list                                 # inspect
ant profile set workspace_id wrkspc_01... --profile <name>    # edit config keys (workspace_id, base_url, organization_id, …)
```

`ant profile set` edits an existing profile's config — it never creates one, and it does **not** rebind already-issued credentials; run `ant auth login` again under that profile to mint a token for the new target. Pointing `ANTHROPIC_PROFILE` at a profile that doesn't exist is an error, not a fall-through. Refresh tokens eventually hard-expire (they don't slide with use) — when a previously working profile starts failing auth, re-run `ant auth login` before debugging anything else.

**Scopes** — a profile's OAuth scope set is requested at login (`--scope`) and persists on the profile (`scope` is also a `profile set` config key; like other config edits, changing it requires a fresh `ant auth login` to take effect). Privileged scopes — e.g. `org:admin` for organization-administration endpoints — are **not** in the default scope set: pass the full set you want explicitly (`ant auth login --profile admin --scope "... org:admin"`), and the server grants a privileged scope only if your role actually has it. Because the scope set rides on every token the profile mints, keep privileged work on a dedicated profile (`admin` vs `default`) and do day-to-day inference on the unprivileged one, switching with `--profile`/`ANTHROPIC_PROFILE`. Check `ant auth login --help` for the current scope list, and `ant auth status` to see what the active token carries.

To hand the active credential to a subprocess or raw-HTTP script:

```sh
# Bare access token — for curl's Authorization header
curl https://api.anthropic.com/v1/messages \
  -H "Authorization: Bearer $(ant auth print-credentials --access-token)" \
  -H "anthropic-version: 2023-06-01" \
  -H "anthropic-beta: oauth-2025-04-20" \
  -H "content-type: application/json" \
  -d '{"model": "claude-opus-4-8", "max_tokens": 1024, "messages": [{"role": "user", "content": "Hello"}]}'

# .env format — sets ANTHROPIC_AUTH_TOKEN (and ANTHROPIC_BASE_URL if the profile has one).
# Output is bare KEY=value (no `export`), so use `set -a` to auto-export for child processes:
set -a; eval "$(ant auth print-credentials --env)"; set +a
python my_script.py   # SDK picks up ANTHROPIC_AUTH_TOKEN
```

OAuth tokens go on `Authorization: Bearer` (not `x-api-key:`) **plus the `anthropic-beta: oauth-2025-04-20` header** — converting a raw curl/httpx script from an API key is a header change, not a key swap. The beta header requirement is endpoint-dependent (some endpoints happen to work without it; `/v1/messages` does not) — always send it so requests don't break when you switch endpoints. The token is short-lived and not auto-refreshed when passed via env var, so re-run `print-credentials` before it expires for long-running scripts (`print-credentials` itself refreshes the token if needed). If both `ANTHROPIC_API_KEY` and `ANTHROPIC_AUTH_TOKEN` are set, the SDKs send both and the API rejects the request — unset `ANTHROPIC_API_KEY` before `eval`ing the `--env` output.

**Foot-gun:** `ant auth print-credentials` with **no flags** prints the entire credentials JSON, not the bare token — putting that in an `Authorization` header yields an empty response or HTTP/2 protocol error. Always use `--access-token` for headers (it always reads the named/active profile; a set `ANTHROPIC_API_KEY` doesn't override credential printing).

## Command structure

```
ant <resource>[:<subresource>] <action> [flags]
```

Beta resources (agents, sessions, environments, deployments, skills, vaults, memory stores) live under `beta:` — the CLI auto-sends the right `anthropic-beta` header, so don't pass it yourself unless overriding with `--beta <header>`. For self-hosted environments, `ant beta:worker poll/run` and `ant beta:environments:work stats/stop` drive and monitor the work queue — see `shared/managed-agents-self-hosted-sandboxes.md`.

```sh
ant models list
ant messages create --model claude-opus-4-8 --max-tokens 1024 --message '{role: user, content: "Hello"}'
ant beta:agents retrieve --agent-id agent_01...
ant beta:sessions:events list --session-id session_01...
```

`ant --help` lists resources; append `--help` to any subcommand for its flags.

## Global flags

| Flag | Purpose |
| --- | --- |
| `--format` | `auto` (default: pretty if TTY, compact if piped), `json`, `jsonl`, `yaml`, `pretty`, `raw`, `explore` (interactive TUI) |
| `--transform` | GJSON path applied to the response (per-item on list endpoints). Not applied when `--format raw`. |
| `-r`, `--raw-output` | If the transformed result is a string, print it without quotes (jq semantics). Pair with `--transform` for scalar capture. |
| `--max-items` | Cap total results returned from auto-paginating list endpoints (distinct from `--limit`, which is the server page size). |
| `--format-error` / `--transform-error` | Same as `--format`/`--transform`, applied to error responses. `-r` does not apply to the error path — use `--format-error yaml` for unquoted error scalars. |
| `--base-url` | Override API host |
| `--debug` | Print full HTTP request + response to stderr (API key redacted) |

## Output — `--transform` + `--format`

`--transform` takes a [GJSON path](https://github.com/tidwall/gjson/blob/master/SYNTAX.md). On list endpoints it runs **per item**, not on the envelope.

```sh
ant beta:agents list --transform '{id,name,model}' --format jsonl
```

**Extract a scalar for shell use:** pair `--transform` with `-r` (`--raw-output` — prints strings unquoted, jq-style):

```sh
AGENT_ID=$(ant beta:agents create --name "My Agent" --model '{id: claude-sonnet-4-6}' \
  --transform id -r)
```

## Input — flags, stdin, `@file`

**Flags** — scalar fields map directly. Structured fields accept relaxed-YAML syntax (unquoted keys) or strict JSON. Repeatable flags build arrays (each `--tool`, `--event`, `--message` appends one element):

```sh
ant beta:agents create \
  --name "Research Agent" \
  --model '{id: claude-opus-4-8}' \
  --tool '{type: agent_toolset_20260401}' \
  --tool '{type: custom, name: search_docs, input_schema: {type: object, properties: {query: {type: string}}}}'
```

**Stdin** — pipe a full JSON or YAML body. Merged with flags; flags win on conflict (for array fields, any flag **replaces** the stdin array entirely — it does not append). Quote the heredoc delimiter (`<<'YAML'`) to disable shell expansion inside the body:

```sh
ant beta:agents create <<'YAML'
name: Research Agent
model: claude-opus-4-8
system: |
  You are a research assistant. Cite sources for every claim.
tools:
  - type: agent_toolset_20260401
YAML
```

**`@file` references** — inline a file's contents into any string-valued field. Inside structured flag values, quote the path. Binary files are auto-base64'd; force with `@file://` (text) or `@data://` (base64). Escape a literal leading `@` as `\@`.

```sh
ant beta:agents create --name "Researcher" --model '{id: claude-sonnet-4-6}' --system @./prompts/researcher.txt

ant messages create --model claude-opus-4-8 --max-tokens 1024 \
  --message '{role: user, content: [
    {type: document, source: {type: base64, media_type: application/pdf, data: "@./scan.pdf"}},
    {type: text, text: "Extract the text from this scanned document."}
  ]}' \
  --transform 'content.0.text' -r
```

Flags that natively take a file path (e.g. `--file` on `beta:files upload`) accept a bare path without `@`.

## Version-controlled Managed Agents resources

This is the recommended flow for defining agents and environments — check the YAML into your repo and sync via `create` (first time) / `update` (thereafter). See `shared/managed-agents-core.md` for the field reference.

```yaml
# summarizer.agent.yaml
name: Summarizer
model: claude-sonnet-4-6
system: |
  You are a helpful assistant that writes concise summaries.
tools:
  - type: agent_toolset_20260401
```

```sh
# Create (once) — capture the ID
AGENT_ID=$(ant beta:agents create < summarizer.agent.yaml --transform id -r)

# Update (CI) — needs ID + current version (optimistic lock)
ant beta:agents update --agent-id "$AGENT_ID" --version 1 < summarizer.agent.yaml
```

Same pattern for environments (`ant beta:environments create|update < env.yaml`), then start a session with both IDs:

```sh
ant beta:sessions create --agent "$AGENT_ID" --environment-id "$ENV_ID" --title "Task"
ant beta:sessions:events send --session-id "$SID" \
  --event '{type: user.message, content: [{type: text, text: "Summarize X"}]}'
ant beta:sessions:events list --session-id "$SID" --transform 'content.0.text' -r
ant beta:sessions:events stream --session-id "$SID"   # live event stream
```

### Interactive session loop (stream-before-send)

`ant beta:sessions:events stream` only delivers events emitted *after* the stream opens — so open it **before** sending the kickoff to avoid missing early events. Use process substitution to hold the stream on a file descriptor, send, then read:

```sh
exec {stream}< <(ant beta:sessions:events stream --session-id "$SID" \
  --transform '{type,text:content.#(type=="text").text,err:error.message}' --format yaml)

ant beta:sessions:events send --session-id "$SID" > /dev/null <<'YAML'
events:
  - type: user.message
    content:
      - type: text
        text: Summarize the repo README
YAML

type=
while IFS= read -r -u "$stream" line; do
  case "$line" in
    type:\ session.status_idle) break ;;
    type:\ session.error)
      IFS= read -r -u "$stream" next || next=
      case "$next" in err:\ *) msg=${next#err: } ;; *) msg=unknown ;; esac
      printf '\n[Error: %s]\n' "$msg"; break ;;
    type:\ *) type=${line#type: } ;;
    text:*)
      [[ $type == agent.message ]] || continue
      val=${line#text: }
      case "$val" in '|-'|'|') ;; *) printf '%s' "$val" ;; esac ;;
    \ \ *)
      if [[ $type == agent.message ]]; then printf '%s\n' "${line#  }"; fi ;;
  esac
done
exec {stream}<&-
```

This works for interactive exploration and demos. For application code that needs to react to `agent.tool_use` / `agent.custom_tool_use` events, reconnect after drops, or dedup against `events.list`, use the SDK — see `shared/managed-agents-client-patterns.md`.

## Scripting patterns

`--transform id -r` on a list endpoint emits one bare ID per line — compose with `xargs`, or use `--max-items N` to bound the result set without piping through `head`:

```sh
FIRST=$(ant beta:agents list --transform id -r --max-items 1)
ant beta:agents:versions list --agent-id "$FIRST" --transform '{version,created_at}' --format jsonl
```

Error shaping mirrors the success path (note: `-r` does not apply to error output — use `--format-error yaml` for an unquoted scalar here):

```sh
ant beta:agents retrieve --agent-id bogus --transform-error error.message --format-error yaml 2>&1
```

Shell completion: `ant @completion {zsh|bash|fish|powershell}`.

For the full, always-current reference (including per-endpoint flags), WebFetch the **Anthropic CLI** URL in `shared/live-sources.md`.

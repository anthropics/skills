# Agora CLI Automation and Machine-Readable Use

Verified against Agora CLI `0.1.3`.

## Rule for Agents

If an agent or script needs to consume CLI output, prefer an explicitly machine-readable form:

```bash
agora ... --json
```

For project environment values, prefer:

```bash
agora project env --json
```

Do not tell agents to parse pretty output unless the user explicitly wants human-readable terminal text.

## Output Modes

Verified in `0.1.3`:

- default output mode: `pretty`
- one-shot override: `--json`
- persistent default: `agora config update --output json`

`agora project env` is special:

- it prints the selected export format directly
- `--json` and `--format json` return raw env JSON, not the normal CLI envelope
- `--shell` returns `export ...` lines for direct `eval`

Useful commands:

```bash
agora config path
agora config get
agora config update --output json
agora project env --json
eval "$(agora project env --shell)"
```

## Persisted Defaults

The example config for `0.1.3` includes these persisted defaults:

- `output`
- `apiBaseUrl`
- `oauthBaseUrl`
- `oauthClientId`
- `oauthScope`
- `telemetryEnabled`
- `browserAutoOpen`
- `logLevel`
- `verbose`

## Local Isolation

For local testing, isolated automation, or CI-style runs, use:

```bash
AGORA_HOME=/custom/path
```

This moves the CLI's local state away from the default config directory.

## Suggested Agent Pattern

Use this order:

```bash
agora login
agora project use <project>
agora project env --json
agora project doctor --json
```

If the agent needs to materialize an env file into the repo:

```bash
agora project env write
```

If the agent needs to inspect defaults first:

```bash
agora config get --json
```

If the agent needs project metadata beyond the env contract:

```bash
agora project show --json
```

## Things Not to Promise

- Do not claim pretty output is a stable API.
- Do not recommend `agora project show --json` as the primary env-export workflow when `agora project env` is available.
- Do not claim hidden env vars beyond the documented config directory override and public config commands unless you have verified them for the user's version.

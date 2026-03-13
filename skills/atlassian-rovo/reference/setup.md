# Setup Guide — ACLI + REST API

How to connect your AI coding agent to Jira + Confluence using the Atlassian CLI (ACLI) for Jira and the Confluence REST API via curl.

## Prerequisites

- **Atlassian Cloud site** with both Jira and Confluence (e.g., `https://yoursite.atlassian.net`)
- **Homebrew** (macOS) for installing ACLI
- **curl** (pre-installed on macOS/Linux)
- **Atlassian API token** (generated in Step 3)

## Step 1: Install ACLI

```bash
brew tap atlassian/homebrew-acli
brew install acli
```

Verify the installation:

```bash
acli --version
```

## Step 2: Generate an API Token

1. Go to [Atlassian API Token Management](https://id.atlassian.com/manage-profile/security/api-tokens)
2. Click **Create API token**
3. Give it a label (e.g., `ai-agent`)
4. Copy the token — you won't be able to see it again

## Step 3: Configure `.env`

Create a `.env` file in your project root (add it to `.gitignore`):

```bash
ATLASSIAN_EMAIL="you@example.com"
ATLASSIAN_API_TOKEN="your-api-token-here"
ATLASSIAN_SITE="https://yoursite.atlassian.net"
```

> **Variable names:** The skill expects exactly these three variable names. If your project's `.env` uses different names (e.g., `ATLASSIAN_BASE_URL`), either rename them or add aliases so both work.

For Claude Code, source this file before running commands. Other agents can set these as environment variables in their own configuration.

## Step 4: Authenticate ACLI

Source your `.env` and log in:

```bash
source .env
# ACLI expects the bare domain (e.g., mysite.atlassian.net), not the full URL.
# Strip the https:// prefix if your ATLASSIAN_SITE includes it:
ACLI_SITE="${ATLASSIAN_SITE#https://}"
acli jira auth login \
  --site "$ACLI_SITE" \
  --email "$ATLASSIAN_EMAIL" \
  --token < <(echo "$ATLASSIAN_API_TOKEN")
```

> **Note:** The pipe syntax from the ACLI docs (`echo "$TOKEN" | acli ... --token -`) doesn't work reliably. Use process substitution (`< <(echo ...)`) instead.

## Step 5: Verify Connection

### Test Jira

```bash
# List recent issues in your project
acli jira workitem search --jql "project = YOUR_PROJECT_KEY ORDER BY created DESC" --limit 5
```

### Test Confluence

```bash
# Search for pages using the REST API
source .env
curl -s -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  "$ATLASSIAN_SITE/wiki/rest/api/content?limit=5&type=page" \
  | python3 -m json.tool | head -20
```

If both commands return results, your setup is working.

## Step 6: Project Config (Optional)

For Claude Code, add to your project's `CLAUDE.md` to set defaults:

```markdown
## Atlassian ACLI + REST API

- **MUST** use Jira project key = `{YOUR_PROJECT_KEY}`
- **MUST** use site = `{YOUR_SITE}.atlassian.net`
- **MUST** use `--limit 10` for all Jira list operations
- **MUST** use `limit=10` query param for all Confluence REST API calls
```

To find your values:
- **Project key**: Visit your Jira board — the key is the prefix on tickets (e.g., `PROJ` in `PROJ-123`)
- **Site URL**: Your Atlassian URL (e.g., `https://myteam.atlassian.net`)

## Troubleshooting

### `acli: command not found`
ACLI isn't installed or not on your PATH. Re-run `brew install acli` and ensure `/opt/homebrew/bin` is in your PATH.

### `401 Unauthorized` from curl
Your API token or email is incorrect. Verify:
```bash
source .env
curl -s -u "$ATLASSIAN_EMAIL:$ATLASSIAN_API_TOKEN" \
  "$ATLASSIAN_SITE/wiki/rest/api/user/current" | python3 -m json.tool
```

### ACLI login fails with "invalid credentials"
- Confirm the email matches your Atlassian account (not a Google alias)
- Confirm the API token was copied correctly (no trailing whitespace)
- Regenerate the token if in doubt

### `403 Forbidden` on Confluence REST calls
Your API token may lack the necessary scopes. Ensure the Atlassian account has read/write access to the target Confluence space.

### ACLI authenticated but can't find project
- Verify the project key is correct: `acli jira project list`
- Ensure the authenticated user has access to the project

### Agent-Specific Notes

- **Claude Code**: Source `.env` in your shell or add `source .env` to your workflow scripts. Claude Code can read `.env` files directly.
- **Cursor / Cline / Windsurf**: Set `ATLASSIAN_EMAIL`, `ATLASSIAN_API_TOKEN`, and `ATLASSIAN_SITE` as environment variables in your agent's configuration.
- **CI/CD**: Store credentials as pipeline secrets and export them as environment variables.
- **Subshell environments**: In agentic contexts where each shell command runs in a new subprocess, credentials from `source .env` don't persist. Combine sourcing and execution in one command: `bash -c 'set -a; source .env; set +a; <your command>'`.

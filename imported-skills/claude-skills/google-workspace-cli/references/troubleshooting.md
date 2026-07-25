# Google Workspace CLI Troubleshooting

Common errors, fixes, and platform-specific guidance for the `gws` CLI ([github.com/googleworkspace/cli](https://github.com/googleworkspace/cli)).

> **Verify against your installed version.** `gws` is pre-v1.0 and generates its command surface dynamically from Google's Discovery Service. Confirm any `gws` command below with `gws --help` / `gws auth --help` before relying on it.

---

## Installation Issues

### gws not found on PATH

**Error:** `command not found: gws`

**Fixes:**
```bash
# Check if installed
npm list -g @googleworkspace/cli 2>/dev/null || echo "Not installed via npm"
which gws || echo "Not on PATH"

# Install via npm
npm install -g @googleworkspace/cli

# If npm global bin not on PATH
export PATH="$(npm config get prefix)/bin:$PATH"
# Add to ~/.zshrc or ~/.bashrc for persistence
```

### npm permission errors

**Error:** `EACCES: permission denied`

**Fixes:**
```bash
# Option 1: Fix npm prefix (recommended)
mkdir -p ~/.npm-global
npm config set prefix '~/.npm-global'
export PATH=~/.npm-global/bin:$PATH

# Option 2: Use npx without installing
npx @googleworkspace/cli --version
```

### Cargo build failures

**Error:** `error[E0463]: can't find crate`

**Fixes:**
```bash
# Ensure Rust is up to date
rustup update stable

# Clean build
cargo clean && cargo install --git https://github.com/googleworkspace/cli --locked
```

---

## Authentication Errors

### Token expired

**Error:** `401 Unauthorized: Token has been expired or revoked`

**Cause:** OAuth tokens expire after 1 hour.

**Fix:**
```bash
gws auth login   # Re-authenticate (see: gws auth --help)
# If that fails, redo setup:
gws auth setup
```

### Insufficient scopes

**Error:** `403 Forbidden: Request had insufficient authentication scopes`

**Fix:**
```bash
# Re-auth requesting the scopes you need
gws auth login -s gmail,drive,calendar,sheets,tasks

# Or list required scopes for a service
python3 scripts/auth_setup_guide.py --scopes gmail,drive
```

### Keyring/keychain errors

**Error:** `Failed to access keyring` or `SecKeychainFindGenericPassword failed`

**Fixes:**
```bash
# macOS: Unlock keychain
security unlock-keychain ~/Library/Keychains/login.keychain-db

# Linux: Install keyring backend
sudo apt install gnome-keyring  # or libsecret

# Fallback: Use file-based token storage
export GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE=/path/to/credentials.json  # from: gws auth export --unmasked
gws auth setup
```

### Service account delegation errors

**Error:** `403: Not Authorized to access this resource/api`

**Fix:**
1. Verify domain-wide delegation is enabled on the service account
2. Verify client ID is authorized in Admin Console > Security > API Controls
3. Verify scopes match exactly (no trailing slashes)
4. Verify the delegated user is a valid admin account

```bash
# Debug — confirm how your gws version configures service accounts first:
gws auth --help
echo $GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE  # Should point to valid credentials JSON
```

---

## API Errors

### Rate limit exceeded (429)

**Error:** `429 Too Many Requests: Rate Limit Exceeded`

**Cause:** Google Workspace APIs have per-user, per-service rate limits.

**Fix:**
```bash
# Add delays between bulk operations
for id in $(cat file_ids.txt); do
    gws drive files get $id --json >> results.json
    sleep 0.5  # 500ms delay
done

# Use --limit to reduce result size
gws drive files list --limit 100 --json

# For admin operations, batch in groups of 50
```

**Rate limits by service:**
| Service | Limit |
|---------|-------|
| Gmail | 250 quota units/second/user |
| Drive | 1,000 requests/100 seconds/user |
| Sheets | 60 read requests/minute/user |
| Calendar | 500 requests/100 seconds/user |
| Admin SDK | 2,400 requests/minute |

### Permission denied (403)

**Error:** `403 Forbidden: The caller does not have permission`

**Causes and fixes:**
1. **Wrong scope** — Re-auth with correct scopes
2. **Not the file owner** — Request access from the owner
3. **Domain policy** — Check Admin Console sharing policies
4. **API not enabled** — Enable the API in Google Cloud Console

```bash
# Check which APIs are enabled
gws schema --list

# Enable an API
# Go to: console.cloud.google.com > APIs & Services > Library
```

### Not found (404)

**Error:** `404 Not Found: File not found`

**Causes:**
1. File was deleted or moved to trash
2. File ID is incorrect
3. No permission to see the file

```bash
# Check trash
gws drive files list --query "trashed=true and name='filename'" --json

# Verify file ID
gws drive files get <fileId> --json
```

---

## Output Parsing Issues

### NDJSON vs JSON array

**Problem:** Output format varies between commands and versions.

```bash
# Force JSON array output
gws drive files list --json

# Force NDJSON output
gws drive files list --format ndjson

# Handle both in output_analyzer.py (automatic detection)
gws drive files list --json | python3 scripts/output_analyzer.py --count
```

### Pagination

**Problem:** Only partial results returned.

```bash
# Fetch all pages
gws drive files list --page-all --json

# Or set a high limit
gws drive files list --limit 1000 --json

# Check if more pages exist (look for nextPageToken in output)
gws drive files list --params '{"pageSize": 100}' | grep nextPageToken
```

### Empty response

**Problem:** Command returns empty or `{}`.

```bash
# Check auth (see: gws auth --help for your version's status command)
gws auth login

# Enable debug logging
GOOGLE_WORKSPACE_CLI_LOG=debug gws drive files list --params '{"pageSize": 1}'

# Check if the service is accessible (verify: gws schema drive.about.get)
gws drive about get --params '{"fields": "*"}'
```

---

## Platform-Specific Issues

### macOS

**Keychain access prompts:**
```bash
# Allow gws to access keychain without repeated prompts
# In Keychain Access.app, find "gws" entries and set "Allow all applications"

# Or use file-based storage
export GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE=/path/to/credentials.json  # from: gws auth export --unmasked
```

**Browser not opening for OAuth:**
```bash
# If default browser doesn't open
gws auth setup --no-browser
# Copy the URL manually and paste in browser
```

### Linux

**Headless OAuth (no browser):**
```bash
# Use out-of-band flow
gws auth setup --no-browser
# Prints a URL — open on another machine, paste code back

# Or export credentials from an interactive machine (documented headless flow)
gws auth export --unmasked > credentials.json
export GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE=/path/to/credentials.json
```

**Missing keyring backend:**
```bash
# Install a keyring backend
sudo apt install gnome-keyring libsecret-1-dev

# Or use file-based storage
export GOOGLE_WORKSPACE_CLI_CREDENTIALS_FILE=/path/to/credentials.json  # from: gws auth export --unmasked
```

### Windows

**PATH issues:**
```powershell
# Add npm global bin to PATH
$env:PATH += ";$(npm config get prefix)\bin"

# Or use npx
npx @googleworkspace/cli --version
```

**PowerShell quoting:**
```powershell
# Use single quotes for JSON arguments
gws gmail users.settings.filters create me `
  --criteria '{"from":"test@example.com"}' `
  --action '{"addLabelIds":["Label_1"]}'
```

---

## Getting Help

```bash
# General help
gws --help
gws <service> --help
gws <service> <resource> --help

# API schema for a method
gws schema gmail.users.messages.send

# Version info
gws --version

# Debug mode
gws --verbose <command>

# Report issues
# https://github.com/googleworkspace/cli/issues
```
